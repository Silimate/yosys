/*
 * yosys -- Yosys Open SYnthesis Suite
 *
 * Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 * 2026  Abhinav Tondapu <abhinav@silimate.com>
 *
 * Permission to use, copy, modify, and/or distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

 #include "kernel/register.h"
 #include "kernel/sigtools.h"
 #include "kernel/log.h"
 #include "kernel/celltypes.h"
 #include <cstdint>
 #include <stdlib.h>
 #include <algorithm>
 #include <limits>
 #include <queue>
 #include <stdexcept>
 #include <vector>
 
 USING_YOSYS_NAMESPACE
 PRIVATE_NAMESPACE_BEGIN

// ============================================================================
// Tuning Parameters & Constants
// ============================================================================

/*
 * ECONOMIC MODEL EXPLANATION:
 * This pass decides whether to push a Mux through an Operator based on a
 * Cost (Debt) vs. Benefit (Credit) analysis.
 *
 * - DEBT (Cost): Represents the area penalty. Pushing a Mux through an Op
 * usually requires duplicating the Op (one for Mux-A input, one for Mux-B).
 * Debt is proportional to the size/complexity of the logic cone feeding the Mux.
 *
 * - CREDIT (Benefit): Represents the timing/area gain.
 * 1. Arithmetic Credit: Reducing the logic depth (moving Mux off critical path).
 * 2. Mux Credit: Eliminating the Mux entirely (if constant folding happens).
 *
 * - RATIO: We perform the transform if Debt <= Credit * Ratio.
 */

static constexpr int kMaxLeafRecursionDepth = 1024;
static constexpr int kMaxDownstreamRecursionDepth = 1024;
static constexpr int64_t kMinComponentBudget = 1024;
static constexpr int64_t kComponentBudgetDivisor = 8;

struct RationalScale {
  uint64_t num;
  uint64_t den;
};
// Internal structural mux credit weight: 1/2 of operator width
static constexpr RationalScale kMuxCreditScale = {1, 2};

// ============================================================================
// Mathematical Helpers (Saturating Arithmetic)
// ============================================================================

// We use saturating arithmetic to prevent cost/score overflows.
// If a logic cone is "infinitely" complex (max uint64), we stop traversing
// and assume it's too expensive to duplicate.

struct SatMath {
    static constexpr uint64_t MAX_U64 = std::numeric_limits<uint64_t>::max();
    static constexpr int64_t MAX_I64 = std::numeric_limits<int64_t>::max();
    static constexpr int64_t MIN_I64 = std::numeric_limits<int64_t>::min();

    static uint64_t add(uint64_t a, uint64_t b) {
        return (a > MAX_U64 - b) ? MAX_U64 : a + b;
    }

    static uint64_t mul(uint64_t a, uint64_t b) {
        if (a == 0 || b == 0) return 0;
        return (a > MAX_U64 / b) ? MAX_U64 : a * b;
    }

    static int64_t from_u64(uint64_t value) {
        return (value > static_cast<uint64_t>(MAX_I64)) ? MAX_I64 : static_cast<int64_t>(value);
    }

    static int64_t add_i64(int64_t a, int64_t b) {
        if (b > 0 && a > MAX_I64 - b) return MAX_I64;
        if (b < 0 && a < MIN_I64 - b) return MIN_I64;
        return a + b;
    }

    static int64_t sub_i64(int64_t a, int64_t b) {
        if (b == MIN_I64) return (a >= 0) ? MAX_I64 : a - b;
        return add_i64(a, -b);
    }

    static uint64_t ceil_log2(uint64_t x) {
        if (x <= 1) return 0;
        return 64u - static_cast<uint64_t>(__builtin_clzll(x - 1));
    }
};

// ============================================================================
// Transparency & Netlist Helpers
// ============================================================================

struct TransparencyHelper {
    static bool is_transparent(RTLIL::Cell *cell) {
        if (cell == nullptr) return false;
        static const pool<IdString> transparent_types = {
            ID($slice), ID($pos), ID($buf), ID($signed), ID($unsigned), ID($concat)
        };
        return transparent_types.count(cell->type);
    }

    // Enumerate the dataflow mapping from output Y bit index -> input bit.
    //
    // This allows the algorithm to "see through" bit-shuffling cells
    // (like $slice, $concat, $buf) as if they were wires. This ensures we
    // don't stop optimization just because a signal changes names or gets
    // sliced before hitting an operator.
    template <typename Fn>
    static void enumerate_input_bits(SigMap &sigmap, RTLIL::Cell *cell, Fn &&fn) {
        if (cell == nullptr || !cell->hasPort(ID::Y)) return;

        RTLIL::SigSpec y = sigmap(cell->getPort(ID::Y));
        if (y.empty()) return;

        if (cell->type == ID($concat)) {
            RTLIL::SigSpec a = cell->hasPort(ID::A) ? sigmap(cell->getPort(ID::A)) : RTLIL::SigSpec();
            RTLIL::SigSpec b = cell->hasPort(ID::B) ? sigmap(cell->getPort(ID::B)) : RTLIL::SigSpec();
            int bw = GetSize(b);
            int y_size = GetSize(y);
            int a_size = GetSize(a);

            for (int yi = 0; yi < y_size; yi++) {
                if (yi < bw) {
                    fn(yi, ID::B, b[yi]);
                } else {
                    int ai = yi - bw;
                    if (ai >= 0 && ai < a_size) fn(yi, ID::A, a[ai]);
                }
            }
        } else if (cell->type == ID($slice)) {
            RTLIL::SigSpec a = cell->hasPort(ID::A) ? sigmap(cell->getPort(ID::A)) : RTLIL::SigSpec();
            int offset = cell->hasParam(ID::OFFSET) ? cell->getParam(ID::OFFSET).as_int() : 0;
            int a_size = GetSize(a);

            for (int yi = 0; yi < GetSize(y); yi++) {
                int ai = yi + offset;
                if (ai >= 0 && ai < a_size) fn(yi, ID::A, a[ai]);
            }
        } else if (cell->hasPort(ID::A)) {
            RTLIL::SigSpec a = sigmap(cell->getPort(ID::A));
            int n = std::min(GetSize(a), GetSize(y));
            for (int yi = 0; yi < n; yi++) fn(yi, ID::A, a[yi]);
        }
    }

    // For transparent wrappers, derive only the input subset that contributes
    // to a selected set of output Y bit indices.
    static std::vector<RTLIL::SigSpec> transparent_selected_inputs(SigMap &sigmap, RTLIL::Cell *drv, const std::vector<int> &y_sel)
    {
        std::vector<RTLIL::SigSpec> inputs;
        if (drv == nullptr) return inputs;

        pool<int> wanted;
        for (int yi : y_sel) wanted.insert(yi);

        if (drv->type == ID($concat)) {
            RTLIL::SigSpec sel_a, sel_b;
            enumerate_input_bits(sigmap, drv, [&](int yi, IdString port, const SigBit &bit) {
                if (!wanted.count(yi)) return;
                if (port == ID::A) sel_a.append(bit);
                else if (port == ID::B) sel_b.append(bit);
            });
            if (!sel_a.empty()) inputs.push_back(sel_a);
            if (!sel_b.empty()) inputs.push_back(sel_b);
            return inputs;
        }

        RTLIL::SigSpec sel_a;
        enumerate_input_bits(sigmap, drv, [&](int yi, IdString port, const SigBit &bit) {
            if (port == ID::A && wanted.count(yi)) sel_a.append(bit);
        });
        if (!sel_a.empty()) inputs.push_back(sel_a);
        return inputs;
    }

    // Propagate traced input bits through transparent wrappers to produce the
    // exact traced subset at the wrapper output.
    static RTLIL::SigSpec transparent_traced_output(SigMap &sigmap, RTLIL::Cell *cell, const pool<SigBit> &traced_inputs)
    {
        RTLIL::SigSpec traced_y;
        if (cell == nullptr || !cell->hasPort(ID::Y)) return traced_y;

        RTLIL::SigSpec y = sigmap(cell->getPort(ID::Y));
        if (y.empty()) return traced_y;

        enumerate_input_bits(sigmap, cell, [&](int yi, IdString, const SigBit &bit) {
            if (yi >= 0 && yi < GetSize(y) && bit.wire != nullptr && traced_inputs.count(bit))
                traced_y.append(y[yi]);
        });
        return traced_y;
    }
};

// ============================================================================
// Budget Management
// ============================================================================

struct BudgetState {
    int64_t module_limit = 0;
    int64_t component_limit = 0;
    int64_t module_remaining = 0;
    int64_t component_remaining = 0;
    bool module_exhausted = false;
    bool component_exhausted = false;

    explicit BudgetState(int64_t limit = 0) {
        module_limit = limit;
        component_limit = limit > 0 ? std::max<int64_t>(kMinComponentBudget, limit / kComponentBudgetDivisor) : 0;
        module_remaining = limit;
        component_remaining = component_limit;
    }

    bool consume(int64_t cost = 1) {
        if (module_limit <= 0) return true;
        if (cost < 0) cost = 0;

        module_remaining -= cost;
        if (component_limit > 0) component_remaining -= cost;

        if (module_remaining < 0) module_exhausted = true;
        if (component_limit > 0 && component_remaining < 0) component_exhausted = true;

        return !is_exhausted();
    }

    void reset_component() {
        component_exhausted = false;
        component_remaining = component_limit;
    }

    bool is_exhausted() const { return module_exhausted || component_exhausted; }

    const char *exhaust_reason() const {
        if (module_exhausted) return "module budget exhausted";
        return component_exhausted ? "component budget exhausted" : "budget ok";
    }
};

// ============================================================================
// Connectivity Database
// ============================================================================

using ConnectionList = std::vector<std::pair<IdString, RTLIL::SigSpec>>;

class ConnectivityDB {
public:
    dict<SigBit, RTLIL::Cell*> driver_map;
    dict<SigBit, int> fanout_map;
    dict<SigBit, pool<RTLIL::Cell*>> user_map;
    dict<SigBit, pool<RTLIL::Cell*>> bit_drivers;
    pool<SigBit> port_output_bits;
    
    // Caches
    dict<RTLIL::Cell*, pool<SigBit>> cached_input_bits;
    dict<RTLIL::Cell*, pool<SigBit>> cached_output_bits;
    dict<RTLIL::Cell*, ConnectionList> sorted_conns_cache;

    RTLIL::Design *design;
    RTLIL::Module *module;
    SigMap &sigmap;
    CellTypes &ct;

    ConnectivityDB(RTLIL::Design *d, RTLIL::Module *m, SigMap &sm, CellTypes &c) 
        : design(d), module(m), sigmap(sm), ct(c) {}

    void clear() {
        driver_map.clear();
        fanout_map.clear();
        user_map.clear();
        bit_drivers.clear();
        cached_input_bits.clear();
        cached_output_bits.clear();
        sorted_conns_cache.clear();
        port_output_bits.clear();
    }

    // Build connectivity for the whole module
    void build_connectivity() {
        clear();

        for (auto cell : module->cells())
            add_cell(cell);

        for (auto wire : module->wires()) {
            if (!wire->port_output) continue;
            RTLIL::SigSpec sig = sigmap(RTLIL::SigSpec(wire));
            for (auto &bit : sig) {
                if (bit.wire == nullptr) continue;
                fanout_map[bit]++;
                port_output_bits.insert(bit);
            }
        }
    }

    /*
     * Cache a stable per-cell connection ordering so traversal and ROI
     * decisions are deterministic across runs.
     * Yosys internal storage (dict/pool) iteration order can vary
     * by pointer address or platform so we sort connections by port ID
     * to ensure the optimization pass behaves exactly the same way every time.
    */
    const ConnectionList &get_sorted_connections(RTLIL::Cell *cell) {
        auto it = sorted_conns_cache.find(cell);
        if (it != sorted_conns_cache.end()) return it->second;

        ConnectionList conns;
        conns.reserve(cell->connections().size());
        for (auto &conn : cell->connections()) conns.push_back(conn);
        
        std::sort(conns.begin(), conns.end(), [](const std::pair<IdString, RTLIL::SigSpec> &a,
                                                const std::pair<IdString, RTLIL::SigSpec> &b) {
            return a.first < b.first;
        });
        
        return sorted_conns_cache[cell] = std::move(conns);
    }

    void add_cell(RTLIL::Cell *cell) {
        sorted_conns_cache.erase(cell);
        pool<SigBit> in_bits, out_bits;
        collect_cell_bits(cell, in_bits, out_bits);

        cached_input_bits[cell] = in_bits;
        cached_output_bits[cell] = out_bits;

        for (auto &bit : in_bits) {
            fanout_map[bit]++;
            user_map[bit].insert(cell);
        }
        for (auto &bit : out_bits) {
            bit_drivers[bit].insert(cell);
            refresh_driver_entry(bit);
        }
    }

    void remove_cell(RTLIL::Cell *cell) {
        sorted_conns_cache.erase(cell);

        auto it_in = cached_input_bits.find(cell);
        if (it_in != cached_input_bits.end()) {
            for (auto &bit : it_in->second) {
                if (--fanout_map[bit] <= 0) fanout_map.erase(bit);
                auto uit = user_map.find(bit);
                if (uit != user_map.end()) {
                    uit->second.erase(cell);
                    if (uit->second.empty()) user_map.erase(bit);
                }
            }
            cached_input_bits.erase(cell);
        }

        auto it_out = cached_output_bits.find(cell);
        if (it_out != cached_output_bits.end()) {
            for (auto &bit : it_out->second) {
                auto dit = bit_drivers.find(bit);
                if (dit != bit_drivers.end()) {
                    dit->second.erase(cell);
                    if (dit->second.empty()) bit_drivers.erase(bit);
                }
                refresh_driver_entry(bit);
            }
            cached_output_bits.erase(cell);
        }
    }

    bool is_opaque(RTLIL::Cell *cell) const {
        if (cell == nullptr) return true;
        if (!ct.cell_known(cell->type)) return true;
        auto mod = design->module(cell->type);
        return mod && mod->get_bool_attribute(ID::blackbox);
    }

    bool sig_has_opaque_driver(const RTLIL::SigSpec &sig) const {
        for (auto &bit : sig) {
            if (bit.wire == nullptr) continue;
            auto it_drv = driver_map.find(bit);
            if (it_drv == driver_map.end()) continue; 
            if (is_opaque(it_drv->second)) return true;
        }
        return false;
    }

    bool get_unique_driver(const RTLIL::SigSpec &sig, RTLIL::Cell *&drv_cell) {
        drv_cell = nullptr;
        for (auto &bit : sig) {
            if (bit.wire == nullptr) return false;
            auto it_drv = driver_map.find(bit);
            if (it_drv == driver_map.end() || it_drv->second == nullptr) return false;
            if (drv_cell == nullptr) drv_cell = it_drv->second;
            else if (drv_cell != it_drv->second) return false;
        }
        return drv_cell != nullptr;
    }

private:
    void refresh_driver_entry(const SigBit &bit) {
        auto it = bit_drivers.find(bit);
        if (it == bit_drivers.end() || it->second.empty()) {
            driver_map.erase(bit);
        } else if (it->second.size() == 1) {
            driver_map[bit] = *it->second.begin();
        } else {
            driver_map[bit] = nullptr;
        }
    }

    void collect_cell_bits(RTLIL::Cell *cell, pool<SigBit> &in_bits, pool<SigBit> &out_bits) {
        in_bits.clear();
        out_bits.clear();
        for (auto &it : cell->connections()) {
            RTLIL::SigSpec sig = sigmap(it.second);
            if (cell->input(it.first)) {
                for (auto &bit : sig) if (bit.wire) in_bits.insert(bit);
            }
            if (cell->output(it.first)) {
                for (auto &bit : sig) if (bit.wire) out_bits.insert(bit);
            }
        }
    }
};

// ============================================================================
// Main Optimization Worker
// ============================================================================

struct OptMuxPushWorker
{
    // Candidate rewrite site: push one mux through one operator input
    struct Candidate {
        int id = -1;
        RTLIL::Cell *op = nullptr;
        RTLIL::Cell *mux = nullptr;
        IdString port;
        RTLIL::SigSpec op_out;
        int width = 0;

        std::vector<int> succ;
        std::vector<int> pred;
        std::vector<int> peer_same_mux;

        int component = -1;
        bool blocked = false;
        std::string blocked_reason;
        bool approved = false;
        bool bridge_ok = false;

        uint64_t up_ops = 1;       // Complexity of logic feeding the mux (Upstream)
        uint64_t down_ops = 1;     // Complexity of logic consuming the op (Downstream)
        uint64_t multiplicity = 1; // Estimated number of times this Op will be duplicated
        
        uint64_t credit_arith = 0; // Score for reducing logic levels
        uint64_t credit_mux = 0;   // Score for removing/absorbing the mux
        uint64_t credit = 0;       // Total Benefit
        uint64_t debt = 0;         // Total Cost (Area/Complexity)

        // Static helper to reset analysis state
        static void reset_candidate_scores(Candidate &cand, uint64_t debt) {
            cand.credit_arith = 0;
            cand.credit_mux = 0;
            cand.credit = 0;
            cand.debt = debt;
            cand.bridge_ok = false;
        }

        // Static helper to reset analysis state
        static void reset_candidate_analysis(Candidate &cand) {
            cand.up_ops = 1;
            cand.down_ops = 1;
            cand.multiplicity = 1;
            reset_candidate_scores(cand, 0);
        }
    };

    struct LocalPolicyEval {
        bool ribbon_node = false;
        bool local_arith_ok = false;
        bool local_struct_ok = false;
        bool eligible = false;
    };

    struct ComponentStats {
        bool blocked = false;
        bool ineligible = false;
        bool ribbon_only = true;
        int ineligible_count = 0;
        uint64_t raw_credit_arith = 0;
        uint64_t raw_credit = 0;
        uint64_t raw_debt = 0;
        uint64_t credit_arith = 0;
        uint64_t credit = 0;
        uint64_t debt = 0;
    };

    // Traversal state passed through recursive counting. This keeps recursive
    // signatures stable while allowing component-aware "see-through mux wall"
    // logic only when requested.
    struct TraversalContext {
        const std::vector<Candidate> *candidates = nullptr;
        const dict<RTLIL::Cell*, std::vector<int>> *mux_map = nullptr;
        bool component_mode = false;
        int component_id = -1;
        int current_depth = 0;
    };

    RTLIL::Design *design;
    RTLIL::Module *module;
    SigMap sigmap;
    CellTypes ct;
    ConnectivityDB conn;

    pool<IdString> target_types;
    int fanout_limit;
    double ratio;
    BudgetState budget;
    int total_count;
    bool leaf_depth_limit_hit;
    bool downstream_depth_limit_hit;

    // Helper for scaling credits
    static uint64_t apply_rational_scale_ceil(uint64_t value, const RationalScale &scale)
    {
        if (value == 0 || scale.num == 0) return 0;
        uint64_t numer = SatMath::mul(value, scale.num);
        return std::max<uint64_t>(1, (numer + scale.den - 1) / scale.den);
    }

    OptMuxPushWorker(RTLIL::Design *design, RTLIL::Module *module,
        const pool<IdString> &target_types, int fanout_limit, double ratio, int64_t budget_limit) :
        design(design), module(module), sigmap(module), ct(design), conn(design, module, sigmap, ct),
        target_types(target_types), fanout_limit(fanout_limit), ratio(ratio),
        budget(budget_limit), total_count(0),
        leaf_depth_limit_hit(false), downstream_depth_limit_hit(false)
    {}

    // ---------- Analysis Logic ----------

    static bool roi_allows(uint64_t debt, uint64_t credit, double ratio) {
        return credit > 0 && double(debt) <= double(credit) * ratio;
    }

    double effective_ratio() const {
        return fanout_limit > 1 ? std::min(ratio, 1.0) : ratio;
    }

    LocalPolicyEval evaluate_local_policy(const Candidate &cand, const std::vector<Candidate> &candidates, double ratio_eff) const
    {
        LocalPolicyEval eval;
        if (cand.blocked) return eval;

        eval.ribbon_node = is_ribbon_topology(cand, candidates);
        eval.local_arith_ok = roi_allows(cand.debt, cand.credit_arith, ratio_eff);

        // Structural-only credit is intentionally constrained: with wide fanout
        // configurations we require some arithmetic credit to avoid over-pushing
        // area-expensive mux-only transforms.
        bool structural_gate = fanout_limit == 1 || cand.credit_arith > 0;
        if (eval.ribbon_node && structural_gate)
            eval.local_struct_ok = roi_allows(cand.debt, cand.credit, ratio_eff);

        eval.eligible = eval.local_arith_ok || (cand.bridge_ok && eval.local_struct_ok) || eval.local_struct_ok;
        return eval;
    }

    /* A "ribbon" is a strictly serial chain neighborhood (<=1 pred/succ and
     * neighbors also serial).
     * In a complex branching DAG, pushing a mux might explode area.
     * area. In a "ribbon" (a straight line of logic), the cost is predictable.
     * We allow riskier moves (lower ROI) inside ribbons because they usually
     * resolve cleanly.
     */
    static bool is_ribbon_topology(const Candidate &cand, const std::vector<Candidate> &candidates)
    {
        if (cand.pred.size() > 1 || cand.succ.size() > 1) return false;
        for (int pred_id : cand.pred) if (candidates.at(pred_id).succ.size() != 1) return false;
        for (int succ_id : cand.succ) if (candidates.at(succ_id).pred.size() != 1) return false;
        return true;
    }

    ComponentStats collect_component_stats(const std::vector<int> &ids, const std::vector<Candidate> &candidates, const std::vector<LocalPolicyEval> &eval_cache) const
    {
        ComponentStats stats;
        for (int id : ids) {
            const auto &cand = candidates.at(id);
            const auto &eval = eval_cache.at(id);
            
            stats.raw_credit_arith = SatMath::add(stats.raw_credit_arith, cand.credit_arith);
            stats.raw_credit = SatMath::add(stats.raw_credit, cand.credit);
            stats.raw_debt = SatMath::add(stats.raw_debt, cand.debt);
            
            if (cand.blocked) stats.blocked = true;
            if (!eval.eligible) {
                stats.ineligible = true;
                stats.ineligible_count++;
                continue;
            }
            if (!eval.ribbon_node) stats.ribbon_only = false;
            
            stats.credit_arith = SatMath::add(stats.credit_arith, cand.credit_arith);
            stats.credit = SatMath::add(stats.credit, cand.credit);
            stats.debt = SatMath::add(stats.debt, cand.debt);
        }
        return stats;
    }

    bool component_accepts(const ComponentStats &stats, double ratio_eff, bool &accept_global_arith) const
    {
        accept_global_arith = false;
        if (stats.blocked) return false;

        bool accept = roi_allows(stats.debt, stats.credit_arith, ratio_eff);
        if (!accept && fanout_limit == 1 && roi_allows(stats.raw_debt, stats.raw_credit_arith, ratio_eff)) {
            accept = true;
            accept_global_arith = true;
        }
        if (!accept && stats.ribbon_only && (fanout_limit == 1 || stats.credit_arith > 0))
            accept = roi_allows(stats.debt, stats.credit, ratio_eff);
        return accept;
    }

    // ---------- Connectivity & Traversal ----------

    static bool sig_intersects_bits(const RTLIL::SigSpec &mapped_sig, const pool<SigBit> &bits)
    {
        for (auto &bit : mapped_sig) {
            if (bit.wire != nullptr && bits.count(bit)) return true;
        }
        return false;
    }

    bool input_consumes_signal_bits(RTLIL::Cell *cell, const ConnectionList &conns, const pool<SigBit> &mapped_bits)
    {
        for (auto &it : conns) {
            if (!cell->input(it.first)) continue;
            if (sig_intersects_bits(sigmap(it.second), mapped_bits)) return true;
        }
        return false;
    }

    bool mux_drives_sig(const RTLIL::SigSpec &sig, RTLIL::Cell *&mux_cell) {
        if (!conn.get_unique_driver(sig, mux_cell)) return false;
        return mux_cell != nullptr && mux_cell->type == ID($mux);
    }

    bool fanout_within_limit(const RTLIL::SigSpec &sig) const {
        for (auto &bit : sig) {
            if (bit.wire == nullptr) return false;
            auto it = conn.fanout_map.find(bit);
            if (it == conn.fanout_map.end() || it->second > fanout_limit) return false;
        }
        return true;
    }

    bool sig_has_live_input_users(const RTLIL::SigSpec &sig, RTLIL::Cell *ignore_driver = nullptr)
    {
        RTLIL::SigSpec mapped = sigmap(sig);
        for (auto &bit : mapped) {
            if (bit.wire == nullptr) continue;
            auto it_users = conn.user_map.find(bit);
            if (it_users != conn.user_map.end()) {
                for (auto cell : it_users->second) {
                    if (cell != ignore_driver) return true;
                }
            }
            if (conn.port_output_bits.count(bit)) return true;
        }
        return false;
    }

    // Trace selected Y indices back to specific inputs for transparent cells
    std::vector<int> selected_y_indices(RTLIL::Cell *drv, const RTLIL::SigSpec &requested_sig)
    {
        std::vector<int> indices;
        if (drv == nullptr || !drv->hasPort(ID::Y)) return indices;

        RTLIL::SigSpec req = sigmap(requested_sig);
        RTLIL::SigSpec y = sigmap(drv->getPort(ID::Y));
        pool<int> uniq;

        for (int i = 0; i < GetSize(req); i++) {
            if (req[i].wire == nullptr) continue;
            for (int j = 0; j < GetSize(y); j++) {
                if (y[j] == req[i]) {
                    uniq.insert(j);
                    break;
                }
            }
        }
        indices.assign(uniq.begin(), uniq.end());
        std::sort(indices.begin(), indices.end());
        return indices;
    }

    // ---------- Leaf Counting Recursion ----------


    /* 
     * Estimates the "weight" of the logic cone feeding a signal.
     * Returns 1 for a leaf (primary input/opaque cell), or sum of children.
     * used to calculate "Debt": complex cones are expensive to duplicate.
     */
    uint64_t count_operand_leaves_impl(const RTLIL::SigSpec &sig,
        dict<RTLIL::Cell*, uint64_t> &leaf_cache,
        pool<RTLIL::Cell*> &active_stack,
        TraversalContext &ctx)
    {
        if (ctx.current_depth > kMaxLeafRecursionDepth) {
            // Bound recursion so pathological carry chains terminate safely.
            leaf_depth_limit_hit = true;
            return 1;
        }
        if (budget.is_exhausted() || !budget.consume()) return 1;

        RTLIL::SigSpec mapped = sigmap(sig);
        RTLIL::Cell *drv = nullptr;

        if (!conn.get_unique_driver(mapped, drv)) {
            // Mixed/fragmented signal: split by bit driver and conservatively
            // aggregate complexity. Unknown/constant fragments count as 1 leaf.
            dict<RTLIL::Cell*, RTLIL::SigSpec> per_drv_sigs;
            bool has_other_leaf = false;
            for (auto &bit : mapped) {
                if (!budget.consume()) return 1;
                if (bit.wire == nullptr) { has_other_leaf = true; continue; }
                
                auto it_drv = conn.driver_map.find(bit);
                if (it_drv == conn.driver_map.end() || it_drv->second == nullptr) {
                    has_other_leaf = true; continue;
                }
                per_drv_sigs[it_drv->second].append(bit);
            }

            uint64_t total = has_other_leaf ? 1 : 0;
            ctx.current_depth++;
            for (auto &it : per_drv_sigs) {
                if (!budget.consume()) return std::max<uint64_t>(1, total);
                total = SatMath::add(total, count_operand_leaves_impl(it.second, leaf_cache, active_stack, ctx));
            }
            ctx.current_depth--;
            return std::max<uint64_t>(1, total);
        }

        if (drv == nullptr) return 1;

        bool transparent_drv = TransparencyHelper::is_transparent(drv);
        if (!transparent_drv) {
            auto it_cached = leaf_cache.find(drv);
            if (it_cached != leaf_cache.end()) return it_cached->second;
        }

        if (active_stack.count(drv)) return 1;
        active_stack.insert(drv);

        uint64_t total = 0;
        std::vector<int> y_sel = selected_y_indices(drv, mapped);
        ctx.current_depth++;

        if (ctx.component_mode && drv->type == ID($mux)) {
            // Component-mode traversal intentionally crosses candidate mux walls
            // to model the "post-push" arithmetic cone on either branch.
            bool component_mux = false;
            auto it_mux = ctx.mux_map->find(drv);
            if (it_mux != ctx.mux_map->end()) {
                for (int cand_id : it_mux->second) {
                    if (!budget.consume()) break;
                    const auto &cand = ctx.candidates->at(cand_id);
                    if (cand.component == ctx.component_id && !cand.blocked) {
                        component_mux = true;
                        break;
                    }
                }
            }
            if (component_mux) {
                uint64_t a = count_operand_leaves_impl(drv->getPort(ID::A), leaf_cache, active_stack, ctx);
                uint64_t b = count_operand_leaves_impl(drv->getPort(ID::B), leaf_cache, active_stack, ctx);
                total = std::max<uint64_t>(a, b);
            }
        } else if (transparent_drv) {
            auto selected_inputs = TransparencyHelper::transparent_selected_inputs(sigmap, drv, y_sel);
            for (auto &sel : selected_inputs) {
                if (!budget.consume()) break;
                total = SatMath::add(total, count_operand_leaves_impl(sel, leaf_cache, active_stack, ctx));
            }
        } else if (target_types.count(drv->type) && !drv->get_bool_attribute(ID::keep) && !conn.is_opaque(drv)) {
            const auto &conns = conn.get_sorted_connections(drv);
            for (auto &it : conns) {
                if (!budget.consume()) break;
                if (!drv->input(it.first)) continue;
                total = SatMath::add(total, count_operand_leaves_impl(it.second, leaf_cache, active_stack, ctx));
            }
        }

        ctx.current_depth--;
        active_stack.erase(drv);
        if (total == 0) total = 1;
        total = std::max<uint64_t>(1, total);
        if (!transparent_drv) leaf_cache[drv] = total;
        return total;
    }

    // Helper wrapper for the implementation
    uint64_t count_operand_leaves(const RTLIL::SigSpec &sig, dict<RTLIL::Cell*, uint64_t> &leaf_cache, pool<RTLIL::Cell*> &active_stack) {
        TraversalContext ctx;
        return count_operand_leaves_impl(sig, leaf_cache, active_stack, ctx);
    }

    uint64_t count_operand_leaves_component(const RTLIL::SigSpec &sig, int component_id,
        const std::vector<Candidate> &candidates, const dict<RTLIL::Cell*, std::vector<int>> &mux_map,
        dict<RTLIL::Cell*, uint64_t> &leaf_cache, pool<RTLIL::Cell*> &active_stack) 
    {
        TraversalContext ctx;
        ctx.component_mode = true;
        ctx.component_id = component_id;
        ctx.candidates = &candidates;
        ctx.mux_map = &mux_map;
        return count_operand_leaves_impl(sig, leaf_cache, active_stack, ctx);
    }

    // ---------- Downstream Analysis ----------

    /* 
     * "Lookahead" Analysis:
     * Walks forward from the Operator's output to see if pushing the Mux here
     * would enable *more* optimizations downstream.
     * If we push a Mux through an ADD, and that ADD feeds an AND, we might
     * be able to push the Mux through the AND next. This function detects that
     * potential chain reaction to increase the "Credit" score.
     */
    uint64_t count_downstream_operands(const RTLIL::SigSpec &sig, IdString op_type,
        dict<RTLIL::Cell*, uint64_t> &leaf_cache,
        pool<RTLIL::Cell*> &leaf_active_stack,
        pool<RTLIL::Cell*> &down_active_stack,
        pool<RTLIL::Cell*> &seen_assoc_users,
        const std::vector<Candidate> &candidates,
        const dict<RTLIL::Cell*, std::vector<int>> &mux_map,
        int component_id,
        pool<int> &seen_component_candidates,
        int depth)
    {
        if (depth > kMaxDownstreamRecursionDepth) {
            downstream_depth_limit_hit = true;
            return 0;
        }
        if (budget.is_exhausted() || !budget.consume()) return 0;

        RTLIL::SigSpec mapped = sigmap(sig);
        RTLIL::Cell *drv = nullptr;
        if (!conn.get_unique_driver(mapped, drv) || drv == nullptr) return 0;
        if (down_active_stack.count(drv)) return 0;
        down_active_stack.insert(drv);

        pool<SigBit> mapped_bits;
        for (auto &bit : mapped) if (bit.wire) mapped_bits.insert(bit);

        pool<RTLIL::Cell*> users;
        collect_users_for_bits(mapped_bits, users);

        uint64_t total = 0;
        for (auto user : users)
        {
            if (!budget.consume()) break;
            if (user == drv || user->get_bool_attribute(ID::keep) || conn.is_opaque(user)) continue;

            const auto &conns = conn.get_sorted_connections(user);

            if (TransparencyHelper::is_transparent(user))
            {
                bool consumes = false;
                pool<SigBit> traced_inputs;
                for (auto &it : conns) {
                    if (!user->input(it.first)) continue;
                    RTLIL::SigSpec in_mapped = sigmap(it.second);
                    if (sig_intersects_bits(in_mapped, mapped_bits)) {
                        consumes = true;
                        for (auto &bit : in_mapped) if (bit.wire && mapped_bits.count(bit)) traced_inputs.insert(bit);
                    }
                }
                if (consumes && user->hasPort(ID::Y)) {
                    RTLIL::SigSpec traced_y = TransparencyHelper::transparent_traced_output(sigmap, user, traced_inputs);
                    if (traced_y.empty()) traced_y = user->getPort(ID::Y);
                    total = SatMath::add(total, count_downstream_operands(traced_y, op_type,
                        leaf_cache, leaf_active_stack, down_active_stack, seen_assoc_users,
                        candidates, mux_map, component_id, seen_component_candidates, depth + 1));
                }
                continue;
            }

            if (user->type == ID($mux))
            {
                // Crossing a downstream candidate mux lets us continue through
                // the operator on the other side, accounting for chain effects.
                if (!input_consumes_signal_bits(user, conns, mapped_bits)) continue;
                auto it_mux = mux_map.find(user);
                if (it_mux == mux_map.end()) continue;

                for (int cand_id : it_mux->second) {
                    if (!budget.consume()) break;
                    if (seen_component_candidates.count(cand_id)) continue;
                    
                    auto &cand = candidates.at(cand_id);
                    if (cand.component != component_id || cand.blocked) continue;
                    if (cand.op == nullptr || cand.op->type != op_type) continue;
                    
                    seen_component_candidates.insert(cand_id);
                    if (seen_assoc_users.count(cand.op)) continue;
                    seen_assoc_users.insert(cand.op);

                    const auto &op_conns = conn.get_sorted_connections(cand.op);
                    for (auto &it : op_conns) {
                        if (!cand.op->input(it.first) || it.first == cand.port) continue;
                        total = SatMath::add(total, count_operand_leaves(it.second, leaf_cache, leaf_active_stack));
                    }
                    if (!cand.op_out.empty()) {
                        total = SatMath::add(total, count_downstream_operands(cand.op_out, op_type,
                            leaf_cache, leaf_active_stack, down_active_stack, seen_assoc_users,
                            candidates, mux_map, component_id, seen_component_candidates, depth + 1));
                    }
                }
                continue;
            }

            if (user->type != op_type) continue;
            if (seen_assoc_users.count(user)) continue;
            seen_assoc_users.insert(user);

            bool consumes = false;
            for (auto &it : conns) {
                if (!user->input(it.first)) continue;
                if (sig_intersects_bits(sigmap(it.second), mapped_bits)) {
                    consumes = true;
                } else {
                    total = SatMath::add(total, count_operand_leaves(it.second, leaf_cache, leaf_active_stack));
                }
            }

            if (consumes && user->hasPort(ID::Y)) {
                total = SatMath::add(total, count_downstream_operands(user->getPort(ID::Y), op_type,
                    leaf_cache, leaf_active_stack, down_active_stack, seen_assoc_users,
                    candidates, mux_map, component_id, seen_component_candidates, depth + 1));
            }
        }

        down_active_stack.erase(drv);
        return total;
    }

    void collect_users_for_bits(const pool<SigBit> &bits, pool<RTLIL::Cell*> &out_users) {
        out_users.clear();
        for (auto &bit : bits) {
            auto it = conn.user_map.find(bit);
            if (it != conn.user_map.end()) {
                for (auto cell : it->second) out_users.insert(cell);
            }
        }
    }

    // ---------- Candidate Discovery & Graph Building ----------

    std::vector<Candidate> build_candidates()
    {
        std::vector<Candidate> candidates;
        std::vector<RTLIL::Cell*> selected_ops;
        
        for (auto cell : module->selected_cells()) selected_ops.push_back(cell);
        std::sort(selected_ops.begin(), selected_ops.end(), [](RTLIL::Cell *a, RTLIL::Cell *b) {
            return a->name < b->name;
        });

        for (auto cell : selected_ops)
        {
            if (!target_types.count(cell->type)) continue;
            if (cell->get_bool_attribute(ID::keep) || !cell->hasPort(ID::Y)) continue;

            Candidate cand;
            cand.id = (int)candidates.size();
            cand.op = cell;
            cand.op_out = sigmap(cell->getPort(ID::Y));
            cand.width = GetSize(cand.op_out);

            if (cand.width <= 0) continue;
            
            // Check if op output has keep
            for (auto &bit : cand.op_out) {
                if (bit.wire && bit.wire->get_bool_attribute(ID::keep)) {
                    cand.blocked = true;
                    cand.blocked_reason = "operator output has keep";
                    break;
                }
            }

            const auto &conns = conn.get_sorted_connections(cell);
            bool found = false;

            for (auto &it : conns)
            {
                if (!cell->input(it.first)) continue;
                RTLIL::SigSpec in_sig = sigmap(it.second);
                RTLIL::Cell *mux_cell = nullptr;

                if (!mux_drives_sig(in_sig, mux_cell)) {
                    RTLIL::Cell *drv_cell = nullptr;
                    if (conn.get_unique_driver(in_sig, drv_cell) && drv_cell && drv_cell->type == ID($pmux))
                        log_debug("    muxpush skip op=%s port=%s: driver is $pmux (unsupported)\n", log_id(cell->name), log_id(it.first));
                    continue;
                }
                
                if (!design->selected(module, mux_cell) || mux_cell->get_bool_attribute(ID::keep)) continue;

                RTLIL::SigSpec mux_out = sigmap(mux_cell->getPort(ID::Y));
                if (mux_out != in_sig) continue;
                
                int in_width = GetSize(in_sig);
                if (in_width <= 0 || 
                    GetSize(mux_cell->getPort(ID::A)) != in_width ||
                    GetSize(mux_cell->getPort(ID::B)) != in_width) continue;
                    
                if (!fanout_within_limit(mux_out)) continue;

                // Check keep on mux output
                bool mux_keep = false;
                for (auto &bit : mux_out) if (bit.wire && bit.wire->get_bool_attribute(ID::keep)) mux_keep = true;
                if (mux_keep) continue;

                cand.mux = mux_cell;
                cand.port = it.first;
                found = true;
                break;
            }

            if (!found) continue;

            if (!cand.blocked && conn.sig_has_opaque_driver(sigmap(cand.mux->getPort(ID::S)))) {
                cand.blocked = true;
                cand.blocked_reason = "mux select crosses opaque boundary";
            }

            if (!cand.blocked) {
                for (auto &it : conns) {
                    if (cell->input(it.first) && it.first != cand.port && conn.sig_has_opaque_driver(sigmap(it.second))) {
                        cand.blocked = true;
                        cand.blocked_reason = "operator side input crosses opaque boundary";
                        break;
                    }
                }
            }

            candidates.push_back(cand);
        }
        return candidates;
    }

    void collect_mux_candidate_users_through_transparent(const RTLIL::SigSpec &sig,
        const dict<RTLIL::Cell*, std::vector<int>> &mux_map, pool<int> &out_ids, pool<RTLIL::Cell*> &active_cells)
    {
        // Reachability helper used to build candidate dependency edges.
        // It follows transparent wrappers but stops at mux boundaries.
        RTLIL::SigSpec mapped = sigmap(sig);
        RTLIL::Cell *drv = nullptr;
        conn.get_unique_driver(mapped, drv);
        if (drv != nullptr && active_cells.count(drv)) return;
        if (drv != nullptr) active_cells.insert(drv);

        pool<SigBit> mapped_bits;
        for (auto &bit : mapped) if (bit.wire) mapped_bits.insert(bit);

        pool<RTLIL::Cell*> users;
        collect_users_for_bits(mapped_bits, users);

        for (auto user : users)
        {
            if (user == drv || user->get_bool_attribute(ID::keep) || conn.is_opaque(user)) continue;

            const auto &conns = conn.get_sorted_connections(user);
            if (user->type == ID($mux)) {
                if (!input_consumes_signal_bits(user, conns, mapped_bits)) continue;
                auto it = mux_map.find(user);
                if (it != mux_map.end()) for (int id : it->second) out_ids.insert(id);
                continue;
            }

            if (!TransparencyHelper::is_transparent(user)) continue;

            bool consumes = false;
            pool<SigBit> traced_inputs;
            for (auto &it : conns) {
                if (!user->input(it.first)) continue;
                RTLIL::SigSpec in_mapped = sigmap(it.second);
                if (sig_intersects_bits(in_mapped, mapped_bits)) {
                    consumes = true;
                    for (auto &bit : in_mapped) if (bit.wire && mapped_bits.count(bit)) traced_inputs.insert(bit);
                }
            }
            if (!consumes || !user->hasPort(ID::Y)) continue;

            RTLIL::SigSpec traced_y = TransparencyHelper::transparent_traced_output(sigmap, user, traced_inputs);
            if (traced_y.empty()) traced_y = user->getPort(ID::Y);
            collect_mux_candidate_users_through_transparent(traced_y, mux_map, out_ids, active_cells);
        }

        if (drv != nullptr) active_cells.erase(drv);
    }

    // ---------- Pipeline: Graph, ROI, Decide, Apply ----------

    void compute_credit_and_debt(std::vector<Candidate> &candidates)
    {
        if (candidates.empty()) return;
        const double ratio_eff = effective_ratio();

        for (auto &cand : candidates) Candidate::reset_candidate_analysis(cand);

        dict<RTLIL::Cell*, std::vector<int>> mux_map;
        for (auto &cand : candidates) mux_map[cand.mux].push_back(cand.id);
        
        // --- 1. Cone complexity estimation ---
        // up_ops: complexity feeding mux inputs (worst branch)
        // down_ops: complexity reachable after current operator output
        // Both are bounded by budget + recursion guards.
        dict<int, std::vector<int>> comp_to_ids;
        for (auto &cand : candidates) comp_to_ids[cand.component].push_back(cand.id);

        dict<RTLIL::Cell*, uint64_t> leaf_cache;
        dict<int, dict<RTLIL::Cell*, uint64_t>> component_leaf_cache;
        pool<RTLIL::Cell*> leaf_active_stack;
        pool<RTLIL::Cell*> down_active_stack;

        for (auto &it : comp_to_ids) {
            int comp_id = it.first;
            auto &ids = it.second;
            budget.reset_component();
            bool comp_blocked = budget.module_exhausted;

            for (int id : ids) {
                auto &cand = candidates.at(id);
                if (cand.blocked || comp_blocked) continue;

                // Upstream
                leaf_active_stack.clear();
                uint64_t up_a = count_operand_leaves_component(cand.mux->getPort(ID::A), comp_id, candidates, mux_map, component_leaf_cache[comp_id], leaf_active_stack);
                leaf_active_stack.clear();
                uint64_t up_b = count_operand_leaves_component(cand.mux->getPort(ID::B), comp_id, candidates, mux_map, component_leaf_cache[comp_id], leaf_active_stack);
                cand.up_ops = std::max<uint64_t>(up_a, up_b);

                if (budget.is_exhausted()) { comp_blocked = true; break; }

                // Downstream
                uint64_t down = 0;
                const auto &conns = conn.get_sorted_connections(cand.op);
                for (auto &conn_it : conns) {
                    if (!budget.consume()) { comp_blocked = true; break; }
                    if (!cand.op->input(conn_it.first) || conn_it.first == cand.port) continue;
                    down = SatMath::add(down, count_operand_leaves(conn_it.second, leaf_cache, leaf_active_stack));
                }

                if (comp_blocked) break;

                pool<RTLIL::Cell*> seen_assoc;
                pool<int> seen_comp_cands;
                down = SatMath::add(down, count_downstream_operands(cand.op_out, cand.op->type, 
                    leaf_cache, leaf_active_stack, down_active_stack, seen_assoc, 
                    candidates, mux_map, comp_id, seen_comp_cands, 0));
                
                cand.down_ops = std::max<uint64_t>(1, down);
            }

            if (comp_blocked) {
                const char *reason = budget.exhaust_reason();
                for (int id : ids) {
                    auto &cand = candidates.at(id);
                    if (!cand.blocked) { cand.blocked = true; cand.blocked_reason = reason; }
                }
            }
        }

        // --- 2. Debt/credit model ---
        // multiplicity approximates speculative duplication pressure when this
        // candidate is pushed in the context of its downstream dependencies.
        std::vector<int> order = topo_order(candidates);
        if ((int)order.size() != (int)candidates.size()) {
            for (auto &cand : candidates) if (!cand.blocked) { cand.blocked = true; cand.blocked_reason = "dependency cycle"; }
            return;
        }

        for (int i = (int)order.size() - 1; i >= 0; i--) {
            int id = order[i];
            uint64_t mult = 0;
            if (candidates[id].succ.empty()) mult = 1;
            else if (candidates[id].succ.size() == 1) mult = SatMath::add(candidates[candidates[id].succ[0]].multiplicity, 1);
            else for (int sid : candidates[id].succ) mult = SatMath::add(mult, candidates[sid].multiplicity);
            candidates[id].multiplicity = std::max<uint64_t>(1, mult);
        }

        for (auto &cand : candidates) {
            if (cand.blocked) {
                Candidate::reset_candidate_scores(cand, SatMath::mul(cand.width, cand.multiplicity));
                continue;
            }

            uint64_t op_up = std::max<uint64_t>(1, cand.up_ops);
            uint64_t op_down = std::max<uint64_t>(1, cand.down_ops);
            uint64_t d_curr = SatMath::ceil_log2(op_up) + SatMath::ceil_log2(op_down);
            uint64_t d_comb = SatMath::ceil_log2(SatMath::add(op_up, op_down));

            if (d_curr > d_comb) cand.credit_arith = SatMath::mul(d_curr - d_comb, cand.width);
            else cand.credit_arith = 0;

            cand.credit_mux = apply_rational_scale_ceil(cand.width, kMuxCreditScale);
            cand.credit = SatMath::add(cand.credit_arith, cand.credit_mux);
            cand.debt = SatMath::mul(cand.width, cand.multiplicity);
            
            if (cand.credit == 0 && !cand.blocked) cand.blocked_reason = "zero total credit";
        }

        // --- 3. Bridge detection (suffix DP) ---
        
        /* 
         * A "Bridge" is a candidate that effectively has bad ROI on its own
         * (Debt > Credit), but it sits between two very good candidates.
         * We calculate a "Suffix Surplus" to see if taking a loss on this 
         * node allows us to reach a massive gain downstream.
         */
        std::vector<int64_t> suffix_surplus(candidates.size(), 0);
        for (int i = (int)order.size() - 1; i >= 0; i--) {
            int id = order[i];
            auto &cand = candidates[id];
            if (cand.blocked) continue;

            int64_t local = SatMath::sub_i64(SatMath::from_u64(cand.credit_arith), SatMath::from_u64(std::max<uint64_t>(1, cand.debt)));
            int64_t best = std::max<int64_t>(0, local);

            if (cand.succ.size() == 1) {
                int sid = cand.succ[0];
                if (candidates[sid].pred.size() == 1) {
                    int64_t chain = SatMath::add_i64(local, suffix_surplus[sid]);
                    best = std::max(best, chain);
                    if (cand.credit_arith == 0 && suffix_surplus[sid] > 0 && chain > 0) cand.bridge_ok = true;
                }
            }
            suffix_surplus[id] = best;
        }

        for (auto &cand : candidates) {
            if (cand.blocked) continue;
            auto eval = evaluate_local_policy(cand, candidates, ratio_eff);
            if (!eval.eligible && cand.blocked_reason.empty()) cand.blocked_reason = "ineligible bridge floor";
        }
    }

    // Decide which components to approve
    void decide_components(std::vector<Candidate> &candidates)
    {
        if (candidates.empty()) return;
        const double ratio_eff = effective_ratio();
        std::vector<LocalPolicyEval> eval_cache(candidates.size());
        for (auto &cand : candidates)
            eval_cache.at(cand.id) = evaluate_local_policy(cand, candidates, ratio_eff);

        dict<int, std::vector<int>> comp_to_cands;
        for (auto &cand : candidates)
            comp_to_cands[cand.component].push_back(cand.id);

        std::vector<int> comp_ids;
        for (auto &it : comp_to_cands) comp_ids.push_back(it.first);
        std::sort(comp_ids.begin(), comp_ids.end());

        for (int comp_id : comp_ids)
        {
            auto &ids = comp_to_cands.at(comp_id);
            std::sort(ids.begin(), ids.end());
            ComponentStats stats = collect_component_stats(ids, candidates, eval_cache);

            bool accept_global_arith = false;
            bool accept = component_accepts(stats, ratio_eff, accept_global_arith);

            log_debug("    muxpush chain[%d]: credit_arith=%llu credit_total=%llu debt=%llu ratio=%.3f decision=%s\n",
                comp_id,
                (unsigned long long)stats.credit_arith,
                (unsigned long long)stats.credit,
                (unsigned long long)stats.debt,
                ratio_eff,
                accept ? "accept" : "reject");

            for (int id : ids)
            {
                auto &cand = candidates.at(id);
                const LocalPolicyEval &eval = eval_cache.at(id);
                // If global arithmetic ROI is positive, allow ribbon bridges
                // that were locally ineligible but still needed for chain win.
                bool allow_bridge = accept_global_arith && !cand.blocked && cand.credit > 0 && eval.ribbon_node;
                cand.approved = accept && (eval.eligible || allow_bridge);
            }
        }
    }

    int apply_candidates(const std::vector<Candidate> &candidates)
    {
        std::vector<const Candidate*> approved;
        for (const auto &cand : candidates) if (cand.approved) approved.push_back(&cand);
        if (approved.empty()) return 0;

        std::vector<int> order = topo_order(candidates);
        std::vector<int> rank(candidates.size(), -1);
        for (int i = 0; i < (int)order.size(); i++) rank[order[i]] = i;

        std::sort(approved.begin(), approved.end(), [&](const Candidate *a, const Candidate *b) {
            int ra = rank[a->id], rb = rank[b->id];
            if (ra != rb) return ra > rb; // Sinks first
            if (a->op->name == b->op->name) return a->port < b->port;
            return a->op->name < b->op->name;
        });

        pool<RTLIL::Cell*> maybe_remove_muxes;
        pool<RTLIL::Cell*> cells_to_remove;
        int applied = 0;

        for (auto cand : approved)
        {
            RTLIL::Cell *cell = module->cell(cand->op->name);
            RTLIL::Cell *mux = module->cell(cand->mux->name);

            if (!cell || !mux) continue;
            if (!target_types.count(cell->type)) continue;

            // Re-verify candidate shape on the live netlist: earlier rewrites
            // in the same iteration can invalidate stale candidate handles.
            RTLIL::SigSpec live_in = sigmap(cell->getPort(cand->port));
            RTLIL::Cell *live_drv = nullptr;
            if (!mux_drives_sig(live_in, live_drv) || live_drv != mux) continue;
            
            log_debug("    ROI-approved push: mux=%s op=%s port=%s\n", log_id(mux->name), log_id(cell->name), log_id(cand->port));

            // Clone op: Branch A (rewired to Mux A), Branch B (rewired to Mux B)
            // Rename original cell to 'mpa' to avoid name collision logic in equiv check later
            RTLIL::Cell *br_a = cell;
            module->rename(br_a, NEW_ID2_SUFFIX("mpa"));
            conn.remove_cell(br_a);

            RTLIL::Cell *br_b = module->addCell(NEW_ID2, cell->type);
            br_b->parameters = cell->parameters;
            br_b->attributes = cell->attributes;
            br_b->attributes.erase(ID::keep);
            br_b->attributes.erase(ID::minimize);
            br_b->set_src_attribute(cell->get_src_attribute());

            const auto &conns = conn.get_sorted_connections(cell);
            for (auto &p : conns) {
                if (p.first == cand->port) {
                    br_a->setPort(p.first, mux->getPort(ID::A));
                    br_b->setPort(p.first, mux->getPort(ID::B));
                } else {
                    br_a->setPort(p.first, p.second);
                    br_b->setPort(p.first, p.second);
                }
            }

            RTLIL::SigSpec orig_y = cell->getPort(ID::Y);
            RTLIL::SigSpec out_a = module->addWire(NEW_ID2_SUFFIX("mpa_y"), GetSize(orig_y));
            RTLIL::SigSpec out_b = module->addWire(NEW_ID2_SUFFIX("mpb_y"), GetSize(orig_y));
            
            br_a->setPort(ID::Y, out_a);
            br_b->setPort(ID::Y, out_b);
            br_a->fixup_parameters();
            br_b->fixup_parameters();

            RTLIL::Cell *new_mux = module->addMux(NEW_ID2_SUFFIX("muxpush"), out_a, out_b, mux->getPort(ID::S), orig_y);
            new_mux->set_src_attribute(cell->get_src_attribute());

            conn.add_cell(br_a);
            conn.add_cell(br_b);
            conn.add_cell(new_mux);

            maybe_remove_muxes.insert(mux);
            applied++;
            total_count++;
        }

        for (auto mux : maybe_remove_muxes) {
            if (module->cell(mux->name) && !sig_has_live_input_users(mux->getPort(ID::Y), mux)) {
                conn.remove_cell(mux);
                module->remove(mux);
            }
        }

        return applied;
    }

    // ---------- Utilities ----------

    std::vector<int> topo_order(const std::vector<Candidate> &candidates)
    {
        std::vector<int> indeg(candidates.size(), 0);
        for (auto &c : candidates) indeg[c.id] = c.pred.size();

        std::queue<int> q;
        for (auto &c : candidates) if (indeg[c.id] == 0) q.push(c.id);

        std::vector<int> res;
        res.reserve(candidates.size());
        while (!q.empty()) {
            int u = q.front(); q.pop();
            res.push_back(u);
            for (int v : candidates[u].succ) if (--indeg[v] == 0) q.push(v);
        }
        return res;
    }

    void build_candidate_graph(std::vector<Candidate> &candidates)
    {
        dict<RTLIL::Cell*, std::vector<int>> mux_map;
        for (auto &c : candidates) mux_map[c.mux].push_back(c.id);

        for (auto &cand : candidates) {
            pool<int> succ;
            pool<RTLIL::Cell*> active;
            collect_mux_candidate_users_through_transparent(cand.op_out, mux_map, succ, active);
            succ.erase(cand.id);
            cand.succ.assign(succ.begin(), succ.end());
            std::sort(cand.succ.begin(), cand.succ.end());
        }

        for (auto &cand : candidates) {
            for (int sid : cand.succ) candidates[sid].pred.push_back(cand.id);
        }
        for (auto &cand : candidates) std::sort(cand.pred.begin(), cand.pred.end());

        // Peer mapping (candidates sharing the same mux)
        for (auto &it : mux_map) {
            auto &ids = it.second;
            for (size_t i = 0; i < ids.size(); i++) {
                for (size_t j = i + 1; j < ids.size(); j++) {
                    candidates[ids[i]].peer_same_mux.push_back(ids[j]);
                    candidates[ids[j]].peer_same_mux.push_back(ids[i]);
                }
            }
        }
    }

    void compute_components(std::vector<Candidate> &candidates)
    {
        std::vector<int> comp_ids(candidates.size(), -1);
        int count = 0;
        
        for (auto &cand : candidates) {
            if (comp_ids[cand.id] != -1) continue;
            std::queue<int> q;
            q.push(cand.id);
            comp_ids[cand.id] = count;

            while (!q.empty()) {
                int u = q.front(); q.pop();
                auto visit = [&](int v) { if (comp_ids[v] == -1) { comp_ids[v] = count; q.push(v); } };
                for (int v : candidates[u].succ) visit(v);
                for (int v : candidates[u].pred) visit(v);
                for (int v : candidates[u].peer_same_mux) visit(v);
            }
            count++;
        }
        for (auto &cand : candidates) cand.component = comp_ids[cand.id];
    }

    void run()
    {
        conn.build_connectivity();
        leaf_depth_limit_hit = false;
        downstream_depth_limit_hit = false;

        while (true) {
            auto candidates = build_candidates();
            if (candidates.empty()) break;

            build_candidate_graph(candidates);
            compute_components(candidates);
            compute_credit_and_debt(candidates);
            decide_components(candidates);
            
            if (!apply_candidates(candidates)) break;
        }

        if (leaf_depth_limit_hit || downstream_depth_limit_hit)
            log_warning("  muxpush: recursion depth guard hit in module %s.\n", log_id(module->name));
    }
};

struct OptMuxPushPass : public Pass {
    OptMuxPushPass() : Pass("muxpush", "push muxes through lightweight operators") { }

    void help() override
    {
        log("\n");
        log("    muxpush [options] [selection]\n");
        log("\n");
        log("Push $mux cells forward through lightweight operators by cloning\n");
        log("the operator and re-inserting the mux at the output.\n");
        log("Decisions are made with deterministic chain-level ROI (credit vs debt).\n");
        log("\n");
        log("    -limit <int>\n");
        log("        maximum fanout allowed for the mux output (default: 1)\n");
        log("\n");
        log("    -types <string>\n");
        log("        comma-separated list of operator cell types to push through\n");
        log("        (default: $add,$sub,$and,$or,$xor)\n");
        log("\n");
        log("    -ratio <float>\n");
        log("        ROI sensitivity ratio, push if debt <= credit * ratio\n");
        log("        (default: 1.0)\n");
        log("\n");
        log("    -budget <int>\n");
        log("        approximate analysis work budget per module\n");
        log("        <= 0 disables budgeting (default: 250000)\n");
        log("\n");
    }

    void execute(std::vector<std::string> args, RTLIL::Design *design) override
    {
        int fanout_limit = 1;
        std::string types = "$add,$sub,$and,$or,$xor";
        double ratio = 1.0;
        int64_t budget = 250000;

        log_header(design, "Executing MUXPUSH pass (deterministic ROI mux pushing).\n");

        size_t argidx;
        for (argidx = 1; argidx < args.size(); argidx++) {
            if (args[argidx] == "-limit" && argidx+1 < args.size()) {
                fanout_limit = std::stoi(args[++argidx]);
                continue;
            }
            if (args[argidx] == "-types" && argidx+1 < args.size()) {
                types = args[++argidx];
                continue;
            }
            if (args[argidx] == "-ratio" && argidx+1 < args.size()) {
                ratio = std::stod(args[++argidx]);
                continue;
            }
            if (args[argidx] == "-budget" && argidx+1 < args.size()) {
                budget = std::stoll(args[++argidx]);
                continue;
            }
            break;
        }
        extra_args(args, argidx, design);

        if (fanout_limit < 1) log_cmd_error("muxpush -limit must be >= 1.\n");
        if (ratio < 0.0) log_cmd_error("muxpush -ratio must be >= 0.\n");

        pool<IdString> target_types;
        for (auto &tok : split_tokens(types, ", \t\r\n")) {
            if (!tok.empty()) target_types.insert(RTLIL::escape_id(tok));
        }

        if (target_types.empty()) log_cmd_error("muxpush requires at least one -types entry.\n");

        int total_count = 0;
        for (auto module : design->selected_modules()) {
            if (module->get_bool_attribute(ID::blackbox)) continue;
            OptMuxPushWorker worker(design, module, target_types, fanout_limit, ratio, budget);
            worker.run();
            total_count += worker.total_count;
        }

        log("  Pushed muxes through %d operator inputs.\n", total_count);
    }
} OptMuxPushPass;

PRIVATE_NAMESPACE_END
