/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026  Silimate Inc.
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/consteval.h"
#include "kernel/ff.h"
#include "kernel/ffinit.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct RstInitPass : public Pass {
	RstInitPass() : Pass("rstinit", "set FF init values to their post-reset values") { }

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    rstinit [selection]\n");
		log("\n");
		log("This pass sets the init value of every FF and latch to the value it holds\n");
		log("after one clock with every reset asserted, so a proof from the init state\n");
		log("only covers the sequences that follow reset.\n");
		log("\n");
		log("The resets are the async and sync reset controls (ARST/SRST) of the FFs\n");
		log("in the module, all held at their active level together. Each FF's value\n");
		log("then follows its own priority: a SET/CLR, ARST or ALOAD that evaluates\n");
		log("active wins, else an active SRST gives its reset value, else an active or\n");
		log("absent clock enable gives D. D and every other signal are evaluated with\n");
		log("unknown inputs and FF outputs set to x, so a reset folded into the D logic\n");
		log("(e.g. q <= ~(rst ? 1'b0 : d)) is found as well.\n");
		log("\n");
		log("A reset driven through inverters or buffers is asserted at its source, so\n");
		log("rst and ~rst are never both held active. A source that some FFs reset on\n");
		log("high and others on low is not asserted, with a warning.\n");
		log("\n");
		log("Bits that stay undefined keep their current init value; a defined\n");
		log("post-reset value replaces any declared one. Modules without reset controls\n");
		log("are left unchanged.\n");
		log("\n");
	}

	struct Worker {
		Module *module;
		SigMap sigmap;
		FfInitVals initvals;
		ConstEval ce;
		int from_reset = 0; // FFs set from a reset or set/clear value
		int from_data = 0;  // FFs set from D or AD with the resets held

		Worker(Module *module) : module(module), sigmap(module), initvals(&sigmap, module),
				ce(module, State::Sx) { }

		// Level of a control under reset: S1 active, S0 inactive, Sx unknown
		static State active(State s, bool pol)
		{
			if (s != State::S0 && s != State::S1)
				return State::Sx;
			return (s == State::S1) == pol ? State::S1 : State::S0;
		}

		Const eval(SigSpec sig)
		{
			SigSpec undef;
			if (!ce.eval(sig, undef) || !sig.is_fully_const()) // combinational loop or unevaluable cell
				return Const(State::Sx, GetSize(sig));
			return sig.as_const();
		}

		// Post-reset value of one FF, x where it is not determined
		Const post_reset(FfData &ff, bool &data)
		{
			Const val(State::Sx, ff.width);
			data = false;

			// Clocked update, the lowest priority
			if (ff.has_clk || ff.has_gclk) {
				State en = ff.has_ce ? active(eval(ff.sig_ce)[0], ff.pol_ce) : State::S1;
				State srst = ff.has_srst ? active(eval(ff.sig_srst)[0], ff.pol_srst) : State::S0;
				if (srst == State::S1 && (!ff.ce_over_srst || en == State::S1))
					val = ff.val_srst;
				else if (srst == State::S0 && en == State::S1)
					val = eval(ff.sig_d), data = true;
			}

			// Async controls override the clocked value
			if (ff.has_aload) {
				State aload = active(eval(ff.sig_aload)[0], ff.pol_aload);
				if (aload == State::S1)
					val = eval(ff.sig_ad), data = true;
				else if (aload == State::Sx)
					val = Const(State::Sx, ff.width);
			}
			if (ff.has_arst) {
				State arst = active(eval(ff.sig_arst)[0], ff.pol_arst);
				if (arst == State::S1)
					val = ff.val_arst, data = false;
				else if (arst == State::Sx)
					val = Const(State::Sx, ff.width);
			}
			if (ff.has_sr) {
				Const clr = eval(ff.sig_clr), set = eval(ff.sig_set);
				for (int i = 0; i < ff.width; i++) {
					State c = active(clr[i], ff.pol_clr), s = active(set[i], ff.pol_set);
					if (c == State::S1)
						val.set(i, State::S0), data = false;
					else if (s == State::S1)
						val.set(i, State::S1), data = false;
					else if (c == State::Sx || s == State::Sx)
						val.set(i, State::Sx);
				}
			}
			return val;
		}

		void run()
		{
			std::vector<FfData> ffs;
			for (auto cell : module->selected_cells())
				if (cell->is_builtin_ff())
					ffs.emplace_back(&initvals, cell);

			// Inverters and buffers, so resets derived from one another (rst, ~rst) are
			// asserted through their common source rather than forced independently
			dict<SigBit, std::pair<SigBit, bool>> drivers; // output -> (input, inverted)
			for (auto cell : module->cells()) {
				bool inv = cell->type.in(ID($_NOT_), ID($not), ID($logic_not), ID($reduce_xnor));
				bool bitwise = cell->type.in(ID($_NOT_), ID($not), ID($_BUF_), ID($buf), ID($pos));
				if (!inv && !bitwise &&
						!cell->type.in(ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_bool)))
					continue;
				SigSpec a = sigmap(cell->getPort(ID::A)), y = sigmap(cell->getPort(ID::Y));
				if (!bitwise) { // a 1-bit reduction or logic_not is a buffer or inverter
					if (GetSize(a) == 1)
						drivers[y[0]] = {a[0], inv};
					continue;
				}
				for (int i = 0; i < GetSize(y) && i < GetSize(a); i++)
					drivers[y[i]] = {a[i], inv};
			}

			// SET/CLR are left out: proc builds them from reset and data (rst & d), so
			// forcing them active would assert set and clear together
			dict<SigBit, State> resets;
			pool<SigBit> conflicting;
			auto add = [&](const SigSpec &sig, bool pol) {
				SigBit bit = sigmap(sig[0]);
				pool<SigBit> seen;
				while (drivers.count(bit) && seen.insert(bit).second) {
					pol ^= drivers.at(bit).second;
					bit = drivers.at(bit).first;
				}
				if (!bit.wire)
					return;
				State level = pol ? State::S1 : State::S0;
				if (resets.count(bit) && resets.at(bit) != level)
					conflicting.insert(bit);
				resets[bit] = level;
			};
			for (auto &ff : ffs) {
				if (ff.has_arst)
					add(ff.sig_arst, ff.pol_arst);
				if (ff.has_srst)
					add(ff.sig_srst, ff.pol_srst);
			}
			for (auto bit : conflicting) {
				log_warning("Reset %s is used at both polarities in module %s; not asserting it.\n",
						log_signal(bit), log_id(module));
				resets.erase(bit);
			}
			if (resets.empty())
				return;
			for (auto &it : resets)
				ce.set(it.first, Const(it.second, 1));

			// Evaluate every FF before writing any init, so each sees the same reset cycle
			std::vector<std::pair<FfData *, Const>> updates;
			for (auto &ff : ffs) {
				bool data;
				Const val = post_reset(ff, data);
				if (val.is_fully_undef())
					continue;
				updates.emplace_back(&ff, val);
				(data ? from_data : from_reset)++;
			}
			for (auto &it : updates)
				for (int i = 0; i < it.first->width; i++)
					if (it.second[i] == State::S0 || it.second[i] == State::S1)
						initvals.set_init(it.first->sig_q[i], it.second[i]);

			log("Module %s: %d reset(s); %d FF(s) set from reset values, %d from D.\n",
					log_id(module), GetSize(resets), from_reset, from_data);
		}
	};

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing RSTINIT pass (set FF init values to post-reset values).\n");

		extra_args(args, 1, design);

		int total_reset = 0, total_data = 0;
		for (auto module : design->selected_modules()) {
			Worker worker(module);
			worker.run();
			total_reset += worker.from_reset;
			total_data += worker.from_data;
		}

		log("Set %d FF(s) from reset values and %d from D.\n", total_reset, total_data);
	}
} RstInitPass;

PRIVATE_NAMESPACE_END
