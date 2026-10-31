/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2026 Silimate, Inc.
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

// SILIMATE: `verific -promote_params`. A module instantiated in a generate loop with a parameter
// taken from the loop index elaborates once per index. When such a parameter only ever supplies a
// value, this turns it into an input port of the same name before elaboration, and each instance
// connects its old override to that port, so the module elaborates once and stays equivalent.

#include "kernel/yosys.h"

#if defined(YOSYS_ENABLE_VERIFIC) && defined(VERIFIC_HIER_TREE_SUPPORT) // hier_tree counts the copies

#include "Array.h"
#include "Map.h"
#include "Message.h"
#include "Strings.h"
#include "hier_tree.h"
#include "HierTreeNode.h"
#include "VeriBaseValue_Stat.h"
#include "VeriConstVal.h"
#include "VeriCopy.h"
#include "VeriExpression.h"
#include "VeriId.h"
#include "VeriMisc.h"
#include "VeriModule.h"
#include "VeriModuleItem.h"
#include "VeriScope.h"
#include "VeriStatement.h"
#include "VeriVisitor.h"
#include "veri_tokens.h"

#ifdef VERIFIC_NAMESPACE
using namespace Verific;
#endif

YOSYS_NAMESPACE_BEGIN

void msg_func(msg_type_t msg_type, const char *message_id, linefile_type linefile, const char *msg, va_list args);

namespace {

static void quiet(msg_type_t, const char *, linefile_type, const char *, va_list) {}

template<class T> static std::vector<T *> items(const Array *array)
{
	std::vector<T *> v;
	unsigned i;
	void *item;
	FOREACH_ARRAY_ITEM(array, i, item)
		if (item)
			v.push_back(static_cast<T *>(item));
	return v;
}

// Every identifier a tree reads
struct RefCollector : public VeriVisitor {
	using VeriVisitor::Visit;
	std::vector<VeriIdDef *> ids;
	void Visit(VeriIdRef &node) override { ids.push_back(node.GetId()); }
};

static std::vector<VeriIdDef *> refs(VeriTreeNode *node)
{
	RefCollector c;
	if (node)
		node->Accept(c);
	return c.ids;
}

struct InstCollector : public VeriVisitor {
	using VeriVisitor::Visit;
	std::vector<VeriModuleInstantiation *> insts;
	bool defparam = false;
	void Visit(VeriModuleInstantiation &node) override { insts.push_back(&node); }
	void Visit(VeriDefParam &) override { defparam = true; }
};

// An untyped parameter takes its value's type (LRM 6.20.2)
static bool untyped(VeriIdDef *id)
{
	VeriDataType *t = id->GetDataType();
	return !t || (!t->GetType() && !t->GetSigning() && !t->GetDimensions());
}

// A value's self-determined width and signedness; width 0 when this can't tell
struct ValueType {
	int width = 0;
	bool sign = false;
	bool operator==(const ValueType &o) const { return width == o.width && sign == o.sign; }
};
typedef dict<VeriIdDef *, ValueType> Types;

static int num(VeriExpression *e, bool &ok)
{
	ok = ok && e && e->GetClassId() == ID_VERIINTVAL;
	return ok ? static_cast<VeriIntVal *>(e)->GetNum() : 0;
}

// The type a typed parameter declares, when its range is literal
static ValueType declared(VeriDataType *t)
{
	bool sign = t->GetSigning() == VERI_SIGNED, word = t->GetSigning() != VERI_UNSIGNED;
	switch (t->GetClassId() == ID_VERIDATATYPE ? t->GetType() : ~0u) {
	case VERI_BYTE: return {8, word};
	case VERI_SHORTINT: return {16, word};
	case VERI_INT: case VERI_INTEGER: return {32, word};
	case VERI_LONGINT: return {64, word};
	case 0: case VERI_LOGIC: case VERI_BIT: case VERI_REG: {
		VeriRange *r = t->GetDimensions();
		bool ok = r && !r->GetNext();
		int l = num(r ? r->GetLeft() : nullptr, ok), rr = num(r ? r->GetRight() : nullptr, ok);
		return !r ? ValueType{1, sign} : ok ? ValueType{std::abs(l - rr) + 1, sign} : ValueType{};
	}
	}
	return {};
}

// A value's type, width 0 unless it is a number, and its image
static std::pair<ValueType, std::string> evaluated(VeriBaseValue *v)
{
	std::pair<ValueType, std::string> out;
	if (!v)
		return out;
	if (v->Type() == VeriBaseValue::INTEGER || v->Type() == VeriBaseValue::BASEDNUM) {
		verific_int64 size_sign = v->StaticSizeSign();
		out.first = {int(std::abs(size_sign)), size_sign < 0};
	}
	char *image = v->Image();
	out.second = image ? image : "";
	Strings::free(image);
	return out;
}

static VeriRange *range(int msb)
{
	return new VeriRange(new VeriIntVal(msb), new VeriIntVal(0));
}

// The net type that holds a parameter's value, or null if none does
static VeriDataType *wire_type(VeriIdDef *id, const Types &types)
{
	if (untyped(id)) {
		// It takes its value's type, which must be the same in every copy
		ValueType t = types.count(id) ? types.at(id) : ValueType{};
		return t.width ? new VeriDataType(VERI_WIRE, t.sign ? VERI_SIGNED : 0, range(t.width - 1)) : nullptr;
	}
	VeriDataType *t = id->GetDataType();
	if (t->GetClassId() != ID_VERIDATATYPE)
		return nullptr;
	if (t->GetType() != 0 && t->GetType() != VERI_LOGIC && t->GetType() != VERI_BIT && t->GetType() != VERI_REG) {
		ValueType v = t->GetDimensions() ? ValueType{} : declared(t);
		return v.width ? new VeriDataType(VERI_WIRE, v.sign ? VERI_SIGNED : 0, range(v.width - 1)) : nullptr;
	}
	VeriMapForCopy map;
	return new VeriDataType(VERI_WIRE, t->GetSigning(), t->GetDimensions() ? t->GetDimensions()->CopyRange(map) : nullptr);
}

static bool has_wire_type(VeriIdDef *id, const Types &types)
{
	VeriDataType *t = wire_type(id, types);
	delete t;
	return t != nullptr;
}

// Whether an override differs per instance: it reads a parameter being promoted, a genvar if
// `genvars`, or a parameter computed from either
static bool varies(VeriExpression *e, const pool<VeriIdDef *> &promoted, bool genvars, pool<VeriIdDef *> &seen)
{
	for (auto id : refs(e)) {
		if (!id || !seen.insert(id).second)
			continue;
		if ((genvars && id->IsGenVar()) || promoted.count(id))
			return true;
		if (id->IsParam() && varies(id->GetInitialValue(), promoted, genvars, seen))
			return true;
	}
	return false;
}

// What an instantiation overrides each parameter with, by name or by position
static dict<VeriIdDef *, VeriExpression *> overrides(VeriModuleInstantiation *mi, VeriModule *mod)
{
	dict<VeriIdDef *, VeriExpression *> out;
	std::vector<VeriIdDef *> params = items<VeriIdDef>(mod->GetParameters());
	unsigned i;
	VeriExpression *e;
	FOREACH_ARRAY_ITEM(mi->GetParamValues(), i, e) {
		if (e && e->GetClassId() == ID_VERIPORTCONNECT) {
			auto pc = static_cast<VeriPortConnect *>(e);
			VeriIdDef *p = mod->GetScope()->FindLocal(pc->GetNamedFormal());
			if (p && pc->GetConnection())
				out[p] = pc->GetConnection();
		} else if (e && i < params.size())
			out[params[i]] = e;
	}
	return out;
}

// Name positional overrides, which RemoveParamRef can't find and a removed parameter would shift
static void name_overrides(VeriModuleInstantiation *mi, VeriModule *mod)
{
	std::vector<VeriIdDef *> params = items<VeriIdDef>(mod->GetParameters());
	unsigned i;
	VeriExpression *e;
	FOREACH_ARRAY_ITEM(mi->GetParamValues(), i, e)
		if (e && e->GetClassId() != ID_VERIPORTCONNECT && i < params.size())
			mi->GetParamValues()->Insert(i, new VeriPortConnect(Strings::save(params[i]->Name()), e));
}

// Where a module reads the tracked identifiers. A read that elaboration must evaluate blocks it.
struct UseScan : public VeriVisitor {
	using VeriVisitor::Visit;
	const pool<VeriIdDef *> &tracked, &derivable;
	dict<VeriIdDef *, std::string> blocked;
	dict<VeriIdDef *, pool<VeriIdDef *>> feeds;                      // id -> localparams computed from it
	std::vector<std::tuple<VeriIdDef *, VeriModule *, VeriIdDef *>> passed; // id -> child parameter it sets
	const char *why = nullptr;
	VeriIdDef *init_of = nullptr;
	VeriModule *child = nullptr;
	VeriIdDef *formal = nullptr;

	UseScan(const pool<VeriIdDef *> &tracked, const pool<VeriIdDef *> &derivable) : tracked(tracked), derivable(derivable) {}

	void use(VeriIdDef *id)
	{
		if (!id || !tracked.count(id))
			return;
		if (why)
			blocked.emplace(id, why);
		else if (init_of)
			feeds[id].insert(init_of);
		else if (child)
			passed.emplace_back(id, child, formal);
	}
	void fixed(VeriTreeNode *node, const char *reason)
	{
		const char *w = why;
		why = why ? why : reason;
		if (node)
			node->Accept(*this);
		why = w;
	}
	void fixed(const Array *nodes, const char *reason)
	{
		for (auto n : items<VeriTreeNode>(nodes))
			fixed(n, reason);
	}

	void Visit(VeriIdRef &node) override { use(node.GetId()); }
	void Visit(VeriIndexedId &node) override { use(node.GetId()); VeriVisitor::Visit(node); }
	void Visit(VeriIndexedMemoryId &node) override { use(node.GetId()); VeriVisitor::Visit(node); }
	void Visit(VeriSelectedName &node) override // Rebind doesn't follow these
	{
		const char *w = why;
		why = "a hierarchical name";
		use(node.GetId());
		why = w;
		VeriVisitor::Visit(node);
	}

	void Visit(VeriRange &node) override
	{
		bool indexed = node.GetPartSelectToken() == VERI_PARTSELECT_UP || node.GetPartSelectToken() == VERI_PARTSELECT_DOWN;
		if (indexed && node.GetLeft())
			node.GetLeft()->Accept(*this);
		else
			fixed(node.GetLeft(), "a range bound");
		fixed(node.GetRight(), indexed ? "a part-select width" : "a range bound");
		fixed(node.GetNext(), "a range bound");
	}
	void Visit(VeriMultiConcat &node) override
	{
		fixed(node.GetRepeat(), "a replication count");
		for (auto e : items<VeriExpression>(node.GetExpressions()))
			e->Accept(*this);
	}

#define FIXED(T, reason) void Visit(T &node) override { const char *w = why; why = why ? why : reason; VeriVisitor::Visit(node); why = w; }
	FIXED(VeriSystemFunctionCall, "a system function argument")
	FIXED(VeriCast, "a cast")
	FIXED(VeriTypeOperator, "a type")
	FIXED(VeriInitialConstruct, "an initial block")
	FIXED(VeriFunctionDecl, "a function")
	FIXED(VeriTaskDecl, "a task")
#undef FIXED

	void Visit(VeriGenerateConditional &node) override { fixed(node.GetIfExpr(), "a generate condition"); VeriVisitor::Visit(node); }
	void Visit(VeriGenerateCase &node) override
	{
		fixed(node.GetCondition(), "a generate condition");
		for (auto item : items<VeriGenerateCaseItem>(node.GetCaseItems()))
			fixed(item->GetConditions(), "a generate condition");
		VeriVisitor::Visit(node);
	}
	void Visit(VeriGenerateFor &node) override
	{
		fixed(node.GetInitial(), "a loop bound");
		fixed(node.GetCondition(), "a loop bound");
		fixed(node.GetRepetition(), "a loop bound");
		VeriVisitor::Visit(node);
	}
	void Visit(VeriFor &node) override
	{
		fixed(node.GetInitials(), "a loop bound");
		fixed(node.GetCondition(), "a loop bound");
		fixed(node.GetRepetitions(), "a loop bound");
		VeriVisitor::Visit(node);
	}
	void Visit(VeriWhile &node) override { fixed(node.GetCondition(), "a loop bound"); VeriVisitor::Visit(node); }
	void Visit(VeriDoWhile &node) override { fixed(node.GetCondition(), "a loop bound"); VeriVisitor::Visit(node); }
	void Visit(VeriRepeat &node) override { fixed(node.GetCondition(), "a loop bound"); VeriVisitor::Visit(node); }
	void Visit(VeriDelayControlStatement &node) override { fixed(node.GetDelay(), "a delay"); VeriVisitor::Visit(node); }
	void Visit(VeriEventControlStatement &node) override { fixed(node.GetAt(), "an event control"); VeriVisitor::Visit(node); }

	// The first branch of a block triggered by two or more edges loads a flop's asynchronous reset
	void Visit(VeriAlwaysConstruct &node) override
	{
		VeriStatement *s = node.GetStmt();
		if (s && s->GetClassId() == ID_VERIEVENTCONTROLSTATEMENT) {
			int edges = 0;
			for (auto e : items<VeriExpression>(s->GetAt()))
				edges += e->GetEdgeToken() != 0;
			VeriStatement *body = s->GetStmt();
			while (body && body->GetClassId() == ID_VERISEQBLOCK && body->GetStatements() && body->GetStatements()->Size() == 1)
				body = static_cast<VeriStatement *>(body->GetStatements()->GetFirst());
			if (edges > 1 && body && body->GetClassId() == ID_VERICONDITIONALSTATEMENT)
				fixed(body->GetThenStmt(), "an asynchronous reset value");
		}
		VeriVisitor::Visit(node);
	}

	void decl(VeriDataDecl &node)
	{
		fixed(node.GetDataType(), "a declared type");
		for (auto id : items<VeriIdDef>(node.GetIds())) {
			fixed(id->GetDimensions(), "a declared type");
			VeriExpression *init = id->GetInitialValue();
			if (!init)
				continue;
			if (derivable.count(id)) {
				init_of = id;
				init->Accept(*this);
				init_of = nullptr;
			} else if (id->IsNet())
				init->Accept(*this);
			else
				fixed(init, id->IsParam() ? "a parameter value" : "an initial value");
		}
	}
	void Visit(VeriDataDecl &node) override { decl(node); }
	void Visit(VeriNetDecl &node) override { decl(node); }
	void Visit(VeriAnsiPortDecl &node) override
	{
		fixed(node.GetDataType(), "a declared type");
		for (auto id : items<VeriIdDef>(node.GetIds())) {
			fixed(id->GetDimensions(), "a declared type");
			fixed(id->GetInitialValue(), "a port default");
		}
	}

	void Visit(VeriModuleInstantiation &node) override
	{
		if (VeriModule *mod = node.GetInstantiatedModule())
			for (auto &o : overrides(&node, mod)) {
				child = mod, formal = o.first;
				o.second->Accept(*this);
				child = nullptr, formal = nullptr;
			}
		else
			fixed(node.GetParamValues(), "a parameter override");
		for (auto inst : items<VeriInstId>(node.GetIds())) {
			fixed(inst->GetDimensions(), "an instance array range");
			for (auto e : items<VeriExpression>(inst->GetPortConnects()))
				e->Accept(*this);
		}
	}
};

struct Rebind : public VeriVisitor {
	using VeriVisitor::Visit;
	const dict<VeriIdDef *, VeriIdDef *> &repl;
	Rebind(const dict<VeriIdDef *, VeriIdDef *> &repl) : repl(repl) {}
	template<class T> void rebind(T &node)
	{
		auto it = repl.find(node.GetId());
		if (it != repl.end())
			node.SetId(it->second);
	}
	void Visit(VeriIdRef &node) override { rebind(node); }
	void Visit(VeriIndexedId &node) override { rebind(node); VeriVisitor::Visit(node); }
	void Visit(VeriIndexedMemoryId &node) override { rebind(node); VeriVisitor::Visit(node); }
};

// Module-level localparams, which can become wires
static pool<VeriIdDef *> derivable(VeriModule *mod)
{
	pool<VeriIdDef *> ids;
	for (auto decls : {mod->GetModuleItems(), mod->GetParameterConnects()})
		for (auto item : items<VeriModuleItem>(decls))
			if (item->IsDataDecl() && (static_cast<VeriDataDecl *>(item)->IsParamDecl() || static_cast<VeriDataDecl *>(item)->IsLocalParamDecl()))
				for (auto id : items<VeriIdDef>(item->GetIds()))
					if (id->IsLocalParam() && !id->IsType() && id->GetInitialValue())
						ids.insert(id);
	return ids;
}

// RemoveParameter only covers the parameter port list
static void remove_local(VeriModule *mod, const char *name)
{
	Array *mitems = mod->GetModuleItems();
	for (unsigned i = 0; mitems && i < mitems->Size(); i++) {
		auto item = static_cast<VeriModuleItem *>(mitems->At(i));
		Array *ids = item && item->IsDataDecl() ? item->GetIds() : nullptr;
		for (unsigned j = 0; ids && j < ids->Size(); j++) {
			auto id = static_cast<VeriIdDef *>(ids->At(j));
			if (!id || strcmp(id->Name(), name))
				continue;
			mod->GetScope()->Undeclare(id);
			ids->Remove(j);
			delete id;
			if (!ids->Size()) {
				mitems->Remove(i);
				delete item;
			}
			return;
		}
	}
}

// The localparams computed from the given parameters, transitively
static pool<VeriIdDef *> derived(VeriModule *mod, const pool<VeriIdDef *> &params)
{
	pool<VeriIdDef *> all = params, local = derivable(mod), out;
	for (bool grew = true; grew;) {
		grew = false;
		for (auto id : local)
			if (!all.count(id))
				for (auto ref : refs(id->GetInitialValue()))
					if (all.count(ref)) {
						all.insert(id), out.insert(id), grew = true;
						break;
					}
	}
	return out;
}

template<class T> static std::vector<T *> by_name(const pool<T *> &set)
{
	std::vector<T *> v(set.begin(), set.end());
	std::sort(v.begin(), v.end(), [](T *a, T *b) { return strcmp(a->Name(), b->Name()) < 0; });
	return v;
}

} // namespace

int verific_promote_params(const Array *veri_modules, const Array *vhdl_units, const Map *parameters, int min_variants)
{
	// Modules the tops reach and the statements instantiating each
	dict<VeriModule *, std::vector<std::pair<VeriModule *, VeriModuleInstantiation *>>> uses;
	std::vector<VeriModule *> order = items<VeriModule>(veri_modules);
	pool<VeriModule *> seen(order.begin(), order.end());
	for (size_t k = 0; k < order.size(); k++) {
		InstCollector c;
		order[k]->Accept(c);
		if (c.defparam) {
			log("Not promoting parameters: module %s has a defparam.\n", order[k]->Name());
			return 0;
		}
		for (auto mi : c.insts)
			if (VeriModule *m = mi->GetInstantiatedModule()) {
				uses[m].emplace_back(order[k], mi);
				if (seen.insert(m).second)
					order.push_back(m);
			}
	}

	// Parameters an instantiation sets from a loop index, and later ones it sets from parameters
	// already chosen: a parent can only promote those if the child follows, whatever its copies
	dict<VeriModule *, pool<VeriIdDef *>> promote;
	pool<VeriIdDef *> all;
	pool<VeriModule *> under_vhdl;
	auto grow = [&](const pool<VeriIdDef *> &from, bool genvars) {
		bool grew = false;
		for (auto &it : uses) {
			if (it.first->IsInterface() || it.first->IsPrimitive() || under_vhdl.count(it.first))
				continue;
			for (auto &use : it.second)
				for (auto &o : overrides(use.second, it.first)) {
					VeriIdDef *p = o.first;
					pool<VeriIdDef *> visited;
					if (p->IsParam() && !p->IsType() && !p->IsLocalParam() && !all.count(p) && varies(o.second, from, genvars, visited))
						promote[it.first].insert(p), all.insert(p), grew = true;
				}
		}
		return grew;
	};
	grow({}, true);
	if (all.empty())
		return 0;

	// How many copies each module would elaborate to, from Verific's tree of instances, with the
	// values each copy gives its parameters and the type each value has in every copy
	dict<VeriModule *, pool<std::string>> variants;
	dict<VeriModule *, pool<std::vector<std::string>>> copies;
	Types types;
	pool<VeriIdDef *> mixed;
	dict<VeriModule *, std::vector<VeriIdDef *>> local_ids;
	auto record = [&](HierTreeNode *node, VeriModule *mod, const std::string &sig) {
		if (!local_ids.count(mod))
			local_ids[mod] = by_name(derivable(mod));
		std::vector<std::string> values;
		std::vector<VeriIdDef *> params = items<VeriIdDef>(mod->GetParameters());
		for (auto ids : {&params, &local_ids.at(mod)})
			for (auto id : *ids) {
				// The tree leaves a constant as written unevaluated: an override or the default
				InterfaceInfo *info = node->GetParamValue(id);
				VeriBaseValue *v = info ? info->GetVeriEvaluatedValue() : nullptr, *own = nullptr;
				VeriExpression *e = info && !v && !id->IsType() ? info->GetVeriExpression() : nullptr;
				if (e && refs(e).empty())
					v = own = e->StaticEvaluate(0, nullptr);
				auto value = evaluated(v);
				delete own;
				if (mixed.count(id) || (types.count(id) && !(types.at(id) == value.first)) || !value.first.width)
					types.erase(id), mixed.insert(id);
				else
					types[id] = value.first;
				// A value this can't print tells this copy apart from every other
				if (ids == &params)
					values.push_back(value.second.empty() ? "?" + sig : value.second);
			}
		copies[mod].insert(values);
	};
	std::function<void(HierTreeNode *, bool)> walk = [&](HierTreeNode *node, bool vhdl) {
		if (node->IsInstance()) {
			VeriModuleItem *item = node->IsVerilogNode() ? node->GetVerilogModule() : nullptr;
			if (item && item->IsModule()) {
				auto mod = static_cast<VeriModule *>(item);
				char *sig = node->GetSignature();
				std::string s = sig ? sig : "";
				Strings::free(sig);
				if (variants[mod].insert(s).second)
					record(node, mod, s);
				if (vhdl)
					under_vhdl.insert(mod);
			}
			vhdl = !node->IsVerilogNode();
		}
		MapIter mi;
		HierTreeNode *child;
		FOREACH_MAP_ITEM(node->GetChildren(), mi, 0, &child)
			if (child)
				walk(child, vhdl);
	};
	unsigned errors = Message::ErrorCount();
	Message::RegisterCallBackMsg(quiet);
	const Map *tops = hier_tree::CreateHierarchicalTree(veri_modules, vhdl_units, parameters);
	bool failed = Message::ErrorCount() != errors;
	MapIter mi;
	HierTreeNode *top;
	FOREACH_MAP_ITEM(tops, mi, 0, &top)
		if (top && !failed)
			walk(top, false);
	hier_tree::DeleteHierarchicalTree();
	Message::RegisterCallBackMsg(msg_func);
	if (failed)
		return 0;
	for (auto &it : promote)
		if (GetSize(variants[it.first]) < min_variants || under_vhdl.count(it.first)) {
			for (auto p : it.second)
				all.erase(p);
			it.second.clear();
		}
	while (grow(all, false)) {}

	pool<VeriModule *> keys;
	for (auto &it : promote)
		keys.insert(it.first);
	std::vector<VeriModule *> modules = by_name(keys);

	// The copies a module would still elaborate to, told apart by the parameters it keeps
	auto copies_left = [&](VeriModule *m) {
		std::vector<VeriIdDef *> params = items<VeriIdDef>(m->GetParameters());
		pool<std::vector<std::string>> left;
		for (auto &values : copies[m]) {
			std::vector<std::string> kept;
			for (size_t i = 0; i < params.size(); i++)
				if (!promote.at(m).count(params[i]))
					kept.push_back(values[i]);
			left.insert(kept);
		}
		return GetSize(left);
	};

	// Drop every parameter that some read, type or instantiation keeps a constant
	auto keep = [&](VeriModule *m, VeriIdDef *p, const std::string &why) {
		if (promote[m].erase(p))
			log("Keeping parameter %s of module %s: %s.\n", p->Name(), m->Name(), why.c_str());
	};
	for (bool changed = true; changed;) {
		changed = false;
		for (auto m : modules) {
			pool<VeriIdDef *> ps = promote.at(m);
			if (ps.empty())
				continue;
			dict<VeriIdDef *, std::string> blocked;
			for (auto &use : uses[m]) {
				VeriModuleInstantiation *inst = use.second;
				dict<VeriIdDef *, VeriExpression *> ov = overrides(inst, m);
				for (auto id : items<VeriInstId>(inst->GetIds())) {
					std::vector<VeriExpression *> conns = items<VeriExpression>(id->GetPortConnects());
					bool positional = !conns.empty() && conns[0]->GetClassId() != ID_VERIPORTCONNECT && conns[0]->GetClassId() != ID_VERIDOTSTAR;
					if (positional && GetSize(conns) != GetSize(items<VeriIdDef>(m->GetPorts())))
						for (auto p : ps)
							blocked.emplace(p, "an instantiation leaves positional ports open");
				}
				for (auto p : ps) {
					VeriExpression *value = ov.count(p) ? ov.at(p) : p->GetInitialValue();
					if (!ov.count(p) && !refs(value).empty())
						blocked.emplace(p, "its default reads other parameters");
				}
			}
			pool<VeriIdDef *> locals = derived(m, ps), tracked = ps, local_ok = derivable(m);
			tracked.insert(locals.begin(), locals.end());
			for (auto id : tracked)
				if (!has_wire_type(id, types))
					blocked.emplace(id, untyped(id) ? "its values don't share one known width and sign" : "its type has no matching port");
			UseScan scan(tracked, local_ok);
			m->Accept(scan);
			for (auto &b : scan.blocked)
				blocked.emplace(b.first, stringf("it is read in %s", b.second.c_str()));
			for (auto &pass : scan.passed) {
				VeriModule *c = std::get<1>(pass);
				VeriIdDef *q = std::get<2>(pass);
				if (!promote.count(c) || !promote.at(c).count(q))
					blocked.emplace(std::get<0>(pass), stringf("it sets parameter %s of module %s", q->Name(), c->Name()));
			}
			// A localparam that stays one keeps every parameter it is computed from
			for (bool grew = true; grew;) {
				grew = false;
				for (auto &f : scan.feeds)
					if (!blocked.count(f.first))
						for (auto l : by_name(f.second))
							if (blocked.count(l)) {
								blocked.emplace(f.first, stringf("it feeds localparam %s (%s)", l->Name(), blocked.at(l).c_str()));
								grew = true;
								break;
							}
			}
			for (auto p : by_name(ps))
				if (blocked.count(p))
					keep(m, p, blocked.at(p)), changed = true;
			// Ports only pay for themselves by merging copies. A child still collapses when its
			// parent keeps these: it connects the parent's parameter instead.
			int before = GetSize(copies[m]), after = copies_left(m);
			if (!promote.at(m).empty() && 2 * after > before)
				for (auto p : by_name(promote.at(m)))
					keep(m, p, stringf("promoting it would leave %d of the module's %d copies", after, before)), changed = true;
		}
	}

	int promoted = 0;
	for (auto m : modules) {
		if (promote.at(m).empty())
			continue;
		std::vector<VeriIdDef *> ps = by_name(promote.at(m));
		std::vector<VeriIdDef *> locals = by_name(derived(m, promote.at(m)));

		// Each instance connects what it overrode the parameter with, or its default
		for (auto &use : uses[m]) {
			VeriModuleInstantiation *inst = use.second;
			name_overrides(inst, m);
			dict<VeriIdDef *, VeriExpression *> ov = overrides(inst, m);
			for (auto p : ps) {
				VeriExpression *value = ov.count(p) ? ov.at(p) : p->GetInitialValue();
				for (auto id : items<VeriInstId>(inst->GetIds())) {
					VeriMapForCopy map;
					VeriExpression *copy = value->CopyExpression(map);
					Array *conns = id->GetPortConnects();
					VeriExpression *first = conns->Size() ? static_cast<VeriExpression *>(conns->GetFirst()) : nullptr;
					bool positional = first && first->GetClassId() != ID_VERIPORTCONNECT && first->GetClassId() != ID_VERIDOTSTAR;
					conns->InsertLast(positional ? copy : new VeriPortConnect(Strings::save(p->Name()), copy));
				}
				inst->RemoveParamRef(p->Name());
			}
		}

		// The parameters become ports and the localparams computed from them wires, first under
		// temporary names because the old declarations still hold theirs
		Array *ports = m->GetPortConnects();
		bool ansi = !ports || !ports->Size() || static_cast<VeriTreeNode *>(ports->GetFirst())->GetClassId() == ID_VERIANSIPORTDECL;
		dict<VeriIdDef *, VeriIdDef *> repl;
		std::vector<std::pair<VeriIdDef *, std::string>> names;
		for (auto p : ps) {
			std::string name = p->Name();
			repl[p] = m->AddPort((name + "$promoted").c_str(), VERI_INPUT, wire_type(p, types), 0, 0, ansi);
			names.emplace_back(repl[p], name);
		}
		for (auto l : locals) {
			std::string name = l->Name();
			VeriMapForCopy map;
			repl[l] = m->AddSignal((name + "$promoted").c_str(), wire_type(l, types), l->GetInitialValue()->CopyExpression(map));
			names.emplace_back(repl[l], name);
		}
		Rebind rebind(repl);
		m->Accept(rebind);
		for (auto &n : names)
			if (!m->RemoveParameter(n.second.c_str()))
				remove_local(m, n.second.c_str());
		VeriScope *scope = m->GetScope();
		for (auto &n : names) {
			scope->Undeclare(n.first);
			n.first->SetName(n.second.c_str());
			scope->Declare(n.first);
		}

		std::string list;
		for (size_t i = 0; i < ps.size(); i++)
			list += (i ? ", " : "") + names[i].second;
		log("Promoted parameter(s) %s of module %s (%d copies) to input ports.\n", list.c_str(), m->Name(), GetSize(variants[m]));
		promoted += GetSize(ps);
	}
	return promoted;
}

YOSYS_NAMESPACE_END

#endif
