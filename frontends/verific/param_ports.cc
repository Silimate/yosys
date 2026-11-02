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

#include <sstream>

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

// Whether a value is a number with no x or z bits that isn't negative, so that any type at least as
// wide holds it unchanged, signed or not
static bool natural(VeriBaseValue *v)
{
	if (!v || (v->Type() != VeriBaseValue::INTEGER && v->Type() != VeriBaseValue::BASEDNUM) || v->HasXZ())
		return false;
	verific_int64 size_sign = v->StaticSizeSign();
	if (size_sign >= 0)
		return size_sign > 0;
	// A signed value's sign bit, which only a value that fits 64 bits shows here
	return -size_sign <= 64 && !((v->Get64bitUnsigned() >> (-size_sign - 1)) & 1);
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
	const pool<VeriExpression *> &moved; // generate condition parts that move to parameters of their own
	dict<VeriIdDef *, std::string> blocked;
	dict<VeriIdDef *, pool<VeriIdDef *>> feeds;                      // id -> localparams computed from it
	std::vector<std::tuple<VeriIdDef *, VeriModule *, VeriIdDef *>> passed; // id -> child parameter it sets
	const char *why = nullptr;
	VeriIdDef *init_of = nullptr;
	VeriModule *child = nullptr;
	VeriIdDef *formal = nullptr;

	UseScan(const pool<VeriIdDef *> &tracked, const pool<VeriIdDef *> &derivable, const pool<VeriExpression *> &moved) :
		tracked(tracked), derivable(derivable), moved(moved) {}

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
	void Visit(VeriBinaryOperator &node) override { if (!moved.count(&node)) VeriVisitor::Visit(node); }
	void Visit(VeriUnaryOperator &node) override { if (!moved.count(&node)) VeriVisitor::Visit(node); }
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

// Whether a tree holds an unbased unsized literal ('0, '1, 'x or 'z), which takes the width of the
// expression around it
struct FillScan : public VeriVisitor {
	using VeriVisitor::Visit;
	bool found = false;
	void Visit(VeriConstVal &node) override { found = found || node.IsUnsizedBit(); }
};

static bool fills(VeriTreeNode *node)
{
	FillScan scan;
	if (node)
		node->Accept(scan);
	return scan.found;
}

// An operand whose value doesn't depend on the width of the expression around it: a name, a select,
// a concatenation or a literal, unless it holds a literal that fills that width
static bool primary(VeriExpression *e)
{
	if (!e || fills(e))
		return false;
	switch (e->GetClassId()) {
	case ID_VERIIDREF: case ID_VERIINDEXEDID: case ID_VERIINDEXEDMEMORYID:
	case ID_VERICONCAT: case ID_VERIMULTICONCAT: case ID_VERICONSTVAL: case ID_VERIINTVAL:
		return true;
	default:
		return false;
	}
}

// Counts a parameter's reads, and those that take its value whole, where a type at least as wide that
// holds each copy's value unchanged gives the same result: the right side of an assignment, a port or
// parameter connection, or a comparison with an operand the width can't change. A comparison is
// signed only if both sides are, so unless every copy has the same sign, that operand must be
// unsigned in every copy, and so name no parameter or genvar, whose type a copy may change.
struct WholeScan : public VeriVisitor {
	using VeriVisitor::Visit;
	VeriIdDef *id;
	bool same_sign;
	int reads = 0, whole = 0;

	WholeScan(VeriIdDef *id, bool same_sign) : id(id), same_sign(same_sign) {}

	bool is(VeriExpression *e) { return e && e->GetClassId() == ID_VERIIDREF && static_cast<VeriIdRef *>(e)->GetId() == id; }
	void take(VeriExpression *e) { whole += is(e); }
	// The other side of a comparison
	bool other(VeriExpression *e)
	{
		if (!primary(e))
			return false;
		if (same_sign)
			return true;
		if (e->Sign())
			return false;
		for (auto ref : refs(e))
			if (!ref || ref->IsParam() || ref->IsGenVar())
				return false;
		return true;
	}

	void Visit(VeriIdRef &node) override { reads += node.GetId() == id; }
	void Visit(VeriIndexedId &node) override { reads += node.GetId() == id; VeriVisitor::Visit(node); }
	void Visit(VeriIndexedMemoryId &node) override { reads += node.GetId() == id; VeriVisitor::Visit(node); }
	void Visit(VeriSelectedName &node) override { reads += node.GetId() == id; VeriVisitor::Visit(node); }

	void Visit(VeriNetRegAssign &node) override { take(node.GetRValExpr()); VeriVisitor::Visit(node); }
	void Visit(VeriBlockingAssign &node) override
	{
		if (node.OperType() == VERI_EQUAL_ASSIGN)
			take(node.GetValue());
		VeriVisitor::Visit(node);
	}
	void Visit(VeriNonBlockingAssign &node) override { take(node.GetValue()); VeriVisitor::Visit(node); }
	void Visit(VeriBinaryOperator &node) override
	{
		switch (node.OperType()) {
		case VERI_LOGEQ: case VERI_LOGNEQ: case VERI_CASEEQ: case VERI_CASENEQ:
		case VERI_LT: case VERI_GT: case VERI_LEQ: case VERI_GEQ:
			whole += is(node.GetLeft()) && other(node.GetRight());
			whole += is(node.GetRight()) && other(node.GetLeft());
			break;
		default:
			break;
		}
		VeriVisitor::Visit(node);
	}

	// Declarations and instantiations are walked by hand, as UseScan does, so every read is counted.
	// A net's declaration assignment is a continuous assignment.
	void decl(VeriDataType *type, const Array *ids, bool nets)
	{
		if (type)
			type->Accept(*this);
		for (auto i : items<VeriIdDef>(ids)) {
			if (i->GetDimensions())
				i->GetDimensions()->Accept(*this);
			if (VeriExpression *init = i->GetInitialValue()) {
				if (nets && i->IsNet())
					take(init);
				init->Accept(*this);
			}
		}
	}
	void Visit(VeriDataDecl &node) override { decl(node.GetDataType(), node.GetIds(), true); }
	void Visit(VeriNetDecl &node) override { decl(node.GetDataType(), node.GetIds(), true); }
	void Visit(VeriAnsiPortDecl &node) override { decl(node.GetDataType(), node.GetIds(), false); }
	void Visit(VeriModuleInstantiation &node) override
	{
		if (VeriModule *mod = node.GetInstantiatedModule())
			for (auto &o : overrides(&node, mod))
				take(o.second);
		for (auto e : items<VeriExpression>(node.GetParamValues()))
			e->Accept(*this);
		for (auto inst : items<VeriInstId>(node.GetIds())) {
			if (inst->GetDimensions())
				inst->GetDimensions()->Accept(*this);
			for (auto e : items<VeriExpression>(inst->GetPortConnects())) {
				take(e->GetClassId() == ID_VERIPORTCONNECT ? static_cast<VeriPortConnect *>(e)->GetConnection() : e);
				e->Accept(*this);
			}
		}
	}
};

// Every identifier a tree reads, and those it reads through a select or a hierarchical name
struct Reads : public VeriVisitor {
	using VeriVisitor::Visit;
	pool<VeriIdDef *> ids, selected;
	void Visit(VeriIdRef &node) override { ids.insert(node.GetId()); }
	void Visit(VeriIndexedId &node) override { ids.insert(node.GetId()), selected.insert(node.GetId()); VeriVisitor::Visit(node); }
	void Visit(VeriIndexedMemoryId &node) override { ids.insert(node.GetId()), selected.insert(node.GetId()); VeriVisitor::Visit(node); }
	void Visit(VeriSelectedName &node) override { ids.insert(node.GetId()), selected.insert(node.GetId()); VeriVisitor::Visit(node); }
};

struct GenerateIfs : public VeriVisitor {
	using VeriVisitor::Visit;
	std::vector<VeriGenerateConditional *> nodes;
	void Visit(VeriGenerateConditional &node) override { nodes.push_back(&node); VeriVisitor::Visit(node); }
};

// Whether an expression is a comparison or a logical operation, whose one-bit value its context can't widen
static bool one_bit(VeriExpression *e)
{
	if (e && e->GetClassId() == ID_VERIUNARYOPERATOR)
		return static_cast<VeriUnaryOperator *>(e)->OperType() == VERI_LOGNOT;
	if (!e || e->GetClassId() != ID_VERIBINARYOPERATOR)
		return false;
	switch (static_cast<VeriBinaryOperator *>(e)->OperType()) {
	case VERI_LOGEQ: case VERI_LOGNEQ: case VERI_CASEEQ: case VERI_CASENEQ:
	case VERI_LT: case VERI_GT: case VERI_LEQ: case VERI_GEQ: case VERI_LOGAND: case VERI_LOGOR:
		return true;
	default:
		return false;
	}
}

// The operands of an operator, the only places `direct`, `replace` and `split` look into
static std::vector<VeriExpression *> operands(VeriExpression *e)
{
	switch (e ? e->GetClassId() : ID_VERIIDREF) {
	case ID_VERIBINARYOPERATOR: {
		auto b = static_cast<VeriBinaryOperator *>(e);
		return {b->GetLeft(), b->GetRight()};
	}
	case ID_VERIUNARYOPERATOR:
		return {static_cast<VeriUnaryOperator *>(e)->GetArg()};
	case ID_VERIQUESTIONCOLON: {
		auto q = static_cast<VeriQuestionColon *>(e);
		return {q->GetIfExpr(), q->GetThenExpr(), q->GetElseExpr()};
	}
	default:
		return {};
	}
}

static bool is_ref(VeriExpression *e, VeriIdDef *id)
{
	return e && e->GetClassId() == ID_VERIIDREF && static_cast<VeriIdRef *>(e)->GetId() == id;
}

// How many references to `id` an expression holds as operands of operators
static int direct(VeriExpression *e, VeriIdDef *id)
{
	int n = is_ref(e, id);
	for (auto o : operands(e))
		n += direct(o, id);
	return n;
}

// Replaces each reference to `id` that `direct` counts with a copy of `value`
static void replace(VeriExpression *e, VeriIdDef *id, VeriExpression *value)
{
	for (auto o : operands(e)) {
		if (!is_ref(o, id)) {
			replace(o, id, value);
			continue;
		}
		VeriMapForCopy map;
		e->ReplaceChildExpr(o, value->CopyExpression(map), 1);
	}
}

// A copy of `e` that reads `value` wherever `e` reads `id`
static VeriExpression *substitute(VeriExpression *e, VeriIdDef *id, VeriExpression *value)
{
	VeriMapForCopy map;
	VeriExpression *copy = e->CopyExpression(map);
	replace(copy, id, value);
	return copy;
}

// A generate condition part that moves to a parameter of its own, and the node holding it
typedef std::pair<VeriTreeNode *, VeriExpression *> Part;

// Collects the parts of a generate condition that read `p` and otherwise only constants and yield
// one bit. False when the condition reads `p` anywhere else.
static bool split(VeriTreeNode *parent, VeriExpression *e, VeriIdDef *p, std::vector<Part> &out)
{
	Reads r;
	if (e)
		e->Accept(r);
	if (!r.ids.count(p))
		return true;
	int all = 0;
	for (auto id : refs(e))
		all += id == p;
	if (GetSize(r.ids) == 1 && !r.selected.count(p) && one_bit(e) && direct(e, p) == all) {
		out.emplace_back(parent, e);
		return true;
	}
	std::vector<VeriExpression *> ops = operands(e);
	if (ops.empty())
		return false;
	for (auto o : ops)
		if (!split(e, o, p, out))
			return false;
	return true;
}

static std::string text(VeriTreeNode *node)
{
	std::ostringstream s;
	node->PrettyPrint(s, 0);
	return s.str();
}

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
	// The widest of each identifier's value types, signed only if every value is, and the identifiers
	// with values of both signs or with a value no wider type holds unchanged
	Types widest;
	pool<VeriIdDef *> both_signs, unnatural;
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
				if (!natural(v))
					unnatural.insert(id);
				delete own;
				if (mixed.count(id) || (types.count(id) && !(types.at(id) == value.first)) || !value.first.width)
					types.erase(id), mixed.insert(id);
				else
					types[id] = value.first;
				if (!widest.count(id))
					widest[id] = value.first;
				else {
					ValueType &w = widest.at(id);
					if (w.sign != value.first.sign)
						both_signs.insert(id);
					w = {std::max(w.width, value.first.width), w.sign && value.first.sign};
				}
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

	// A generate condition only needs the outcome of a test on a parameter, so each one-bit part of it
	// that reads the parameter and otherwise only constants moves to a parameter of its own, which every
	// instance sets by evaluating the part on what it gives the parameter. The parameter can then become
	// a port. That evaluation sees the same type and value the copy did only when the parameter is untyped
	// and every instance sets it to a name or literal, so only those split. The default, which the new
	// parameters' defaults test, must be a constant of its own.
	dict<VeriIdDef *, std::vector<Part>> parts;
	pool<VeriExpression *> moved;
	for (auto m : modules) {
		GenerateIfs gen;
		m->Accept(gen);
		for (auto p : promote.at(m)) {
			bool ok = untyped(p) && primary(p->GetInitialValue()) && refs(p->GetInitialValue()).empty();
			for (auto &use : uses[m]) {
				dict<VeriIdDef *, VeriExpression *> ov = overrides(use.second, m);
				ok = ok && (!ov.count(p) || primary(ov.at(p)));
			}
			std::vector<Part> found;
			for (auto g : gen.nodes)
				ok = ok && split(g, g->GetIfExpr(), p, found);
			if (!ok || found.empty())
				continue;
			parts[p] = found;
			for (auto &f : found)
				moved.insert(f.second);
		}
	}
	// The distinct parts that read a parameter, each a parameter of its own once it is promoted
	auto tests = [&](VeriIdDef *p) {
		std::vector<std::string> out;
		if (parts.count(p))
			for (auto &f : parts.at(p))
				if (std::find(out.begin(), out.end(), text(f.second)) == out.end())
					out.push_back(text(f.second));
		return out;
	};

	// The copies a module would still elaborate to, told apart by the parameters it keeps. Each part
	// moved to a parameter can tell them apart further, by its one bit.
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
		int bits = 0;
		for (auto p : promote.at(m))
			bits += GetSize(tests(p));
		return GetSize(left) << std::min(bits, 16);
	};

	// Copies that disagree on an untyped parameter's width or sign still share one port when every
	// value is a non-negative number, no localparam is computed from it, and the module only reads it
	// whole: the widest copy's width, signed only if every copy is, holds each value unchanged
	pool<VeriIdDef *> widened;
	for (auto m : modules)
		for (auto p : promote.at(m)) {
			if (!untyped(p) || !mixed.count(p) || !widest.count(p) || unnatural.count(p) || !derived(m, {p}).empty())
				continue;
			// A value written as '1 would fill the wider port
			bool filled = fills(p->GetInitialValue());
			for (auto &use : uses[m]) {
				dict<VeriIdDef *, VeriExpression *> ov = overrides(use.second, m);
				filled = filled || (ov.count(p) && fills(ov.at(p)));
			}
			if (filled)
				continue;
			WholeScan scan(p, !both_signs.count(p));
			m->Accept(scan);
			if (scan.whole == scan.reads)
				types[p] = widest.at(p), widened.insert(p);
		}

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
			UseScan scan(tracked, local_ok, moved);
			m->Accept(scan);
			for (auto &b : scan.blocked)
				blocked.emplace(b.first, stringf("it is read in %s", b.second.c_str()));
			for (auto &pass : scan.passed) {
				VeriModule *c = std::get<1>(pass);
				VeriIdDef *q = std::get<2>(pass);
				if (!promote.count(c) || !promote.at(c).count(q))
					blocked.emplace(std::get<0>(pass), stringf("it sets parameter %s of module %s", q->Name(), c->Name()));
				// The parameters that hold q's tests are set from what this passes
				else if (parts.count(q))
					blocked.emplace(std::get<0>(pass),
							stringf("it sets parameter %s of module %s, which a generate condition reads", q->Name(), c->Name()));
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

		// A parameter for each distinct test a generate condition makes on a promoted parameter, which
		// defaults to the test on the parameter's default
		dict<VeriIdDef *, std::vector<std::pair<VeriIdDef *, VeriExpression *>>> outcomes;
		dict<VeriExpression *, VeriIdDef *> outcome_of;
		Array *formals = m->GetParameterConnects();
		for (auto p : ps) {
			std::vector<std::string> done;
			std::string names;
			for (auto &f : parts.count(p) ? parts.at(p) : std::vector<Part>()) {
				auto it = std::find(done.begin(), done.end(), text(f.second));
				if (it != done.end()) {
					outcome_of[f.second] = outcomes[p][it - done.begin()].first;
					continue;
				}
				std::string name;
				for (int k = GetSize(done); name.empty() || m->GetScope()->FindLocal(name.c_str()); k++)
					name = stringf("%s$cond%d", p->Name(), k);
				VeriIdDef *g = m->AddParameter(name.c_str(), nullptr, substitute(f.second, p, p->GetInitialValue()),
							       formals && formals->Size());
				outcomes[p].emplace_back(g, f.second);
				outcome_of[f.second] = g;
				done.push_back(text(f.second));
				names += (names.empty() ? "" : ", ") + name;
			}
			if (!names.empty())
				log("Moved the generate condition(s) of module %s that read %s onto parameter(s) %s.\n", m->Name(), p->Name(),
				    names.c_str());
		}

		// Each instance connects what it overrode the parameter with, or its default, and sets each test
		// on it to the test on what it overrode it with
		for (auto &use : uses[m]) {
			VeriModuleInstantiation *inst = use.second;
			name_overrides(inst, m);
			dict<VeriIdDef *, VeriExpression *> ov = overrides(inst, m);
			for (auto p : ps) {
				if (ov.count(p) && outcomes.count(p))
					for (auto &o : outcomes.at(p))
						inst->AddParamRef(o.first->Name(), substitute(o.second, p, ov.at(p)), m->GetScope());
				VeriExpression *value = ov.count(p) ? ov.at(p) : p->GetInitialValue();
				for (auto id : items<VeriInstId>(inst->GetIds())) {
					VeriMapForCopy map;
					VeriExpression *copy = value->CopyExpression(map);
					// A port wider than the value would evaluate its operators at the port's width,
					// where a narrower sum no longer wraps. A concatenation keeps it to its own width.
					if (widened.count(p) && !primary(copy)) {
						Array *one = new Array(1);
						one->InsertLast(copy);
						copy = new VeriConcat(one);
					}
					Array *conns = id->GetPortConnects();
					VeriExpression *first = conns->Size() ? static_cast<VeriExpression *>(conns->GetFirst()) : nullptr;
					bool positional = first && first->GetClassId() != ID_VERIPORTCONNECT && first->GetClassId() != ID_VERIDOTSTAR;
					conns->InsertLast(positional ? copy : new VeriPortConnect(Strings::save(p->Name()), copy));
				}
				inst->RemoveParamRef(p->Name());
			}
		}

		// Then each condition reads the parameter holding its test
		for (auto p : ps)
			for (auto &f : parts.count(p) ? parts.at(p) : std::vector<Part>())
				f.first->ReplaceChildExpr(f.second, new VeriIdRef(outcome_of.at(f.second)), 1);

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
