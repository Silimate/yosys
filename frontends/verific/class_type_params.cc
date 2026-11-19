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

// SILIMATE: a class can reach a type through its type parameter T (IEEE 1800-2017 8.25.1):
//   class C #(type T) ; typedef T::y x ; endclass  -- C#(A)::x is A::y
//   class C #(type T) extends T ; endclass        -- C#(A)::x is A::x
// Verific's hier_tree elaboration resolves C#(A)::x in the generic class, where T is unbound: it
// reports 'T' is not declared (VERI-1128) or x not declared under C (VERI-1187), and past that RTL
// elaboration takes the class handle as the type. Before elaboration, this rewrites each such type
// name to the name it stands for. A::y is the form a module type parameter takes (parameter type
// t = cfg_t::y), which elaboration already specializes per instance.

#include "kernel/yosys.h"

#if defined(YOSYS_ENABLE_VERIFIC) && defined(VERIFIC_SYSTEMVERILOG_SUPPORT)

#include "Array.h"
#include "Map.h"
#include "Set.h"
#include "Strings.h"
#include "VeriCopy.h"
#include "VeriExpression.h"
#include "VeriId.h"
#include "VeriLibrary.h"
#include "VeriModule.h"
#include "VeriModuleItem.h"
#include "VeriScope.h"
#include "VeriVisitor.h"
#include "veri_file.h"

#ifdef VERIFIC_NAMESPACE
using namespace Verific;
#endif

YOSYS_NAMESPACE_BEGIN

namespace {

// The type a parameter actual names: a name, or a type reference without dimensions or signing
VeriName *type_name_of(VeriExpression *actual)
{
	if (!actual)
		return nullptr;
	if (VeriName *name = actual->NameCast())
		return name;
	VeriDataType *type = actual->DataTypeCast();
	if (type && !type->GetDimensions() && !type->GetSigning())
		return type->GetTypeName();
	return nullptr;
}

// The name C#(A)::x stands for when C reaches x through its type parameter T: A::y for typedef T::y x
// in C, A::x when C extends T. A is the specialization's actual for T, else T's default; a default
// naming another of C's type parameters (type T = U) stands for that one's actual, found the same
// way. Returns a new name, still to be resolved in 'actual_scope' (where A was written), or nullptr.
VeriName *name_through_type_param(VeriName *type_name, VeriScope *use_scope, VeriScope *&actual_scope)
{
	actual_scope = nullptr;
	if (!type_name || !type_name->IsScopeName() || type_name->GetParamValues() || type_name->GetFunctionType())
		return nullptr;
	const char *suffix = type_name->GetSuffix();
	VeriName *prefix = type_name->GetPrefix();
	VeriIdDef *class_id = prefix ? prefix->GetId() : nullptr;
	if (!suffix || !class_id || !class_id->IsClass())
		return nullptr;
	VeriModuleItem *class_decl = class_id->GetModuleItem();
	VeriScope *class_scope = class_decl ? class_decl->GetScope() : nullptr;
	Array *formals = class_decl ? class_decl->GetParameters() : nullptr;
	Map *own_ids = class_scope ? class_scope->GetThisScope() : nullptr;
	if (!formals || !own_ids)
		return nullptr;

	// T, and the name x has in T's actual
	VeriIdDef *type_param = nullptr;
	const char *member = nullptr;
	VeriIdDef *suffix_id = type_name->GetId();
	VeriIdDef *own_id = (VeriIdDef *)own_ids->GetValue(suffix);
	if (suffix_id && suffix_id == own_id && suffix_id->IsType() && !suffix_id->IsParam() && !suffix_id->GetDimensions()) {
		// typedef T::y x
		VeriDataType *type = suffix_id->GetDataType();
		VeriName *ref = type ? type->GetTypeName() : nullptr;
		VeriName *ref_prefix = ref ? ref->GetPrefix() : nullptr;
		if (ref && ref->IsScopeName() && !ref->GetParamValues() && !type->GetDimensions() && !type->GetSigning() &&
				ref_prefix && !ref_prefix->GetPrefix() && !ref_prefix->GetParamValues()) {
			type_param = ref_prefix->GetId();
			member = ref->GetSuffix();
		}
	} else if (!suffix_id && !own_id) {
		// class C #(type T) extends T
		VeriName *base = class_decl->GetBaseClassName();
		if (base && !base->GetPrefix() && !base->GetParamValues()) {
			type_param = base->GetId();
			member = suffix;
		}
	}
	if (!type_param || !member || !type_param->IsParam() || !type_param->IsType())
		return nullptr;

	Array *actuals = prefix->GetParamValues();
	VeriName *actual_name = nullptr;
	pool<VeriIdDef *> visited;
	while (!actual_name) {
		if (!type_param || !visited.insert(type_param).second)
			return nullptr;
		unsigned position = 0;
		VeriIdDef *formal;
		FOREACH_ARRAY_ITEM(formals, position, formal)
			if (formal == type_param)
				break;
		if (position >= formals->Size())
			return nullptr; // a type parameter of an enclosing scope

		VeriExpression *actual = nullptr;
		unsigned i;
		VeriExpression *expr;
		FOREACH_ARRAY_ITEM(actuals, i, expr) {
			if (!expr || expr->IsOpen())
				continue;
			const char *formal_name = expr->NamedFormal();
			if (formal_name ? Strings::compare(formal_name, type_param->Name()) : i == position) {
				actual = expr->GetConnection();
				break;
			}
		}
		bool from_default = !actual;
		if (from_default)
			actual = type_param->GetInitialValue();
		actual_scope = from_default ? class_scope : use_scope;
		VeriName *name = type_name_of(actual);
		if (!name)
			return nullptr;
		if (!from_default) {
			actual_name = name;
			break;
		}
		// A default depending on C's other parameters is unbound outside C, unless it is one (type T = U)
		VeriName *root = name;
		bool has_param_values = false;
		while (true) {
			if (root->GetParamValues())
				has_param_values = true;
			if (!root->GetPrefix())
				break;
			root = root->GetPrefix();
		}
		VeriIdDef *root_id = root->GetId();
		bool names_own_id = root_id && own_ids->GetValue(root_id->Name()) == root_id;
		if (names_own_id && root == name && !has_param_values) {
			type_param = root_id;
			continue;
		}
		if (names_own_id || has_param_values)
			return nullptr;
		actual_name = name;
	}
	VeriIdDef *actual_id = actual_name->GetId();
	if (!actual_id || !actual_id->IsType())
		return nullptr; // a class, typedef or type parameter

	VeriMapForCopy old2new;
	VeriName *bound = new VeriScopeName(actual_name->CopyName(old2new), Strings::save(member), nullptr);
	bound->SetLinefile(type_name->Linefile());
	return bound;
}

struct Rewriter : public VeriVisitor {
	using VeriVisitor::Visit;
	VeriScope *scope = nullptr;
	int rewrites = 0;

	void Visit(VeriClass &node) override
	{
		VeriScope *outer = scope;
		if (node.GetScope())
			scope = node.GetScope();
		VeriVisitor::Visit(node);
		scope = outer;
	}

	void Visit(VeriTypeRef &node) override
	{
		VeriVisitor::Visit(node);
		if (node.IsVirtualInterface())
			return;
		VeriScope *actual_scope = nullptr;
		for (int steps = 0; steps < 16; steps++) {
			VeriName *bound = name_through_type_param(node.GetTypeName(), scope, actual_scope);
			if (!bound)
				break;
			bound->Resolve(actual_scope, VeriTreeNode::VERI_TYPE_ENV);
			node.ReplaceChildName(node.GetTypeName(), bound);
			node.SetId(bound->GetId());
			rewrites++;
		}
	}
};

} // namespace

// Rewrite every type name that reaches a member through a class type parameter, in all analyzed
// Verilog units. A chain (a class whose typedef is D#(U)::x) needs its class rewritten before its
// users, so this repeats until nothing changes. Returns the number of names rewritten.
int verific_resolve_class_type_params()
{
	int total = 0;
	for (int pass = 0; pass < 16; pass++) {
		Rewriter rewriter;
		MapIter li, mi;
		VeriLibrary *lib;
		VeriModule *module;
		FOREACH_VERILOG_LIBRARY(li, lib) {
			FOREACH_VERILOG_MODULE_IN_LIBRARY(lib, mi, module) {
				if (!module)
					continue;
				rewriter.scope = module->GetScope();
				module->Accept(rewriter);
			}
		}
		total += rewriter.rewrites;
		if (!rewriter.rewrites)
			break;
	}
	if (total)
		log("Resolved %d type name(s) reached through a class type parameter.\n", total);
	return total;
}

YOSYS_NAMESPACE_END

#endif
