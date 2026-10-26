#include <gmock/gmock.h>
#include <gtest/gtest.h>
#include "kernel/yosys.h"
#include "kernel/consteval.h"
#include "frontends/verific/verific.h"

#ifdef YOSYS_ENABLE_VERIFIC
#include "veri_file.h"

#include <filesystem>
#include <fstream>

YOSYS_NAMESPACE_BEGIN

#ifdef VERIFIC_NAMESPACE
using namespace Verific;
#endif

class VerificImportTest : public testing::Test {
protected:
	static void SetUpTestSuite() {
		yosys_setup();
		if (logger().empty()) logger().add_sink<ConsoleLogSink>();
	}
	void TearDown() override { verific_cleanup(); }
	void analyze(Design &design, const std::string &sv) {
		std::string path = make_temp_file();
		std::ofstream(path) << sv;
		Pass::call(&design, "verific -sv " + path);
		std::filesystem::remove(path);
	}
};

TEST_F(VerificImportTest, KeepStateAllowsAnotherImport)
{
	Design first, second;
	analyze(first, "module top(input a, output y); assign y = ~a; endmodule\n");
	verific_import(&first, {}, "top", {.keep_state = true});
	EXPECT_NE(first.module(RTLIL::escape_id("top")), nullptr);
	EXPECT_FALSE(verific_import_pending);
	ASSERT_NE(veri_file::GetModule("top"), nullptr);
	verific_import(&second, {}, "top");
	EXPECT_NE(second.module(RTLIL::escape_id("top")), nullptr);
	EXPECT_EQ(veri_file::GetModule("top"), nullptr);
}

TEST_F(VerificImportTest, ThrowErrorsRemovesTheInterruptedModule)
{
	Design design;
	analyze(design, "module bad(inout a, b); tran t(a, b); endmodule\n"
			"module top(inout a, b); bad u(a, b); endmodule\n");
	try {
		verific_import(&design, {}, "top", {.keep_state = true, .throw_errors = true});
		FAIL() << "no VerificImportError";
	} catch (const VerificImportError &e) {
		EXPECT_EQ(e.module, "bad");
		EXPECT_THAT(e.what(), testing::HasSubstr("Unsupported Verific primitive"));
	}
	EXPECT_NE(design.module(RTLIL::escape_id("top")), nullptr);
	EXPECT_EQ(design.module(RTLIL::escape_id("bad")), nullptr);
	EXPECT_NE(veri_file::GetModule("top"), nullptr);
}

TEST_F(VerificImportTest, ThrowErrorsResetsVerificUnlessKeepState)
{
	Design design;
	analyze(design, "module top(input a, output y); assign y = a; endmodule\n");
	try {
		verific_import(&design, {}, "nope", {.throw_errors = true});
		FAIL() << "no VerificImportError";
	} catch (const VerificImportError &e) {
		EXPECT_EQ(e.module, "");
		EXPECT_STREQ(e.what(), "Can't find module/unit 'nope'.");
	}
	EXPECT_EQ(veri_file::GetModule("top"), nullptr);
}

TEST_F(VerificImportTest, NosvaDropsAssertions)
{
	Design with, without;
	analyze(with, "module top(input clk, a); assert property (@(posedge clk) a); endmodule\n");
	verific_import(&with, {}, "top", {.keep_state = true});
	verific_import(&without, {}, "top", {.nosva = true});
	auto asserts = [](Design &d) {
		int n = 0;
		for (auto cell : d.module(RTLIL::escape_id("top"))->cells())
			n += cell->type == ID($assert);
		return n;
	};
	EXPECT_EQ(asserts(with), 1);
	EXPECT_EQ(asserts(without), 0);
}

TEST_F(VerificImportTest, NetlistsImportTheCallersElaboration)
{
	Design design;
	analyze(design, "module sub #(parameter W = 1) (input [W-1:0] a, output [W-1:0] y);\n"
			"  assign y = a & {W{top.en}};\n"
			"endmodule\n"
			"module top #(parameter W = 1) (input en, input [W-1:0] a, output [W-1:0] y);\n"
			"  sub #(W) u(a, y);\n"
			"endmodule\n");
	Map params(STRING_HASH);
	params.Insert("W", "4");
	ASSERT_TRUE(veri_file::Elaborate("top", "work", &params));
	verific_import(&design, {}, "", {.throw_errors = true, .netlists = {Netlist::PresentDesign()}});
	ASSERT_EQ(GetSize(design.modules()), 2);
	EXPECT_EQ(design.module(RTLIL::escape_id("top"))->wire(RTLIL::escape_id("a"))->width, 4);
	Module *sub = design.module(RTLIL::escape_id("sub(W=4)"));
	ASSERT_NE(sub, nullptr);
	// VerificExtNets gave sub ports for top.en
	EXPECT_GT(GetSize(sub->ports), 2);
}

TEST_F(VerificImportTest, ErrorsLeaveTheFailingModuleAsABlackBox)
{
	Design design;
	analyze(design, "module bad(inout a, b); tran t(a, b); endmodule\n"
			"module good(input a, output y); assign y = a; endmodule\n"
			"module top(inout a, b, output y); bad u(a, b); good g(a, y); endmodule\n");
	std::vector<VerificImportError> errors;
	verific_import(&design, {}, "top", {.errors = &errors});
	ASSERT_EQ(GetSize(errors), 1);
	EXPECT_EQ(errors[0].module, "bad");
	EXPECT_THAT(errors[0].what(), testing::HasSubstr("Unsupported Verific primitive"));
	Module *bad = design.module(RTLIL::escape_id("bad"));
	ASSERT_NE(bad, nullptr);
	EXPECT_TRUE(bad->get_blackbox_attribute());
	EXPECT_EQ(GetSize(bad->ports), 2);
	EXPECT_EQ(bad->cells().size(), 0u);
	// the import went on after bad
	EXPECT_NE(design.module(RTLIL::escape_id("good")), nullptr);
}

TEST_F(VerificImportTest, BlackboxPrimsKeepSwitchPrimitives)
{
	Design design;
	analyze(design, "module top(inout a, b, input g, gn, output y, z);\n"
			"  tran(a, b); rtran(a, b); tranif0(a, b, g); tranif1(a, b, g); rtranif0(a, b, g); rtranif1(a, b, g);\n"
			"  nmos(y, a, g); pmos(y, a, g); rnmos(y, a, g); rpmos(y, a, g); cmos(y, a, g, gn); rcmos(y, a, g, gn);\n"
			"  assign z = g & gn;\n"
			"endmodule\n");
	verific_import(&design, {}, "top", {.throw_errors = true, .blackbox_prims = true});
	int prims = 0, ands = 0;
	for (auto cell : design.module(RTLIL::escape_id("top"))->cells()) {
		ands += cell->type == ID($and);
		if (!cell->type.begins_with("$verific$"))
			continue;
		prims++;
		EXPECT_TRUE(cell->get_bool_attribute(ID::keep));
		ASSERT_NE(design.module(cell->type), nullptr);
		EXPECT_TRUE(design.module(cell->type)->get_blackbox_attribute());
	}
	EXPECT_EQ(prims, 12);
	EXPECT_EQ(ands, 1);
}

TEST_F(VerificImportTest, RouteAllRefsDrivesEveryInstance)
{
	Design design;
	analyze(design, "module leaf(input d); wire s = ~d; endmodule\n"
			"module mid(input d); leaf l(d); endmodule\n"
			"module child(input a, output y, z, w);\n"
			"  assign y = top.x; // a port that is the referenced net\n"
			"  assign z = top.x & a;\n"
			"  assign w = top.m1.l.s;\n"
			"endmodule\n"
			"module wrap(input a, output y, z, w); child c(a, y, z, w); endmodule\n"
			"module top(input x, a, b, d, e, output y1, z1, w1, y2, z2, w2);\n"
			"  mid m1(d);\n"
			"  mid m2(e);\n"
			"  wrap u1(a, y1, z1, w1);\n"
			"  wrap u2(b, y2, z2, w2);\n"
			"endmodule\n");
	verific_import(&design, {}, "top", {.throw_errors = true, .route_all_refs = true});
	Pass::call(&design, "flatten");
	Module *top = design.module(RTLIL::escape_id("top"));
	for (int x = 0; x < 2; x++)
	for (int d = 0; d < 2; d++) {
		ConstEval ce(top);
		for (auto [name, value] : {std::pair{"x", x}, {"a", 1}, {"b", 0}, {"d", d}, {"e", 0}})
			ce.set(top->wire(RTLIL::escape_id(name)), Const(value, 1));
		auto eval = [&](const char *name) {
			SigSpec sig = top->wire(RTLIL::escape_id(name));
			return ce.eval(sig) ? sig.as_int() : -1; // -1: undriven
		};
		EXPECT_EQ(eval("y1"), x);
		EXPECT_EQ(eval("y2"), x);
		EXPECT_EQ(eval("z1"), x);
		EXPECT_EQ(eval("z2"), 0);
		EXPECT_EQ(eval("w1"), !d);
		EXPECT_EQ(eval("w2"), !d);
	}
}

TEST_F(VerificImportTest, ExtNetsRouteInEveryInstanceOfASharedModule)
{
	Design design;
	analyze(design, "module child(input a, output y); assign y = mid.r & a; endmodule\n"
			"module mid(input x, a, output y); wire r = ~x; child c(a, y); endmodule\n"
			"module top(input x1, x2, a, output y1, y2); mid m1(x1, a, y1); mid m2(x2, a, y2); endmodule\n");
	verific_import(&design, {}, "top");
	// opt_clean, for the buffers VerificExtNets inserts
	Pass::call(&design, "flatten; opt_clean");
	Module *top = design.module(RTLIL::escape_id("top"));
	ConstEval ce(top);
	for (auto [name, value] : {std::pair{"x1", 0}, {"x2", 1}, {"a", 1}})
		ce.set(top->wire(RTLIL::escape_id(name)), Const(value, 1));
	SigSpec y = {top->wire(ID(y2)), top->wire(ID(y1))};
	ASSERT_TRUE(ce.eval(y));
	EXPECT_EQ(y.as_const(), Const(0b01, 2));
}

TEST_F(VerificImportTest, SvaContinueImportsTheRestOfTheModule)
{
	Design failed, continued;
	// disable iff in a procedural assertion, which the SVA importer can't read in that context
	const char *sv = "module top(input clk, rst, en, req, output reg ack);\n"
			 "  always @(posedge clk) ack <= req;\n"
			 "  always @(posedge clk) if (en) begin\n"
			 "    gated: assert property (disable iff (rst) req |=> ack);\n"
			 "  end\n"
			 "  plain: assert property (@(posedge clk) req |=> ack);\n"
			 "endmodule\n";
	analyze(failed, sv);
	try {
		verific_import(&failed, {}, "top", {.keep_state = true, .throw_errors = true});
		FAIL() << "no VerificImportError";
	} catch (const VerificImportError &e) {
		EXPECT_EQ(e.module, "top");
	}
	verific_import(&continued, {}, "top", {.throw_errors = true, .sva_continue = true});
	Module *top = continued.module(RTLIL::escape_id("top"));
	ASSERT_NE(top, nullptr);
	Cell *gated = top->cell(RTLIL::escape_id("gated")), *plain = top->cell(RTLIL::escape_id("plain"));
	ASSERT_NE(gated, nullptr);
	ASSERT_NE(plain, nullptr);
	EXPECT_TRUE(gated->get_bool_attribute(ID(unsupported_sva)));
	EXPECT_EQ(gated->getPort(ID::A), SigSpec(State::Sx));
	EXPECT_FALSE(plain->get_bool_attribute(ID(unsupported_sva)));
	EXPECT_FALSE(plain->getPort(ID::A).is_fully_const());
}

YOSYS_NAMESPACE_END

#endif
