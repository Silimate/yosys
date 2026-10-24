#include <gmock/gmock.h>
#include <gtest/gtest.h>
#include "kernel/yosys.h"
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

YOSYS_NAMESPACE_END

#endif
