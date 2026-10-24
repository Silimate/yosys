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

YOSYS_NAMESPACE_END

#endif
