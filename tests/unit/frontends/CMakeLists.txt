if (YOSYS_ENABLE_VERIFIC AND "systemverilog" IN_LIST YOSYS_VERIFIC_FEATURES)
	yosys_gtest(frontends
		verificImportTest.cc
		COMPONENTS
			read_verific
	)
endif()
