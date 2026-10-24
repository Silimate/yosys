if (YOSYS_ENABLE_VERIFIC)
	yosys_gtest(frontends
		verificImportTest.cc
		COMPONENTS
			read_verific
	)
endif()
