if (YOSYS_ENABLE_VERIFIC)
	# user-facing options
	option(WITH_VERIFIC_SYSTEMVERILOG "Enable Verific SystemVerilog support" ON)
	option(WITH_VERIFIC_VHDL "Enable Verific VHDL support" ON)
	option(WITH_VERIFIC_HIER_TREE "Enable Verific hier_tree component" ON)
	option(WITH_VERIFIC_SILIMATE_EXTENSIONS "Enable Silimate-specific Verific modifications" ON)
	option(WITH_VERIFIC_YOSYSHQ_EXTENSIONS "Enable YosysHQ-specific Verific modifications" OFF)
	option(WITH_VERIFIC_EDIF "Enable Verific EDIF support" OFF)
	option(WITH_VERIFIC_LIBERTY "Enable Verific Liberty file support" OFF)
	option(WITH_VERIFIC_UPF "Enable Verific UPF support (requires Tcl support)" OFF)

	# further checks and conditions
	condition(ENABLE_VERIFIC_SYSTEMVERILOG WITH_VERIFIC_SYSTEMVERILOG)
	condition(ENABLE_VERIFIC_VHDL WITH_VERIFIC_VHDL)
	condition(ENABLE_VERIFIC_HIER_TREE WITH_VERIFIC_HIER_TREE)
	condition(ENABLE_VERIFIC_SILIMATE_EXTENSIONS WITH_VERIFIC_SILIMATE_EXTENSIONS)
	condition(ENABLE_VERIFIC_YOSYSHQ_EXTENSIONS WITH_VERIFIC_YOSYSHQ_EXTENSIONS)
	condition(ENABLE_VERIFIC_EDIF WITH_VERIFIC_EDIF)
	condition(ENABLE_VERIFIC_LIBERTY WITH_VERIFIC_LIBERTY)
	condition(ENABLE_VERIFIC_UPF WITH_VERIFIC_UPF AND YOSYS_ENABLE_TCL)

	# construct component list
	if (ENABLE_VERIFIC_SYSTEMVERILOG)
		list(APPEND YOSYS_VERIFIC_COMPONENTS verilog)
	endif()
	list(APPEND YOSYS_VERIFIC_COMPONENTS database util containers pct)
	if (ENABLE_VERIFIC_HIER_TREE)
		list(APPEND YOSYS_VERIFIC_COMPONENTS hier_tree)
	endif()
	if (ENABLE_VERIFIC_VHDL)
		list(APPEND YOSYS_VERIFIC_COMPONENTS vhdl)
	endif()
	if (ENABLE_VERIFIC_EDIF)
		list(APPEND YOSYS_VERIFIC_COMPONENTS edif)
	endif()
	if (ENABLE_VERIFIC_LIBERTY)
		list(APPEND YOSYS_VERIFIC_COMPONENTS synlib)
	endif()
	if (ENABLE_VERIFIC_UPF)
		list(APPEND YOSYS_VERIFIC_COMPONENTS hdl_file_sort verilog_nl commands upf)
	endif()
	if (ENABLE_VERIFIC_YOSYSHQ_EXTENSIONS)
		list(APPEND YOSYS_VERIFIC_COMPONENTS extensions)
	endif()

	# Prepare verific interface library as in YosysVerific.cmake
	add_library(verific INTERFACE)
	get_verific_options(verific_include_dirs verific_libraries ${YOSYS_VERIFIC_COMPONENTS})
	target_include_directories(verific INTERFACE
		${verific_include_dirs}
	)

	if (NOT YOSYS_VERIFIC_FEATURES)
		foreach (component ${YOSYS_VERIFIC_COMPONENTS})
			if (component MATCHES "^(hier_tree|vhdl|edif|extensions)$")
				list(APPEND YOSYS_VERIFIC_FEATURES ${component})
			elseif (component STREQUAL "verilog")
				list(APPEND YOSYS_VERIFIC_FEATURES systemverilog)
			elseif (component STREQUAL "synlib")
				list(APPEND YOSYS_VERIFIC_FEATURES liberty)
			endif()
		endforeach()
	endif()

	message(STATUS "Verific library components: ${YOSYS_VERIFIC_COMPONENTS}")
	message(STATUS "Verific frontend features: ${YOSYS_VERIFIC_FEATURES}")

	set(verific_data_files)
	if ("vhdl" IN_LIST YOSYS_VERIFIC_FEATURES)
		foreach (vdb_std 1987 1993 2008 2019)
			set(vdb_std_root ${YOSYS_VERIFIC_DIR}/vhdl_packages/vdbs_${vdb_std})
			file(GLOB_RECURSE vdb_files RELATIVE ${vdb_std_root} ${vdb_std_root}/*)
			foreach (vdb_file ${vdb_files})
				list(APPEND verific_data_files
					verific/vhdl_vdbs_${vdb_std}/${vdb_file}
					${YOSYS_VERIFIC_DIR}/vhdl_packages/vdbs_${vdb_std}/${vdb_file}
				)
			endforeach()
		endforeach()
	endif()

	# Compiled from Verific's source; its flex and bison outputs are checked in. Headers are installed
	# for code that calls Verific's API: each compiled package's and, with SystemVerilog, the std
	# package's source
	foreach (component ${YOSYS_VERIFIC_COMPONENTS})
		file(GLOB component_sources ${YOSYS_VERIFIC_DIR}/${component}/*.cpp)
		list(APPEND verific_sources ${component_sources})
		file(GLOB component_headers RELATIVE ${YOSYS_VERIFIC_DIR} ${YOSYS_VERIFIC_DIR}/${component}/*.h)
		foreach (header ${component_headers})
			list(APPEND verific_data_files include/verific/${header} ${YOSYS_VERIFIC_DIR}/${header})
		endforeach()
	endforeach()
	if ("verilog" IN_LIST YOSYS_VERIFIC_COMPONENTS)
		list(APPEND verific_data_files
			include/verific/verilog_packages/std.sv ${YOSYS_VERIFIC_DIR}/verilog_packages/std.sv
		)
	endif()
	add_library(verific_source STATIC ${verific_sources})
	target_include_directories(verific_source PRIVATE ${verific_include_dirs})
	target_link_libraries(verific_source PUBLIC PkgConfig::zlib)
	target_link_libraries(verific INTERFACE $<LINK_LIBRARY:WHOLE_ARCHIVE,verific_source>)
else()
	condition(ENABLE_VERIFIC_SILIMATE_EXTENSIONS OFF)
endif()
