// Replaces pkg_a of wildcard_import_reload.sv, with one more parameter
package pkg_a;
	localparam int unsigned Width = 8;
	localparam int unsigned A_ONLY = 1;
	localparam int unsigned A_MORE = 2;
endpackage
