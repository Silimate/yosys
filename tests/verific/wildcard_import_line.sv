// `line directives renumber lines, but not the order of the wildcard imports
package pkg_a;
	localparam int unsigned Width = 8;
endpackage

package pkg_b;
	localparam int unsigned Width = 16;
endpackage

module top (
	output logic [31:0] w
);
`line 100 "wildcard_import_line.sv" 0
	import pkg_a::*;
`line 10 "wildcard_import_line.sv" 0
	import pkg_b::*;
`line 200 "wildcard_import_line.sv" 0
	assign w = Width;
endmodule
