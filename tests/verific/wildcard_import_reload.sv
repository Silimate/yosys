// pkg_a is analyzed again (wildcard_import_reload_pkg.sv) while top, which imports it, is kept
package pkg_a;
	localparam int unsigned Width = 8;
	localparam int unsigned A_ONLY = 1;
endpackage

package pkg_b;
	localparam int unsigned Width = 16;
endpackage

module top
	import pkg_a::A_ONLY;
(
	output logic [31:0] w
);
	`include "wildcard_import_first_a.svh"
	import pkg_b::*;
	assign w = Width;
endmodule
