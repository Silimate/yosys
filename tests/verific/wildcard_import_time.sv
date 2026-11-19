// A time is not the same value in packages with different time units, though written the same
package pkg_ns;
	timeunit 1ns;
	timeprecision 1ps;
	localparam int unsigned Delay = 1ns;
endpackage

package pkg_ps;
	timeunit 1ps;
	timeprecision 1ps;
	localparam int unsigned Delay = 1ns;
endpackage

module top
	import pkg_ns::*;
	import pkg_ps::*;
(
	output logic [31:0] d
);
	timeunit 1ns;
	timeprecision 1ps;
	assign d = Delay;
endmodule
