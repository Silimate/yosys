// Latch-based ICG model: CE is captured while clkin is low, so clkout cannot glitch
module pdk_icg( input ce, clkin, output clkout );
	reg en;
	always @*
		if ( ~clkin )
			en = ce;
	assign clkout = clkin & en;
endmodule
