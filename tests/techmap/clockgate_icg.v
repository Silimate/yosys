// Latch-based ICG models: CE is captured while the clock is inactive, so clkout cannot glitch

module pdk_icg( input ce, clkin, output clkout );
	reg en;
	always @*
		if ( ~clkin )
			en = ce;
	assign clkout = clkin & en;
endmodule

module pdk_icg_neg( input ce, clkin, output clkout );
	reg en;
	always @*
		if ( clkin )
			en = ce;
	assign clkout = clkin | ~en;
endmodule
