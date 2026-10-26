module sdffe_pp( input clk, rst, en,
			input [1:0] d1, output reg [1:0] q1,
		);
	always @( posedge clk ) begin
		if ( rst )
			q1 <= 0;
		else if ( en )
			q1 <= d1;
	end
endmodule

module sdffe_nn( input clk, rst, en,
			input [1:0] d1, output reg [1:0] q1,
		);
	always @( posedge clk ) begin
		if ( ~rst )
			q1 <= 2'b10;
		else if ( ~en )
			q1 <= d1;
	end
endmodule

module sdffe_two_rst( input clk, rst1, rst2, en,
			input d1, d2, output reg q1, q2,
		);
	always @( posedge clk ) begin
		if ( rst1 )
			q1 <= 0;
		else if ( en )
			q1 <= d1;
		if ( rst2 )
			q2 <= 1;
		else if ( en )
			q2 <= d2;
	end
endmodule

module sdffce( input clk, rst, en,
			input d1, output reg q1,
		);
	always @( posedge clk ) begin
		if ( en ) begin
			if ( rst )
				q1 <= 0;
			else
				q1 <= d1;
		end
	end
endmodule

module sdffe_neg( input clk, rst, en,
			input [1:0] d1, output reg [1:0] q1,
		);
	always @( negedge clk ) begin
		if ( rst )
			q1 <= 0;
		else if ( en )
			q1 <= d1;
	end
endmodule
