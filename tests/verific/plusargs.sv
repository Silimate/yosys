module top(output logic [7:0] o, output logic f);
	logic [7:0] n;
	always_comb begin
		n = 8'd5;
		f = $value$plusargs("N=%d", n);
		o = $test$plusargs("FOO") ? 8'd1 : 8'd2;
	end
endmodule
