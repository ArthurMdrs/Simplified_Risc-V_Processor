module register #(
    int WIDTH = 8
) (
	output logic [WIDTH-1:0] reg_o,
	input  logic [WIDTH-1:0] reg_i,
	input  logic             clk, 
	input  logic             rst_n
);
	
	always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            reg_o <= 0;
        else
            reg_o <= reg_i;
    end
	
endmodule