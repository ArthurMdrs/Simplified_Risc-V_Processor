module alu import typedefs_pkg::*; #(
    int DWIDTH = 8
) (
	output logic [DWIDTH-1:0] res, 
	output logic              res_is_0,
	input  logic [DWIDTH-1:0] src1,
	input  logic [DWIDTH-1:0] src2,
    input  aluop_sel_t        sel
);

logic signed [DWIDTH-1:0] src1_s, src2_s;
assign src1_s = src1;
assign src2_s = src2;

always_comb
    case (sel)
        AND : res = src1 & src2;
        OR  : res = src1 | src2;
        ADD : res = src1 + src2;
        SUB : res = src1 - src2;
        XOR : res = src1 ^ src2;
        SLT : res = (src1_s < src2_s);
        SLTU: res = (src1   < src2  );
        SLL : res = src1   <<  src2[4:0];
        SRL : res = src1   >>  src2[4:0];
        SRA : res = src1_s >>> src2[4:0];
        default: res = 'x;
    endcase

assign res_is_0 = (res == 0);

endmodule