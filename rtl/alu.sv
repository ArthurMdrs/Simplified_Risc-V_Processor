module alu import typedefs_pkg::*; #(
    // int SWIDTH = 3,
    int DWIDTH = 8
) (
	output logic [DWIDTH-1:0] res, 
	output logic              res_is_0,
	input  logic [DWIDTH-1:0] src1,
	input  logic [DWIDTH-1:0] src2,
	// input  logic [SWIDTH-1:0] sel
    input  aluop_sel_t        sel
);

// typedef bit [SWIDTH-1:0] sel_t;
// localparam sel_t AND = 0, OR  = 1, ADD = 2, XOR = 3, SUB = 6, SLT = 7;

always_comb
    case (sel)
        AND: res = src1 & src2;
        OR : res = src1 | src2;
        ADD: res = src1 + src2;
        XOR: res = src1 ^ src2;
        SUB: res = src1 + ~src2 + 1;
        SLT: res = (src1 < src2);
        default: res = 0;
    endcase

assign res_is_0 = (res == 0);


    
`ifdef SVA_ON

bind alu alu_vc #(
    // .SWIDTH(SWIDTH),
    .DWIDTH(DWIDTH)
) alu_vc_inst (
	.res, 
	.res_is_0,
	.src1,
	.src2,
	.sel
);

`endif
endmodule