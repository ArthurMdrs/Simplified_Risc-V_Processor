module alu_vc #(
    int SWIDTH = 3,
    int DWIDTH = 8
) (
	input  logic [DWIDTH-1:0] res, 
	input  logic              res_is_0,
	input  logic [DWIDTH-1:0] src1,
	input  logic [DWIDTH-1:0] src2,
	input  logic [SWIDTH-1:0] sel
);

`ifdef SVA_ON

`ifndef SIM

// Properties
property SIGNAL_CAN_BE_VALUE (signal, value);
    (signal == value);
endproperty

// property VALID_OPERATIONS ();
//     (res == src1 & src2)      ||
//     (res == src1 | src2)      ||
//     (res == src1 + src2)      ||
//     (res == src1 + ~src2 + 1) ||
//     (res == src1 < src2)         ;
// endproperty

// Assertions
// AST_VALID_OPERATIONS: assert property (VALID_OPERATIONS); // This doesn't work!

// Covers
generate
    for (genvar i = 0; i < DWIDTH; i++) begin
        COV_RES_CAN_BE_VAL: cover property (SIGNAL_CAN_BE_VALUE(res, 2**i-1));
    end
endgenerate

// Assumes 
property VALID_SEL;
    (sel == 0) || (sel == 1) || (sel == 2) || (sel == 6) || (sel == 7);
endproperty
ASM_VALID_SEL: assume property (VALID_SEL);

`endif

`endif

endmodule