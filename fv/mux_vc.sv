module mux_vc #(
    int N_INPUTS = 2,
    int DWIDTH = 8
) (
    input  logic [DWIDTH-1:0] out,
    input  logic [DWIDTH-1:0] in [N_INPUTS],
    input  logic [$clog2(N_INPUTS)-1:0] sel
);

`ifdef SVA_ON

// Properties
bit [$clog2(N_INPUTS)-1:0] sel_aux; // Non-deterministic constant
property CORRECT_SELECT;
    (sel == sel_aux) |-> (out == in[sel_aux]);
endproperty

// Assertions
AST_CORRECT_SELECT: assert property (CORRECT_SELECT);

// Covers
generate
    for (genvar i = 0; i < N_INPUTS; i++) begin
        COV_OUT_EQUALS_IN: cover property (out == in[i]);
    end
endgenerate

// Assumes
ASM_VALID_SEL: assume property (sel < N_INPUTS);

`endif
    
endmodule