module decoder_vc #(
    int INWIDTH = 3
) (
    input  logic [2**INWIDTH-1:0] out,
    input  logic [INWIDTH-1:0] in
);

`ifdef SVA_ON

`ifndef SIM

// Properties
property SIG_IS_ONE_HOT (signal);
    $onehot(signal);
endproperty

// Assertions
AST_OUT_IS_ONE_HOT: assert property (SIG_IS_ONE_HOT(out));

// Covers
generate
    for (genvar i = 0; i < 2**INWIDTH; i++) begin
        COV_OBSERVE_IN: cover property (in == i);
    end
endgenerate

`endif

`endif
    
endmodule