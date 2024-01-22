module decoder #(
    int INWIDTH = 3
) (
    output logic [2**INWIDTH-1:0] out,
    input  logic [INWIDTH-1:0] in
);

always_comb begin
    out = 0;
    out[in] = 1;
end

    

`ifdef SVA_ON

bind decoder decoder_vc #(
    .INWIDTH(INWIDTH)
) decoder_vc_inst (
    .out,
    .in
);

`endif
    
endmodule