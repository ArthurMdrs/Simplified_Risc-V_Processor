module mux #(
    int N_INPUTS = 2,
    int DWIDTH = 8
) (
    output logic [DWIDTH-1:0] out,
    input  logic [DWIDTH-1:0] in [N_INPUTS],
    input  logic [$clog2(N_INPUTS)-1:0] sel
);

always_comb begin
    out = 'x;
    for (int i = 0; i < N_INPUTS; i++) begin
        if (sel == i)
            out = in[i];
    end
end

    

`ifdef SVA_ON

`ifndef SIM

bind mux mux_vc #(
    .N_INPUTS(N_INPUTS),
    .DWIDTH(DWIDTH)
) mux_vc_inst (
    .out,
    .in,
    .sel
);

`endif

`endif
    
endmodule