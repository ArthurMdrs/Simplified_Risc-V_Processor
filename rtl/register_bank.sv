module register_bank #(
    int AWIDTH = 3,
    int DWIDTH = 8
) (
    output logic [DWIDTH-1:0] rdata1,
    output logic [DWIDTH-1:0] rdata2,
    input  logic [AWIDTH-1:0] raddr1,
    input  logic [AWIDTH-1:0] raddr2,
    input  logic [DWIDTH-1:0] wdata,
    input  logic [AWIDTH-1:0] waddr,
    input  logic              wen,
    input  logic              clk,
    input  logic              rst_n
);

// Internal memory
logic [DWIDTH-1:0] mem [2**AWIDTH];

`ifdef USE_BSC_BLKS

    // Decode address
    logic [2**AWIDTH-1:0] waddr_1hot;
    decoder #(.INWIDTH(AWIDTH)) decoder_inst (.out(waddr_1hot), .in(waddr));

    // Drive registers load signal
    logic [2**AWIDTH-1:0] load;
    assign load = waddr_1hot & {(2**AWIDTH-1){wen}};

    // Define write operation
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mem <= '{(2**AWIDTH){0}};
        end else begin
            foreach (mem[i])
                if (load[i] && i != '0)
                    mem[i] <= wdata;
        end
    end

    // Define read operation
    mux #(.N_INPUTS(2**AWIDTH), .DWIDTH(DWIDTH)) mux_inst1 (.out(rdata1), .in(mem), .sel(raddr1));
    mux #(.N_INPUTS(2**AWIDTH), .DWIDTH(DWIDTH)) mux_inst2 (.out(rdata2), .in(mem), .sel(raddr2));



`else // Higher level code below

    // Define write operation
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mem <= '{(2**AWIDTH){0}};
        end else begin
            if (wen && waddr != 0)
                mem[waddr] <= wdata;
        end
    end

    // Define read operation
    always_comb begin
        rdata1 = mem[raddr1];
        rdata2 = mem[raddr2];
    end

`endif

    

`ifdef SVA_ON

bind register_bank register_bank_vc #(
    .AWIDTH(AWIDTH),
    .DWIDTH(DWIDTH)
) register_bank_vc_inst (
    .rdata1,
    .rdata2,
    .raddr1,
    .raddr2,
    .wdata,
    .waddr,
    .wen,
    .clk,
    .rst_n
);

`endif
    
endmodule