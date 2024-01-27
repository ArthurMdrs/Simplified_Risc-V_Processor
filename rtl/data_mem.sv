module data_mem #(
    int AWIDTH = 8,
    int DWIDTH = 8
) (
    output logic [DWIDTH-1:0] rdata,
    input  logic [DWIDTH-1:0] wdata,
    input  logic [AWIDTH-1:0] addr,
    input  logic              wen,
    input  logic              clk,
    input  logic              rst_n
);

// Internal memory
logic [DWIDTH-1:0] mem [2**AWIDTH];

// Define write operation
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        mem <= '{(2**AWIDTH){0}};
    end else begin
        if (wen)
            mem[addr] <= wdata;
    end
end

// Define read operation
assign rdata = mem[addr];

    

`ifdef SVA_ON

bind data_mem data_mem_vc #(
    .AWIDTH(AWIDTH),
    .DWIDTH(DWIDTH)
) data_mem_vc_inst (
    .rdata,
    .wdata,
    .addr,
    .wen,
    .clk,
    .rst_n
);

`endif
    
endmodule