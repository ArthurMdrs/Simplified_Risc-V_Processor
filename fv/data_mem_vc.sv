module data_mem_vc #(
    int AWIDTH = 3,
    int DWIDTH = 8,
    localparam int MWIDTH = DWIDTH/8
) (
    input  logic [DWIDTH-1:0] rdata,
    input  logic [DWIDTH-1:0] wdata,
    input  logic [AWIDTH-1:0] addr,
    input  logic              wen,
    input  logic              clk,
    input  logic              rst_n,
    input  logic [MWIDTH-1:0] wdata_mask
);    

`ifdef SVA_ON

// Defaults
default clocking def_clk @(posedge clk); 
endclocking

default disable iff (!rst_n);

// Aux code
bit write_happened;
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        write_happened <= 0;
    else if (wen)
        write_happened <= 1;
end



// Properties
property SIGNAL_CAN_BE_VALUE (signal, value);
    (signal == value);
endproperty

property NO_RDATA_WO_WRITE (rdata);
    (rdata != 0) |-> (write_happened);
endproperty

property VALID_DWIDTH;
    (DWIDTH % 8 == 0);
endproperty

property VALID_MASK (W);
    (wdata_mask inside {0, 1, 3, 15, 255});
    //   0 -> not a store operation
    //   1 -> storing byte
    //   3 -> storing half-word
    //  15 -> storing word
    // 255 -> storing double-word
endproperty

property IF_WEN_THEN_MASK_NOT_0;
    (wen) |-> (wdata_mask != '0);
endproperty



// Assertions
AST_NO_RDATA_WO_WRITE: assert property (NO_RDATA_WO_WRITE(rdata));
AST_VALID_DWIDTH: assert property (VALID_DWIDTH);



// Covers
generate
    for (genvar i = 0; i < DWIDTH; i++) begin
        COV_RDATA_CAN_BE_VAL: cover property (SIGNAL_CAN_BE_VALUE(rdata, 2**i-1));
    end
    for (genvar i = 1; i <= MWIDTH; i = 2*i) begin
        COV_MASK_CAN_BE_VAL: cover property (
            (wdata_mask == 2**i-1) ##[*] (rdata != '0)
        );
    end
endgenerate



// Assumes
ASM_NO_MISALIGNMENT: assume property (addr % 4 == 0);
ASM_VALID_MASK: assume property (VALID_MASK(MWIDTH));
ASM_IF_WEN_THEN_MASK_NOT_0: assume property (IF_WEN_THEN_MASK_NOT_0);



`ifndef SIM

logic [DWIDTH-1:0] big_mask;
always_comb
    foreach (wdata_mask[i])
        big_mask[i*8+:8] = {8{wdata_mask[i]}};

// Data integrity check (NDC only possible in formal!)

bit [AWIDTH-1:0] addr_ndc; // Non-deterministic constant
bit [DWIDTH-1:0] xptd_data; // Expected data
bit wr_to_addr_ndc; // Write happened to addr_ndc location
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        xptd_data <= '0;
        wr_to_addr_ndc <= 0;
    end else if (wen && addr == addr_ndc) begin
        foreach (big_mask[i])
            if (big_mask[i]) xptd_data[i] <= wdata[i];
        wr_to_addr_ndc <= 1;
    end
end

property DATA_INTEGRITY (raddr, rdata);
    (wr_to_addr_ndc && raddr == addr_ndc) |-> (rdata == xptd_data);
endproperty 

AST_DATA_INTEGRITY1: assert property (DATA_INTEGRITY(addr, rdata));

ASM_ADDR_NDC_CONST: assume property (addr_ndc == $past(addr_ndc));

COV_MASK_EQ_0_SANITY: cover property (
    (wdata_mask == '0) ##1 (rdata == xptd_data)
);

`endif
    
`endif

endmodule