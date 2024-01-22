module register_bank_vc #(
    int AWIDTH = 3,
    int DWIDTH = 8
) (
    input  logic [DWIDTH-1:0] rdata1,
    input  logic [DWIDTH-1:0] rdata2,
    input  logic [AWIDTH-1:0] raddr1,
    input  logic [AWIDTH-1:0] raddr2,
    input  logic [DWIDTH-1:0] wdata,
    input  logic [AWIDTH-1:0] waddr,
    input  logic              wen,
    input  logic              clk,
    input  logic              rst_n
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

property MEM0_ALWAYS_0 (addr, rdata);
    (addr == 0) |-> SIGNAL_CAN_BE_VALUE (rdata, 0);
endproperty

property NO_RDATA_WO_WRITE (rdata);
    (rdata != 0) |-> (write_happened);
endproperty



// Assertions
AST_MEM0_ALWAYS_0_1: assert property (MEM0_ALWAYS_0(raddr1, rdata1));
AST_MEM0_ALWAYS_0_2: assert property (MEM0_ALWAYS_0(raddr2, rdata2));
AST_NO_RDATA_WO_WRITE1: assert property (NO_RDATA_WO_WRITE(rdata1));
AST_NO_RDATA_WO_WRITE2: assert property (NO_RDATA_WO_WRITE(rdata2));



// Covers
generate
    for (genvar i = 0; i < DWIDTH; i++) begin
        COV_RDATA1_CAN_BE_VAL: cover property (SIGNAL_CAN_BE_VALUE(rdata1, 2**i-1));
        COV_RDATA2_CAN_BE_VAL: cover property (SIGNAL_CAN_BE_VALUE(rdata1, 2**i+1));
    end
endgenerate



`ifndef SIM

// Data integrity check (NDC only possible in formal!)

bit [AWIDTH-1:0] addr_ndc; // Non-deterministic constant
bit [DWIDTH-1:0] xptd_data; // Expected data
bit wr_to_addr_ndc; // Write to addr_ndc location
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        xptd_data <= '0;
        wr_to_addr_ndc <= 0;
    end else if (wen && waddr == addr_ndc) begin
        xptd_data <= wdata;
        wr_to_addr_ndc <= 1;
    end
end

property DATA_INTEGRITY (raddr, rdata);
    (wr_to_addr_ndc && raddr == addr_ndc) |-> (rdata == xptd_data);
endproperty 

AST_DATA_INTEGRITY1: assert property (DATA_INTEGRITY(raddr1, rdata1));
AST_DATA_INTEGRITY2: assert property (DATA_INTEGRITY(raddr2, rdata2));

ASM_ADDR_NDC_NOT_0: assume property (addr_ndc != '0);
ASM_ADDR_NDC_CONST: assume property (addr_ndc == $past(addr_ndc));

`endif
    
`endif

endmodule