module rom_mem #(
    int AWIDTH = 8,
    int DWIDTH = 32
) (
    output logic [DWIDTH-1:0] rdata,
    input  logic [AWIDTH-1:0] addr
);

// Internal memory
logic [DWIDTH-1:0] mem [2**AWIDTH];

// Drive read data
always_comb begin
    rdata = mem[addr];
end

// NOTE THERE IS NO WRITE OPERATION
// SO THIS IS A ROM!!

// Suggestion: look up an open-source ROM memory IP to replace this
    
endmodule