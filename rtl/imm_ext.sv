module imm_ext import typedefs_pkg::*; #(
    int DWIDTH = 32
) (
    output logic [DWIDTH-1:0] imm_ext,
    input  instr_t            instr
);

assign imm_ext = {{(DWIDTH-12){instr.I[31]}}, instr.I.imm};

// AST_DWIDTH_MORE_THAN_IMM_SIZE: assert property (DWIDTH > 12);

endmodule