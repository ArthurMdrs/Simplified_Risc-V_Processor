module imm_extender import typedefs_pkg::*; #(
    int DWIDTH = 32
) (
    output logic [DWIDTH-1:0] imm_ext,
    input  instr_t            instr
);

always_comb begin
    AST_DWIDTH_MORE_THAN_IMM_SIZE: assert (DWIDTH > 12);
    case(instr.I.opcode)
        OP_IMM: imm_ext = {{(DWIDTH-12){instr.I[31]}}, instr.I.imm};
        LOAD  : imm_ext = {{(DWIDTH-12){instr.I[31]}}, instr.I.imm};
        STORE : imm_ext = {{(DWIDTH-12){instr.I[31]}}, instr.S.imm_up, instr.S.imm_dn};
        default: imm_ext = {{(DWIDTH-12){instr.I[31]}}, instr.I.imm};
    endcase
end

endmodule