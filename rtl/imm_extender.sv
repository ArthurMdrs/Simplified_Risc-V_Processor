module imm_extender import typedefs_pkg::*; #(
    int DWIDTH = 32
) (
    output logic [DWIDTH-1:0] imm_ext,
    input  instr_t            instr
);

always_comb begin
    AST_DWIDTH_MORE_THAN_IMM_SIZE: assert (DWIDTH > 12);
    case(instr.I.opcode)
        OP_IMM : imm_ext = {{(DWIDTH-12){instr.I[31]}}, instr.I.imm};
        LOAD   : imm_ext = {{(DWIDTH-12){instr.I[31]}}, instr.I.imm};
        JALR   : imm_ext = {{(DWIDTH-12){instr.I[31]}}, instr.I.imm};
        STORE  : imm_ext = {{(DWIDTH-12){instr.S[31]}}, instr.S.imm_up, instr.S.imm_dn};
        BRANCH : imm_ext = {{(DWIDTH-11){instr.B[31]}}, instr.B.imm_12, instr.B.imm_11, instr.B.imm_10_5, instr.B.imm_4_1, 1'b0};
        JAL    : imm_ext = {{(DWIDTH-11){instr.J[31]}}, instr.J.imm_20, instr.J.imm_19_12, instr.J.imm_11, instr.J.imm_10_1, 1'b0};
        LUI    : imm_ext = {instr.U.imm, {(DWIDTH-20){1'b0}}};
        AUIPC  : imm_ext = {instr.U.imm, {(DWIDTH-20){1'b0}}};
        default: imm_ext = 'x;
    endcase
end

endmodule