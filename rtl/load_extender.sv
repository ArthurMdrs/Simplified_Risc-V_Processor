module load_extender import typedefs_pkg::*; #(
    int DWIDTH = 32
) (
    output logic [DWIDTH-1:0] load_ext,
    input  instr_t            instr,
    input  logic [DWIDTH-1:0] load_word
);

always_comb begin
    AST_DWIDTH_MORE_THAN_IMM_SIZE: assert (DWIDTH > 8);
    case (instr.I.funct3)
        0: load_ext = {{(DWIDTH- 8){load_word[ 7]}}, load_word[ 7:0]}; // lb
        1: load_ext = {{(DWIDTH-16){load_word[15]}}, load_word[15:0]}; // lh
        2: load_ext = load_word;                                       // lw
        4: load_ext = {{(DWIDTH- 8){        1'b0 }}, load_word[ 7:0]}; // lbu
        5: load_ext = {{(DWIDTH-16){        1'b0 }}, load_word[15:0]}; // lhu
        default: load_ext = 'x;
    endcase
end

endmodule