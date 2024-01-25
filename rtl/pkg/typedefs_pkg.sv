package typedefs_pkg;

    typedef enum logic [2:0] {
        AND, OR, ADD, XOR, SUB, SLT
    } aluop_sel_t;

    typedef struct packed {
        logic [6:0] funct7;
        logic [4:0] rs2;
        logic [4:0] rs1;
        logic [2:0] funct3;
        logic [4:0] rd;
        logic [6:0] opcode;
    } R_instr;

    typedef struct packed {
        logic [11:0] imm;
        logic [4:0]  rs1;
        logic [2:0]  funct3;
        logic [4:0]  rd;
        logic [6:0]  opcode;
    } I_instr;

    typedef struct packed {
        logic [6:0] imm_up;
        logic [4:0] rs2;
        logic [4:0] rs1;
        logic [2:0] funct3;
        logic [4:0] imm_dn;
        logic [6:0] opcode;
    } S_instr;

    typedef struct packed {
        logic       imm_12;
        logic [5:0] imm_10_5;
        logic [4:0] rs2;
        logic [4:0] rs1;
        logic [2:0] funct3;
        logic [3:0] imm_4_1;
        logic       imm_11;
        logic [6:0] opcode;
    } B_instr;

    typedef struct packed {
        logic [19:0] imm;
        logic [4:0]  rd;
        logic [6:0]  opcode;
    } U_instr;

    typedef struct packed {
        logic       imm_20;
        logic [9:0] imm_10_1;
        logic       imm_11;
        logic [7:0] imm_19_12;
        logic [4:0] rd;
        logic [6:0] opcode;
    } J_instr;

    typedef union packed {
        R_instr R;
        I_instr I;
        S_instr S;
        B_instr B;
        U_instr U;
        J_instr J;
    } instr_t;

    typedef enum logic [2:0] {
        R, I, S, B, U, J
    } instr_type_t;

    // opcodes
    localparam logic [6:0] OP_IMM = 7'b001_0011, OP = 7'b011_0011;

endpackage 