module ctrl_unit import typedefs_pkg::*; #(
    int WIDTH = 8
) (
	output aluop_sel_t alu_sel,
    output logic alu_src1, 
    output logic alu_src2, 
    output logic mem_wen, 
    output logic reg_wen, 
    output logic [1:0] pc_src, 
    output logic [1:0] reg_wdata_src, 
	input  logic [6:0] opcode,
	input  logic [6:0] funct7,
	input  logic [2:0] funct3,
    input  logic ops_equal,
    input  logic op1_lt_op2
);

// Drive ALU operation selection (typedef in pkg)
always_comb begin
    alu_sel = 'x;
    if (opcode == OP || opcode == OP_IMM)
        case (funct3)
            3'h0: begin
                if (funct7 == 7'h00 || opcode == OP_IMM) alu_sel = ADD; 
                else if (funct7 == 7'h20)                alu_sel = SUB; 
            end
            3'h1: 
                alu_sel = SLL;
            3'h2: 
                alu_sel = SLT;
            3'h3: 
                alu_sel = SLTU;
            3'h4:
                alu_sel = XOR;
            3'h5: begin
                if (funct7 == 7'h00) alu_sel = SRL; 
                if (funct7 == 7'h20) alu_sel = SRA; 
            end
            3'h6:
                alu_sel = OR;
            3'h7:
                alu_sel = AND;
        endcase

    else if (opcode == BRANCH)
        case (funct3)
            3'h0: 
                alu_sel = SUB;  // beq
            3'h1: 
                alu_sel = SUB;  // bne
            3'h4:
                alu_sel = SLT;  // blt
            3'h5: 
                alu_sel = SLT;  // bge
            3'h6:
                alu_sel = SLTU; // bltu
            3'h7:
                alu_sel = SLTU; // bgeu
        endcase

    else if (opcode == STORE || opcode == LOAD)
        alu_sel = ADD;

    else if (opcode == JALR)
        alu_sel = ADD;

    else if (opcode == AUIPC)
        alu_sel = ADD;
end

// Drive ALU source selection
// alu_src1 = 0 -> 1st ALU source is reg bank
// alu_src1 = 1 -> 1st ALU source is PC
// alu_src2 = 0 -> 2nd ALU source is reg bank
// alu_src2 = 1 -> 2nd ALU source is immediate operand
always_comb begin
    alu_src2 = 'x;
    case (opcode)
        OP    : alu_src2 = 0;
        OP_IMM: alu_src2 = 1;
        LOAD  : alu_src2 = 1;
        STORE : alu_src2 = 1;
        BRANCH: alu_src2 = 0;
        JALR  : alu_src2 = 1;
        AUIPC : alu_src2 = 1;
    endcase

    alu_src1 = 'x;
    case (opcode)
        OP    : alu_src1 = 0;
        OP_IMM: alu_src1 = 0;
        LOAD  : alu_src1 = 0;
        STORE : alu_src1 = 0;
        BRANCH: alu_src1 = 0;
        JALR  : alu_src1 = 0;
        AUIPC : alu_src1 = 1;
    endcase
end

// Drive data memory write enable
assign mem_wen = (opcode == STORE);

// Drive register write enable
assign reg_wen = (opcode inside {OP, OP_IMM, LOAD, JAL, JALR, LUI, AUIPC});

// Drive pc_src signal
// pc_src = 2'b00 -> next PC = PC + 4
// pc_src = 2'b01 -> next PC = branch/jump target
// pc_src = 2'b10 -> next PC = return address register
always_comb begin
    pc_src = 2'b00;
    if(opcode == BRANCH)
        case (1'b1)
            (funct3==0 &&  ops_equal):  // beq
                pc_src = 2'b01;
            (funct3==1 && !ops_equal):  // bne
                pc_src = 2'b01;
            (funct3==4 &&  op1_lt_op2): // blt
                pc_src = 2'b01;
            (funct3==5 && !op1_lt_op2): // bge
                pc_src = 2'b01;
            (funct3==6 &&  op1_lt_op2): // bltu
                pc_src = 2'b01;
            (funct3==7 && !op1_lt_op2): // bgeu
                pc_src = 2'b01;
        endcase
    else if (opcode == JAL)
        pc_src = 2'b01;
    else if (opcode == JALR)
        pc_src = 2'b10;
end

// Drive result source
// reg_wdata_src = 2'b00 -> reg bank wdata is ALU result
// reg_wdata_src = 2'b01 -> reg bank wdata is data mem rdata
// reg_wdata_src = 2'b10 -> reg bank wdata is PC + 4
// reg_wdata_src = 2'b11 -> reg bank wdata is immediate (LUI)
always_comb begin
    reg_wdata_src = 'x;
    case (opcode)
        OP    : reg_wdata_src = 2'b00;
        OP_IMM: reg_wdata_src = 2'b00;
        LOAD  : reg_wdata_src = 2'b01;
        JAL   : reg_wdata_src = 2'b10;
        JALR  : reg_wdata_src = 2'b10;
        LUI   : reg_wdata_src = 2'b11;
        AUIPC : reg_wdata_src = 2'b00;
    endcase
end
    
endmodule