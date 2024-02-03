module ctrl_unit import typedefs_pkg::*; #(
    int WIDTH = 8
) (
	output aluop_sel_t alu_sel,
    output logic alu_src, 
    output logic mem_wen, 
    output logic reg_wen, 
    output logic branch, 
    output logic reg_wdata_src, 
	input  logic [6:0] opcode,
	input  logic [6:0] funct7,
	input  logic [2:0] funct3,
    input  logic ops_equal,
    input  logic op1_lt_op2
);

// Drive ALU operation selection (typedef in pkg)
always_comb begin
    alu_sel = ADD;
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
end

// Drive ALU source selection
// alu_src = 0 -> 2nd ALU source is reg bank
// alu_src = 1 -> 2nd ALU source is immediate operand
always_comb begin
    alu_src = 0;
    case (opcode)
        OP    : alu_src = 0;
        OP_IMM: alu_src = 1;
        LOAD  : alu_src = 1;
        STORE : alu_src = 1;
        BRANCH: alu_src = 0;
    endcase
end

// Drive data memory write enable
assign mem_wen = (opcode == STORE);

// Drive register write enable
assign reg_wen = (opcode inside {OP, OP_IMM, LOAD});

// Drive branch signal
always_comb begin
    branch = 0;
    if(opcode == BRANCH)
        case (1'b1)
            (funct3==0 &&  ops_equal):  // beq
                branch = 1;
            (funct3==1 && !ops_equal):  // bne
                branch = 1;
            (funct3==4 &&  op1_lt_op2): // blt
                branch = 1;
            (funct3==5 && !op1_lt_op2): // bge
                branch = 1;
            (funct3==6 &&  op1_lt_op2): // bltu
                branch = 1;
            (funct3==7 && !op1_lt_op2): // bgeu
                branch = 1;
        endcase
end

// Drive result source
// reg_wdata_src = 0 -> reg bank wdata is ALU result
// reg_wdata_src = 1 -> reg bank wdata is data mem rdata
assign reg_wdata_src = (opcode == LOAD);
    
endmodule