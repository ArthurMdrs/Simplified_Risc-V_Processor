module ctrl_unit import typedefs_pkg::*; #(
    int WIDTH = 8
) (
	output aluop_sel_t alu_sel,
	// output logic Jump, 
    // output logic MemtoReg, 
    // output logic MemWrite, 
    // output logic BNE, 
    // output logic BEQ, 
    output logic alu_src, 
    // output logic RegDst, 
    output logic wen, 
    // output logic Ext, 
	input  logic [6:0] opcode,
	input  logic [6:0] funct7,
	input  logic [2:0] funct3
);

    // Drive ALU operation selection
    always_comb begin
        alu_sel = ADD;
        if (opcode == OP)
            case (funct3)
                3'h0: begin
                    if (funct7 == 7'h00) alu_sel = ADD; 
                    if (funct7 == 7'h20) alu_sel = SUB; 
                end
                3'h1: 
                    ;// alu_sel = SLL;
                3'h2: 
                    alu_sel = SLT;
                3'h3: 
                    ;// alu_sel = SLTU;
                3'h4:
                    alu_sel = XOR;
                3'h5: begin
                    // if (funct7 == 7'h00) alu_sel = SRL; 
                    // if (funct7 == 7'h20) alu_sel = SRA; 
                end
                3'h6:
                    alu_sel = OR;
                3'h7:
                    alu_sel = AND;
            endcase
    end

    // Drive ULA source selection
    always_comb begin
        alu_src = 0;
        case (opcode)
            OP    : alu_src = 0;
            OP_IMM: alu_src = 1;
        endcase
    end

    // Drive register write enable
    always_comb begin
        wen = 1;
    end
    
endmodule