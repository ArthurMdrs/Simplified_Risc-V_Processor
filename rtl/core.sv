module core (
    input  logic clk,
    input  logic rst_n,

    // Interface with data memory
    input  logic [31:0] dmem_rdata,
    output logic [31:0] dmem_wdata,
    output logic [31:0] dmem_addr,
    output logic        dmem_wen,
    output logic  [3:0] dmem_wr_mask,

    // Interface with instruction memory
    input  logic [31:0] imem_rdata,
    output logic [31:0] imem_addr
);

import typedefs_pkg::*;

// Program counter
logic [31:0] pc_next, pc;
// Instruction
instr_t instr;

// Control signals
aluop_sel_t alu_sel;
logic       alu_src1;
logic       alu_src2;
logic       mem_wen;
logic       reg_wen;
logic [1:0] pc_src;
logic [1:0] reg_wdata_src;

// Internal wires
logic [31:0] rdata1;
logic [31:0] rdata2;
logic [31:0] alu_op1;
logic [31:0] alu_op2;
logic [31:0] imm;
logic [31:0] load_word;
logic [31:0] load_ext;
logic [31:0] reg_wdata;
logic [31:0] alu_res;
logic        res_is_0;

//==============   Module instantiations - BEGIN   ==============//

next_pc_value #(
    .WIDTH(32)
) next_pc_val_inst (
    .next_pc(pc_next),
    .curr_pc(pc), 
    .alu_res,
    .pc_src,
    .imm
);

register #(
    .WIDTH(32)
) pc_reg (
	.reg_o(pc),
	.reg_i(pc_next),
	.clk, 
	.rst_n
);

ctrl_unit ctrl_unit_inst (
	.alu_sel,
    .alu_src1, 
    .alu_src2, 
    .mem_wen, 
    .reg_wen, 
    .pc_src, 
    .reg_wdata_src,
	.opcode(instr.R.opcode),
	.funct7(instr.R.funct7),
	.funct3(instr.R.funct3),
    .ops_equal(res_is_0),
    .op1_lt_op2(alu_res[0])
);

mux #(
    .N_INPUTS(4),
    .DWIDTH(32)
) mux_reg_wdata (
    .out(reg_wdata),
    .in({ alu_res,  load_ext,  pc+4,  imm }),
    .sel(reg_wdata_src)
);

register_bank #(
    .AWIDTH(5),
    .DWIDTH(32)
) register_bank_inst (
    .rdata1(rdata1),
    .rdata2(rdata2),
    .raddr1(instr.R.rs1),
    .raddr2(instr.R.rs2),
    .wdata (reg_wdata),
    .waddr (instr.R.rd),
    .wen(reg_wen),
    .clk,
    .rst_n
);

alu #(
    .DWIDTH(32)
) alu_inst (
	.res(alu_res), 
	.res_is_0,
	.src1(alu_op1),
	.src2(alu_op2),
	.sel(alu_sel)
);

mux #(
    .N_INPUTS(2),
    .DWIDTH(32)
) mux_alu_src1 (
    .out(alu_op1),
    .in({ rdata1,  pc }),
    .sel(alu_src1)
);

mux #(
    .N_INPUTS(2),
    .DWIDTH(32)
) mux_alu_src2 (
    .out(alu_op2),
    .in({ rdata2,  imm }),
    .sel(alu_src2)
);

imm_extender #(
    .DWIDTH(32)
) imm_ext_inst (
    .imm_ext(imm),
    .instr
);

load_extender #(
    .DWIDTH(32)
) load_ext_inst (
    .load_ext,
    .instr,
    .load_word
);

//==============   Module instantiations - END   ==============//

// Signals from data memory interface

assign load_word  = dmem_rdata;

assign dmem_wdata = rdata2;
assign dmem_addr  = alu_res;
assign dmem_wen   = mem_wen;

always_comb begin // dmem_wr_mask
    case (instr.S.funct3)
        0: dmem_wr_mask = 4'b0001;
        1: dmem_wr_mask = 4'b0011;
        2: dmem_wr_mask = 4'b1111;
        default: dmem_wr_mask = '0;
    endcase
end



// Signals from instruction memory interface

assign instr = imem_rdata;

assign imem_addr = pc;

endmodule