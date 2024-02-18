/* 
    This was the 5rd testbench.

    RTL I had done at the time: alu, ctrl_unit, data_mem, imm_extender, load_extender,
    mux, next_pc_value, register_bank, register (program counter) and rom_mem 
    (instruction memory).

    This is an upgrade from the 4th testbench.

    Opcodes supported: OP, OP-IMM, LOAD, STORE, BRANCH, JAL, JALR.

*/

module jump_tb;

import typedefs_pkg::*;

localparam int XLEN = 32;
localparam int AWIDTH = 5;
// localparam int INSTR_MEM_SIZE = 2**8 * 4;           // holds 2**8 instructions
localparam int INSTR_MEM_SIZE = 1024;           // holds 2**8 instructions
localparam int IMEM_AWIDTH = $clog2(INSTR_MEM_SIZE);
// localparam int DATA_MEM_SIZE = 2**8 * 4;            // holds 2**8 words of data
localparam int DATA_MEM_SIZE = 1024;           // holds 2**8 words of data
localparam int DMEM_AWIDTH = $clog2(DATA_MEM_SIZE);

// Primary inputs
logic clk;
logic rst_n;

// Primary outputs
logic [XLEN-1:0] alu_res;
logic            res_is_0;
logic [XLEN-1:0] dmem_rdata;

// Internal wires
logic [XLEN-1:0] pc_i, pc_o;
instr_t                 instr;
aluop_sel_t             alu_sel;
logic                   alu_src;
logic                   mem_wen;
logic                   reg_wen;
logic   [     1:0]      pc_src;
logic   [     1:0]      reg_wdata_src;
logic   [XLEN-1:0]      rdata1_aluSrc1;
logic   [XLEN-1:0]      rdata2;
logic   [XLEN-1:0]      alu_src2;
logic   [XLEN-1:0]      imm;
logic   [XLEN-1:0]      load_ext;
logic   [XLEN-1:0]      reg_wdata;
logic   [     3:0]      mem_wdata_mask; // Each bit set = valid byte in wdata
logic   [     3:0]      mem_rdata_mask; // Unused!

//==============   Module instantiations - BEGIN   ==============//

next_pc_value #(
    .WIDTH(XLEN)
) next_pc_val_inst (
    .next_pc(pc_i),
    .curr_pc(pc_o), 
    .alu_res,
    .pc_src,
    .imm
);

register #(
    .WIDTH(XLEN)
) pc (
	.reg_o(pc_o),
	.reg_i(pc_i),
	.clk, 
	.rst_n
);

rom_mem #(
    .AWIDTH(IMEM_AWIDTH),
    .DWIDTH(XLEN)
) instr_mem (
    .rdata(instr),
    .addr(pc_o)
);

ctrl_unit ctrl_unit_inst (
	.alu_sel,
    .alu_src, 
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
    .N_INPUTS(3),
    .DWIDTH(XLEN)
) mux_reg_wdata (
    .out(reg_wdata),
    .in({ alu_res,  load_ext,  pc_o+4 }),
    .sel(reg_wdata_src)
);

register_bank #(
    .AWIDTH(AWIDTH),
    .DWIDTH(XLEN)
) register_bank_inst (
    .rdata1(rdata1_aluSrc1),
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
    .DWIDTH(XLEN)
) alu_inst (
	.res(alu_res), 
	.res_is_0,
	.src1(rdata1_aluSrc1),
	.src2(alu_src2),
	.sel(alu_sel)
);

mux #(
    .N_INPUTS(2),
    .DWIDTH(XLEN)
) mux_alu_src2 (
    .out(alu_src2),
    .in({ rdata2,  imm }),
    .sel(alu_src)
);

imm_extender #(
    .DWIDTH(XLEN)
) imm_ext_inst (
    .imm_ext(imm),
    .instr
);

always_comb begin
    case (instr.S.funct3)
        0: mem_wdata_mask = 4'b0001;
        1: mem_wdata_mask = 4'b0011;
        2: mem_wdata_mask = 4'b1111;
        default: mem_wdata_mask = '0;
    endcase
end

data_mem #(
    .AWIDTH(DMEM_AWIDTH),
    .DWIDTH(XLEN)
) data_mem_inst (
    .rdata(dmem_rdata),
    .wdata(rdata2),
    .addr(alu_res),
    .wen(mem_wen),
    .clk,
    .rst_n,
    // .rdata_mask(mem_rdata_mask),
    .wdata_mask(mem_wdata_mask)
);

load_extender #(
    .DWIDTH(XLEN)
) load_ext_inst (
    .load_ext,
    .instr,
    .load_word(dmem_rdata)
);

//==============   Module instantiations - END   ==============//

//=================   Simulation - BEGIN   =================//

int n_mismatches;
bit verbose = 0;
logic [XLEN-1:0] expected;

logic [XLEN-1:0] regs_clone [2**AWIDTH];
assign regs_clone = register_bank_inst.mem;
logic [XLEN-1:0] dmem_clone [DATA_MEM_SIZE/4];
always_comb foreach(dmem_clone[i]) dmem_clone[i] = data_mem_inst.mem[i*4+:4];

logic [XLEN-1:0] xptd_dmem [DATA_MEM_SIZE/4];

string progs [] = '{"BRANCH", "JAL", "OP", "OP-IMM", "ST_LD", "WR_ALL_MEM"};

string prog_name = progs[5];
string prog_file = {"programs/", prog_name, "_prog.txt"};
string dmem_file = {"programs/", prog_name, "_data.txt"};

localparam int PERIOD = 2;
localparam int MAX_CYCLES = 10000;
initial begin
    clk = 0; 
    repeat(MAX_CYCLES) #(PERIOD/2) clk = ~clk;
    $display ("\nSimulation reached the time limit. Terminating simulation.\n");
    $finish;
end

initial begin
    // Specifying time format (%t)
    $timeformat(-9, 0, "ns", 5); // e.g.: "900ns"

    $display("#==========================================================#");

    $display("%t: Running program %s.", $time, prog_name);
    
    reset ();

    // Load instructions into instruction memory
    load_instr_mem();
    if (verbose)
        print_instr_mem();
    
    // Wait for instructions to end
    do begin
        @(negedge clk);
    end while (instr !== 'x);

    // Get expected data memory values (got from RARS simulator)
    load_xptd_dmem();
    if (verbose)
        foreach (xptd_dmem[i]) begin
            if(i == 64) break;
            $display("xptd_dmem[%2d] = %h. dmem[%2d] = %h.", i, xptd_dmem[i], i, dmem_clone[i]);
        end
    checkit("dmem", xptd_dmem, dmem_clone);

    if (verbose)
        print_regs();

    $display("%t: Simulation end. Number of mismatches: %0d.", $time, n_mismatches);

    $display("#==========================================================#");
    $finish;
end

//=================   Simulation - END   =================//

//==============   Tasks and functions - BEGIN   ==============//

task reset ();
    rst_n = 0;
    @(negedge clk) rst_n = 1;
    $display("%t: Reset done.", $time);
endtask

task load_instr_mem;
    logic [XLEN-1:0] mem [INSTR_MEM_SIZE];
    $readmemh(prog_file, mem);
    foreach(mem[i]) instr_mem.mem[i*4+:4] = mem[i];
endtask

task print_instr_mem;
    for(int i = 0; instr_mem.mem[i*4+:4] != '0; i++) begin
        $display("%t: Read 0x%h from memory address %0d.", $time, instr_mem.mem[i*4+:4], i);
    end
endtask

task print_regs;
    foreach(regs_clone[i]) begin
        $display("%t: Read 0x%h from register %0d.", $time, regs_clone[i], i);
    end
endtask

task load_xptd_dmem;
    $readmemh(dmem_file, xptd_dmem);
endtask

task checkit (string what_mem, logic [XLEN-1:0] expected [], logic [XLEN-1:0] actual []);
    foreach (expected[i]) begin
        if (expected[i] != actual[i]) begin
            n_mismatches++;
            $display("%t: ERROR! Index = %0d. Expected = %h. Actual = %h. Mem = %s.", $time, i, expected[i], actual[i], what_mem);
        end
    end
endtask

//==============   Tasks and functions - END   ==============//

endmodule