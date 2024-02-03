/* 
    This was the 3rd testbench.

    RTL I had done at the time: register_bank, alu, mux, register (program counter), 
    rom_mem (instruction memory), ctrl_unit (supporting more isntructions), imm_extender,
    load_extender and data_mem.

    This is basically an upgrade from the 2nd testbench.

    Opcodes supported: OP, OP-IMM, LOAD, STORE.

*/

module data_mem_tb;

import typedefs_pkg::*;

localparam int XLEN = 32;
localparam int AWIDTH = 5;
localparam int DWIDTH = 8;
localparam int INSTR_MEM_SIZE = 2**8 * 4;
localparam int INSTR_MEM_W = $clog2(INSTR_MEM_SIZE);
localparam int DATA_MEM_SIZE = 2**8 * 4;
localparam int DATA_MEM_W = $clog2(DATA_MEM_SIZE);

// Primary inputs
logic clk;
logic rst_n;

// Primary outputs
logic [XLEN-1:0] alu_res;
logic            res_is_0;
logic [XLEN-1:0] dmem_rdata;

// Internal wires
logic [INSTR_MEM_W-1:0] pc_i, pc_o;
instr_t                 instr;
aluop_sel_t             alu_sel;
logic                   alu_src;
logic                   mem_wen;
logic                   reg_wen;
// logic   [     1:0]      imm_src;
logic                   reg_wdata_src;
logic   [XLEN-1:0]      rdata1_aluSrc1;
logic   [XLEN-1:0]      rdata2;
logic   [XLEN-1:0]      alu_src2;
logic   [XLEN-1:0]      imm_ext;
logic   [XLEN-1:0]      load_ext;
logic   [XLEN-1:0]      reg_wdata;
logic   [     3:0]      mem_wdata_mask; // Each bit set = valid byte in wdata
logic   [     3:0]      mem_rdata_mask; // Unused!

//==============   Module instantiations - BEGIN   ==============//

register #(
    .WIDTH(INSTR_MEM_W)
) pc (
	.reg_o(pc_o),
	.reg_i(pc_i),
	.clk, 
	.rst_n
);

assign pc_i = pc_o + 4;

rom_mem #(
    .AWIDTH(INSTR_MEM_W),
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
    .branch(),
    // .imm_src, 
    .reg_wdata_src,
	.opcode(instr.R.opcode),
	.funct7(instr.R.funct7),
	.funct3(instr.R.funct3),
    .ops_equal(0),
    .op1_lt_op2(0)
);

mux #(
    .N_INPUTS(2),
    .DWIDTH(XLEN)
) mux_reg_wdata (
    .out(reg_wdata),
    .in({ alu_res,  load_ext }),
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
    .in({ rdata2,  imm_ext }),
    .sel(alu_src)
);

imm_extender #(
    .DWIDTH(XLEN)
) imm_ext_inst (
    .imm_ext,
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
    .AWIDTH(DATA_MEM_W),
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
bit verbose = 1;
logic [XLEN-1:0] expected;

logic [XLEN-1:0] regs_clone [2**AWIDTH];
assign regs_clone = register_bank_inst.mem;
logic [XLEN-1:0] dmem_clone [2**AWIDTH];
always_comb foreach(dmem_clone[i]) dmem_clone[i] = data_mem_inst.mem[i*4+:4];

logic [XLEN-1:0] xptd_regs [32];
logic [XLEN-1:0] xptd_dmem [32];

string prog_name = "ST_LD";
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
        foreach (xptd_dmem[i])
            $display("xptd_dmem[%2d] = %h. dmem[%2d] = %h.", i, xptd_dmem[i], i, dmem_clone[i]);
    checkit("dmem", xptd_dmem, dmem_clone);


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

task load_xptd_regs;
    $readmemh(prog_file, xptd_regs);
endtask

task load_xptd_dmem;
    $readmemh(dmem_file, xptd_dmem, 0, 31);
endtask

task checkit (string what_mem, logic [XLEN-1:0] expected [32], logic [XLEN-1:0] actual [32]);
    foreach (expected[i]) begin
        if (expected[i] != actual[i]) begin
            n_mismatches++;
            $display("%t: ERROR! Index = %0d. Expected = %h. Actual = %h. Mem = %s.", $time, i, expected[i], actual[i], what_mem);
        end
    end
endtask

//==============   Tasks and functions - END   ==============//

endmodule