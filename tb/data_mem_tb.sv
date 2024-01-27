/* 
    This was the 3rd testbench.

    RTL I had done at the time: register_bank, alu, mux, register (program counter), 
    rom_mem (instruction memory), ctrl_unit (supporting more isntructions), imm_ext and data_mem.

    This is basically an upgrade from the 2nd testbench.

*/

module data_mem_tb;

import typedefs_pkg::*;

localparam int XLEN = 32;
localparam int AWIDTH = 5;
localparam int DWIDTH = 8;
localparam int INSTR_MEM_SIZE = 2**8;
localparam int INSTR_MEM_W = $clog2(INSTR_MEM_SIZE);
localparam int DATA_MEM_SIZE = 2**8;

// Primary inputs
logic clk;
logic rst_n;

// Primary outputs
logic [XLEN-1:0] alu_res;
logic            res_is_0;

// Internal wires
logic [INSTR_MEM_W-1:0] pc_i, pc_o;
instr_t                 instr;
logic                   reg_wen;
logic                   alu_src;
aluop_sel_t             alu_sel;
logic   [XLEN-1:0]      rdata1_aluSrc1;
logic   [XLEN-1:0]      rdata2_muxSrc1;
logic   [XLEN-1:0]      muxOut_aluSrc2;
logic   [XLEN-1:0]      imm_ext;

//==============   Module instantiations - BEGIN   ==============//
register #(
    .WIDTH(INSTR_MEM_W)
) pc (
	.reg_o(pc_o),
	.reg_i(pc_i),
	.clk, 
	.rst_n
);

assign pc_i = pc_o + 1;

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
    .mem_wen(), 
    .reg_wen, 
    .imm_src(), 
    .reg_wdata_src(),
	.opcode(instr.R.opcode),
	.funct7(instr.R.funct7),
	.funct3(instr.R.funct3)
);

register_bank #(
    .AWIDTH(AWIDTH),
    .DWIDTH(XLEN)
) register_bank_inst (
    .rdata1(rdata1_aluSrc1),
    .rdata2(rdata2_muxSrc1),
    .raddr1(instr.R.rs1),
    .raddr2(instr.R.rs2),
    .wdata (alu_res),
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
	.src2(muxOut_aluSrc2),
	.sel(alu_sel)
);

mux #(
    .N_INPUTS(2),
    .DWIDTH(XLEN)
) mux_alu_src2 (
    .out(muxOut_aluSrc2),
    .in({rdata2_muxSrc1, imm_ext}),
    .sel(alu_src)
);

imm_ext #(
    .DWIDTH(XLEN)
) imm_ext_inst (
    .imm_ext,
    .instr
);

//==============   Module instantiations - END   ==============//

//=================   Simulation - BEGIN   =================//

int n_mismatches;
bit verbose = 0;
logic [XLEN-1:0] expected;
logic [XLEN-1:0] regs_clone [2**AWIDTH];
assign regs_clone = register_bank_inst.mem;
logic [XLEN-1:0] xptd_regs [32];

string program_to_run = "programs/prog_OP-IMM.txt";
string xptd_regs_file = "programs/regs_OP-IMM.txt";

localparam int PERIOD = 2;
localparam int MAX_CYCLES = 100;
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
        if (verbose)
            print_ctrl_sigs();
    end while (instr !== 'x);

    // Get expected register values (got from RARS simulator)
    load_xptd_regs();
    foreach (xptd_regs[i])
        $display("xptd_regs[%2d] = %h. regs[%2d] = %h.", i, xptd_regs[i], i, regs_clone[i]);
    
    foreach (xptd_regs[i]) begin
        if (xptd_regs[i] != regs_clone[i]) begin
            $display("Mismatch on reg %0d.", i);
            n_mismatches++;
        end
    end

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

task checkit (logic [XLEN-1:0] expected, logic [XLEN-1:0] actual, aluop_sel_t op);
    if (expected != actual) begin
        $display("%t: ERROR! Expected = %h. Actual = %h. Op = %s.", $time, expected, actual, op.name());
        n_mismatches++;
    end
endtask

function logic [XLEN-1:0] ref_model (logic [XLEN-1:0] op1, logic [XLEN-1:0] op2, aluop_sel_t op);
    logic [XLEN-1:0] res;
    res = 0;
    case (op)
        AND: res = op1 & op2;
        OR : res = op1 | op2;
        ADD: res = op1 + op2;
        XOR: res = op1 ^ op2;
        SUB: res = op1 - op2;
        SLT: res = op1 < op2;
    endcase
    return res;
endfunction

task load_instr_mem;
    $readmemh(program_to_run, instr_mem.mem);
endtask

task print_instr_mem;
    // for(int i = 0; i < INSTR_MEM_SIZE; i++) begin
    for(int i = 0; i < 20; i++) begin
        $display("%t: Read 0x%h from memory address %0d.", $time, instr_mem.mem[i], i);
    end
endtask

task load_xptd_regs;
    $readmemh(xptd_regs_file, xptd_regs);
endtask

task print_ctrl_sigs ();
    $display("%t: Printing control signals.", $time);
    $display("alu_sel = %s;\talu_src = %b\tmem_wen = %b\treg_wen = %b\timm_src = %b\treg_wdata_src = %b", 
             alu_sel.name(), alu_src     , 1'b0        , reg_wen     , 1'b0        , 1'b0                );
endtask

//==============   Tasks and functions - END   ==============//

endmodule