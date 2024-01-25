module ctrl_unit_tb;

import typedefs_pkg::*;

localparam int XLEN = 32;
localparam int AWIDTH = 5;
localparam int DWIDTH = 8;
localparam int INSTR_MEM_SIZE = 2**8;
localparam int INSTR_MEM_W = $clog2(INSTR_MEM_SIZE);

// Primary inputs
logic clk;
logic rst_n;

// Primary outputs
logic [DWIDTH-1:0] alu_res;
logic              res_is_0;

// Internal wires
logic [INSTR_MEM_W-1:0] pc_i, pc_o;
instr_t                 instr;
logic                   wen;
logic                   alu_src;
aluop_sel_t             alu_sel;
logic   [DWIDTH-1:0]    rdata1_aluSrc1;
logic   [DWIDTH-1:0]    rdata2_muxSrc1;
logic   [DWIDTH-1:0]    muxOut_aluSrc2;

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

mem_comb #(
    .AWIDTH(INSTR_MEM_W),
    .DWIDTH(XLEN)
) instr_mem (
    .rdata(instr),
    .addr(pc_o)
);

ctrl_unit ctrl_unit_inst (
	.alu_sel,
    .alu_src, 
    .wen, 
	.opcode(instr.R.opcode),
	.funct7(instr.R.funct7),
	.funct3(instr.R.funct3)
);

register_bank #(
    .AWIDTH(AWIDTH),
    .DWIDTH(DWIDTH)
) register_bank_inst (
    .rdata1(rdata1_aluSrc1),
    .rdata2(rdata2_muxSrc1),
    .raddr1(instr.R.rs1),
    .raddr2(instr.R.rs2),
    .wdata (alu_res),
    .waddr (instr.R.rd),
    .wen,
    .clk,
    .rst_n
);

alu #(
    .DWIDTH(DWIDTH)
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
    .in({rdata2_muxSrc1, instr.I.imm}),
    .sel(alu_src)
);

//==============   Module instantiations - END   ==============//

//=================   Simulation - BEGIN   =================//

int n_mismatches;
bit verbose = 1;
logic [DWIDTH-1:0] expected;
logic [DWIDTH-1:0] mem_clone [2**AWIDTH];
assign mem_clone = register_bank_inst.mem;

localparam int PERIOD = 2;
initial begin
    clk = 0; 
    forever #(PERIOD/2) clk = ~clk;
end

initial begin
    // Specifying time format (%t)
    $timeformat(-9, 0, "ns", 5); // e.g.: "900ns"

    $display("#==========================================================#");
    
    reset ();

    write_mem();
    read_mem();
    repeat(7) @(negedge clk);

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

task checkit (logic [DWIDTH-1:0] expected, logic [DWIDTH-1:0] actual, aluop_sel_t op);
    if (expected != actual) begin
        $display("%t: ERROR! Expected = %h. Actual = %h. Op = %s.", $time, expected, actual, op.name());
        n_mismatches++;
    end
endtask

function logic [DWIDTH-1:0] ref_model (logic [DWIDTH-1:0] op1, logic [DWIDTH-1:0] op2, aluop_sel_t op);
    logic [DWIDTH-1:0] res;
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

task write_mem;
    $readmemh("instr.txt", instr_mem.mem);
endtask

task read_mem;
    // for(int i = 0; i < INSTR_MEM_SIZE; i++) begin
    for(int i = 0; i < 20; i++) begin
        if (verbose)
            $display("%t: Read 0x%h from memory address %0d.", $time, instr_mem.mem[i], i);
    end
endtask

//==============   Tasks and functions - END   ==============//
    

endmodule