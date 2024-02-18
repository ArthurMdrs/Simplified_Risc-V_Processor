/* 
    This is the official testbench.

    Instruction set: RV32I.
    Opcodes supported: OP, OP-IMM, LOAD, STORE, BRANCH, 
                       JAL, JALR, LUI, AUIPC.
    Not supported: .

*/

module core_tb;

import typedefs_pkg::*;

localparam int INSTR_MEM_SIZE = 2**14;
localparam int IMEM_AWIDTH = $clog2(INSTR_MEM_SIZE);
localparam int DATA_MEM_SIZE = 2**14;
localparam int DMEM_AWIDTH = $clog2(DATA_MEM_SIZE);

// Primary inputs
logic clk;
logic rst_n;

// Data memory interface
logic [31:0] dmem_rdata;
logic [31:0] dmem_wdata;
logic [31:0] dmem_addr;
logic        dmem_wen;
logic  [3:0] dmem_wr_mask;

//==============   Module instantiations - BEGIN   ==============//

core #(
    .INSTR_MEM_SIZE(INSTR_MEM_SIZE)
) core_inst (
    .clk,
    .rst_n,
    .dmem_rdata,
    .dmem_wdata,
    .dmem_addr,
    .dmem_wen,
    .dmem_wr_mask
);

data_mem #(
    .AWIDTH(DMEM_AWIDTH),
    .DWIDTH(32)
) data_mem_inst (
    .rdata(dmem_rdata),
    .wdata(dmem_wdata),
    .addr(dmem_addr),
    .wen(dmem_wen),
    .clk,
    .rst_n,
    .wdata_mask(dmem_wr_mask)
);

//==============   Module instantiations - END   ==============//

//=================   Simulation - BEGIN   =================//

int n_mismatches;
bit verbose = 1;
logic [31:0] expected;

logic [31:0] regs_clone [32];
assign regs_clone = core_inst.register_bank_inst.mem;
logic [31:0] dmem_clone [DATA_MEM_SIZE/4];
always_comb foreach(dmem_clone[i]) dmem_clone[i] = data_mem_inst.mem[i*4+:4];
instr_t instr_clone;
assign instr_clone = core_inst.instr;

logic [31:0] xptd_dmem [DATA_MEM_SIZE/4];

string progs [] = '{"BRANCH", "JAL", "OP", "OP-IMM", "ST_LD", "WR_ALL_MEM", "LUI_AUIPC"};

string prog_name = progs[0];
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
    // if (verbose)
    //     print_instr_mem();
    
    // Wait for instructions to end
    do begin
        @(negedge clk);
    end while (instr_clone !== 'x);

    // Get expected data memory values (got from RARS simulator)
    load_xptd_dmem();
    if (verbose)
        foreach (xptd_dmem[i]) begin
            if(i == 32) break;
            $display("xptd_dmem[%2d] = %h. dmem[%2d] = %h.", i, xptd_dmem[i], i, dmem_clone[i]);
        end
    checkit("dmem", xptd_dmem, dmem_clone);

    // if (verbose)
    //     print_regs();

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
    logic [31:0] mem [INSTR_MEM_SIZE];
    $readmemh(prog_file, mem);
    foreach(mem[i]) core_inst.instr_mem.mem[i*4+:4] = mem[i];
endtask

task print_instr_mem;
    for(int i = 0; core_inst.instr_mem.mem[i*4+:4] != '0; i++) begin
        $display("%t: Read 0x%h from memory address %0d.", $time, core_inst.instr_mem.mem[i*4+:4], i);
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

task checkit (string what_mem, logic [31:0] expected [], logic [31:0] actual []);
    foreach (expected[i]) begin
        if (expected[i] != actual[i]) begin
            n_mismatches++;
            $display("%t: ERROR! Index = %0d. Expected = %h. Actual = %h. Mem = %s.", $time, i, expected[i], actual[i], what_mem);
        end
    end
endtask

//==============   Tasks and functions - END   ==============//

endmodule