/* 
    This was the 1st testbench.

    The only RTL I had done was register_bank, alu and mux.

    This makes it easier to test the ALU operations.

    Opcodes supported: OP.

*/

module alu_tb;

import typedefs_pkg::*;

localparam int AWIDTH = 3;
localparam int DWIDTH = 32;

// Primary inputs
logic              clk, rst_n;
logic [AWIDTH-1:0] raddr1, raddr2, waddr;
logic [DWIDTH-1:0] wdata;
logic              wen;
aluop_sel_t        alu_sel;
logic              mux_sel;
logic [DWIDTH-1:0] some_const;

// Primary outputs
logic [DWIDTH-1:0] res;
logic              res_is_0;

// Internal wires
logic [DWIDTH-1:0] rdata1_aluSrc1;
logic [DWIDTH-1:0] rdata2_muxSrc1;
logic [DWIDTH-1:0] muxOut_aluSrc2;

//==============   Module instantiations - BEGIN   ==============//
register_bank #(
    .AWIDTH(AWIDTH),
    .DWIDTH(DWIDTH)
) register_bank_inst (
    .rdata1(rdata1_aluSrc1),
    .rdata2(rdata2_muxSrc1),
    .raddr1,
    .raddr2,
    .wdata,
    .waddr,
    .wen,
    .clk,
    .rst_n
);

alu #(
    .DWIDTH(DWIDTH)
) alu_inst (
	.res, 
	.res_is_0,
	.src1(rdata1_aluSrc1),
	.src2(muxOut_aluSrc2),
	.sel(alu_sel)
);

mux #(
    .N_INPUTS(2),
    .DWIDTH(DWIDTH)
) mux_alu_src2 (
    .out(muxOut_aluSrc2),
    .in({rdata2_muxSrc1, some_const}),
    .sel(mux_sel)
);

//==============   Module instantiations - END   ==============//

//=================   Simulation - BEGIN   =================//

int n_mismatches;
bit verbose = 1;
logic [DWIDTH-1:0] expected;
logic [DWIDTH-1:0] mem_clone [2**AWIDTH];

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

    // Set constant value
    some_const = 2;

    // Write to memory
    write_mem();

    // Read from memory
    read_mem();

    // Tests with mux_sel = 0
    mux_sel = 0;
    alu_sel = alu_sel.first();
    do begin
        repeat(10)
            do_operation(0);
        alu_sel = alu_sel.next();
    end while (alu_sel != alu_sel.first());

    // Tests with mux_sel = 1
    mux_sel = 1;
    repeat(20)
        do_operation(1);

    $display("%t: Simulation end. Number of mismatches: %0d.", $time, n_mismatches);

    $display("#==========================================================#");
    $finish;
end

//=================   Simulation - END   =================//

//==============   Tasks and functions - BEGIN   ==============//

task reset ();
    rst_n = 0;
    #3 rst_n = 1;
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
    logic [4:0]        shamt;
    res   = 0;
    shamt = op2[4:0];
    case (op)
        AND : res = op1 & op2;
        OR  : res = op1 | op2;
        ADD : res = op1 + op2;
        XOR : res = op1 ^ op2;
        SUB : res = $signed(op1) - $signed(op2);
        SLT : res = $signed(op1) < $signed(op2);
        SLTU: res = op1 < op2;
        SLL : res = op1 << shamt;
        SRL : res = op1 >> shamt;
        SRA : res = $signed(op1) >>> shamt;
    endcase
    if (verbose)
        $display("%t: [refmod] op = %s. op1 = %h. op2 = %h. res = %h.", $time, op.name(), op1, op2, res);
    return res;
endfunction

task write_mem;
    wen = 1;
    for(int i = 0; i < 2**AWIDTH; i++) begin
        @(negedge clk);
        waddr = i;
        assert(randomize(wdata));
        mem_clone[i] = (i == 0) ? 0 : wdata;
        if (verbose)
            $display("%t: Writing 0x%h to memory address %0d.", $time, wdata, waddr);
    end
    @(negedge clk);
    wen = 0;
endtask

task read_mem;
    mux_sel = 1;
    for(int i = 0; i < 2**AWIDTH; i++) begin
        raddr1 = i;
        #1step;
        ast_rdata_valid: assert(rdata1_aluSrc1 == mem_clone[raddr1]);
        if (verbose)
            $display("%t: Read 0x%h from memory address %0d.", $time, rdata1_aluSrc1, raddr1);
    end
endtask

task do_operation (bit rand_sel);
    assert(randomize(raddr1, raddr2));
    // assert(randomize(alu_sel) with {alu_sel inside {AND, OR, ADD, SUB, SLT};});
    if (rand_sel)
        assert(randomize(alu_sel));
    #1step;
    ast_mux_out_valid: assert(muxOut_aluSrc2 == ((mux_sel) ? some_const : rdata2_muxSrc1));
    expected = ref_model(rdata1_aluSrc1, muxOut_aluSrc2, alu_sel);
    checkit(expected, res, alu_sel);
    if (res_is_0 != (expected==0))
        $display("%t: ERROR! Result is zero, but res_is_0 is not asserted. ", $time);
endtask

//==============   Tasks and functions - END   ==============//
    

endmodule