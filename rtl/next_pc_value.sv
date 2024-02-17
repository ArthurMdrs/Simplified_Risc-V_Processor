module next_pc_value #(
    int WIDTH = 32
) (
    output logic [WIDTH-1:0] next_pc,
    input  logic [WIDTH-1:0] curr_pc, 
    input  logic [WIDTH-1:0] alu_res, 
    input  logic       [1:0] pc_src,
    input  logic [WIDTH-1:0] imm 
);

// always_comb begin
//     if (branch)
//         next_pc = curr_pc + imm;
//     else 
//         next_pc = curr_pc + 4;
// end

wire [WIDTH-1:0] pc_p_4    = curr_pc + 4;
wire [WIDTH-1:0] pc_p_imm  = curr_pc + imm;

// logic [WIDTH-1:0] mux_in [3];
// assign mux_in[0] = pc_p_4;
// assign mux_in[1] = pc_p_imm;
// assign mux_in[2] = alu_res;

mux #(
    .N_INPUTS(3),
    .DWIDTH(WIDTH)
) mux_pc_i (
    .out(next_pc),
    .in({ pc_p_4,  pc_p_imm,  alu_res }),
    // .in(mux_in),
    .sel(pc_src)
);

endmodule