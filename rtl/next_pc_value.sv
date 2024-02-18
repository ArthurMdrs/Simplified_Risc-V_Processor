module next_pc_value #(
    int WIDTH = 32
) (
    output logic [WIDTH-1:0] next_pc,
    input  logic [WIDTH-1:0] curr_pc, 
    input  logic [WIDTH-1:0] alu_res, 
    input  logic       [1:0] pc_src,
    input  logic [WIDTH-1:0] imm 
);

wire [WIDTH-1:0] pc_p_4    = curr_pc + 4;
wire [WIDTH-1:0] pc_p_imm  = curr_pc + imm;

mux #(
    .N_INPUTS(3),
    .DWIDTH(WIDTH)
) mux_pc_i (
    .out(next_pc),
    .in({ pc_p_4,  pc_p_imm,  alu_res }),
    .sel(pc_src)
);

endmodule