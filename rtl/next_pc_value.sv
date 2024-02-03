module next_pc_value #(
    int WIDTH = 32
) (
    output logic [WIDTH-1:0] next_pc,
    input  logic [WIDTH-1:0] curr_pc, 
    input  logic             branch,
    input  logic [WIDTH-1:0] imm 
);

always_comb begin
    if (branch)
        next_pc = curr_pc + imm;
    else 
        next_pc = curr_pc + 4;
end

endmodule