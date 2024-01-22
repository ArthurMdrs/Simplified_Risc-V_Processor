module alu (
	input [7:0] SrcA, SrcB,
	input [2:0] ULAControl,
	output reg [7:0] ULAResult, 
	output Z
);
	always @ (*)
		case (ULAControl)
			0: ULAResult = SrcA & SrcB;
			1: ULAResult = SrcA | SrcB;
			2: ULAResult = SrcA + SrcB;
			6: ULAResult = SrcA + ~SrcB + 1;
			//7: ULAResult = (SrcA < SrcB) ? 1 : 0;
			7: ULAResult = SrcA < SrcB;
			default: ULAResult = 0;
		endcase
	
	//assign Z = (ULAResult == 0) ? 1 : 0;
	assign Z = ULAResult == 0;
endmodule