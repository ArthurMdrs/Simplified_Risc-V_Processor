SVA = +define+SVA_ON=1
# SVA = 

RTL = ../rtl/pkg/*.sv ../rtl/*.sv
FV = ../fv/*.sv
TB = ./*_tb.sv
TOP = -top branch_tb

SEED = -svseed 2

run: sim

sim:
	xrun -64bit -sv +define+SIM $(RTL) $(FV) $(TB) $(SVA) $(TOP) \
		 -timescale 1ns/1ps -access +rwc $(SEED)

gui:
	xrun -64bit -sv +define+SIM $(RTL) $(FV) $(TB) $(SVA) $(TOP) \
		 -timescale 1ns/1ps -access +rwc $(SEED) -gui

clean:
	rm -rf xcelium.d xrun* .simvision .symbol* waves*
