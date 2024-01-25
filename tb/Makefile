SVA = +define+SVA_ON=1
# SVA = 

RTL = ../rtl/pkg/*.sv ../rtl/*.sv
FV = ../fv/*.sv
TB = ./*_tb.sv
TOP = -top ctrl_unit_tb

GUI = -gui
# GUI =

SEED = -svseed 2

run: sim

sim:
	xrun -64bit -sv +DEFINE+SIM $(RTL) $(FV) $(TB) $(SVA) $(TOP) \
		 -timescale 1ns/1ps -access +rwc $(SEED) $(GUI)

clean:
	rm -rf xcelium.d xrun* .simvision .symbol* waves*
