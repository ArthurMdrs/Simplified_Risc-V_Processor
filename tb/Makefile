SVA = +define+SVA_ON=1
# SVA = 

RTL = ../rtl/*.sv
FV = ../fv/*.sv
TB = ./*_tb.sv
TOP = -top alu_tb

# GUI = -gui
GUI =

SEED = -svseed 2

run: sim

sim:
	xrun -64bit -sv +DEFINE+SIM $(FV) $(RTL) $(TB) $(SVA) $(TOP) \
		 -timescale 1ns/1ns -access +rwc $(SEED) $(GUI)

clean:
	rm -rf xcelium.d xrun* .simvision
