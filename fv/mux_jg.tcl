clear -all

analyze -sv12 +define+SVA_ON=1 ./mux_vc.sv
analyze -sv12 +define+SVA_ON=1 ../rtl/mux.sv
elaborate -top mux -create_related_covers witness -parameter {DWIDTH} {8} -parameter {N_INPUTS} {3}

clock -none

reset -none

prove -all