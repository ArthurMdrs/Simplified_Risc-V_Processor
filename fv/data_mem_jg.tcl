clear -all

analyze -sv12 +define+SVA_ON=1 ./data_mem_vc.sv
analyze -sv12 +define+SVA_ON=1 ../rtl/data_mem.sv
elaborate -top data_mem -create_related_covers witness -parameter {DWIDTH} {32} -parameter {AWIDTH} {5}

clock clk

reset !rst_n

prove -all -bg
