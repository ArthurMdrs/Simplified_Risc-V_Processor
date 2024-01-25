clear -all

analyze -sv12 +define+SVA_ON=1 ../rtl/pkg/typedefs_pkg.sv
analyze -sv12 +define+SVA_ON=1 ../rtl/alu.sv
analyze -sv12 +define+SVA_ON=1 ./alu_vc.sv
elaborate -top alu -create_related_covers witness -parameter {DWIDTH} {32}

clock -none

reset -none

prove -all

#get_needed_assumptions -property <embedded>::alu.decoder_inst.decoder_vc_inst.genblk1\[4\].COV_OBSERVE_IN -status unreachable
