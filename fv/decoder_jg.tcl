clear -all

analyze -sv12 +define+SVA_ON=1 ./decoder_vc.sv
analyze -sv12 +define+SVA_ON=1 ../rtl/decoder.sv
elaborate -top decoder -create_related_covers witness -parameter {INWIDTH} {5}

clock -none

reset -none

prove -all