clear -all

set DEF_BSC_BLKS "+define+USE_BSC_BLKS=1"
set DEF_BSC_BLKS ""

if {$DEF_BSC_BLKS != ""} {
    analyze -sv12 +define+SVA_ON=1 ./decoder_vc.sv
    analyze -sv12 +define+SVA_ON=1 ../rtl/decoder.sv
    analyze -sv12 +define+SVA_ON=1 ./mux_vc.sv
    analyze -sv12 +define+SVA_ON=1 ../rtl/mux.sv
}

analyze -sv12 +define+SVA_ON=1 ./register_bank_vc.sv
analyze -sv12 +define+SVA_ON=1 $DEF_BSC_BLKS ../rtl/register_bank.sv
elaborate -top register_bank -create_related_covers witness -parameter {DWIDTH} {16} -parameter {AWIDTH} {5}

if {$DEF_BSC_BLKS != ""} {
    assume -disable <embedded>::register_bank.mux_inst1.mux_vc_inst.ASM_VALID_SEL
    assume -disable <embedded>::register_bank.mux_inst2.mux_vc_inst.ASM_VALID_SEL
}

clock clk

reset !rst_n

prove -all

#get_needed_assumptions -property <embedded>::register_bank.decoder_inst.decoder_vc_inst.genblk1\[4\].COV_OBSERVE_IN -status unreachable
