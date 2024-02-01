
# XM-Sim Command File
# TOOL:	xmsim(64)	23.09-s003
#
#
# You can restore this configuration with:
#
#      xrun -64bit -sv +define+SIM ../rtl/pkg/typedefs_pkg.sv ../rtl/alu.sv ../rtl/ctrl_unit.sv ../rtl/data_mem.sv ../rtl/decoder.sv ../rtl/imm_extender.sv ../rtl/load_extender.sv ../rtl/mux.sv ../rtl/next_pc_value.sv ../rtl/register.sv ../rtl/register_bank.sv ../rtl/rom_mem.sv ../fv/alu_vc.sv ../fv/data_mem_vc.sv ../fv/decoder_vc.sv ../fv/mux_vc.sv ../fv/register_bank_vc.sv ./alu_tb.sv ./branch_tb.sv ./ctrl_unit_tb.sv ./data_mem_tb.sv +define+SVA_ON=1 -top branch_tb -timescale 1ns/1ps -access +rwc -svseed 2 -s -input /home/pedro.medeiros/Simplified_Risc-V_Processor/tb/simvision/branch_tb_restore.tcl
#

set tcl_prompt1 {puts -nonewline "xcelium> "}
set tcl_prompt2 {puts -nonewline "> "}
set vlog_format %h
set vhdl_format %v
set real_precision 6
set display_unit auto
set time_unit module
set heap_garbage_size -200
set heap_garbage_time 0
set assert_report_level note
set assert_stop_level error
set autoscope yes
set assert_1164_warnings yes
set pack_assert_off {}
set severity_pack_assert_off {note warning}
set assert_output_stop_level failed
set tcl_debug_level 0
set relax_path_name 1
set vhdl_vcdmap XX01ZX01X
set intovf_severity_level ERROR
set probe_screen_format 0
set rangecnst_severity_level ERROR
set textio_severity_level ERROR
set vital_timing_checks_on 1
set vlog_code_show_force 0
set assert_count_attempts 1
set tcl_all64 false
set tcl_runerror_exit false
set assert_report_incompletes 0
set show_force 1
set force_reset_by_reinvoke 0
set tcl_relaxed_literal 0
set probe_exclude_patterns {}
set probe_packed_limit 4k
set probe_unpacked_limit 16k
set assert_internal_msg no
set svseed 2
set assert_reporting_mode 0
set vcd_compact_mode 0
set vhdl_forgen_loopindex_enum_pos 0
alias . run
alias indago verisium
alias quit exit
database -open -shm -into waves.shm waves -default
probe -create -database waves branch_tb.clk branch_tb.rst_n branch_tb.instr branch_tb.pc_i branch_tb.pc_o branch_tb.alu_inst.sel branch_tb.alu_inst.src1 branch_tb.alu_inst.src2 branch_tb.alu_inst.res branch_tb.alu_inst.res_is_0 branch_tb.regs_clone branch_tb.ctrl_unit_inst.funct3 branch_tb.ctrl_unit_inst.funct7 branch_tb.ctrl_unit_inst.opcode branch_tb.ctrl_unit_inst.ops_equal branch_tb.ctrl_unit_inst.op1_lt_op2 branch_tb.ctrl_unit_inst.alu_sel branch_tb.ctrl_unit_inst.alu_src branch_tb.ctrl_unit_inst.branch branch_tb.ctrl_unit_inst.mem_wen branch_tb.ctrl_unit_inst.reg_wdata_src branch_tb.ctrl_unit_inst.reg_wen branch_tb.data_mem_inst.addr[7:0] branch_tb.data_mem_inst.wdata branch_tb.data_mem_inst.wdata_mask branch_tb.data_mem_inst.rdata branch_tb.dmem_clone[0:31]
probe -create -database waves branch_tb.imm
probe -create -database waves branch_tb.next_pc_val_inst.curr_pc

simvision -input branch_tb_restore.tcl.svcf
