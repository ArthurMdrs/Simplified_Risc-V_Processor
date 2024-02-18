This is a very simple RISC-V processor I made while learning about the RISC-V architecture and microarchitecture.
It is single-cycle and supports the base RV31I instruction set, except: fence, ecall and ebreak. CSR instructions are not supported, as they are not part of the base ISA. 
For simplicity, there the core does not generate exceptions or traps. 
Different privilege levels not implemented.

References (last accessed on Feb 17th, 2024):
- HARRIS, S.; HARRIS, D. Digital Design and Computer Architecture: RISC-V Edition. 1. ed. [S.l.]: Morgan Kaufmann, 2021. 
- https://github.com/riscv/riscv-isa-manual/releases/tag/Ratified-IMAFDQC
- https://www.youtube.com/playlist?list=PLKM6TRQ8YHKfz2YgbS8OvrcaEFIhxhEMJ
- https://five-embeddev.com/riscv-isa-manual/latest/rv32.html#rv32
- https://www.cs.sfu.ca/~ashriram/Courses/CS295/assets/notebooks/RISCV/RISCV_CARD.pdf
