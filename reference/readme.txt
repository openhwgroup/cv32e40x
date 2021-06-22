- Bit Manipulation

 ../rtl/cv32e40x_alu.sv - Contains commented out shifter based on
 https://github.com/riscv/riscv-bitmanip/blob/main-history/verilog/rvb_shifter/rvb_shifter.v 

- PMP (from https://github.com/lowRISC/ibex.git, 93a76b390081b6b3b6cea2671c469f9293b998f2)

 - ibex_pmp.sv - Core of the Physical Memory Protection unit
 - ibex_cs_registers.sv - Programming interface of PMP
 - ibex_pkg.sv - Helper types, constants, etc. for Physical Memory Protection unit 
 
- Random instructions (from https://github.com/lowRISC/ibex.git, 93a76b390081b6b3b6cea2671c469f9293b998f2)

 - prim_secded_39_32_enc.sv - ECC encoder for the register file
 - prim_secded_39_32_dec.sv - ECC decoder for the register file
 - ibex_dummy_instr.sv - Dummy instruction generator
 - ibex_if_stage.sv Dummy instruction generator instantiation
 - ibex_register_file_ff.sv - Register file
 - ibex_core.sv - Core (showing ECC encoder/decoder instantiations)
