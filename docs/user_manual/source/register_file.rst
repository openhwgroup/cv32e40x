.. _register-file:

Register File
=============

Source file: :file:`rtl/cv32e40x_register_file.sv`

|corev| has 31 32-bit wide registers which form registers ``x1`` to ``x31``.
Register ``x0`` is statically bound to 0 and can only be read, it does not
contain any sequential logic.

The register file has two read ports and one write port. Register file reads are performed in the ID stage.
Register file writes are performed in the WB stage.

General Purpose Register File
-----------------------------

The general purpose register file is flip-flop-based. It uses regular, positive-edge-triggered flip-flops to implement the registers.

FPU Register File
-----------------

In case the optional FPU is instantiated, the register file is extended
with an additional register bank of 32 registers ``f0``-``f31``. These registers
are stacked on top of the existing register file and can be accessed
concurrently with the limitation that a maximum of three operands per
cycle can be read. Each of the three operands addresses is extended with
an fp_reg_sel signal which is generated in the instruction decoder
when a FP instruction is decoded. This additional signals determines if
the operand is located in the integer or the floating point register
file.

Forwarding paths, and write-back logic are shared for the integer and
floating point operations and are not replicated.
