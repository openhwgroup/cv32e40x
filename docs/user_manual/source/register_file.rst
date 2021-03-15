.. _register-file:

Register File
=============

Source file: :file:`rtl/cv32e40x_register_file.sv`

|corev| has 31 32-bit wide registers which form registers ``x1`` to ``x31``.
Register ``x0`` is statically bound to 0 and can only be read, it does not
contain any sequential logic.

The number of read ports and the number of write ports of the register file depends on the parameter settings of |corev|.
The register file has two read ports and one write port unless at least one of the ``B_EXT``, ``P_EXT``, ``X_EXT`` parameters
is set to 1, in which case three read ports and two write ports will be instantiated.  Register file reads are performed in the ID stage.
Register file writes are performed in the WB stage.


General Purpose Register File
-----------------------------

The general purpose register file is flip-flop-based. It uses regular, positive-edge-triggered flip-flops to implement the registers.
