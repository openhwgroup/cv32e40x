.. _rvfi:

RISC-V Formal Interface
=======================

.. note::

   A bindable RISC-V Formal Interface (RVFI) interface will be provided for |corev|. See https://github.com/SymbioticEDA/riscv-formal/blob/master/docs/rvfi.md for
   details on RVFI.

The module ``cv32e40x_rvfi`` can be used to create a log of the executed instructions.
It is a behavioral, non-synthesizable, module that can be bound to the ``cv32e40x_core``.

RVFI serves the following purposes:

* It can be used for formal verification.
* It can be used to produce an instruction trace during simulation.
* It can be used as a monitor to ease interfacing with an external scoreboard that itself can be interfaced to an Instruction Set Simulator (ISS) for verification reasons.

Trace output file
-----------------

Tracing can be enabled during simulation by defining **CV32E40X_TRACE_EXECUTION**. All traced instructions are written to a log file.
The log file is named ``trace_core_<HARTID>.log``, with ``<HARTID>`` being the 32 digit hart ID of the core being traced.

Trace output format
-------------------

The trace output is in tab-separated columns.

1. **Time**: The current simulation time.
2. **Cycle**: The number of cycles since the last reset.
3. **PC**: The program counter
4. **Instr**: The executed instruction (base 16).
   32 bit wide instructions (8 hex digits) are uncompressed instructions, 16 bit wide instructions (4 hex digits) are compressed instructions.
5. **Decoded instruction**: The decoded (disassembled) instruction in a format equal to what objdump produces when calling it like ``objdump -Mnumeric -Mno-aliases -D``.
   - Unsigned numbers are given in hex (prefixed with ``0x``), signed numbers are given as decimal numbers.
   - Numeric register names are used (e.g. ``x1``).
   - Symbolic CSR names are used.
   - Jump/branch targets are given as absolute address if possible (PC + immediate).
6. **Register and memory contents**: For all accessed registers, the value before and after the instruction execution is given. Writes to registers are indicated as ``registername=value``, reads as ``registername:value``. For memory accesses, the address and the loaded and stored data are given.

.. code-block:: text

  Time          Cycle      PC       Instr    Decoded instruction Register and memory contents
            130         61 00000150 4481     c.li    x9,0        x9=0x00000000
            132         62 00000152 00008437 lui     x8,0x8      x8=0x00008000
            134         63 00000156 fff40413 addi    x8,x8,-1    x8:0x00008000  x8=0x00007fff
            136         64 0000015a 8c65     c.and   x8,x9       x8:0x00007fff  x9:0x00000000  x8=0x00000000
            142         67 0000015c c622     c.swsp  x8,12(x2)   x2:0x00002000  x8:0x00000000 PA:0x0000200c store:0x00000000  load:0xffffffff
