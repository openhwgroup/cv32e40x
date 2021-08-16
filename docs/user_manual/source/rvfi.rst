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
The log file is named ``trace_rvfi.log``.

Trace output format
-------------------

The trace output is in tab-separated columns.

1.  **PC**: The program counter
2.  **Instr**: The executed instruction (base 16).
    32 bit wide instructions (8 hex digits) are uncompressed instructions, 16 bit wide instructions (4 hex digits) are compressed instructions.
3.  **rs1_addr** Register read port 1 source address, 0x0 if not used by instruction
4.  **rs1_data** Register read port 1 read data, 0x0 if not used by instruction
5.  **rs2_addr** Register read port 2 source address, 0x0 if not used by instruction
6.  **rs2_data** Register read port 2 read data, 0x0 if not used by instruction
7.  **rd_addr**  Register write port 1 destination address, 0x0 if not used by instruction
8.  **rd_data**  Register write port 1 write data, 0x0 if not used by instruction
9.  **mem_addr** Memory address for instructions accessing memory
10. **rvfi_mem_rmask** Bitmask specifying which bytes in rvfi_mem_rdata contain valid read data
11. **rvfi_mem_wmask** Bitmask specifying which bytes in rvfi_mem_wdata contain valid write data
12. **rvfi_mem_rdata** The data read from memory address specified in mem_addr
13. **rvfi_mem_wdata** The data written to memory address specified in mem_addr


.. code-block:: text

PC        Instr     rs1_addr  rs1_rdata  rs2_addr  rs2_rdata  rd_addr  rd_wdata    mem_addr mem_rmask mem_wmask mem_rdata mem_wdata
00001f9c  14c70793        0e   000096c8        0c   00000000       0f  00009814    00009814         0         0  00000000  00000000
00001fa0  14f72423        0e   000096c8        0f   00009814       00  00000000    00009810         0         f  00000000  00009814
00001fa4  0000bf6d        1f   00000000        1b   00000000       00  00000000    00001fa6         0         0  00000000  00000000
00001f5e  000043d8        0f   00009814        04   00000000       0e  00000000    00009818         f         0  00000000  00000000
00001f60  0000487d        00   00000000        1f   00000000       10  0000001f    0000001f         0         0  00000000  00000000

