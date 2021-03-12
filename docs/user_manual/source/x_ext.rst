.. _x_ext:

eXtension Interface
===================

.. note::

   The eXtension interface has not been implemented yet. Its specification is currently being developed
   and can be found in https://github.com/pulp-platform/riscv-extension-interface.

The eXtension interface enables extending |corev| with custom instructions without the need to change the RTL
of |corev| itself. Custom extensions can be provided in separate modules external to |corev| and are integrated
at system level by connecting them to the eXtension interface.

The eXtension interface provides low latency (tightly integrated) read and write access to the |corev| register file.
All opcodes which are not used (i.e. considered to be invalid) by |corev| can be used by custom extensions. It is recommended
however that custom instructions do not use opcodes that are reserved/used by the RISC-V organization.

The eXtension interface enables extension of |corev| with:

* Custom ALU type instructions.
* Custom load/store type instructions.
* Custom CSRs and related instructions.

Branch type instructions are not supported via the eXtension interface.

.. note::

   |corev| does not implement the **F** extension for single-precision floating-point instructions internal to the core. The **F** extension
   can be supported by interfacing the |corev| to an external FPU via the eXtension interface.
