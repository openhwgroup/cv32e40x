Introduction
=============

CV32E40P is a 4-stage in-order 32-bit RISC-V
processor core. The ISA of CV32E40P
has been extended to support multiple additional instructions including
hardware loops, post-increment load and store instructions and
additional ALU instructions that are not part of the standard RISC-V
ISA. :numref:`blockdiagram` shows a block diagram of the core.

.. figure:: ../images/CV32E40P_Block_Diagram.png
   :name: blockdiagram
   :align: center
   :alt:

   Block Diagram of CV32E40P RISC-V Core

License
-------
Copyright 2020 OpenHW Group.

Copyright 2018 ETH Zurich and University of Bologna.

Copyright and related rights are licensed under the Solderpad Hardware
License, Version 0.51 (the “License”); you may not use this file except
in compliance with the License. You may obtain a copy of the License at
http://solderpad.org/licenses/SHL-0.51. Unless required by applicable
law or agreed to in writing, software, hardware and materials
distributed under this License is distributed on an “AS IS” BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Standards Compliance
--------------------

CV32E40P is a standards-compliant 32-bit RISC-V processor.
It follows these specifications:

* `RISC-V Instruction Set Manual, Volume I: User-Level ISA, Document Version 20191213 (December 13, 2019) <https://github.com/riscv/riscv-isa-manual/releases/download/Ratified-IMAFDQC/riscv-spec-20191213.pdf>`_
* `RISC-V Instruction Set Manual, Volume II: Privileged Architecture, document version 20190608-Base-Ratified (June 8, 2019) <https://github.com/riscv/riscv-isa-manual/releases/download/Ratified-IMFDQC-and-Priv-v1.11/riscv-privileged-20190608.pdf>`_.
  CV32E40P implements the Machine ISA version 1.11.
* `RISC-V External Debug Support, version 0.13.2 <https://content.riscv.org/wp-content/uploads/2019/03/riscv-debug-release.pdf>`_

Many features in the RISC-V specification are optional, and CV32E40P can be parametrized to enable or disable some of them.

CV32E40P supports the following base instruction set.

* The RV32I Base Integer Instruction Set, version 2.1

In addition, the following standard instruction set extensions are available.

.. list-table:: CV32E40P Standard Instruction Set Extensions
   :header-rows: 1

   * - Standard Extension
     - Version
     - Configurability

   * - **C**: Standard Extension for Compressed Instructions
     - 2.0
     - always enabled

   * - **M**: Standard Extension for Integer Multiplication and Division
     - 2.0
     - always enabled

   * - **Zicount**: Performance Counters
     - 2.0
     - always enabled

   * - **Zicsr**: Control and Status Register Instructions
     - 2.0
     - always enabled

   * - **Zifencei**: Instruction-Fetch Fence
     - 2.0
     - always enabled

   * - **F**: Single-Precision Floating-Point
     - 2.2
     - optionally enabled based on ``FPU`` parameter

Most content of the RISC-V privileged specification is optional.
CV32E40P currently supports the following features according to the RISC-V Privileged Specification, version 1.11.

* M-Mode
* All CSRs listed in :ref:`cs-registers`
* Hardware Performance Counters as described in :ref:`performance-counters` based on ``NUM_MHPMCOUNTERS`` parameter
* Trap handling supporting direct mode or vectored mode as described at :ref:`exceptions-interrupts`


Synthesis guidelines
--------------------

The CV32E40P core is fully synthesizable.
It has been designed mainly for ASIC designs, but FPGA synthesis
is supported as well.

All the files in the ``rtl`` and ``rtl/include`` folders are synthesizable.
The user should first decide whether to use the flip-flop or latch-based register-file ( see :ref:`register-file`).
Secondly, the user must provide a clock-gating module that instantiates the clock-gating cells of the target technology. This file must have the same interface and module name of the one provided for simulation-only purposes
at ``bhv/cv32e40p_sim_clock_gate.sv`` (see :ref:`clock-gating-cell`).
The  ``rtl/cv32e40p_pmp.sv`` should not be included in the synthesis scripts as it is not supported.
This file is kept in the repository as a starting-point for users that want to implement their own.

The ``constraints/cv32e40p_core.sdc`` file provides an example of synthesis constraints.


ASIC Synthesis
^^^^^^^^^^^^^^

ASIC synthesis is supported for CV32E40P. The whole design is completely
synchronous and uses positive-edge triggered flip-flops, except for the
register file, which can be implemented either with latches or with
flip-flops. See :ref:`register-file` for more details. The
core occupies an area of about 50 kGE when the latch based register file
is used. With the FPU, the area increases to about 90 kGE (30 kGE
FPU, 10 kGE additional register file). A technology specific implementation
of a clock gating cell as described in :ref:`clock-gating-cell` needs to
be provided.

FPGA Synthesis
^^^^^^^^^^^^^^^

FPGA synthesis is supported for CV32E40P when the flip-flop based register
file is used. Since latches are not well supported on FPGAs, it is
crucial to select the flip-flop based register file. The user needs to provide
a technology specific implementation of a clock gating cell as described
in :ref:`clock-gating-cell`.

Verification
------------

The verification environment (testbenches, testcases, etc.) for the CV32E40P
core can be found at  `core-v-verif <https://github.com/openhwgroup/core-v-verif>`_.
It is recommended that you start by reviewing the
`CORE-V Verification Strategy <https://core-v-docs-verif-strat.readthedocs.io/en/latest/>`_.

Contents
--------

 * :ref:`getting-started` discusses the requirements and initial steps to start using CV32E40P.
 * :ref:`core-integration` provides the instantiation template and gives descriptions of the design parameters as well as the input and output ports.
 * :ref:`pipeline-details` described the overal pipeline structure.
 * The instruction and data interfaces of CV32E40P are explained in :ref:`instruction-fetch` and :ref:`load-store-unit`, respectively.
 * The two register-file flavors are described in :ref:`register-file`.
 * :ref:`fpu` describes the Floating Point Unit (FPU).
 * :ref:`sleep_unit` describes the Sleep unit.
 * The control and status registers are explained in :ref:`cs-registers`.
 * :ref:`performance-counters` gives an overview of the performance monitors and event counters available in CV32E40P.
 * :ref:`exceptions-interrupts` deals with the infrastructure for handling exceptions and interrupts.
 * :ref:`debug-support` gives a brief overview on the debug infrastructure.
 * :ref:`tracer` gives a brief overview of the tracer module.
 * :ref:`custom-isa-extensions` describes the custom instruction set extensions.
 * :ref:`glossary` provides definitions of used terminology.

History
-------

CV32E40P started its life as a fork of the OR10N CPU core that is based on the OpenRISC ISA. Then, under the name of RI5CY, it became a RISC-V core (2016), and it has been maintained by the PULP platform <https://pulp-platform.org> team until February 2020, when it has been contributed to OpenHW Group https://www.openhwgroup.org>.

References
----------

1. `Gautschi, Michael, et al. "Near-Threshold RISC-V Core With DSP Extensions for Scalable IoT Endpoint Devices." in IEEE Transactions on Very Large Scale Integration (VLSI) Systems, vol. 25, no. 10, pp. 2700-2713, Oct. 2017 <https://ieeexplore.ieee.org/document/7864441>`_

2. `Schiavone, Pasquale Davide, et al. "Slow and steady wins the race? A comparison of ultra-low-power RISC-V cores for Internet-of-Things applications." 27th International Symposium on Power and Timing Modeling, Optimization and Simulation (PATMOS 2017) <https://doi.org/10.1109/PATMOS.2017.8106976>`_

Contributors
------------

| Andreas Traber
  (`*atraber@iis.ee.ethz.ch* <mailto:atraber@iis.ee.ethz.ch>`__)

Michael Gautschi
(`*gautschi@iis.ee.ethz.ch* <mailto:gautschi@iis.ee.ethz.ch>`__)

Pasquale Davide Schiavone
(`*pschiavo@iis.ee.ethz.ch* <mailto:pschiavo@iis.ee.ethz.ch>`__)

Arjan Bink (`*arjan.bink@silabs.com* <mailto:arjan.bink@silabs.com>`__)

Paul Zavalney (`*paul.zavalney@silabs.com* <mailto:paul.zavalney@silabs.com>`__)

| Micrel Lab and Multitherman Lab
| University of Bologna, Italy

| Integrated Systems Lab
| ETH Zürich, Switzerland
