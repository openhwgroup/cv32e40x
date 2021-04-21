Introduction
=============

|corev| is a 4-stage in-order 32-bit RISC-V
processor core. :numref:`blockdiagram` shows a block diagram of the core.

.. figure:: ../images/CV32E40X_Block_Diagram.png
   :name: blockdiagram
   :align: center
   :alt:

   Block Diagram of |corev| RISC-V Core

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

|corev| is a standards-compliant 32-bit RISC-V processor.
It follows these specifications:

.. [RISC-V-UNPRIV] RISC-V Instruction Set Manual, Volume I: User-Level ISA, Document Version 20191213 (December 13, 2019),
   https://github.com/riscv/riscv-isa-manual/releases/download/Ratified-IMAFDQC/riscv-spec-20191213.pdf

.. [RISC-V-PRIV] RISC-V Instruction Set Manual, Volume II: Privileged Architecture, document version 20190608-Base-Ratified (June 8, 2019),
   https://github.com/riscv/riscv-isa-manual/releases/download/Ratified-IMFDQC-and-Priv-v1.11/riscv-privileged-20190608.pdf

.. [RISC-V-DEBUG] RISC-V External Debug Support, version 0.13.2,
   https://content.riscv.org/wp-content/uploads/2019/03/riscv-debug-release.pdf

.. [RISC-V-ZCE] RISC-V Standard Extension for Enhanced Compressed Instructions, v0.29.1 (not ratified yet),
   https://github.com/riscv/riscv-code-size-reduction/blob/master/ISA%20proposals/Huawei/Zce_spec.adoc

.. [OPENHW-OBI] OpenHW Open Bus Interface (OBI) protocol, version 1.2,
   https://github.com/openhwgroup/core-v-docs/blob/master/cores/cv32e40p/OBI-v1.2.pdf

.. [OPENHW-X] OpenHW eXtension Interface, version 0.1,
   https://github.com/pulp-platform/riscv-extension-interface

Many features in the RISC-V specification are optional, and |corev| can be parameterized to enable or disable some of them.

|corev| supports the following base instruction set from [RISC-V-UNPRIV]_.

* The RV32I Base Integer Instruction Set, version 2.1

In addition, the following standard instruction set extensions are available from [RISC-V-UNPRIV]_ and [RISC-V-ZCE]_.

.. list-table:: |corev| Standard Instruction Set Extensions
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

   * - **Zicount**: Performance Counters (as described in the Counters chapter of the RISC-V unprivileged specification)
     - 2.0
     - always enabled

   * - **Zicsr**: Control and Status Register Instructions
     - 2.0
     - always enabled

   * - **Zifencei**: Instruction-Fetch Fence
     - 2.0
     - always enabled

   * - **Zce**: Standard Extension for Code-Size Reduction
     - v0.29.1 (not ratified yet; version will change)
     - always enabled

   * - **A**: Atomic Instructions
     - 2.1
     - optionally enabled based on ``A_EXT`` parameter

   * - **B**: Bit Manipulation
     - 0.93 (not ratified yet; version will change)
     - optionally enabled based on ``B_EXT`` parameter

   * - **P**: Packed-SIMD Instructions
     - 0.9.2-draft-20210202 (not ratified yet; version will change)
     - optionally enabled based on ``P_EXT`` parameter

The following custom instruction set extensions are available.

.. list-table:: |corev| Custom Instruction Set Extensions
   :header-rows: 1

   * - Custom Extension
     - Version
     - Configurability

   * - **X**: eXtension Interface
     - 0.1 (not finalized yet; version will change)
     - optionally enabled based on ``X_EXT`` parameter

.. note::

   |corev| does not implement the **F** extension for single-precision floating-point instructions internal to the core. The **F** extension
   can be supported by interfacing the |corev| to an external FPU via the eXtension interface.

.. note::

   **Zicount** is used in this User Manual to refer to the counter, timer, and performance counter related functionality described
   in the Counters chapter of the RISC-V unprivileged specification. Unfortunately RISC-V International did not name this extension,
   so for now we introduced our own name to refer to this functionality.

Most content of the RISC-V privileged specification is optional.
|corev| currently supports the following features according to the RISC-V Privileged Specification, version 1.11.

* M-Mode
* All CSRs listed in :ref:`cs-registers`
* Hardware Performance Counters as described in :ref:`performance-counters` based on ``NUM_MHPMCOUNTERS`` parameter
* Trap handling supporting direct mode or vectored mode as described at :ref:`exceptions-interrupts`
* Physical Memory Attribution (PMA) as described in :ref:`pma`

Synthesis guidelines
--------------------

The |corev| core is fully synthesizable.
It has been designed mainly for ASIC designs, but FPGA synthesis
is supported as well.

All the files in the ``rtl`` and ``rtl/include`` folders are synthesizable. The user must provide a clock-gating module that instantiates
the clock-gating cells of the target technology. This file must have the same interface and module name of the one provided for simulation-only purposes
at ``bhv/cv32e40x_sim_clock_gate.sv`` (see :ref:`clock-gating-cell`).

The ``constraints/cv32e40x_core.sdc`` file provides an example of synthesis constraints.

ASIC Synthesis
^^^^^^^^^^^^^^

ASIC synthesis is supported for |corev|. The whole design is completely
synchronous and uses positive-edge triggered flip-flops. A technology specific implementation
of a clock gating cell as described in :ref:`clock-gating-cell` needs to
be provided.

FPGA Synthesis
^^^^^^^^^^^^^^^

FPGA synthesis is supported for |corev|. The user needs to provide
a technology specific implementation of a clock gating cell as described
in :ref:`clock-gating-cell`.

Verification
------------

The verification environment (testbenches, testcases, etc.) for the |corev|
core can be found at  `core-v-verif <https://github.com/openhwgroup/core-v-verif>`_.
It is recommended that you start by reviewing the
`CORE-V Verification Strategy <https://core-v-docs-verif-strat.readthedocs.io/en/latest/>`_.

Contents
--------

 * :ref:`getting-started` discusses the requirements and initial steps to start using |corev|.
 * :ref:`core-integration` provides the instantiation template and gives descriptions of the design parameters as well as the input and output ports.
 * :ref:`pipeline-details` described the overal pipeline structure.
 * The instruction and data interfaces of |corev| are explained in :ref:`instruction-fetch` and :ref:`load-store-unit`, respectively.
 * :ref:`pma` describes the Physical Memory Attribution (PMA) unit.
 * The register-file is described in :ref:`register-file`.
 * :ref:`x_ext` describes the custom eXtension interface.
 * :ref:`sleep_unit` describes the Sleep unit.
 * The control and status registers are explained in :ref:`cs-registers`.
 * :ref:`performance-counters` gives an overview of the performance monitors and event counters available in |corev|.
 * :ref:`exceptions-interrupts` deals with the infrastructure for handling exceptions and interrupts.
 * :ref:`debug-support` gives a brief overview on the debug infrastructure.
 * :ref:`rvfi` gives a brief overview of the RVFI module.
 * :ref:`glossary` provides definitions of used terminology.

History
-------
|corev| started its life as a fork of the CV32E40P from the OpenHW Group <https://www.openhwgroup.org>.

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
