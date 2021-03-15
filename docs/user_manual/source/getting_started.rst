.. _getting-started:

Getting Started with |corev|
=============================

This page discusses initial steps and requirements to start using |corev| in your design.

.. _clock-gating-cell:

Clock Gating Cell
-----------------

|corev| requires clock gating cells.
These cells are usually specific to the selected target technology and thus not provided as part of the RTL design.
A simulation-only version of the clock gating cell is provided in ``cv32e40x_sim_clock_gate.sv``. This file contains
a module called ``cv32e40x_clock_gate`` that has the following ports:

* ``clk_i``: Clock Input
* ``en_i``: Clock Enable Input
* ``scan_cg_en_i``: Scan Clock Gate Enable Input (activates the clock even though ``en_i`` is not set)
* ``clk_o``: Gated Clock Output

And the following Parameters:
* ``LIB`` : Standard cell library (semantics defined by integrator)

Inside |corev|, the clock gating cell is used in ``cv32e40x_sleep_unit.sv``.

The ``cv32e40x_sim_clock_gate.sv`` file is not intended for synthesis. For ASIC synthesis and FPGA synthesis the manifest
should be adapted to use a customer specific file that implements the ``cv32e40x_clock_gate`` module using design primitives
that are appropriate for the intended synthesis target technology.
