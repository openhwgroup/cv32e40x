.. _sleep_unit:

Sleep Unit
==========

Source File: :file:`rtl/cv32e40x_sleep_unit.sv`

The Sleep Unit contains and controls the instantiated clock gate, see :ref:`clock-gating-cell`, that gates ``clk_i`` and produces a gated clock
for use by the other modules inside |corev|. The Sleep Unit is the only place in which ``clk_i`` itself is used; all
other modules use the gated version of ``clk_i``.

The clock gating in the Sleep Unit is impacted by the following:

 * ``rst_ni``
 * ``fetch_enable_i``
 * **wfi** instruction

:numref:`Sleep Unit interface signals` describes the Sleep Unit interface.

.. table:: Sleep Unit interface signals
  :name: Sleep Unit interface signals

  +--------------------------------------+-----------+--------------------------------------------------+
  | Signal                               | Direction | Description                                      |
  +======================================+===========+==================================================+
  | ``core_sleep_o``                     | output    | Core is sleeping because                         |
  |                                      |           | of a **wfi** instruction. If                     |
  |                                      |           | ``core_sleep_o`` = 1, then ``clk_i`` is gated    |
  |                                      |           | off internally and it is allowed to gate off     |
  |                                      |           | ``clk_i`` externally as well. See                |
  |                                      |           | :ref:`wfi` for details.                          |
  +--------------------------------------+-----------+--------------------------------------------------+


Startup behavior
----------------

``clk_i`` is internally gated off (while signaling ``core_sleep_o`` = 0) during |corev| startup:

 * ``clk_i`` is internally gated off during ``rst_ni`` assertion
 * ``clk_i`` is internally gated off from ``rst_ni`` deassertion until ``fetch_enable_i`` = 1

After initial assertion of ``fetch_enable_i``, the ``fetch_enable_i`` signal is ignored until after a next reset assertion.

.. _wfi:

WFI
---

The **wfi** instruction can under certain conditions be used to enter sleep mode awaiting a locally enabled
interrupt to become pending. The operation of **wfi** is unaffected by the global interrupt bits in **mstatus**.

A **wfi** will not enter sleep mode, but will be executed as a regular **nop**, if any of the following conditions apply:

 * ``debug_req_i`` = 1 or a debug request is pending
 * The core is in debug mode
 * The core is performing single stepping (debug)
 * The core has a trigger match (debug)

If a **wfi** causes sleep mode entry, then ``core_sleep_o`` is set to 1 and ``clk_i`` is gated off internally. ``clk_i`` is
allowed to be gated off externally as well in this scenario. A wake-up can be triggered by any of the following:

 * A locally enabled interrupt is pending
 * A debug request is pending
 * Core is in debug mode

Upon wake-up ``core_sleep_o`` is set to 0, ``clk_i`` will no longer be gated internally, must not be gated off externally, and
instruction execution resumes.

If one of the above wake-up conditions coincides with the **wfi** instruction, then sleep mode is not entered and ``core_sleep_o``
will not become 1.

:numref:`wfi-example` shows an example waveform for sleep mode entry because of a **wfi** instruction.

.. figure:: ../images/wfi.svg
   :name: wfi-example
   :align: center

   **wfi** example
