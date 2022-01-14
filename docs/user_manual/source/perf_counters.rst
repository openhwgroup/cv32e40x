.. _performance-counters:

Performance Counters
====================

|corev| implements performance counters according to [RISC-V-PRIV]_.
The performance counters are placed inside the Control and Status Registers (CSRs) and can be accessed with the ``CSRRW(I)`` and ``CSRRS/C(I)`` instructions.

|corev| implements the clock cycle counter ``mcycle(h)``, the retired instruction counter ``minstret(h)``, as well as the parameterizable number of event counters ``mhpmcounter3(h)`` - ``mhpmcounter31(h)`` and the corresponding event selector CSRs ``mhpmevent3`` - ``mhpmevent31``, and the ``mcountinhibit`` CSR to individually enable/disable the counters.
``mcycle(h)`` and ``minstret(h)`` are always available.

All counters are 64 bit wide.

The number of event counters is determined by the parameter ``NUM_MHPMCOUNTERS`` with a range from 0 to 29 (default value of 1).

Unimplemented counters always read 0.

.. note::

   All performance counters are using the gated version of ``clk_i``. The **wfi** instruction impact the gating of ``clk_i`` as explained
   in :ref:`sleep_unit` and can therefore affect the counters.

.. _event_selector:

Event Selector
--------------

The following events can be monitored using the performance counters of |corev|.


+-------------+-----------------+----------------------------------------------------------------------------------------+
| Bit #       | Event Name      |                                                                                        |
+=============+=================+========================================================================================+
| 0           | CYCLES          | Number of cycles                                                                       |
+-------------+-----------------+----------------------------------------------------------------------------------------+
| 1           | INSTR           | Number of instructions retired                                                         |
+-------------+-----------------+----------------------------------------------------------------------------------------+
| 2           | COMP_INSTR      | Number of compressed instructions retired                                              |
+-------------+-----------------+----------------------------------------------------------------------------------------+
| 3           | JUMP            | Number of jumps (unconditional)                                                        |
+-------------+-----------------+----------------------------------------------------------------------------------------+
| 4           | BRANCH          | Number of branches (conditional)                                                       |
+-------------+-----------------+----------------------------------------------------------------------------------------+
| 5           | BRANCH_TAKEN    | Number of branches taken (conditional)                                                 |
+-------------+-----------------+----------------------------------------------------------------------------------------+
| 6           | INTR_TAKEN      | Number of taken interrupts (excluding NMI)                                             |
+-------------+-----------------+----------------------------------------------------------------------------------------+
| 7           | DATA_READ       | Number of read transactions on the OBI data interface.                                 |
+-------------+-----------------+----------------------------------------------------------------------------------------+
| 8           | DATA_WRITE      | Number of write transactions on the OBI data interface.                                |
+-------------+-----------------+----------------------------------------------------------------------------------------+
| 9           | IF_INVALID      | Number of cycles that the IF stage causes ID stage underutilization                    |
+-------------+-----------------+----------------------------------------------------------------------------------------+
| 10          | ID_INVALID      | Number of cycles that the ID stage causes EX stage underutilization                    |
+-------------+-----------------+----------------------------------------------------------------------------------------+
| 11          | EX_INVALID      | Number of cycles that the EX stage causes WB stage underutilization                    |
+-------------+-----------------+----------------------------------------------------------------------------------------+
| 12          | WB_INVALID      | Number of cycles that the WB stage causes register file write port underutilization    |
+-------------+-----------------+----------------------------------------------------------------------------------------+
| 13          | LD_STALL        | Number of stall cycles caused by load use hazards                                      |
+-------------+-----------------+----------------------------------------------------------------------------------------+
| 14          | JMP_STALL       | Number of stall cycles caused by jump register hazards                                 |
+-------------+-----------------+----------------------------------------------------------------------------------------+
| 15          | WB_DATA_STALL   | Number of stall cycles caused in the WB stage by loads/stores.                         |
+-------------+-----------------+----------------------------------------------------------------------------------------+

The event selector CSRs ``mhpmevent3`` - ``mhpmevent31`` define which of these events are counted by the event counters ``mhpmcounter3(h)`` - ``mhpmcounter31(h)``.
If a specific bit in an event selector CSR is set to 1, this means that events with this ID are being counted by the counter associated with that selector CSR.
If an event selector CSR is 0, this means that the corresponding counter is not counting any event.

.. note::

   At most 1 bit should be set in an event selector. If multiple bits are set in an event selector, then the operation of the associated counter is undefined.


Controlling the counters from software
--------------------------------------

By default, all available counters are disabled after reset in order to provide the lowest power consumption.

They can be individually enabled/disabled by overwriting the corresponding bit in the ``mcountinhibit`` CSR at address ``0x320`` as described in [RISC-V-PRIV]_.
In particular, to enable/disable ``mcycle(h)``, bit 0 must be written. For ``minstret(h)``, it is bit 2. For event counter ``mhpmcounterX(h)``, it is bit X.

The lower 32 bits of all counters can be accessed through the base register, whereas the upper 32 bits are accessed through the ``h``-register.
Reads of all these registers are non-destructive.

Parametrization at synthesis time
---------------------------------

The ``mcycle(h)`` and ``minstret(h)`` counters are always available and 64 bit wide.

The number of available event counters ``mhpmcounterX(h)`` can be controlled via the ``NUM_MHPMCOUNTERS`` parameter.
By default ``NUM_MHPCOUNTERS`` set to 1.

An increment of 1 to the NUM_MHPCOUNTERS results in the addition of the following:

   - 64 flops for ``mhpmcounterX``
   - 15 flops for `mhpmeventX`
   -  1 flop  for `mcountinhibit[X]`
   - Adder and event enablement logic

Time Registers (``time(h)``)
----------------------------

The user mode ``time(h)`` registers are not implemented. Any access to these
registers will cause an illegal instruction trap. It is recommended that a software trap handler is
implemented to detect access of these CSRs and convert that into access of the
platform-defined ``mtime`` register (if implemented in the platform).
