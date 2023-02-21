.. _exceptions-interrupts:

Exceptions and Interrupts
=========================

|corev| supports one of two interrupt architectures.
If the ``CLIC`` parameter is set to 0, then the CLINT mode interrupt architecture is supported (see :ref:`clint_interrupt_architecture`).
If the ``CLIC`` parameter is set to 1, then the CLIC mode interrupt architecture is supported (see :ref:`clic_interrupt_architecture`).

Exceptions
----------

|corev| can trigger the following exceptions as reported in ``mcause``:

.. table::
  :class: no-scrollbar-table

  +----------------+----------------+---------------------------------------+---------------------------------------------------------------------------+
  | Interrupt      | Exception Code | Description                           | Scenario(s)                                                               |
  +----------------+----------------+---------------------------------------+---------------------------------------------------------------------------+
  |              0 |              1 | Instruction access fault              | Execution attempt from I/O region.                                        |
  +----------------+----------------+---------------------------------------+---------------------------------------------------------------------------+
  |              0 |              2 | Illegal instruction                   |                                                                           |
  +----------------+----------------+---------------------------------------+---------------------------------------------------------------------------+
  |              0 |              3 | Breakpoint                            | Environment break.                                                        |
  +----------------+----------------+---------------------------------------+---------------------------------------------------------------------------+
  |              0 |              4 | Load address misaligned               | Non-naturally aligned Load-Reserved address.                              |
  +----------------+----------------+---------------------------------------+---------------------------------------------------------------------------+
  |              0 |              5 | Load access fault                     | Non-naturally aligned load access attempt to an I/O region.               |
  |                |                |                                       | Modified load access attempt to an I/O region.                            |
  |                |                |                                       | Load-Reserved attempt to region without atomic support.                   |
  +----------------+----------------+---------------------------------------+---------------------------------------------------------------------------+
  |              0 |              6 | Store/AMO address misaligned          | Non-naturally aligned Store-Conditional / AMO address.                    |
  +----------------+----------------+---------------------------------------+---------------------------------------------------------------------------+
  |              0 |              7 | Store/AMO access fault                | Non-naturally aligned store access attempt to an I/O region.              |
  |                |                |                                       | Modified store access attempt to an I/O region.                           |
  |                |                |                                       | Store-Conditional or Atomic Memory Operation (AMO) attempt                |
  |                |                |                                       | to region without atomic support.                                         |
  +----------------+----------------+---------------------------------------+---------------------------------------------------------------------------+
  |              0 |             11 | Environment call from M-Mode (ECALL)  |                                                                           |
  +----------------+----------------+---------------------------------------+---------------------------------------------------------------------------+
  |              0 |             24 | Instruction bus fault                 | ``instr_err_i`` = 1 and ``instr_rvalid_i`` = 1 for instruction fetch      |
  +----------------+----------------+---------------------------------------+---------------------------------------------------------------------------+

If an instruction raises multiple exceptions, the priority, from high to low, is as follows: 

* ``instruction access fault (1)``
* ``instruction bus fault (24)``
* ``illegal instruction (2)``
* ``environment call from M-Mode (11)``
* ``environment break (3)``
* ``store/AMO access fault (7)``
* ``load access fault (5)``
* ``store/AMO address misaligned (6)``
* ``load address misaligned (4)``

Exceptions in general cannot be disabled and are always active. 
All exceptions are precise.
Whether the PMA will actually cause exceptions depends on its configuration.
|corev|  raises an illegal instruction exception for any instruction in the RISC-V privileged and unprivileged specifications that is explicitly defined as being
illegal according to the ISA implemented by the core, as well as for any instruction that is left undefined in these specifications unless the instruction encoding
is configured as a custom |corev| instruction for specific parameter settings as defined in (see :ref:`custom-isa-extensions`).
An instruction bus error leads to a precise instruction interface bus fault if an attempt is made to execute the instruction that has an associated bus error.
Similarly an instruction fetch with a failing PMA check only leads to an instruction access exception if an actual execution attempt is made for it.

.. note::

   The address misaligned exceptions (exception codes 4 and 6) are only triggered when Load-Reserved, Store-Conditional or AMO instructions use non-naturally aligned addresses for their data access(es)
   and the access is not blocked by a higher priority access fault from the PMA (exception codes 5 or 7).
   Misaligned accesses by non-Atomic instructions are either handled by hardware (no exception) or lead to access faults from the PMA (exception code 5 or 7) as explained in :ref:` misaligned-accesses`.

Non Maskable Interrupts
-----------------------

Non Maskable Interrupts (NMIs) update ``mepc``, ``mcause`` and ``mstatus`` similar to regular interrupts. However, as the faults that result in NMIs are imprecise, the contents of ``mepc`` is not guaranteed to point to the instruction after the faulted load or store.

.. note::

   (Unrecoverable) NMIs and regular interrupts have identical effects on the ``mstatus`` CSR". Specifically ``mstatus.mie`` will get cleared
   to 0 when an (unrecoverable) NMI is taken. [RISC-V-PRIV]_ does not specify the behavior of
   ``mstatus`` in response to NMIs, see https://github.com/riscv/riscv-isa-manual/issues/756. If this behavior is
   specified at a future date, then we will reconsider our implementation.

NMIs have higher priority than other interrupts for both the CLINT mode interrupt architecture and the CLIC mode interrupt architecture.

If ``CLIC`` == 0, then the NMI vector location is as follows:

* Upon an NMI in non-vectored CLINT mode the core jumps to **mtvec[31:7]**, 5'h0, 2'b00} (i.e. index 0).
* Upon an NMI in vectored CLINT mode the core jumps to **mtvec[31:7]**, 5'hF, 2'b00} (i.e. index 15).

If ``CLIC`` == 1, then the NMI vector location is as follows:

* Upon an NMI in CLIC mode the core jumps to **mtvec[31:7]**, 5'h0, 2'b00} (i.e. index 0).

.. note::
   For NMIs the exception codes in the ``mcause`` CSR do not match the table index as for regular interrupts.

An NMI will occur when a load or store instruction experiences a bus fault. The fault resulting in an NMI is handled in an imprecise manner, meaning that the instruction that causes the fault is allowed to retire and the associated NMI is taken afterwards.
NMIs are never masked by the ``MIE`` bit. NMIs are masked however while in debug mode or while single stepping with ``STEPIE`` = 0 in the ``dcsr`` CSR.
This means that many instructions may retire before the NMI is visible to the core if debugging is taking place. Once the NMI is visible to the core, at most two instructions will retire before the NMI is taken.

If an NMI becomes pending while in debug mode as described above, the NMI will be taken immediately after debug mode has been exited.

In case of bufferable stores, the NMI is allowed to become visible an arbitrary time after the instruction retirement. As for the case with debugging, this can cause several instructions to retire
before the NMI becomes visible to the core.

When a data bus fault occurs, the first detected fault will be latched and used for ``mcause`` when the NMI is taken. Any new data bus faults occuring while an NMI is pending will be discarded.
When the NMI handler is entered, new data bus faults may be latched.

While an NMI is pending, ``DCSR.nmip`` will be 1. Note that this CSR is only accessible from debug mode, and is thus not visible for machine mode code.

.. _clint_interrupt_architecture:

CLINT Mode Interrupt Architecture
---------------------------------

If ``CLIC`` == 0, then |corev| supports the CLINT mode interrupt architecture as defined in [RISC-V-PRIV]_. In this configuration only the
CLINT mode interrupt handling modes (non-vectored CLINT mode and vectored CLINT mode) can be used. The ``irq_i[31:16]`` interrupts are a custom extension
that can be used with the CLINT mode interrupt architecture.

When entering an interrupt/exception handler, the core sets the ``mepc`` CSR to the current program counter and saves ``mstatus``.MIE to ``mstatus``.MPIE.
All exceptions cause the core to jump to the base address of the vector table in the ``mtvec`` CSR.
Interrupts are handled in either non-vectored CLINT mode or vectored CLINT mode depending on the value of ``mtvec``.MODE. In non-vectored CLINT mode the core
jumps to the base address of the vector table in the ``mtvec`` CSR. In vectored CLINT mode the core jumps to the base address
plus four times the interrupt ID. Upon executing an MRET instruction, the core jumps to the program counter previously saved in the
``mepc`` CSR and restores ``mstatus``.MPIE to ``mstatus``.MIE.

The base address of the vector table must be aligned to 128 bytes and can be programmed
by writing to the ``mtvec`` CSR (see :ref:`csr-mtvec`).

Interrupt Interface
~~~~~~~~~~~~~~~~~~~

:numref:`CLINT mode interrupt architecture interface signals` describes the interrupt interface used for the CLINT mode interrupt architecture.

.. table:: CLINT mode interrupt architecture interface signals
  :name: CLINT mode interrupt architecture interface signals
  :widths: 10 10 80
  :class: no-scrollbar-table

  +-------------------------+-----------+--------------------------------------------------+
  | Signal                  | Direction | Description                                      |
  +=========================+===========+==================================================+
  | ``irq_i[31:16]``        | input     | Active high, level sensistive interrupt inputs.  |
  |                         |           | Custom extension.                                |
  +-------------------------+-----------+--------------------------------------------------+
  | ``irq_i[15:12]``        | input     | Reserved. Tie to 0.                              |
  +-------------------------+-----------+--------------------------------------------------+
  | ``irq_i[11]``           | input     | Active high, level sensistive interrupt input.   |
  |                         |           | Referred to as Machine External Interrupt (MEI), |
  |                         |           | but integrator can assign a different purpose if |
  |                         |           | desired.                                         |
  +-------------------------+-----------+--------------------------------------------------+
  | ``irq_i[10:8]``         | input     |  Reserved. Tie to 0.                             |
  +-------------------------+-----------+--------------------------------------------------+
  | ``irq_i[7]``            | input     | Active high, level sensistive interrupt input.   |
  |                         |           | Referred to as Machine Timer Interrupt (MTI),    |
  |                         |           | but integrator can assign a different purpose if |
  |                         |           | desired.                                         |
  +-------------------------+-----------+--------------------------------------------------+
  | ``irq_i[6:4]``          | input     |  Reserved. Tie to 0.                             |
  +-------------------------+-----------+--------------------------------------------------+
  | ``irq_i[3]``            | input     | Active high, level sensistive interrupt input.   |
  |                         |           | Referred to as Machine Software Interrupt (MSI), |
  |                         |           | but integrator can assign a different purpose if |
  |                         |           | desired.                                         |
  +-------------------------+-----------+--------------------------------------------------+
  | ``irq_i[2:0]``          | input     |  Reserved. Tie to 0.                             |
  +-------------------------+-----------+--------------------------------------------------+

.. note::

  The ``clic_*_i`` pins are ignored in CLINT mode and should be tied to 0.

Interrupts
~~~~~~~~~~

The ``irq_i[31:0]`` interrupts are controlled via the ``mstatus``, ``mie`` and ``mip`` CSRs. |corev| uses the upper 16 bits of ``mie`` and ``mip`` for custom interrupts (``irq_i[31:16]``),
which reflects an intended custom extension in the RISC-V CLINT mode interrupt architecture.
After reset, all interrupts, except for NMIs, are disabled.
To enable any of the ``irq_i[31:0]`` interrupts, both the global interrupt enable (``MIE``) bit in the ``mstatus`` CSR and the corresponding individual interrupt enable bit in the ``mie`` CSR need to be set. For more information, see the :ref:`cs-registers` documentation.


If multiple interrupts are pending, they are handled in the fixed priority order defined by [RISC-V-PRIV]_.
The highest priority is given to the interrupt with the highest ID, except for the Machine Timer Interrupt, which has the lowest priority. So from high to low priority the interrupts are
ordered as follows: 

* ``store bus fault NMI (1025)``
* ``load bus fault NMI (1024)``
* ``irq_i[31]``
* ``irq_i[30]``
* ...
* ``irq_i[16]``
* ``irq_i[11]``
* ``irq_i[3]``
* ``irq_i[7]``

The ``irq_i[31:0]`` interrupt lines are level-sensitive. The NMIs are triggered by load/store bus fault events.
To clear the ``irq_i[31:0]`` interrupts at the external source, |corev| relies on a software-based mechanism in which the interrupt handler signals completion of the handling routine to the interrupt source, e.g., through a memory-mapped register, which then deasserts the corresponding interrupt line.

In Debug Mode, all interrupts are ignored independent of ``mstatus.MIE`` and the content of the ``mie`` CSR.

|corev| can trigger the following interrupts as reported in ``mcause``:

.. table::
  :widths: 10 10 40 40
  :class: no-scrollbar-table

  +----------------+----------------+-------------------------------------------------+-----------------------------------------------------------------+
  | Interrupt      | Exception Code | Description                                     | Scenario(s)                                                     |
  +----------------+----------------+-------------------------------------------------+-----------------------------------------------------------------+
  |              1 |              3 | Machine Software Interrupt (MSI)                | ``irq_i[3]``                                                    |
  +----------------+----------------+-------------------------------------------------+-----------------------------------------------------------------+
  |              1 |              7 | Machine Timer Interrupt (MTI)                   | ``irq_i[7]``                                                    |
  +----------------+----------------+-------------------------------------------------+-----------------------------------------------------------------+
  |              1 |             11 | Machine External Interrupt (MEI)                | ``irq_i[11]``                                                   |
  +----------------+----------------+-------------------------------------------------+-----------------------------------------------------------------+
  |              1 |          31-16 | Machine Fast Interrupts                         | ``irq_i[31]``-``irq_i[16]``                                     |
  +----------------+----------------+-------------------------------------------------+-----------------------------------------------------------------+
  |              1 |           1024 | Load bus fault NMI (imprecise)                  | ``data_err_i`` = 1 and ``data_rvalid_i`` = 1 for load           |
  +----------------+----------------+-------------------------------------------------+-----------------------------------------------------------------+
  |              1 |           1025 | Store bus fault NMI (imprecise)                 | ``data_err_i`` = 1 and ``data_rvalid_i`` = 1 for store          |
  +----------------+----------------+-------------------------------------------------+-----------------------------------------------------------------+

.. note::

   Load bus fault and store bus fault are handled as imprecise non-maskable interrupts
   (as opposed to precise exceptions).

.. note::

   The NMI vector location is at index 15 of the machine trap vector table for vectored CLINT mode (i.e. at {**mtvec[31:7]**, 5'hF, 2'b00}).
   The NMI vector location therefore does **not** match its exception code as is otherwise the case for vectored CLINT mode.

Nested Interrupt Handling
~~~~~~~~~~~~~~~~~~~~~~~~~
Within the CLINT mode interrupt architecture there is no hardware support for nested interrupt handling. Nested interrupt handling can however still be supported via software.

The hardware automatically disables interrupts upon entering an interrupt/exception handler.
Otherwise, interrupts during the critical part of the handler, i.e. before software has saved the ``mepc`` and ``mstatus`` CSRs, would cause those CSRs to be overwritten.
If desired, software can explicitly enable interrupts by setting ``mstatus``.MIE to 1 from within the handler.
However, software should only do this after saving ``mepc`` and ``mstatus``.
There is no limit on the maximum number of nested interrupts.
Note that, after enabling interrupts by setting ``mstatus``.MIE to 1, the current handler will be interrupted also by lower priority interrupts.
To allow higher priority interrupts only, the handler must configure ``mie`` accordingly.

.. _clic_interrupt_architecture:

CLIC Mode Interrupt Architecture
--------------------------------

If ``CLIC`` == 1, then |corev| supports the  Smclic, Smclicshv and Smclicconfig extensions defined in [RISC-V-CLIC]_. The Ssclic and Suclic extensions are not supported.
In this configuration (i.e. ``CLIC`` == 1) only the CLIC interrupt handling mode can be used (i.e. ``mtvec[1:0]`` = 0x3).

The CLIC implementation is however split into a part internal to the core (containing CSRs and related logic) and a part external to the core (containing memory mapped registers and arbitration logic). |corev| **only**
provides the core internal part of CLIC. The external part can be added on the interface described in :ref:`clic-interrupt-interface`. CLIC provides low-latency, vectored, pre-emptive interrupts.

.. _clic-interrupt-interface:

Interrupt Interface
~~~~~~~~~~~~~~~~~~~

:numref:`CLIC mode interrupt architecture interface signals` describes the interrupt interface used for the CLIC interrupt architecture.

.. table:: CLIC mode interrupt architecture interface signals
  :name: CLIC mode interrupt architecture interface signals
  :widths: 20 10 70
  :class: no-scrollbar-table

  +----------------------------------------+-----------+--------------------------------------------------+
  | Signal                                 | Direction | Description                                      |
  +========================================+===========+==================================================+
  | ``clic_irq_i``                         | input     | Is there any pending-and-enabled interrupt?      |
  +----------------------------------------+-----------+--------------------------------------------------+
  | ``clic_irq_id_i[CLIC_ID_WIDTH-1:0]``   | input     | Index of the most urgent pending-and-enabled     |
  |                                        |           | interrupt.                                       |
  +----------------------------------------+-----------+--------------------------------------------------+
  | ``clic_irq_level_i[7:0]``              | input     | Interrupt level of the most urgent               |
  |                                        |           | pending-and-enabled interrupt.                   |
  +----------------------------------------+-----------+--------------------------------------------------+
  | ``clic_irq_priv_i[1:0]``               | input     | Associated privilege mode of the most urgent     |
  |                                        |           | pending-and-enabled interrupt. Only              |
  |                                        |           | machine-mode interrupts are supported.           |
  +----------------------------------------+-----------+--------------------------------------------------+
  | ``clic_irq_shv_i``                     | input     | Selective hardware vectoring enabled for the     |
  |                                        |           | most urgent pending-and-enabled interrupt?       |
  +----------------------------------------+-----------+--------------------------------------------------+

The term *pending-and-enabled* interrupt in above table refers to *pending-and-locally-enabled*, i.e. based on the ``CLICINTIP`` and
``CLICINTIE`` memory mapped registers from [RISC-V-CLIC]_.

.. note::

   Edge triggered interrupts are not supported.

.. note::

   ``clic_irq_shv_i`` shall be 0 if ``cliccfg.nvbits`` of the externl CLIC module is 0.

.. note::

   ``clic_irq_priv_i[1:0]`` shall be tied to 2'b11 (machine).

.. note::

  The ``irq_i[31:0]`` pins are ignored in CLIC mode and should be tied to 0.

Interrupts
~~~~~~~~~~
Although the [RISC-V-CLIC]_ specification supports up to 4096 interrupts, |corev| itself supports at most 1024 interrupts. The
maximum number of supported CLIC interrupts is equal to ``2^CLIC_ID_WIDTH``, which can range from 2 to 1024. The ``CLIC_ID_WIDTH`` parameter
also impacts the alignment requirement for the trap vector table, see :ref:`csr-mtvt`.

Interrupt prioritization is mostly performed in the part of CLIC that is external to the core, with the exception that |corev| prioritizes all NMIs above interrupts received via ``clic_irq_i``.

Nested Interrupt Handling
~~~~~~~~~~~~~~~~~~~~~~~~~
|corev| offers hardware support for nested interrupt handling when ``CLIC`` == 1. 

CLIC extends interrupt preemption to support up to 256 interrupt levels for each privilege mode,
where higher-numbered interrupt levels can preempt lower-numbered interrupt levels. See [RISC-V-CLIC]_ for details.
