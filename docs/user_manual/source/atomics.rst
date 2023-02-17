.. _atomics:

Atomic instructions
===================

|corev| supports Load-Reserved/Store-Conditional instructions (i.e. ``lr.w`` and ``sc.w``) if ``A_EXT`` = ZALRSC or A.
|corev| supports Load-Reserved/Store-Conditional instructions and Atomic Memory Operations (AMOs) if ``A_EXT`` = A.

Load-Reserved/Store-Conditional Instructions
--------------------------------------------

The ``lr.w`` and ``sc.w`` instructions are supported if ``A_EXT`` = ZALRSC or ``A_EXT`` = A. These instructions perform exclusive transactions via the
data OBI interface. The ``data_atop_o`` signal will indicate the type of exclusive transaction
as specified in [OPENHW-OBI]_.

The definition of the related reservation set as well as registering or invalidating a reservation is outside the scope of |corev|.

Exclusive transaction success of ``lr.w`` and ``sc.w`` instructions is signaled with ``data_err_i`` = 0 and ``data_exokay_i`` = 1.
Exclusive transaction failure of ``lr.w`` and ``sc.w`` instructions is signaled with ``data_err_i`` = 0 and ``data_exokay_i`` = 0.
Bus errors for ``lr.w`` and ``sc.w`` instructions are signaled with ``data_err_i`` = 1 and ``data_exokay_i`` = 0.

If a ``sc.w`` succeeds |corev| writes 0 ``rd``. If a ``sc.w`` fails |corev|  writes a nonzero value (1) to ``rd``. |corev| ignores the ``data_exokay_i``
signal for ``lr.w`` instructions and will therefore **not** detect the failure of ``lr.w`` instructions. If a ``lr.w`` fails because it is attempted on
a region without support for exclusive transactions, then a following ``sc.w`` will fail as well. The PMA's ``atomic`` attribute can be used to detect attempts
to perform any type of atomic transaction (including ``lr.w`` and ``sc.w``) on regions not supporting atomic transactions.

.. note::
  An ``mret`` instruction will **not** clear the reservation set, and thus trap handlers must execute a ``sc.w`` if needed before executing ``mret``.

Atomic Memory Operations
------------------------

The ``amoswap.w``, ``amoadd.w``, ``amoand.w``, ``amoor.w``, ``amoxor.w``, ``amomax[u].w`` and ``amomin[u].w`` instructions are supported if ``A_EXT`` = A. These instructions
perform atomic memory operations (AMOs).

Atomic memory operation (AMO) instructions perform read-modify-write operations for multiprocessor
synchronization. They atomically load a data value from the address in ``rs1``, place the value into register ``rd``,
apply a binary operator to the loaded value and the original value in ``rs2``, then store the result back
to the address in ``rs1``.

|corev| does however **not** provide a full implementation of these instructions as it is assumed
that |corev| is used in combination with an external adapter that transforms the related OBI transactions into the required *read-modify-write* sequences.

|corev| will use the data OBI interface as follows for AMOs:

* ``data_addr_o`` is used to signal the address in ``rs1``.
* ``data_atop_o`` is used to signal the AMO as specified in [OPENHW-OBI]_.
* ``data_wdata_o`` is used to signal the original value in ``rs2``.
* ``data_we_o`` will be 1.
* ``data_rdata_i`` is used to receive the value that is then placed into register ``rd``.

The environment of |corev| is expected to do the following for AMOs:

* Atomically load a data value from the address ``data_addr_o``, return it on ``data_rdata_i`` (even though ``data_we_o`` = 1 for this transaction),
  apply a binary operator as specified via ``data_atop_o`` to the loaded value and ``data_wdata_o``
  and write the result to address ``data_addr_o``.

The timing and validity of the ``data_rdata_i`` and ``data_wdata_o`` signals are the same as for non-AMOs.
