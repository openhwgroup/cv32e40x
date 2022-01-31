.. _fencei:

Fence.i external handshake
==========================
|corev| includes an external handshake that will be exercised upon execution of the fence.i instruction.
The handshake is composed of the signals ``fencei_flush_req_o`` and ``fencei_flush_ack_i`` and can for example be used to flush an externally connected cache.

The ``fencei_flush_req_o`` signal will go high upon executing a ``fence.i`` instruction once possible earlier store instructions have fully completed (including
emptying of the the write buffer).
The ``fencei_flush_req_o`` signal will go low again the cycle after sampling both ``fencei_flush_req_o`` and ``fencei_flush_ack_i`` high.
Once ``fencei_flush_req_o`` has gone low again a branch will be taken to the instruction after the ``fence.i`` thereby flushing possibly prefetched instructions.

Fence instructions are not impacted by the distinction between main and I/O regions (defined in :ref:`pma`) and execute as a conservative fence on all operations, ignoring the predecessor and successor fields.

.. note::

   If the ``fence.i`` external handshake is not used by the environment of |corev|, then it is recommended to tie the ``fencei_flush_ack_i``
   to 1 in order to avoid stalling ``fence.i`` instructions indefinitely.
