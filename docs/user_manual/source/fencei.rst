.. _fencei:

Fence.i external handshake
==========================
|corev| includes an external handshake that will be exercised upon execution of the fence.i instruction.
The handshake is composed of the signals ``fencei_flush_req_o`` and ``fencei_flush_ack_i``.

The ``fencei_flush_req_o`` signal will go high upon a fence.i instruction, but only after possible earlier load/store instructions have fully completed.
The ``fencei_flush_req_o`` signal will go low again the cycle after sampling both ``fencei_flush_req_o`` and ``fencei_flush_ack_i`` high.
Once ``fencei_flush_req_o`` has gone low again a branch will be taken to the instruction after the fence.i.
