.. _load-store-unit:

Load-Store-Unit (LSU)
=====================

The Load-Store Unit (LSU) of the core takes care of accessing the data memory. Load and
stores on words (32 bit), half words (16 bit) and bytes (8 bit) are
supported.

:numref:`LSU interface signals` describes the signals that are used by the LSU.

.. table:: LSU interface signals
  :name: LSU interface signals

  +---------------------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | **Signal**                | **Direction**   | **Description**                                                                                                              |
  +---------------------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``data_req_o``            | output          | Request valid, will stay high until ``data_gnt_i`` is high for one cycle                                                     |
  +---------------------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``data_gnt_i``            | input           | The other side accepted the request. ``data_addr_o``, ``data_atop_o``, ``data_be_o``, ``data_memtype_o[2:0]``,               |
  |                           |                 | ``data_prot_o``, ``data_wdata_o``, ``data_we_o`` may change in the next cycle.                                               |
  +---------------------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``data_addr_o[31:0]``     | output          | Address, sent together with ``data_req_o``.                                                                                  |
  +---------------------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``data_atop_o[5:0]``      | output          | Atomic attributes, sent together with ``data_req_o``.                                                                        |
  +---------------------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``data_be_o[3:0]``        | output          | Byte Enable. Is set for the bytes to write/read, sent together with ``data_req_o``.                                          |
  +---------------------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``data_memtype_o[1:0]``   | output          | Memory Type attributes (cacheable, bufferable), sent together with ``data_req_o``.                                           |
  +---------------------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``data_prot_o[2:0]``      | output          | Protection attributes, sent together with ``data_req_o``.                                                                    |
  +---------------------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``data_dbg_o``            | output          | Debug mode access, sent together with ``data_req_o``.                                                                        |
  +---------------------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``data_wdata_o[31:0]``    | output          | Data to be written to memory, sent together with ``data_req_o``.                                                             |
  +---------------------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``data_we_o``             | output          | Write Enable, high for writes, low for reads. Sent together with ``data_req_o``.                                             |
  +---------------------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``data_rvalid_i``         | input           | ``data_rvalid_i`` will be high for exactly one cycle to signal the end of the response phase of for both read and write      |
  |                           |                 | transactions. For a read transaction ``data_rdata_i`` holds valid data when ``data_rvalid_i`` is high.                       |
  +---------------------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``data_rdata_i[31:0]``    | input           | Data read from memory. Only valid when ``data_rvalid_i`` is high.                                                            |
  +---------------------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``data_err_i``            | input           | A data interface error occurred. Only valid when ``data_rvalid_i`` is high.                                                  |
  +---------------------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``data_exokay_i``         | input           | Exclusive transaction status. Only valid when ``data_rvalid_i`` is high.                                                     |
  +---------------------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+

Misaligned Accesses
-------------------

Misaligned transaction are supported in hardware for Main memory regions, see :ref:`pma`. For loads and stores in Main memory where the effective
address is not naturally aligned to the referenced datatype (i.e., on a four-byte boundary for word accesses, and a two-byte boundary for halfword
accesses) the load/store is performed as two bus transactions in case that the data item crosses a word boundary. A single load/store instruction
is therefore performed as two bus transactions for the following scenarios:

* Load/store of a word for a non-word-aligned address
* Load/store of a halfword crossing a word address boundary

In both cases the transfer corresponding to the lowest address is performed first. All other scenarios can be handled with a single bus transaction.

Misaligned transactions are not supported in I/O regions and will result in an exception trap when attempted, see :ref:`exceptions-interrupts`. 

Protocol
--------

The data bus interface is compliant to the OBI protocol (see [OPENHW-OBI]_ for detailed signal and protocol descriptions).
The |corev| data interface does not implement
the following optional OBI signals: auser, wuser, aid, rready, ruser, rid.
These signals can be thought of as being tied off as specified in the OBI
specification. The |corev| data interface can cause up to two outstanding
transactions.

The OBI protocol that is used by the LSU to communicate with a memory works
as follows.

The LSU provides a valid address on ``data_addr_o``, control information
on ``data_we_o``, ``data_be_o`` (as well as write data on ``data_wdata_o`` in
case of a store) and sets ``data_req_o`` high. The memory sets ``data_gnt_i``
high as soon as it is ready to serve the request. This may happen at any
time, even before the request was sent. After a request has been granted
the address phase signals (``data_addr_o``, ``data_we_o``, ``data_be_o`` and
``data_wdata_o``) may be changed in the next cycle by the LSU as the memory
is assumed to already have processed and stored that information. After
granting a request, the memory answers with a ``data_rvalid_i`` set high
if ``data_rdata_i`` is valid. This may happen one or more cycles after the
request has been granted. Note that ``data_rvalid_i`` must also be set high
to signal the end of the response phase for a write transaction (although
the ``data_rdata_i`` has no meaning in that case). When multiple granted requests 
are outstanding, it is assumed that the memory requests will be kept in-order and
one ``data_rvalid_i`` will be signalled for each of them, in the order they were issued.

:numref:`obi-data-basic`, :numref:`obi-data-back-to-back`, :numref:`obi-data-slow-response` and
:numref:`obi-data-multiple-outstanding` show example timing diagrams of the protocol.

.. figure:: ../images/obi_data_basic.svg
   :name: obi-data-basic
   :align: center
   :alt:

   Basic Memory Transaction

.. figure:: ../images/obi_data_back_to_back.svg
   :name: obi-data-back-to-back
   :align: center
   :alt:

   Back-to-back Memory Transactions

.. figure:: ../images/obi_data_slow_response.svg
   :name: obi-data-slow-response
   :align: center
   :alt:

   Slow Response Memory Transaction

.. figure:: ../images/obi_data_multiple_outstanding.svg
   :name: obi-data-multiple-outstanding
   :align: center
   :alt:

   Multiple Outstanding Memory Transactions

.. only:: PMP

  Physical Memory Protection (PMP) Unit
  -------------------------------------

  The |corev| core has a PMP module which is optionally enabled.
  Such unit has a configurable number of entries (up to 16) and
  supports all the modes as TOR, NAPOT and NA4. Every fetch, load and
  store access executed in USER MODE are first filtered by the PMP unit
  which can possibly generated exceptions. For the moment, the MPRV bit in
  MSTATUS as well as the LOCK mechanism in the PMP are not supported.


.. _write_buffer:

Write buffer
------------

|corev| contains a a single entry write buffer that is used for bufferable transfers. A bufferable transfer is a write transfer originating from a store instruction, where the write address is inside a bufferable region defined by the PMA (:ref:`pma`).
Note that Store Conditional (SC) and Atomic Memory Operation (AMO) instructions will not utilize the write buffer.

The write buffer (when not full) allows |corev| to proceed executing instructions without having to wait for ``data_gnt_i`` = 1 and ``data_rvalid_i`` = 1 for these bufferable transers.

.. note::

   On the OBI interface ``data_gnt_i`` = 1 and ``data_rvalid_i`` = 1 still need to be signaled for every transfer (as specified in [OPENHW-OBI]_), also for bufferable transfers.
 
Bus transfers will occur in program order, no matter if transfers are bufferable and non-bufferable.
Transactions in the write buffer must be completed before the |corev| is able to:
 
 * Retire a fence instruction
 * Enter SLEEP mode
