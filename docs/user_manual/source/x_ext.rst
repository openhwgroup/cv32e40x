.. _x_ext:

eXtension Interface
===================

The eXtension interface enables extending |corev| with custom instructions without the need to change the RTL
of |corev| itself. Custom extensions can be provided in separate modules external to |corev| and are integrated
at system level by connecting them to the eXtension interface.

The eXtension interface provides low latency (tightly integrated) read and write access to the |corev| register file.
All opcodes which are not used (i.e. considered to be invalid) by |corev| can be used for custom extensions. It is recommended
however that custom instructions do not use opcodes that are reserved/used by RISC-V International.

The eXtension interface enables extension of |corev| with:

* Custom ALU type instructions.
* Custom load/store type instructions.
* Custom CSRs and related instructions.

Branch type instructions are not supported via the eXtension interface.

.. note::

   |corev| does not implement the **F** extension for single-precision floating-point instructions internal to the core. The **F** extension
   can be supported by interfacing the |corev| to an external FPU via the eXtension interface.


CORE-V-XIF proposal
-------------------

.. note::

   This section describes a CORE-V-XIF **proposal**. This proposal is **not compatible** with the current CORE-V-XIF specification
   in [OPENHW-X]_. It is the intention that this proposal and the specification in [OPENHW-X]_ become aligned eventually.
   In the remainder of this section CORE-V-XIF refers to the CORE-V-XIF *proposal* as described in the |corev| User Manual.

The |corev| eXtension interface is compliant to CORE-V-XIF. The CORE-V-IF specification contains the following parameters:

* ``X_DATAWIDTH`` is the width of an integer register in bits and needs to match the XLEN of the core, so for  |corev| ``X_DATAWIDTH`` = 32.
* ``X_NUM_RS`` specifies the number of register file read ports that can be used by CORE-V-XIF. Legal values are 2 and 3.
* ``X_NUM_WB`` specifies the number of register file write ports that can be used by CORE-V-XIF. Legal values are 1 and 2.

The major features of CORE-V-XIF are:

* Minimal requirements on custom instruction encoding.

  If a custom instruction relies on reading from or writing to the core's general purpose register file, then the standard
  RISC-V bitfield locations for rs1, rs2, rs3, rd as used for non-compressed instructions ([RISC-V-UNPRIV]_) must be used.
  Bitfields for unused read or write operands can be fully repurposed. Custom instructions can either use the compressed
  or uncompressed instruction format. For offloading compressed instructions the coprocessor must provide the core with
  the related non-compressed instructions.

* Support for dual writeback instructions.

  CORE-V-XIF optionally supports implementation of custom ISA extensions mandating dual register file writebacks. Dual writeback
  is supported for even-odd register pairs (``Xn`` and ``Xn+1`` with ``n <> 0`` and ``Xn`` extracted from instruction bits ``[11:7]``.

* Support for ternary operations.

  CORE-V-XIF optionally supports ISA extensions implementing instructions which use three source operands.
  Ternary instructions must be encoded in the R4-type instruction format defined by [RISC-V-UNPRIV]_.

* Support for instruction speculation.

  CORE-V-XIF indicates whether offloaded instructions are allowed to be commited (or should be killed).

CORE-V-XIF consists of six interfaces:

* **Compressed interface**. Signaling of compressed instruction to be offloaded.
* **Issue (request/response) interface**. Signaling of the uncompressed instruction to be offloaded including its register file based operands.
* **Commit interface**. Signaling of control signals related to whether instructions can be committed or should be killed.
* **Memory (request/response) interface**. Signaling of load/store related signals (i.e. its transaction request signals).
* **Memory result interface**. Signaling of load/store related signals (i.e. its transaction result signals).
* **Result interface**. Signaling of the instruction result(s).

Operating principle
-------------------

|corev| will attempt to offload every (compressed or non-compressed) instruction that it does not recognize as a legal instruction itself. In cases of a
compressed instruction the coprocessor must first provide the core with a matching uncompressed (i.e. 32-bit) instruction using the compressed interface.
This non-compressed instruction is then attempted for offload via the issue interface.

Offloading of the (non-compressed, 32-bit) instructions happens via the issue interface. 
The external coprocessor can decide to accept or reject the instruction offload. In case of acceptation the coprocessor
will further handle the instruction. In case of rejection the core will raise an illegal instruction exception (unless the instruction does not reach the
commit stage). As part of the issue interface transaction the core provides the instruction and required register file operand(s) to the coprocessor. If
an offloaded instruction uses any of the register file sources ``rs1``, ``rs2`` or ``rs3``, then these are always encoded in instruction bits ``[19:15]``,
``[24:20]`` and ``[31:27]`` respectively. The coprocessor only needs to wait for the register file operands that a specific instruction actually uses.
The coprocessor informs the core whether an accepted offloaded instruction is a load/store, to which register(s) in the register file it will writeback, and
whether the offloaded instruction can potentially cause a synchronous exception. |corev| uses this information to reserve the load/store unit, to track
data dependencies between instructions, and to properly deal with exceptions caused by offloaded instructions.

Offloaded instructions are speculative; |corev| has not necessarily committed to them yet and might decide to kill them (e.g.
because they are in the shadow of a taken branch or because they are flushed due to an exception in an earlier instruction). Via the commit interface the
core will inform the coprocessor about whether an offloaded instruction will either need to be killed or whether the core will guarantee that the instruction
is no longer speculative and is allowed to be commited.

In case an accepted offloaded instruction is a load or store, then the coprocessor will use the load/store unit(s) in |corev| to actually perform the load
or store. The coprocessor provides the memory request transaction details (e.g. virtual address, write data, etc.) via the memory request interface and |corev|
will use its PMA to check if the load or store is actually allowed, and if so, will use its bus interface(s) to perform the required memory transaction and
provide the result (e.g. load data and/or fault status) back to the coprocessor via the memory result interface.

The final result of an accepted offloaded instruction can be written back into the coprocessor itself or into the core's register file. Either way, the
result interface is used to signal to the core that the instruction has completed. Apart from a possible writeback into the register file, the result
interface transaction is for example used in the core to increment the ``minstret`` CSR, to implement the fence instructions and to judge if instructions
before a ``WFI`` instruction have fully completed (so that sleep mode can be entered if needed).

In short: From a functional perspective it should not matter whether an instruction is handled inside the core or inside a coprocessor. In both cases
the instructions need to obey the same instruction dependency rules, memory consistency rules, load/store address checks, fences, etc.

:numref:`Compressed interface signals` describes the compressed interface signals.

.. table:: Compressed interface signals
  :name: Compressed interface signals

  +---------------------------+---------------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | **Signal**                | **Type**            | **Direction**   | **Description**                                                                                                              |
  +---------------------------+---------------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``x_compressed_valid_o``  | logic               | output          | Compressed request valid. Request to uncompress a compressed instruction.                                                    |
  +---------------------------+---------------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``x_compressed_ready_i``  | logic               | input           | Compressed request ready. The transactions signaled via ``x_compressed_req_o`` and ``x_compressed_resp_i`` are accepted when |
  |                           |                     |                 | ``x_compressed_valid_o`` and  ``x_compressed_ready_i`` are both 1.                                                           |
  +---------------------------+---------------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``x_compressed_req_o``    | x_compressed_req_t  | output          | Compressed request packet.                                                                                                   |
  +---------------------------+---------------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``x_compressed_resp_i``   | x_compressed_resp_t | input           | Compressed response packet.                                                                                                  |
  +---------------------------+---------------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+

:numref:`Compressed request type` describes the ``x_compressed_req_t`` type.

.. table:: Compressed request type
  :name: Compressed request type

  +------------------------+-------------------------+-----------------------------------------------------------------------------------------------------------------+
  | **Signal**             | **Type**                | **Description**                                                                                                 |
  +------------------------+-------------------------+-----------------------------------------------------------------------------------------------------------------+
  | ``instr``              | logic [15:0]            | Offloaded compressed instruction.                                                                               |
  +------------------------+-------------------------+-----------------------------------------------------------------------------------------------------------------+
  | ``id``                 | logic [3:0]             | Identification number of the offloaded compressed instruction.                                                  |
  +------------------------+-------------------------+-----------------------------------------------------------------------------------------------------------------+

The ``instr[15:0]`` signal is used to signal compressed instructions that are considered illegal by |corev| itself. A coprocessor can provide an uncompressed instruction
in response to receiving this.

The ``id`` is a unique identification number for offloaded instructions. An ``id`` value can be reused after an earlier instruction related to the same ``id`` value
has fully completed (i.e. because it was not accepted for offload, because it was killed or because it retired). The same ``id`` value will be used for all transaction
packets on all interfaces that logically relate to the same instruction.

A compressed request transaction is defined as the combination of all ``x_compressed_req_o`` signals during which ``x_compressed_valid_o`` is 1 and the ``id`` remains unchanged. I.e. a new
transaction can be started by just changing the ``id`` signal and keeping the valid signal asserted.

The signals in ``x_compressed_req_o`` are valid when ``x_compressed_valid_o`` is 1. These signals remain stable during a compressed request transaction.

:numref:`Compressed response type` describes the ``x_compressed_resp_t`` type.

.. table:: Compressed response type
  :name: Compressed response type

  +------------------------+----------------------+-----------------------------------------------------------------------------------------------------------------+ 
  | **Signal**             | **Type**             | **Description**                                                                                                 | 
  +------------------------+----------------------+-----------------------------------------------------------------------------------------------------------------+ 
  | ``instr``              | logic [31:0]         | Uncompressed instruction.                                                                                       |
  +------------------------+----------------------+-----------------------------------------------------------------------------------------------------------------+
  | ``accept``             | logic                | Is the offloaded compressed instruction (``id``) accepted by the coprocessor?                                   | 
  |                        |                      | If the compressed instruction is not accepted, then the core will cause an illegal instruction trap unless this | 
  |                        |                      | instruction is killed in the core's pipeline.                                                                   | 
  +------------------------+----------------------+-----------------------------------------------------------------------------------------------------------------+ 

The signals in ``x_compressed_resp_i`` are valid when ``x_compressed_valid_o`` and ``x_compressed_ready_i`` are both 1. There are no stability requirements.

:numref:`Issue interface signals` describes the issue interface signals.

.. table:: Issue interface signals
  :name: Issue interface signals

  +---------------------------+-----------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | **Signal**                | **Type**        | **Direction**   | **Description**                                                                                                              |
  +---------------------------+-----------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``x_issue_valid_o``       | logic           | output          | Issue request valid. Indicates that |corev| wants to offload an instruction.                                                 |
  +---------------------------+-----------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``x_issue_ready_i``       | logic           | input           | Issue request ready. The transaction signaled via ``x_issue_req_o`` and ``x_issue_resp_i`` is accepted when                  |
  |                           |                 |                 | ``x_issue_valid_o`` and  ``x_issue_ready_i`` are both 1.                                                                     |
  +---------------------------+-----------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``x_issue_req_o``         | x_issue_req_t   | output          | Issue request packet.                                                                                                        |
  +---------------------------+-----------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``x_issue_resp_i``        | x_issue_resp_t  | input           | Issue response packet.                                                                                                       |
  +---------------------------+-----------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+

:numref:`Issue request type` describes the ``x_issue_req_t`` type.

.. table:: Issue request type
  :name: Issue request type

  +------------------------+-------------------------+-----------------------------------------------------------------------------------------------------------------+
  | **Signal**             | **Type**                | **Description**                                                                                                 |
  +------------------------+-------------------------+-----------------------------------------------------------------------------------------------------------------+
  | ``instr``              | logic [31:0]            | Offloaded instruction.                                                                                          |
  +------------------------+-------------------------+-----------------------------------------------------------------------------------------------------------------+
  | ``id``                 | logic [3:0]             | Identification of the offloaded instruction.                                                                    |
  |                        |                         |                                                                                                                 |
  |                        |                         |                                                                                                                 |
  +------------------------+-------------------------+-----------------------------------------------------------------------------------------------------------------+
  | ``rs[X_NUM_RS-1:0]``   | logic [31:0]            | Register file source operands for the offloaded instruction.                                                    |
  +------------------------+-------------------------+-----------------------------------------------------------------------------------------------------------------+
  | ``rs_valid``           | logic [X_NUM_RS-1:0]    | Validity of the register file source operand(s).                                                                |
  +------------------------+-------------------------+-----------------------------------------------------------------------------------------------------------------+

A issue request transaction is defined as the combination of all ``x_issue_req_o`` signals during which ``x_issue_valid_o`` is 1 and the ``id`` remains unchanged. I.e. a new
transaction can be started by just changing the ``id`` signal and keeping the valid signal asserted.

The ``instr``, ``id`` and ``rs_valid`` signals are valid when ``x_issue_valid_o`` is 1. The ``rs`` is only considered valid when ``x_issue_valid_o`` is 1 and the corresponding
bit in ``rs_valid`` is 1 as well.

The ``instr`` signal remain stable during an issue request transaction. The ``rs_valid`` bits are not required to be stable during the transaction. Each bit
can transition from 0 to 1, but is not allowed to transition back to 0 during a transaction. The ``rs`` signals are only required to be stable during the part
of a transaction in which these signals are considered to be valid.

:numref:`Issue response type` describes the ``x_issue_resp_t`` type.

.. table:: Issue response type
  :name: Issue response type

  +------------------------+----------------------+------------------------------------------------------------------------------------------------------------------+ 
  | **Signal**             | **Type**             | **Description**                                                                                                  | 
  +------------------------+----------------------+------------------------------------------------------------------------------------------------------------------+ 
  | ``accept``             | logic                | Is the offloaded instruction (``id``) accepted by the coprocessor? If                                            | 
  |                        |                      | the instruction is not accepted, then the core will cause an illegal instruction trap unless this offloaded      | 
  |                        |                      | instruction is killed.                                                                                           | 
  +------------------------+----------------------+------------------------------------------------------------------------------------------------------------------+ 
  | ``writeback``          | logic [X_NUM_WB-1:0] | Will the coprocessor perform a writeback to ``rd`` (and ``rd+1``)?                                               | 
  |                        |                      | A coprocessor must signal ``writeback`` as 0 for non-accepted instructions.                                      | 
  +------------------------+----------------------+------------------------------------------------------------------------------------------------------------------+ 
  | ``loadstore``          | logic                | Is the offloaded instruction a load/store instruction?                                                           | 
  |                        |                      | A coprocessor must signal ``loadstore`` as 0 for non-accepted instructions. (Only) if an instruction is          | 
  |                        |                      | accepted with ``loadstore`` is 1 and the instruction is not killed, then the coprocessor must perform one or     | 
  |                        |                      | more transactions via the memory group interface.                                                                | 
  +------------------------+----------------------+------------------------------------------------------------------------------------------------------------------+ 
  | ``exc``                | logic                | Can the offloaded instruction possibly cause a synchronous exception?                                            | 
  |                        |                      | A coprocessor must signal ``exc`` as 0 for non-accepted instructions.                                            | 
  +------------------------+----------------------+------------------------------------------------------------------------------------------------------------------+ 

The core will attempt to offload instructions via the issue interface for the following two scenarios:

* The instruction is originally non-compressed and it is not recognized as a valid instruction by the core's non-compressed instruction decoder.
* The instruction is originally compressed and the coprocessor accepted the compressed instruction and provided a 32-bit uncompressed instruction.
  In this case the 32-bit uncompressed instruction will be attempted for offload even if it matches in the core's non-compressed instruction decoder.

A coprocessor can (only) accept an offloaded instruction when:

* It can handle the instruction (based on decoding ``instr``).
* The required source registers are marked valid by the offloading core  (``x_issue_valid_o`` is 1 and required bit(s) ``rs_valid`` are 1).

A transaction is considered offloaded/accepted on the positive edge of ``clk_i`` when ``x_issue_valid_o``, ``x_issue_ready_i`` and ``accept`` are aserted.
A transaction is considered rejected on the positive edge of ``clk_i`` when ``x_issue_valid_o`` and ``x_issue_ready_i`` are asserted while ``accept`` is deaserted.

The signals in ``x_issue_resp_i`` are valid when ``x_issue_req_o`` and ``x_issue_resp_i`` are both 1. There are no stability requirements.

:numref:`Commit interface signals` describes the commit interface signals.

.. table:: Commit interface signals
  :name: Commit interface signals

  +---------------------------+-----------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | **Signal**                | **Type**        | **Direction**   | **Description**                                                                                                              |
  +---------------------------+-----------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``x_commit_valid_o``      | logic           | output          | Commit request valid. Indicates that |corev| has valid commit or kill information for an offloaded instruction.              |
  |                           |                 |                 | There is no corresponding ready signal (it is implicit and assumed 1). The coprocessor must be ready                         |
  |                           |                 |                 | to observe the ``x_commit_valid_o`` and ``x_commit_kill`` signals at any time coincident or after an issue transaction       |
  |                           |                 |                 | initiation.                                                                                                                  |
  +---------------------------+-----------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``x_commit_o``            | x_commit_t      | output          | Commit packet.                                                                                                               |
  +---------------------------+-----------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+

:numref:`Commit packet type` describes the ``x_commit_t`` type.

.. table:: Commit packet type
  :name: Commit packet type

  +---------------------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``id``                    | logic [3:0]     | Identification of the offloaded instruction. Valid when ``x_commit_valid_o`` is 1.                                           |
  +---------------------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``x_commit_kill``         | logic           | Shall an offloaded instruction be killed? If ``x_commit_valid_o`` is 1 and ``x_commit_kill`` is 0, then the core guarantees  |
  |                           |                 | that the offloaded instruction (``id``) is no longer speculative, will not get killed (e.g. due to misspeculation or an      |
  |                           |                 | exception in a preceding instruction), and is allowed to be committed. If ``x_commit_valid_o`` is 1 and ``x_commit_kill`` is |
  |                           |                 | 1, then the offloaded instruction (``id``) shall be killed in the coprocessor and the coprocessor must guarantee that the    |
  |                           |                 | related instruction does/did not change architectural state.                                                                 |
  +---------------------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+

The ``x_commit_valid_o`` signal will be 1 exactly one ``clk_i`` cycle for every offloaded instruction by the coprocessor (whether accepted or not). The ``id`` value indicates which offloaded
instruction is allowed to be committed or is supposed to be killed. The ``id`` values of subsequent commit transactions will increment (and wrap around)

For each offloaded and accepted instruction the core is guaranteed to (eventually) signal that such an instruction is either no longer speculative and can be committed (``x_commit_valid_o`` is 1
and ``x_commit_kill`` is 0) or that the instruction must be killed (``x_commit_valid_o`` is 1 and ``x_commit_kill`` is 1). 

A coprocessor does not have to wait for ``x_commit_valid_o`` to
become asserted. It can speculate that an offloaded accepted instruction will not get killed, but in case this speculation turns out to be wrong because the instruction actually did get killed,
then the coprocessor must undo any of its internal architectural state changes that are due to the killed instruction. 

A coprocessor is allowed to perform speculative memory request transactions, but then must be aware that |corev| can signal a failure for speculative memory request transactions to
certain memory regions. A coprocessor shall never perform memory request transactions for instructions that have already been killed at least a ``clk_i`` cycle earlier.

A coprocessor is not allowed to perform speculative result transactions. A coprocessor shall never perform result  transactions for instructions that have already been killed at least a ``clk_i`` cycle earlier.

The signals in ``x_commit_o`` are valid when ``x_commit_valid_o`` is 1.

:numref:`Memory (request/response) interface signals` describes the memory (request/response) interface signals.

.. table:: Memory (request/response) interface signals
  :name: Memory (request/response) interface signals

  +---------------------------+-----------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | **Signal**                | **Type**        | **Direction**   | **Description**                                                                                                              |
  +---------------------------+-----------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``x_mem_valid_i``         | logic           | input           | Memory (request/response) valid. Indicates that the coprocessor wants to perform a memory transaction for an                 |
  |                           |                 |                 | offloaded instruction.                                                                                                       |
  +---------------------------+-----------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``x_mem_ready_o``         | logic           | output          | Memory (request/response) ready. The memory (request/response) signaled via ``x_mem_req_i`` is accepted by |corev| when      |
  |                           |                 |                 | ``x_mem_valid_i`` and  ``x_mem_ready_o`` are both 1.                                                                         |
  +---------------------------+-----------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``x_mem_req_i``           | x_mem_req_t     | input           | Memory request packet.                                                                                                       |
  +---------------------------+-----------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``x_mem_resp_o``          | x_mem_resp_t    | output          | Memory response packet. Response to memory request (e.g. PMA check response). Note that this is not the memory result.       |
  +---------------------------+-----------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+

:numref:`Memory request type` describes the ``x_mem_req_t`` type.

.. table:: Memory request type
  :name: Memory request type

  +------------------------+------------------+-----------------------------------------------------------------------------------------------------------------+
  | **Signal**             | **Type**         | **Description**                                                                                                 |
  +------------------------+------------------+-----------------------------------------------------------------------------------------------------------------+
  | ``id``                 | [3:0]            | Identification of the offloaded instruction.                                                                    |
  +------------------------+------------------+-----------------------------------------------------------------------------------------------------------------+
  | ``addr``               | logic [31:0]     | Virtual address of the memory transaction.                                                                      |
  +------------------------+------------------+-----------------------------------------------------------------------------------------------------------------+
  | ``we``                 | logic            | Write enable of the memory transaction.                                                                         |
  +------------------------+------------------+-----------------------------------------------------------------------------------------------------------------+
  | ``size``               | logic [1:0]      | Size of the memory transaction. 0: byte, 1: halfword, 2: word.                                                  |
  +------------------------+------------------+-----------------------------------------------------------------------------------------------------------------+
  | ``wdata``              | logic [31:0]     | Write data of a store memory transaction.                                                                       |
  +------------------------+------------------+-----------------------------------------------------------------------------------------------------------------+
  | ``last``               | logic            | Is this the last memory transaction for the offloaded instruction?                                              |
  +------------------------+------------------+-----------------------------------------------------------------------------------------------------------------+
  | ``spec``               | logic            | Is the memory transaction speculative?                                                                          |
  +------------------------+------------------+-----------------------------------------------------------------------------------------------------------------+

The memory request interface can be used by the coprocessor to initiate data side memory read or memory write transactions. All memory transactions, no matter if
they are initiated by |corev| itself or by a coprocessor via the memory request interface, are treated equally. Specifically this equal treatment applies to:

* PMA checks
* PMA attribution
* Misaligned load/store handling (i.e. halfword or word accesses that cross a word boundary are split into two bus transactions)
* Write buffer usage

As for non-offloaded load or store instructions it is assumed that execute permission is never required for offloaded load or store instructions. |corev| itself
never speculates load or store transactions. If desired a coprocessor can avoid performing speculative loads or stores (as indicated by ``spec`` is 1) as well
by waiting for the commit interface to signal that the offloaded instruction is no longer speculative before issuing the memory request.

A memory request transaction is defined as the combination of all ``x_mem_req_i`` signals during which ``x_mem_valid_i`` is 1 and the ``id`` remains unchanged. I.e. a new
transaction can be started by just changing the ``id`` signal and keeping the valid signal asserted.

The signals in ``x_mem_req_i`` are valid when ``x_mem_valid_i`` is 1. These signals remain stable during a memory request transaction. ``wdata`` is only required to remain
stable during memory request transactions in which ``we`` is 1.

:numref:`Memory request type` describes the ``x_mem_resp_t`` type.

.. table:: Memory response type
  :name: Memory response type

  +------------------------+------------------+-----------------------------------------------------------------------------------------------------------------+
  | **Signal**             | **Type**         | **Description**                                                                                                 |
  +------------------------+------------------+-----------------------------------------------------------------------------------------------------------------+
  | ``exc``                | logic            | Did the memory request cause a synchronous exception?                                                           |
  +------------------------+------------------+-----------------------------------------------------------------------------------------------------------------+
  | ``exccode``            | logic [5:0]      | Excecption code.                                                                                                |
  +------------------------+------------------+-----------------------------------------------------------------------------------------------------------------+

The ``exc`` is used to signal synchronous exceptions resulting from the memory request transaction defined in ``x_mem_req_i``. In case of a synchronous exception
no corresponding transaction will be performed over the memory result (``x_mem_result_valid_o``) interface. |corev| can for example signal a synchronous exception
in case of a PMP fault. A synchronous exception will lead to a trap in |corev| unless the corresponding instruction is killed.

The signals in ``x_mem_resp_o`` are valid when ``x_mem_valid_i`` and  ``x_mem_ready_o`` are both 1. There are no stability requirements.

:numref:`Memory result interface signals` describes the memory result interface signals.

.. table:: Memory result interface signals
  :name: Memory result interface signals

  +---------------------------+-----------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | **Signal**                | **Type**        | **Direction**   | **Description**                                                                                                              |
  +---------------------------+-----------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``x_mem_result_valid_o``  | logic           | output          | Memory result valid. Indicates that |corev| has a valid memory result for the corresponding memory request.                  |
  |                           |                 |                 | There is no corresponding ready signal (it is implicit and assumed 1). The coprocessor must be ready to accept               |
  |                           |                 |                 | ``x_mem_result_o`` whenever ``x_mem_result_valid_o`` is 1.                                                                   |
  +---------------------------+-----------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``x_mem_result_o``        | x_mem_result_t  | output          | Memory result packet.                                                                                                        |
  +---------------------------+-----------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+

:numref:`Memory result type` describes the ``x_mem_result_t`` type.

.. table:: Memory result type
  :name: Memory result type

  +------------------------+------------------+-----------------------------------------------------------------------------------------------------------------+
  | **Signal**             | **Type**         | **Description**                                                                                                 |
  +------------------------+------------------+-----------------------------------------------------------------------------------------------------------------+
  | ``id``                 | [3:0]            | Identification of the offloaded instruction.                                                                    |
  +------------------------+------------------+-----------------------------------------------------------------------------------------------------------------+
  | ``rdata``              | logic [31:0]     | Read data of a read memory transaction. Only used for reads.                                                    |
  +------------------------+------------------+-----------------------------------------------------------------------------------------------------------------+
  | ``err``                | logic            | Did the instruction cause a bus error?                                                                          |
  +------------------------+------------------+-----------------------------------------------------------------------------------------------------------------+

The memory result interface is used to provide a result from |corev| to the coprocessor for every memory transaction (i.e. for both read and write transactions).
No memory result transaction is performed for instructions that led to a synchronous exception as signaled via the memory (request/response) interface. If a
memory (request/response) transaction was not killed, then the corresponding memory result transaction will not be killed either.
Memory result transactions are provided by the core in the same order (with matching ``id``) as the memory (request/response) transactions are received. The ``err`` signal
signals whether a bus error occurred. If so, then an NMI is signaled, just like for bus errors caused by non-offloaded loads and stores. 

The signals in ``x_mem_result_o`` are valid when ``x_mem_result_valid_o`` is 1.

:numref:`Result interface signals` describes the result interface signals.

.. table:: Result interface signals
  :name: Result interface signals

  +---------------------------+-----------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | **Signal**                | **Type**        | **Direction**   | **Description**                                                                                                              |
  +---------------------------+-----------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``x_result_valid_i``      | logic           | input           | Result request valid. Indicates that the coprocessor has a valid result (write data or exception) for an offloaded           |
  |                           |                 |                 | instruction.                                                                                                                 |
  +---------------------------+-----------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``x_result_ready_o``      | logic           | output          | Result request ready. The result signaled via ``x_result_i`` is accepted by the core when                                    |
  |                           |                 |                 | ``x_result_valid_i`` and  ``x_result_ready_o`` are both 1.                                                                   |
  +---------------------------+-----------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+
  | ``x_result_i``            | x_result_t      | input           | Result packet.                                                                                                               |
  +---------------------------+-----------------+-----------------+------------------------------------------------------------------------------------------------------------------------------+

The coprocessor shall provide results to the core via the result interface in the same order as it received and accepted issue transactions. Each accepted offloaded (and not killed) instruction shall
have exactly one result group transaction (even if no data needs to be written back to the core's register file).

:numref:`Result packet type` describes the ``x_result_t`` type.

.. table:: Result packet type
  :name: Result packet type

  +------------------------+------------------+-----------------------------------------------------------------------------------------------------------------+
  | **Signal**             | **Type**         | **Description**                                                                                                 |
  +------------------------+------------------+-----------------------------------------------------------------------------------------------------------------+
  | ``id``                 | [3:0]            | Identification of the offloaded instruction.                                                                    |
  +------------------------+------------------+-----------------------------------------------------------------------------------------------------------------+
  | ``data[X_NUM_WB-1:0]`` | logic [31:0]     | Register file write data value(s).                                                                              |
  +------------------------+------------------+-----------------------------------------------------------------------------------------------------------------+
  | ``rd[X_NUM_WB-1:0]``   | logic [4:0]      | Register file destination address(es).                                                                          |
  +------------------------+------------------+-----------------------------------------------------------------------------------------------------------------+
  | ``we[X_NUM_WB-1:0]``   | logic            | Register file write enable(s).                                                                                  |
  +------------------------+------------------+-----------------------------------------------------------------------------------------------------------------+
  | ``exc``                | logic            | Did the instruction cause a synchronous exception?                                                              |
  +------------------------+------------------+-----------------------------------------------------------------------------------------------------------------+
  | ``exccode``            | logic [5:0]      | Excecption code.                                                                                                |
  +------------------------+------------------+-----------------------------------------------------------------------------------------------------------------+

A result transaction is defined as the combination of all ``x_result_i`` signals during which ``x_result_valid_i`` is 1 and the ``id`` remains unchanged. I.e. a new
transaction can be started by just changing the ``id`` signal and keeping the valid signal asserted.

The signals in ``x_result_i`` are valid when ``x_result_valid_i`` is 1. These signals remain stable during a result transaction.

Interface dependencies
----------------------

The following rules apply to the relative ordering of the interface handshakes:

* The compressed interface transactions are in program order (but instructions that are considered valid in the core itself are not attempted for offload).
* Every accepted compressed interface transaction has an associated issue interface transaction (but not the other way around) and both interfaces use a matching transaction ordering.
* The issue interface transactions are in program order (but instructions that are considered valid in the core itself are not attempted for offload).
* Every issue interface transaction has an associated commit interface transaction and both interfaces use a matching transaction ordering.
* If an offloaded instruction is accepted as a ``loadstore`` instruction and not killed, then for each such instruction one or more memory transaction must occur
  via the memory interface. The transaction ordering on the memory interface interface must correspond to the transaction ordering on the issue interface.
* If an offloaded instruction is accepted and not killed, then for each such instruction one result transaction must occur via the result interface (even
  if no writeback needs to happen to the core's register file). The transaction ordering on the result interface must correspond to the transaction ordering
  on the issue interface.
* A commit interface handshake cannot be initiated before the corresponding issue interface handshake is initiated.
* A memory (request/response) interface handshake cannot be initiated before the corresponding issue interface handshake is initiated.
* A memory result interface handshake cannot be initiated before the corresponding memory request interface handshake is completed.
* A result interface handshake cannot be initiated before the corresponding issue interface handshake is initiated.
* A memory (request/response) interface handshake cannot be initiated for instructions that were killed in an earlier cycle.
* A memory result interface handshake cannot be initiated for instructions that were killed in an earlier cycle.
* A result interface handshake cannot be (or have been) initiated for killed instructions.

Handshake rules
---------------

The following handshake pairs exist on the eXtension interface:

* ``x_compressed_valid_o`` with``x_compressed_ready_i``.
* ``x_issue_valid_o`` with``x_issue_ready_i``.
* ``x_commit_valid_o`` with implicit always ready signal.
* ``x_mem_valid_i`` with ``x_mem_ready_o``.
* ``x_mem_result_valid_o`` with implicit always ready signal.
* ``x_result_valid_i`` with ``x_result_ready_o``.

The only rule related to valid and ready signals is that:

* A transaction is considered accepted on the positive ``clk_i`` edge when both valid and (implicit or explicit) ready are 1.

Specifically note the following:

* The valid signal is allowed to be retracted (e.g. in case that the related instruction is killed in the core's pipeline before the corresponding ready is signaled).
* A new transaction can be started by changing the ``id`` signal and keeping the valid signal asserted (thereby possibly terminating a previous transaction before it completed).
* The ready signal is allowed to be 1 when the corresponding valid signal is not asserted.

Signal dependencies
-------------------

|corev| does not have combinatorial paths from its eXtension interface input signals to its eXtension interface output signals. A coprocessor is allowed (and expected) to
have combinatorial paths from its eXtension interface input signals to its eXtension interface output signals.

.. note::

   The above implies that the non-compressed instruction ``instr[31:0]`` received via the compressed interface is not allowed
   to combinatorially feed into the issue interface's ``instr[31:0]`` instruction. In |corev| this is achieved by implementing
   the compressed decoder (including the uncompressed interface) in the fetch stage and by implementing the uncompressed
   decoder (including the issue interface) in the decode stage.

Major differences with respect to CV-X-IF v0.1 specification
------------------------------------------------------------

* Renamed accelerator to coprocessor
* Renamed parameters
* Replaced p_*, q_*, etc. with more logical names
* Limited scope to point-to-point core-coprocessor interface only (but added ``id`` so that interconnect can be build)
* Replaced TernaryOps and DualWriteback  by X_NUM_RS and X_NUM_WB parameters respectively and made result interface match register file interface more closely (data/rd/we).
* Removed concept of *asynchronous external* memory mode
* Removed concept of *probe* memory access mode
* Generalized *error* to *exc* and *exccode* (exceptions are no longer restricted to load/store instructions)
* Generalized *core_mem_pending* / *adapter_mem_pending*  into commit interface (kill/commit)
* Changed *fire-and-forget* option into mandatory result transaction (even if no writeback is performed)
* Made memory interface look more like OBI
* Removed *p_range*
* Removed *rd_clean* (WAW hazards are addressed by not allowing any out of order transactions on any interface)
* Required that all interfaces (also the result interface) perform transactions according to program order




