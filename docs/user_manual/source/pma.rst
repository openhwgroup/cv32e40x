.. _pma:

Physical Memory Attribution (PMA)
=================================
The |corev| includes a Physical Memory Attribution (PMA) unit that allows compile time attribution of the physical memory map.
The PMA is configured through the top level parameters ``PMA_NUM_REGIONS`` and ``PMA_CFG[]``.
The configuration array, ``PMA_CFG[]``, must consist of ``PMA_NUM_REGIONS`` entries of the type ``pma_region_t``, defined in ``cv32e40x_pkg.sv``:

.. code-block:: verilog

  typedef struct packed {
    logic [31:0] word_addr_low;
    logic [31:0] word_addr_high;
    logic        main;
    logic        bufferable;
    logic        cacheable;
    logic        atomic;
  } pma_region_t;

In case of address overlap between PMA regions, the region with the lowest index in ``PMA_CFG[]`` will have priority.

Address range
~~~~~~~~~~~~~
The address boundaries of a PMA region are set in ``word_addr_low/word_addr_high``. These contain bits 33:2 of 34-bit, word aligned addresses. To get an address match, the transfer address ``addr`` must be in the range ``word_addr_low <= addr < word_addr_high``.

Main memory vs I/O
~~~~~~~~~~~~~~~~~~
Memory ranges can be defined as either main (``main=1``) or I/O (``main=0``). 
Code execution is allowed from main memory and main memory is considered to be idempotent. Non-aligned transactions are supported in main memory.
Code execution is not allowed from I/O regions and an instruction access fault is raised when attempting to execute from such regions. 
I/O regions are considered to be non-idempotent and therefore the PMA will prevent speculative accesses to such regions.
Non-aligned transactions are not supported in I/O regions.

Bufferable and Cacheable
~~~~~~~~~~~~~~~~~~~~~~~~
Accesses to regions marked as bufferable (``bufferable=1``) will result in the OBI prot[2] bit being set.
Accesses to regions marked as cacheable (``cacheable=1``) will result in the OBI prot[3] bit being set.

Atomic operations
~~~~~~~~~~~~~~~~~
Regions supporting atomic operations can be defined by setting ``atomic=1``.
An attempt to perform a Load-Reserved to a region in which Atomic operations are not allowed will cause a precise load access fault.
An attempt to perform a Store-Conditional or Atomic Memory Operation (AMO) to a region in which Atomic operations are not allowed will cause a precise store/AMO access fault.
Note that the ``atomic`` attribute is only used when the RV32A extension is included.

Every instruction fetch, load and store will be subject to PMA checks and failed checks will result in an exception. PMA checks cannot be disabled.
See :ref:`exceptions-interrupts` for details.
