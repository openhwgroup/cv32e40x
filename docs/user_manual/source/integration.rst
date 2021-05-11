.. _core-integration:

Core Integration
================

The main module is named ``cv32e40x_core`` and can be found in ``cv32e40x_core.sv``.
Below, the instantiation template is given and the parameters and interfaces are described.

Instantiation Template
----------------------

.. code-block:: verilog

  cv32e40x_core #(
      .LIB                      (         0 ),
      .A_EXT                    (         0 ),
      .B_EXT                    (         0 ),
      .P_EXT                    (         0 ),
      .X_EXT                    (         0 ),
      .NUM_MHPMCOUNTERS         (         1 ),
      .PMA_NUM_REGIONS          (         1 ),
      .PMA_CFG                  ( PMA_CFG[] )
  ) u_core (
      // Clock and reset
      .clk_i                    (),
      .rst_ni                   (),
      .scan_cg_en_i             (),

      // Configuration
      .boot_addr_i              (),
      .mtvec_addr_i             (),
      .nmi_addr_i               (),
      .dm_halt_addr_i           (),
      .dm_exception_addr_i      (),
      .hart_id_i                (),

      // Instruction memory interface
      .instr_req_o              (),
      .instr_gnt_i              (),
      .instr_addr_o             (),
      .instr_memtype_o          (),
      .instr_prot_o             (),
      .instr_rvalid_i           (),
      .instr_rdata_i            (),
      .instr_err_i              (),

      // Data memory interface
      .data_req_o               (),
      .data_gnt_i               (),
      .data_addr_o              (),
      .data_atop_o              (),
      .data_be_o                (),
      .data_memtype_o           (),
      .data_prot_o              (),
      .data_wdata_o             (),
      .data_we_o                (),
      .data_rvalid_i            (),
      .data_rdata_i             (),
      .data_err_i               (),
      .data_exokay_i            (),

       // Interrupt interface
      .irq_i                    (),
      .irq_ack_o                (),
      .irq_id_o                 (),

      // Fencei flush handshake
      .fencei_flush_req_o       (),
      .fencei_flush_ack_i       (),

      // Debug interface
      .debug_req_i              (),
      .debug_havereset_o        (),
      .debug_running_o          (),
      .debug_halted_o           (),

      // Special control signals
      .fetch_enable_i           (),
      .core_sleep_o             ()
  );

Parameters
----------

.. note::
   The non-default (i.e. non-zero) settings of ``FPU`` have not been verified yet.

+------------------------------+----------------+---------------+--------------------------------------------------------------------+
| Name                         | Type/Range     | Default       | Description                                                        |
+==============================+================+===============+====================================================================+
| ``LIB``                      | int            | 0             | Standard cell library (semantics defined by integrator)            |
+------------------------------+----------------+---------------+--------------------------------------------------------------------+
| ``A_EXT``                    | bit            | 0             | Enable Atomic Instruction (A) support  (**not implemented yet**)   |
+------------------------------+----------------+---------------+--------------------------------------------------------------------+
| ``B_EXT``                    | bit            | 0             | Enable Bit Manipulation (B) support  (**not implemented yet**)     |
+------------------------------+----------------+---------------+--------------------------------------------------------------------+
| ``P_EXT``                    | bit            | 0             | Enable Packed-SIMD (P) support (**not implemented yet**)           |
+------------------------------+----------------+---------------+--------------------------------------------------------------------+
| ``X_EXT``                    | bit            | 0             | Enable eXtension Interface (X) support, see :ref:`x_ext`           |
+------------------------------+----------------+---------------+--------------------------------------------------------------------+
| ``NUM_MHPMCOUNTERS``         | int (0..29)    | 1             | Number of MHPMCOUNTER performance counters, see                    |
|                              |                |               | :ref:`performance-counters`                                        |
+------------------------------+----------------+---------------+--------------------------------------------------------------------+
| ``PMA_NUM_REGIONS``          | int (0..16)    | 0             | Number of PMA regions                                              |
+------------------------------+----------------+---------------+--------------------------------------------------------------------+
| ``PMA_CFG[]``                | pma_region_t   | PMA_R_DEFAULT | PMA configuration.                                                 |
|                              |                |               | Array of pma_region_t with PMA_NUM_REGIONS entries, see :ref:`pma` |
+------------------------------+----------------+---------------+--------------------------------------------------------------------+

Interfaces
----------

+-------------------------+-------------------------+-----+--------------------------------------------+
| Signal(s)               | Width                   | Dir | Description                                |
+=========================+=========================+=====+============================================+
| ``clk_i``               | 1                       | in  | Clock signal                               |
+-------------------------+-------------------------+-----+--------------------------------------------+
| ``rst_ni``              | 1                       | in  | Active-low asynchronous reset              |
+-------------------------+-------------------------+-----+--------------------------------------------+
| ``scan_cg_en_i``        | 1                       | in  | Scan clock gate enable. Design for test    |
|                         |                         |     | (DfT) related signal. Can be used during   |
|                         |                         |     | scan testing operation to force            |
|                         |                         |     | instantiated clock gate(s) to be enabled.  |
|                         |                         |     | This signal should be 0 during normal /    |
|                         |                         |     | functional operation.                      |
+-------------------------+-------------------------+-----+--------------------------------------------+
| ``boot_addr_i``         | 32                      | in  | Boot address. First program counter after  |
|                         |                         |     | reset = ``boot_addr_i``. Must be half-word |
|                         |                         |     | aligned. Do not change after enabling core |
|                         |                         |     | via ``fetch_enable_i``                     |
+-------------------------+-------------------------+-----+--------------------------------------------+
| ``mtvec_addr_i``        | 32                      | in  | ``mtvec`` address. Initial value for the   |
|                         |                         |     | address part of :ref:`csr-mtvec`.          |
|                         |                         |     | Do not change after enabling core          |
|                         |                         |     | via ``fetch_enable_i``                     |
+-------------------------+-------------------------+-----+--------------------------------------------+
| ``nmi_addr_i``          | 32                      | in  | ``NMI`` address. Target address for NMIs.  |
|                         |                         |     | Must be half-word aligned.                 |
|                         |                         |     | Do not change after enabling core          |
|                         |                         |     | via ``fetch_enable_i``                     |
+-------------------------+-------------------------+-----+--------------------------------------------+
| ``dm_halt_addr_i``      | 32                      | in  | Address to jump to when entering Debug     |
|                         |                         |     | Mode, see :ref:`debug-support`. Must be    |
|                         |                         |     | word-aligned. Do not change after enabling |
|                         |                         |     | core via ``fetch_enable_i``                |
+-------------------------+-------------------------+-----+--------------------------------------------+
| ``dm_exception_addr_i`` | 32                      | in  | Address to jump to when an exception       |
|                         |                         |     | occurs when executing code during Debug    |
|                         |                         |     | Mode, see :ref:`debug-support`. Must be    |
|                         |                         |     | word-aligned. Do not change after enabling |
|                         |                         |     | core via ``fetch_enable_i``                |
+-------------------------+-------------------------+-----+--------------------------------------------+
| ``hart_id_i``           | 32                      | in  | Hart ID, usually static, can be read from  |
|                         |                         |     | :ref:`csr-mhartid` CSR                     |
+-------------------------+-------------------------+-----+--------------------------------------------+
| ``instr_*``             | Instruction fetch interface, see :ref:`instruction-fetch`                  |
+-------------------------+----------------------------------------------------------------------------+
| ``data_*``              | Load-store unit interface, see :ref:`load-store-unit`                      |
+-------------------------+----------------------------------------------------------------------------+
| ``irq_*``               | Interrupt inputs, see :ref:`exceptions-interrupts`                         |
+-------------------------+----------------------------------------------------------------------------+
| ``debug_*``             | Debug interface, see :ref:`debug-support`                                  |
+-------------------------+-------------------------+-----+--------------------------------------------+
| ``fetch_enable_i``      | 1                       | in  | Enable the instruction fetch of |corev|.   |
|                         |                         |     | The first instruction fetch after reset    |
|                         |                         |     | de-assertion will not happen as long as    |
|                         |                         |     | this signal is 0. ``fetch_enable_i`` needs |
|                         |                         |     | to be set to 1 for at least one cycle      |
|                         |                         |     | while not in reset to enable fetching.     |
|                         |                         |     | Once fetching has been enabled the value   |
|                         |                         |     | ``fetch_enable_i`` is ignored.             |
+-------------------------+-------------------------+-----+--------------------------------------------+
| ``core_sleep_o``        | 1                       | out | Core is sleeping, see :ref:`sleep_unit`.   |
+-------------------------+-------------------------+-----+--------------------------------------------+
