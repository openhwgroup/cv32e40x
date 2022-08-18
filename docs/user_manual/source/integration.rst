.. _core-integration:

Core Integration
================

The main module is named ``cv32e40x_core`` and can be found in ``cv32e40x_core.sv``.
Below, the instantiation template is given and the parameters and interfaces are described.

Instantiation Template
----------------------

.. code-block:: verilog

  cv32e40x_core #(
      .LIB                        (         0 ),
      .RV32                       (     RV32I ),
      .A_EXT                      (         0 ),
      .B_EXT                      (    B_NONE ),
      .M_EXT                      (         M ),
      .X_EXT                      (         0 ),
      .X_NUM_RS                   (         2 ),
      .X_ID_WIDTH                 (         4 ),
      .X_MEM_WIDTH                (        32 ),
      .X_RFR_WIDTH                (        32 ),
      .X_RFW_WIDTH                (        32 ),
      .X_MISA                     (     32'h0 ),
      .X_ECS_XS                   (      2'b0 ),
      .DBG_NUM_TRIGGERS           (         1 ),
      .NUM_MHPMCOUNTERS           (         1 ),
      .PMA_NUM_REGIONS            (         1 ),
      .PMA_CFG                    ( PMA_CFG[] ),
      .SMCLIC                     (         0 ),
      .SMCLIC_ID_WIDTH            (         5 )
  ) u_core (
      // Clock and reset
      .clk_i                    (),
      .rst_ni                   (),
      .scan_cg_en_i             (),

      // Configuration
      .boot_addr_i              (),
      .mtvec_addr_i             (),
      .dm_halt_addr_i           (),
      .dm_exception_addr_i      (),
      .mhartid_i                (),
      .mimpid_patch_i           (),

      // Instruction memory interface
      .instr_req_o              (),
      .instr_gnt_i              (),
      .instr_addr_o             (),
      .instr_memtype_o          (),
      .instr_prot_o             (),
      .instr_dbg_o              (),
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
      .data_dbg_o               (),
      .data_wdata_o             (),
      .data_we_o                (),
      .data_rvalid_i            (),
      .data_rdata_i             (),
      .data_err_i               (),
      .data_exokay_i            (),

      // Cycle, Time
      .mcycle_o                 (),
      .time_i                   (),

      // eXtension interface
      .xif_compressed_if        (),
      .xif_issue_if             (),
      .xif_commit_if            (),
      .xif_mem_if               (),
      .xif_mem_result_if        (),
      .xif_result_if            (),

       // Interrupt interface
      .irq_i                    (),

      .clic_irq_i               (),
      .clic_irq_id_i            (),
      .clic_irq_level_i         (),
      .clic_irq_priv_i          (),
      .clic_irq_shv_i           (),

      // Fencei flush handshake
      .fencei_flush_req_o       (),
      .fencei_flush_ack_i       (),

      // Debug interface
      .debug_req_i              (),
      .debug_havereset_o        (),
      .debug_running_o          (),
      .debug_halted_o           (),
      .debug_pc_valid_o         (),
      .debug_pc_o               (),

      // Special control signals
      .fetch_enable_i           (),
      .core_sleep_o             (),
      .wu_wfe_i                 ()
  );

Parameters
----------

.. note::
   All eXtension interface parameters (``X_NUM_RS``, ``X_ID_WIDTH``, ``X_MEM_WIDTH``, ``X_RFR_WIDTH`` and ``X_RFW_WIDTH``)
   must be set with values matching the actual ``if_xif`` instance and the coprocessor/interconnect available outside of |corev|.

.. table::
  :widths: 20 10 10 60
  :class: no-scrollbar-table

  +--------------------------------+----------------+---------------+--------------------------------------------------------------------+
  | Name                           | Type/Range     | Default       | Description                                                        |
  +================================+================+===============+====================================================================+
  | ``LIB``                        | int            | 0             | Standard cell library (semantics defined by integrator)            |
  +--------------------------------+----------------+---------------+--------------------------------------------------------------------+
  | ``RV32``                       | rv32_e         | RV32I         | Base Integer Instruction Set.                                      |
  |                                |                |               | ``RV32`` = RV32I: RV32I Base Integer Instruction Set.              |
  |                                |                |               | ``RV32`` = RV32E: RV32E Base Integer Instruction Set.              |
  +--------------------------------+----------------+---------------+--------------------------------------------------------------------+
  | ``A_EXT``                      | bit            | 0             | Enable Atomic Instruction (A) support  (**not implemented yet**)   |
  +--------------------------------+----------------+---------------+--------------------------------------------------------------------+
  | ``B_EXT``                      | b_ext_e        | B_NONE        | Enable Bit Manipulation support. ``B_EXT`` = B_NONE: No Bit        |
  |                                |                |               | Manipulation instructions are supported. ``B_EXT`` = ZBA_ZBB:      |
  |                                |                |               | Zba and Zbb are supported. ``B_EXT`` = ZBA_ZBB_ZBS: Zba, Zbb and   |
  |                                |                |               | Zbs are supported. ``B_EXT`` = ZBA_ZBB_ZBC_ZBS: Zba, Zbb, Zbc and  |
  |                                |                |               | Zbs are supported.                                                 |
  +--------------------------------+----------------+---------------+--------------------------------------------------------------------+
  | ``M_EXT``                      | m_ext_e        | M             | Enable Multiply / Divide support. ``M_EXT`` = M_NONE: No multiply /|
  |                                |                |               | divide instructions are supported. ``M_EXT`` = ZMMUL: The          |
  |                                |                |               | multiplication subset of the ``M`` extension is supported.         |
  |                                |                |               | ``M_EXT`` = M: The ``M`` extension is supported.                   |
  +--------------------------------+----------------+---------------+--------------------------------------------------------------------+
  | ``X_EXT``                      | bit            | 0             | Enable eXtension Interface (X) support, see :ref:`x_ext`           |
  +--------------------------------+----------------+---------------+--------------------------------------------------------------------+
  | ``X_NUM_RS``                   | int (2..3)     | 2             | Number of register file read ports that can be used by the         |
  |                                |                |               | eXtension interface.                                               |
  +--------------------------------+----------------+---------------+--------------------------------------------------------------------+
  | ``X_ID_WIDTH``                 | int (3..32)    | 4             | Identification width for the eXtension interface.                  |
  +--------------------------------+----------------+---------------+--------------------------------------------------------------------+
  | ``X_MEM_WIDTH``                | int (32 64,    | 32            | Memory access width for loads/stores via the eXtension interface.  |
  |                                | 128, 256)      |               |                                                                    |
  +--------------------------------+----------------+---------------+--------------------------------------------------------------------+
  | ``X_RFR_WIDTH``                | int (32, 64)   | 32            | Register file read access width for the eXtension interface.       |
  +--------------------------------+----------------+---------------+--------------------------------------------------------------------+
  | ``X_RFW_WIDTH``                | int (32, 64)   | 32            | Register file write access width for the eXtension interface.      |
  +--------------------------------+----------------+---------------+--------------------------------------------------------------------+
  | ``X_MISA``                     | logic [31:0]   | 32'h0         | MISA extensions implemented on the eXtension interface,            |
  |                                |                |               | see :ref:`csr-misa`. X_MISA can only be used to set a subset of    |
  |                                |                |               | the following: {P, V, F, M}.                                       |
  +--------------------------------+----------------+---------------+--------------------------------------------------------------------+
  | ``X_ECS_XS``                   | logic [1:0]    | 2'b0          | Default value for ``mstatus.XS`` if X_EXT = 1,                     |
  |                                |                |               | see :ref:`csr-mstatus`.                                            |
  +--------------------------------+----------------+---------------+--------------------------------------------------------------------+
  | ``NUM_MHPMCOUNTERS``           | int (0..29)    | 1             | Number of MHPMCOUNTER performance counters, see                    |
  |                                |                |               | :ref:`performance-counters`                                        |
  +--------------------------------+----------------+---------------+--------------------------------------------------------------------+
  | ``DBG_NUM_TRIGGERS``           | int (0..4 )    | 1             | Number of debug triggers, see :ref:`debug-support`                 |
  +--------------------------------+----------------+---------------+--------------------------------------------------------------------+
  | ``PMA_NUM_REGIONS``            | int (0..16)    | 0             | Number of PMA regions                                              |
  +--------------------------------+----------------+---------------+--------------------------------------------------------------------+
  | ``PMA_CFG[]``                  | pma_cfg_t      | PMA_R_DEFAULT | PMA configuration.                                                 |
  |                                |                |               | Array of pma_cfg_t with PMA_NUM_REGIONS entries, see :ref:`pma`    |
  +--------------------------------+----------------+---------------+--------------------------------------------------------------------+
  | ``SMCLIC``                     | int (0..1 )    | 0             | Is Smclic supported?                                               |
  +--------------------------------+----------------+---------------+--------------------------------------------------------------------+
  | ``SMCLIC_ID_WIDTH``            | int (1..10 )   | 5             | Width of ``clic_irq_id_i`` and ``clic_irq_id_o``. The maximum      |
  |                                |                |               | number of supported interrupts in CLIC mode is                     |
  |                                |                |               | ``2^SMCLIC_ID_WIDTH``. Trap vector table alignment is restricted   |
  |                                |                |               | as described in :ref:`csr-mtvt`.                                   |
  +--------------------------------+----------------+---------------+--------------------------------------------------------------------+

Interfaces
----------

.. table::
  :widths: 20 10 10 60
  :class: no-scrollbar-table

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
  |                         |                         |     | reset = ``boot_addr_i``. Must be           |
  |                         |                         |     | word aligned. Do not change after enabling |
  |                         |                         |     | core via ``fetch_enable_i``                |
  +-------------------------+-------------------------+-----+--------------------------------------------+
  | ``mtvec_addr_i``        | 32                      | in  | ``mtvec`` address. Initial value for the   |
  |                         |                         |     | address part of :ref:`csr-mtvec`.          |
  |                         |                         |     | Must be 128-byte aligned                   |
  |                         |                         |     | (i.e. ``mtvec_addr_i[6:0]`` = 0).          |
  |                         |                         |     | Do not change after enabling core          |
  |                         |                         |     | via ``fetch_enable_i``                     |
  +-------------------------+-------------------------+-----+--------------------------------------------+
  | ``dm_halt_addr_i``      | 32                      | in  | Address to jump to when entering Debug     |
  |                         |                         |     | Mode, see :ref:`debug-support`. Must be    |
  |                         |                         |     | word aligned. Do not change after enabling |
  |                         |                         |     | core via ``fetch_enable_i``                |
  +-------------------------+-------------------------+-----+--------------------------------------------+
  | ``dm_exception_addr_i`` | 32                      | in  | Address to jump to when an exception       |
  |                         |                         |     | occurs when executing code during Debug    |
  |                         |                         |     | Mode, see :ref:`debug-support`. Must be    |
  |                         |                         |     | word aligned. Do not change after enabling |
  |                         |                         |     | core via ``fetch_enable_i``                |
  +-------------------------+-------------------------+-----+--------------------------------------------+
  | ``mhartid_i``           | 32                      | in  | Hart ID, usually static, can be read from  |
  |                         |                         |     | :ref:`csr-mhartid` CSR                     |
  +-------------------------+-------------------------+-----+--------------------------------------------+
  | ``mimpid_patch_i``      | 4                       | in  | Implementation ID patch. Must be static.   |
  |                         |                         |     | Readable as part of :ref:`csr-mimpid` CSR. |
  +-------------------------+-------------------------+-----+--------------------------------------------+
  | ``instr_*``             | Instruction fetch interface, see :ref:`instruction-fetch`                  |
  +-------------------------+----------------------------------------------------------------------------+
  | ``data_*``              | Load-store unit interface, see :ref:`load-store-unit`                      |
  +-------------------------+----------------------------------------------------------------------------+
  | ``mcycle_o``            | Cycle Counter Output                                                       |
  +-------------------------+----------------------------------------------------------------------------+
  | ``time_i``              | Time input, see :ref:`csr-time` CSR and :ref:`csr-timeh` CSR               |
  +-------------------------+----------------------------------------------------------------------------+
  | ``irq_*``               | Interrupt inputs, see :ref:`exceptions-interrupts`                         |
  +-------------------------+----------------------------------------------------------------------------+
  | ``clic_*_i``            | CLIC interface, see :ref:`exceptions-interrupts`                           |
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
  | ``wu_wfe_i``            | 1                       | in  | Wake-up for ``wfe``, see :ref:`sleep_unit`.|
  +-------------------------+-------------------------+-----+--------------------------------------------+
  | ``xif_compressed_if``   | eXtension compressed interface, see :ref:`x_compressed_if`                 |
  +-------------------------+----------------------------------------------------------------------------+
  | ``xif_issue_if``        | eXtension issue interface, see :ref:`x_issue_if`                           |
  +-------------------------+----------------------------------------------------------------------------+
  | ``xif_commit_if``       | eXtension commit interface, see :ref:`x_commit_if`                         |
  +-------------------------+----------------------------------------------------------------------------+
  | ``xif_mem_if``          | eXtension memory interface, see :ref:`x_mem_if`                            |
  +-------------------------+----------------------------------------------------------------------------+
  | ``xif_mem_result_if``   | eXtension memory result interface, see :ref:`x_mem_result_if`              |
  +-------------------------+----------------------------------------------------------------------------+
  | ``xif_result_if``       | eXtension result interface, see :ref:`x_result_if`                         |
  +-------------------------+----------------------------------------------------------------------------+

