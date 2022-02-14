// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Sven Stucki - svstucki@student.ethz.ch                     //
//                                                                            //
// Additional contributions by:                                               //
//                 Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                 Andrea Bettati - andrea.bettati@studenti.unipr.it          //
//                 Øystein Knauserud - oystein.knauserud@silabs.com           //
//                                                                            //
// Design Name:    Control and Status Registers                               //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Control and Status Registers (CSRs) loosely following the  //
//                 RiscV draft priviledged instruction set spec (v1.9)        //
//                 Added Floating point support                               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_cs_registers import cv32e40x_pkg::*;
#(
  parameter bit          A_EXT            = 0,
  parameter m_ext_e      M_EXT            = M,
  parameter bit          X_EXT            = 0,
  parameter logic [31:0] X_MISA           =  32'h00000000,
  parameter logic [1:0]  X_ECS_XS         =  2'b00, // todo: implement related mstatus bitfields (but only if X_EXT = 1)
  parameter bit          ZC_EXT           = 0, // todo: remove parameter once fully implemented
  parameter bit          SMCLIC           = 0,
  parameter int          NUM_MHPMCOUNTERS = 1,
  parameter int          DBG_NUM_TRIGGERS = 1 // todo: implement support for DBG_NUM_TRIGGERS != 1
)
(
  // Clock and Reset
  input  logic            clk,
  input  logic            rst_n,

  // Hart ID
  input  logic [31:0]     mhartid_i,
  input  logic [31:0]     mimpid_i,
  output logic [23:0]     mtvec_addr_o,
  output logic  [1:0]     mtvec_mode_o,
  
  // Cycle Count
  output logic [MHPMCOUNTER_WIDTH-1:0] mcycle_o,

  // Used for mtvec address
  input  logic [31:0]     mtvec_addr_i,
  input  logic            csr_mtvec_init_i,

  // ID/EX pipeline 
  input id_ex_pipe_t      id_ex_pipe_i,

  // EX/WB pipeline
  input ex_wb_pipe_t      ex_wb_pipe_i,

  // From controller FSM
  input  ctrl_fsm_t       ctrl_fsm_i,

  // To controller bypass logic
  output logic            csr_counter_read_o,
 
  // Interface to registers (SRAM like)
  output logic [31:0]     csr_rdata_o,

  // To EX stage
  output logic            csr_illegal_o, // 1'b1 for illegal CSR access.

  // Interrupts
  output logic [31:0]     mie_o,
  input  logic [31:0]     mip_i,
  output logic            m_irq_enable_o,
  
  output logic [31:0]     mepc_o,

  // debug
  output logic [31:0]     dpc_o,
  output dcsr_t           dcsr_o,
  output logic            trigger_match_o,

  input  logic [31:0]     pc_if_i
);
  
  localparam logic [31:0] CORE_MISA =
  (32'(A_EXT)      <<  0)  // A - Atomic Instructions extension
| (32'(1)          <<  2)  // C - Compressed extension
| (32'(1)          <<  8)  // I - RV32I/64I/128I base ISA
| (32'(M_EXT == M) << 12)  // M - Integer Multiply/Divide extension
| (32'(0)          << 20)  // U - User mode implemented
| (32'(0)          << 23)  // X - Non-standard extensions present
| (32'(MXL)        << 30); // M-XLEN

  localparam logic [31:0] MISA_VALUE = CORE_MISA | (X_EXT ? X_MISA : 32'h0000_0000);

  // CSR update logic
  logic [31:0] csr_wdata_int;
  logic [31:0] csr_rdata_int;
  logic        csr_we_int;

  // Interrupt control signals
  logic [31:0] mepc_q, mepc_n;
  logic mepc_we;
  logic mepc_rd_error;

  // Trigger
  logic [15:0] tinfo_types;
  logic [31:0] tmatch_control_q, tmatch_control_n;
  logic [31:0] tmatch_value_q, tmatch_value_n;
  // Write enables
  logic tmatch_control_we;
  logic tmatch_value_we;
  logic tmatch_control_rd_error;
  logic tmatch_value_rd_error;
  // Debug
  dcsr_t       dcsr_q, dcsr_n;
  logic dcsr_we;
  logic dcsr_rd_error;
  logic [31:0] dcsr_rdata;
  logic [31:0] dpc_q, dpc_n;
  logic dpc_we;
  logic dpc_rd_error;

  logic [31:0] dscratch0_q, dscratch0_n;
  logic dscratch0_we, dscratch1_we;
  logic dscratch0_rd_error, dscratch1_rd_error;
  logic [31:0] dscratch1_q, dscratch1_n;

  logic [31:0] mscratch_q, mscratch_n;
  logic mscratch_we;
  logic mscratch_rd_error;

  jvt_t        jvt_q, jvt_n;
  logic        jvt_we, jvt_rd_error;

  mstatus_t mstatus_q, mstatus_n;
  logic mstatus_we;
  logic mstatus_rd_error;

  mcause_t mcause_q, mcause_n;
  logic mcause_we;
  logic mcause_rd_error;

  mtvec_t mtvec_n, mtvec_q;
  logic mtvec_we;
  logic mtvec_rd_error;

  mtvt_t       mtvt_n, mtvt_q;
  logic        mtvt_we, mtvt_rd_error;

  logic [31:0] mnxti_q, mnxti_n;
  logic        mnxti_we;

  mintstatus_t mintstatus_q, mintstatus_n;
  logic        mintstatus_we, mintstatus_rd_error;

  logic [31:0] mintthresh_q, mintthresh_n;
  logic        mintthresh_we, mintthresh_rd_error;

  logic [31:0] mscratchcsw_q, mscratchcsw_n;
  logic        mscratchcsw_we;

  logic [31:0] mscratchcswl_q, mscratchcswl_n;
  logic        mscratchcswl_we;

  logic [31:0] mclicbase_q, mclicbase_n;
  logic        mclicbase_we;

  logic [31:0] mip;                     // Bits are masked according to IRQ_MASK
  logic [31:0] mie_q, mie_n;            // Bits are masked according to IRQ_MASK
  logic mie_we;
  logic mie_rd_error;

  // Performance Counter Signals
  logic [31:0] [MHPMCOUNTER_WIDTH-1:0] mhpmcounter_q;                    // performance counters
  logic [31:0] [MHPMCOUNTER_WIDTH-1:0] mhpmcounter_n;                    // performance counters next value
  logic [31:0] [1:0]                   mhpmcounter_we;                   // performance counters write enable
  logic [31:0] [31:0]                  mhpmevent_q, mhpmevent_n;         // event enable
  logic [31:0]                         mcountinhibit_q, mcountinhibit_n; // performance counter enable
  logic [NUM_HPM_EVENTS-1:0]           hpm_events;                       // events for performance counters
  logic [31:0] [MHPMCOUNTER_WIDTH-1:0] mhpmcounter_increment;            // increment of mhpmcounter_q
  logic [31:0]                         mhpmcounter_write_lower;          // write 32 lower bits of mhpmcounter_q
  logic [31:0]                         mhpmcounter_write_upper;          // write 32 upper bits mhpmcounter_q
  logic [31:0]                         mhpmcounter_write_increment;      // write increment of mhpmcounter_q

  // Local instr_valid
  logic instr_valid;

  csr_opcode_e csr_op;
  csr_num_e    csr_waddr;
  csr_num_e    csr_raddr;
  logic [31:0] csr_wdata;
  logic        csr_en_gated;

  logic illegal_csr_read;  // Current CSR cannot be read
  logic illegal_csr_write; // Current CSR cannot be written

  // Local instr_valid for write portion (WB)
  assign instr_valid = ex_wb_pipe_i.instr_valid && !ctrl_fsm_i.kill_wb && !ctrl_fsm_i.halt_wb;

  // CSR access. Read in EX, write in WB
  // Setting csr_raddr to zero in case of unused csr to save power (alu_operand_b toggles a lot)
  assign csr_raddr = csr_num_e'((id_ex_pipe_i.csr_en && id_ex_pipe_i.instr_valid) ? id_ex_pipe_i.alu_operand_b[11:0] : 12'b0);

  // Not suppressing csr_waddr to zero when unused since its source are dedicated flipflops and would not save power as for raddr
  assign csr_waddr = csr_num_e'(ex_wb_pipe_i.csr_addr);
  assign csr_wdata = ex_wb_pipe_i.csr_wdata;

  assign csr_op    =  ex_wb_pipe_i.csr_op;

  // CSR write operations in WB, actual csr_we_int may still become 1'b0 in case of CSR_OP_READ
  assign csr_en_gated    = ex_wb_pipe_i.csr_en && instr_valid;
    
  // mip CSR
  assign mip = mip_i;

  ////////////////////////////////////////
  // Determine if CSR access is illegal //
  // Both read and write validity is    //
  // checked in the first (EX) stage    //
  // Invalid writes will suppress ex_wb //
  // signals and avoid writing in WB    //
  ////////////////////////////////////////
  assign illegal_csr_write = (id_ex_pipe_i.csr_op != CSR_OP_READ) &&
                             (id_ex_pipe_i.csr_en) &&
                             (csr_raddr[11:10] == 2'b11); // Priv spec section 2.1

  assign csr_illegal_o = (id_ex_pipe_i.instr_valid && id_ex_pipe_i.csr_en) ? illegal_csr_write || illegal_csr_read : 1'b0;


  ////////////////////////////////////////////
  //   ____ ____  ____    ____              //
  //  / ___/ ___||  _ \  |  _ \ ___  __ _   //
  // | |   \___ \| |_) | | |_) / _ \/ _` |  //
  // | |___ ___) |  _ <  |  _ <  __/ (_| |  //
  //  \____|____/|_| \_\ |_| \_\___|\__, |  //
  //                                |___/   //
  ////////////////////////////////////////////

  // NOTE!!!: Any new CSR register added in this file must also be
  //   added to the valid CSR register list cv32e40x_decoder.v

  // read logic
  always_comb
  begin
    illegal_csr_read = 1'b0;
    csr_counter_read_o = 1'b0;

    case (csr_raddr)
      // jvt: Jump vector table
      CSR_JVT:  begin
        if (ZC_EXT) begin // todo: remove conditional once fully implemented
          csr_rdata_int = jvt_q;
        end else begin
          csr_rdata_int    = '0;
          illegal_csr_read = 1'b1;
        end
      end

      // mstatus: always M-mode, contains IE bit
      CSR_MSTATUS: csr_rdata_int = mstatus_q;

      // mstatush: All bits hardwired to 0
      CSR_MSTATUSH: csr_rdata_int = 'b0;

      // misa: machine isa register
      CSR_MISA: csr_rdata_int = MISA_VALUE;

      // mie: machine interrupt enable
      CSR_MIE: csr_rdata_int = mie_q;

      // mtvec: machine trap-handler base address
      CSR_MTVEC: csr_rdata_int = mtvec_q;

      // mtvt: machine trap-handler vector table base address
      CSR_MTVT: begin
        if (SMCLIC) begin
          csr_rdata_int = mtvt_q;
        end else begin
          csr_rdata_int    = '0;
          illegal_csr_read = 1'b1;
        end
      end

      // mscratch: machine scratch
      CSR_MSCRATCH: csr_rdata_int = mscratch_q;

      // mepc: exception program counter
      CSR_MEPC: csr_rdata_int = mepc_q;

      // mcause: exception cause
      CSR_MCAUSE: csr_rdata_int = mcause_q;

      // mip: interrupt pending
      CSR_MIP: csr_rdata_int = mip;

      // mnxti: Next Interrupt Handler Address and Interrupt Enable
      CSR_MNXTI: begin
        if (SMCLIC) begin
          csr_rdata_int = mnxti_q;
        end else begin
          csr_rdata_int    = '0;
          illegal_csr_read = 1'b1;
        end
      end

      // mintstatus: Interrupt Status
      CSR_MINTSTATUS: begin
        if (SMCLIC) begin
          csr_rdata_int = mintstatus_q;
        end else begin
          csr_rdata_int    = '0;
          illegal_csr_read = 1'b1;
        end
      end

      // mintthresh: Interrupt-Level Threshold
      CSR_MINTTHRESH: begin
        if (SMCLIC) begin
          csr_rdata_int = mintthresh_q;
        end else begin
          csr_rdata_int    = '0;
          illegal_csr_read = 1'b1;
        end
      end

      // mscratchcsw: Scratch Swap for Multiple Privilege Modes
      CSR_MSCRATCHCSW: begin
        if (SMCLIC) begin
          csr_rdata_int = mscratchcsw_q;
        end else begin
          csr_rdata_int    = '0;
          illegal_csr_read = 1'b1;
        end
      end

      // mscratchcswl: Scratch Swap for Interrupt Levels
      CSR_MSCRATCHCSWL: begin
        if (SMCLIC) begin
          csr_rdata_int = mscratchcswl_q;
        end else begin
          csr_rdata_int    = '0;
          illegal_csr_read = 1'b1;
        end
      end

      // mclicbase: CLIC Base
      CSR_MCLICBASE: begin
        if (SMCLIC) begin
          csr_rdata_int = mclicbase_q;
        end else begin
          csr_rdata_int    = '0;
          illegal_csr_read = 1'b1;
        end
      end

      // mhartid: unique hardware thread id
      CSR_MHARTID: csr_rdata_int = mhartid_i;

      // mimpid: implementation id
      CSR_MIMPID: csr_rdata_int = mimpid_i;

      // mconfigptr: Pointer to configuration data structure. Read only, hardwired to 0
      CSR_MCONFIGPTR: csr_rdata_int = 'b0;

      // mvendorid: Machine Vendor ID
      CSR_MVENDORID: csr_rdata_int = {MVENDORID_BANK, MVENDORID_OFFSET};

      // marchid: Machine Architecture ID
      CSR_MARCHID: csr_rdata_int = MARCHID;

      // unimplemented, read 0 CSRs
        CSR_MTVAL :
          csr_rdata_int = 'b0;

      CSR_TSELECT,
        CSR_TDATA3,
        CSR_MCONTEXT,
        CSR_MSCONTEXT,
        CSR_TCONTROL:
              csr_rdata_int = 'b0; // Always read 0
      CSR_TDATA1:
              csr_rdata_int = tmatch_control_q;
      CSR_TDATA2:
              csr_rdata_int = tmatch_value_q;
      CSR_TINFO:
              csr_rdata_int = tinfo_types;

      CSR_DCSR: begin
              csr_rdata_int = dcsr_rdata;
              illegal_csr_read = !ctrl_fsm_i.debug_mode;
      end
      CSR_DPC: begin
              csr_rdata_int = dpc_q;
              illegal_csr_read = !ctrl_fsm_i.debug_mode;
      end
      CSR_DSCRATCH0: begin
              csr_rdata_int = dscratch0_q;
              illegal_csr_read = !ctrl_fsm_i.debug_mode;
      end
      CSR_DSCRATCH1: begin
              csr_rdata_int = dscratch1_q;
              illegal_csr_read = !ctrl_fsm_i.debug_mode;
      end

      // Hardware Performance Monitor
      CSR_MCYCLE,
      CSR_MINSTRET,
      CSR_MHPMCOUNTER3,
      CSR_MHPMCOUNTER4,  CSR_MHPMCOUNTER5,  CSR_MHPMCOUNTER6,  CSR_MHPMCOUNTER7,
      CSR_MHPMCOUNTER8,  CSR_MHPMCOUNTER9,  CSR_MHPMCOUNTER10, CSR_MHPMCOUNTER11,
      CSR_MHPMCOUNTER12, CSR_MHPMCOUNTER13, CSR_MHPMCOUNTER14, CSR_MHPMCOUNTER15,
      CSR_MHPMCOUNTER16, CSR_MHPMCOUNTER17, CSR_MHPMCOUNTER18, CSR_MHPMCOUNTER19,
      CSR_MHPMCOUNTER20, CSR_MHPMCOUNTER21, CSR_MHPMCOUNTER22, CSR_MHPMCOUNTER23,
      CSR_MHPMCOUNTER24, CSR_MHPMCOUNTER25, CSR_MHPMCOUNTER26, CSR_MHPMCOUNTER27,
      CSR_MHPMCOUNTER28, CSR_MHPMCOUNTER29, CSR_MHPMCOUNTER30, CSR_MHPMCOUNTER31,
      CSR_CYCLE,
      CSR_INSTRET,
      CSR_HPMCOUNTER3,
      CSR_HPMCOUNTER4,  CSR_HPMCOUNTER5,  CSR_HPMCOUNTER6,  CSR_HPMCOUNTER7,
      CSR_HPMCOUNTER8,  CSR_HPMCOUNTER9,  CSR_HPMCOUNTER10, CSR_HPMCOUNTER11,
      CSR_HPMCOUNTER12, CSR_HPMCOUNTER13, CSR_HPMCOUNTER14, CSR_HPMCOUNTER15,
      CSR_HPMCOUNTER16, CSR_HPMCOUNTER17, CSR_HPMCOUNTER18, CSR_HPMCOUNTER19,
      CSR_HPMCOUNTER20, CSR_HPMCOUNTER21, CSR_HPMCOUNTER22, CSR_HPMCOUNTER23,
      CSR_HPMCOUNTER24, CSR_HPMCOUNTER25, CSR_HPMCOUNTER26, CSR_HPMCOUNTER27,
      CSR_HPMCOUNTER28, CSR_HPMCOUNTER29, CSR_HPMCOUNTER30, CSR_HPMCOUNTER31: begin
        csr_rdata_int = mhpmcounter_q[csr_raddr[4:0]][31:0];
        csr_counter_read_o = 1'b1;
      end

      CSR_MCYCLEH,
      CSR_MINSTRETH,
      CSR_MHPMCOUNTER3H,
      CSR_MHPMCOUNTER4H,  CSR_MHPMCOUNTER5H,  CSR_MHPMCOUNTER6H,  CSR_MHPMCOUNTER7H,
      CSR_MHPMCOUNTER8H,  CSR_MHPMCOUNTER9H,  CSR_MHPMCOUNTER10H, CSR_MHPMCOUNTER11H,
      CSR_MHPMCOUNTER12H, CSR_MHPMCOUNTER13H, CSR_MHPMCOUNTER14H, CSR_MHPMCOUNTER15H,
      CSR_MHPMCOUNTER16H, CSR_MHPMCOUNTER17H, CSR_MHPMCOUNTER18H, CSR_MHPMCOUNTER19H,
      CSR_MHPMCOUNTER20H, CSR_MHPMCOUNTER21H, CSR_MHPMCOUNTER22H, CSR_MHPMCOUNTER23H,
      CSR_MHPMCOUNTER24H, CSR_MHPMCOUNTER25H, CSR_MHPMCOUNTER26H, CSR_MHPMCOUNTER27H,
      CSR_MHPMCOUNTER28H, CSR_MHPMCOUNTER29H, CSR_MHPMCOUNTER30H, CSR_MHPMCOUNTER31H,
      CSR_CYCLEH,
      CSR_INSTRETH,
      CSR_HPMCOUNTER3H,
      CSR_HPMCOUNTER4H,  CSR_HPMCOUNTER5H,  CSR_HPMCOUNTER6H,  CSR_HPMCOUNTER7H,
      CSR_HPMCOUNTER8H,  CSR_HPMCOUNTER9H,  CSR_HPMCOUNTER10H, CSR_HPMCOUNTER11H,
      CSR_HPMCOUNTER12H, CSR_HPMCOUNTER13H, CSR_HPMCOUNTER14H, CSR_HPMCOUNTER15H,
      CSR_HPMCOUNTER16H, CSR_HPMCOUNTER17H, CSR_HPMCOUNTER18H, CSR_HPMCOUNTER19H,
      CSR_HPMCOUNTER20H, CSR_HPMCOUNTER21H, CSR_HPMCOUNTER22H, CSR_HPMCOUNTER23H,
      CSR_HPMCOUNTER24H, CSR_HPMCOUNTER25H, CSR_HPMCOUNTER26H, CSR_HPMCOUNTER27H,
      CSR_HPMCOUNTER28H, CSR_HPMCOUNTER29H, CSR_HPMCOUNTER30H, CSR_HPMCOUNTER31H: begin
        csr_rdata_int = (MHPMCOUNTER_WIDTH == 64) ? mhpmcounter_q[csr_raddr[4:0]][63:32] : '0;
        csr_counter_read_o = 1'b1;
      end

      CSR_MCOUNTINHIBIT: csr_rdata_int = mcountinhibit_q;

      CSR_MHPMEVENT3,
      CSR_MHPMEVENT4,  CSR_MHPMEVENT5,  CSR_MHPMEVENT6,  CSR_MHPMEVENT7,
      CSR_MHPMEVENT8,  CSR_MHPMEVENT9,  CSR_MHPMEVENT10, CSR_MHPMEVENT11,
      CSR_MHPMEVENT12, CSR_MHPMEVENT13, CSR_MHPMEVENT14, CSR_MHPMEVENT15,
      CSR_MHPMEVENT16, CSR_MHPMEVENT17, CSR_MHPMEVENT18, CSR_MHPMEVENT19,
      CSR_MHPMEVENT20, CSR_MHPMEVENT21, CSR_MHPMEVENT22, CSR_MHPMEVENT23,
      CSR_MHPMEVENT24, CSR_MHPMEVENT25, CSR_MHPMEVENT26, CSR_MHPMEVENT27,
      CSR_MHPMEVENT28, CSR_MHPMEVENT29, CSR_MHPMEVENT30, CSR_MHPMEVENT31:
        csr_rdata_int = mhpmevent_q[csr_raddr[4:0]];


      default: begin
        csr_rdata_int    = '0;
        illegal_csr_read = 1'b1;
      end
    endcase
  end



  // write logic
  always_comb
  begin

    jvt_n                    = '0;
    jvt_we                   = 1'b0;

    mscratch_n               = csr_wdata_int;
    mscratch_we              = 1'b0;
    mepc_n                   = csr_wdata_int & ~32'b1;
    mepc_we                  = 1'b0;
    dpc_n                    = csr_wdata_int & ~32'b1;
    dpc_we                   = 1'b0; 

    dcsr_n                   = '{
                                xdebugver : dcsr_q.xdebugver,
                                ebreakm   : csr_wdata_int[15],
                                stepie    : csr_wdata_int[11],
                                step      : csr_wdata_int[2],
                                prv       : PRIV_LVL_M,
                                cause     : dcsr_q.cause,
                                default   : 'd0
                             };
    dcsr_we                  = 1'b0;

    dscratch0_n              = csr_wdata_int;
    dscratch0_we             = 1'b0;
    dscratch1_n              = csr_wdata_int;
    dscratch1_we             = 1'b0;

    mstatus_n                = '{
                              mprv: 1'b0,
                              mpp:  PRIV_LVL_M,
                              mpie: csr_wdata_int[MSTATUS_MPIE_BIT],
                              mie:  csr_wdata_int[MSTATUS_MIE_BIT],
                              default: 'b0
                            };
    mstatus_we               = 1'b0;

    mcause_n                 = '{
                                  irq:            csr_wdata_int[31],
                                  exception_code: csr_wdata_int[7:0],
                                  default:        'b0
                                };
    mcause_we                = 1'b0;

    mtvec_n.addr             = csr_mtvec_init_i ? mtvec_addr_i[31:8] : csr_wdata_int[31:8];
    mtvec_n.zero0            = mtvec_q.zero0;
    mtvec_n.mode             = csr_mtvec_init_i ? mtvec_q.mode : {1'b0, csr_wdata_int[0]};
    mtvec_we                 = csr_mtvec_init_i;

    mtvt_n                   = MTVT_RESET_VAL; // todo: Implement CLIC support
    mtvt_we                  = 1'b0;
    mnxti_n                  = '0;
    mnxti_we                 = 1'b0;
    mintstatus_n             = MINTSTATUS_RESET_VAL;
    mintstatus_we            = 1'b0;
    mintthresh_n             = '0;
    mintthresh_we            = 1'b0;
    mscratchcsw_n            = '0;
    mscratchcsw_we           = 1'b0;
    mscratchcswl_n           = '0;
    mscratchcswl_we          = 1'b0;
    mie_n                    = csr_wdata_int & IRQ_MASK;
    mie_we                   = 1'b0;
  
    if (csr_we_int) begin
      case (csr_waddr)
        // jvt: Jump vector table
        CSR_JVT: begin
          if (ZC_EXT) begin
          jvt_we = 1'b1;
        end
        end
        // mstatus: IE bit
        CSR_MSTATUS: begin
          mstatus_we = 1'b1;
        end
        CSR_MSTATUSH: begin
          // No bits implemented in MSTATUSH, do nothing
        end
        // mie: machine interrupt enable
        CSR_MIE: begin
              mie_we = 1'b1;
        end
        // mtvec: machine trap-handler base address
        CSR_MTVEC: begin
              mtvec_we = 1'b1;
        end
        // mtvt: machine trap-handler vector table base address
        CSR_MTVT: begin
          if (SMCLIC) begin
            mtvt_we = 1'b1;
          end
        end
        // mscratch: machine scratch
        CSR_MSCRATCH: begin
              mscratch_we = 1'b1;
        end
        // mepc: exception program counter
        CSR_MEPC: begin
              mepc_we = 1'b1;
        end
        // mcause
        CSR_MCAUSE: begin 
                mcause_we = 1'b1;
        end
        CSR_MNXTI: begin
          if (SMCLIC) begin
            mnxti_we = 1'b1;
          end
        end
        CSR_MINTSTATUS: begin
          if (SMCLIC) begin
            mintstatus_we = 1'b1;
          end
        end
        CSR_MINTTHRESH: begin
          if (SMCLIC) begin
            mintthresh_we = 1'b1;
          end
        end
        CSR_MSCRATCHCSW: begin
          if (SMCLIC) begin
            mscratchcsw_we = 1'b1;
          end
        end
        CSR_MSCRATCHCSWL: begin
          if (SMCLIC) begin
            mscratchcswl_we = 1'b1;
          end
        end
        CSR_DCSR: begin
              dcsr_we = 1'b1;
        end
        CSR_DPC: begin
                dpc_we = 1'b1;
        end
        CSR_DSCRATCH0: begin
                dscratch0_we = 1'b1;
        end
        CSR_DSCRATCH1: begin
                dscratch1_we = 1'b1;
        end
                
      endcase
    end

    // exception controller gets priority over other writes
    unique case (1'b1)

      ctrl_fsm_i.csr_save_cause: begin

        if (ctrl_fsm_i.debug_csr_save) begin
            // all interrupts are masked, don't update cause, epc, tval dpc and
            // mpstatus
            // dcsr.nmip is not a flop, but comes directly from the controller
            dcsr_n = '{
              xdebugver : dcsr_q.xdebugver,
              ebreakm   : dcsr_q.ebreakm,
              stepie    : dcsr_q.stepie,
              step      : dcsr_q.step,
              prv       : PRIV_LVL_M,
              cause     : ctrl_fsm_i.debug_cause,
              default   : 'd0
            };
            dcsr_we = 1'b1;

            dpc_n  = ctrl_fsm_i.pipe_pc;
            dpc_we = 1'b1;
        end else begin
            mstatus_n.mpie = mstatus_q.mie;
            mstatus_n.mie  = 1'b0;
            mstatus_n.mpp  = PRIV_LVL_M;
            mstatus_we = 1'b1;

            mepc_n  = ctrl_fsm_i.pipe_pc;
            mepc_we = 1'b1;

            mcause_n  = ctrl_fsm_i.csr_cause;
            mcause_we = 1'b1;
        end
      end //ctrl_fsm_i.csr_save_cause

      ctrl_fsm_i.csr_restore_mret: begin //MRET
        mstatus_n.mie  = mstatus_q.mpie;
        mstatus_n.mpie = 1'b1;
        mstatus_n.mpp  = PRIV_LVL_M;
        mstatus_we = 1'b1;
      end //ctrl_fsm_i.csr_restore_mret

      default:;
    endcase
  end


  // CSR operation logic
  // Using ex_wb_pipe_i.rf_wdata for read-modify-write since CSR was read in EX, written in WB
  always_comb
  begin
    if(!csr_en_gated) begin
      csr_wdata_int = csr_wdata;
      csr_we_int    = 1'b0;
    end else begin
      csr_we_int    = 1'b1;
      case (csr_op)
        CSR_OP_WRITE: csr_wdata_int = csr_wdata;
        CSR_OP_SET:   csr_wdata_int = csr_wdata | ex_wb_pipe_i.rf_wdata;
        CSR_OP_CLEAR: csr_wdata_int = (~csr_wdata) & ex_wb_pipe_i.rf_wdata;

        CSR_OP_READ: begin
          csr_wdata_int = csr_wdata;
          csr_we_int    = 1'b0;
        end
      endcase
    end
  end

  cv32e40x_csr #(
    .WIDTH      (32),
    .SHADOWCOPY (1'b0),
    .RESETVALUE (32'd0)
  ) jvt_csr_i (
    .clk        (clk),
    .rst_n      (rst_n),
    .wr_data_i  (jvt_n),
    .wr_en_i    (jvt_we),
    .rd_data_o  (jvt_q),
    .rd_error_o (jvt_rd_error)
  );

  cv32e40x_csr #(
    .WIDTH      (32),
    .SHADOWCOPY (1'b0),
    .RESETVALUE (32'd0)
  ) dscratch0_csr_i (
    .clk      (clk),
    .rst_n     (rst_n),
    .wr_data_i  (dscratch0_n),
    .wr_en_i    (dscratch0_we),
    .rd_data_o  (dscratch0_q),
    .rd_error_o (dscratch0_rd_error)
  );

  cv32e40x_csr #(
    .WIDTH      (32),
    .SHADOWCOPY (1'b0),
    .RESETVALUE (32'd0)
  ) dscratch1_csr_i (
    .clk      (clk),
    .rst_n     (rst_n),
    .wr_data_i  (dscratch1_n),
    .wr_en_i    (dscratch1_we),
    .rd_data_o  (dscratch1_q),
    .rd_error_o (dscratch1_rd_error)
  );

 cv32e40x_csr #(
    .WIDTH      (32),
    .SHADOWCOPY (1'b0),
    .RESETVALUE (DCSR_RESET_VAL)
  ) dcsr_csr_i (
    .clk      (clk),
    .rst_n     (rst_n),
    .wr_data_i  (dcsr_n),
    .wr_en_i    (dcsr_we),
    .rd_data_o  (dcsr_q),
    .rd_error_o (dcsr_rd_error)
  );

  cv32e40x_csr #(
    .WIDTH      (32),
    .SHADOWCOPY (1'b0),
    .RESETVALUE (32'd0)
  ) dpc_csr_i (
    .clk      (clk),
    .rst_n     (rst_n),
    .wr_data_i  (dpc_n),
    .wr_en_i    (dpc_we),
    .rd_data_o  (dpc_q),
    .rd_error_o (dpc_rd_error)
  );

  cv32e40x_csr #(
    .WIDTH      (32),
    .SHADOWCOPY (1'b0),
    .RESETVALUE (32'd0)
  ) mepc_csr_i (
    .clk      (clk),
    .rst_n     (rst_n),
    .wr_data_i  (mepc_n),
    .wr_en_i    (mepc_we),
    .rd_data_o  (mepc_q),
    .rd_error_o (mepc_rd_error)
  );

  cv32e40x_csr #(
    .WIDTH      (32),
    .SHADOWCOPY (1'b0),
    .RESETVALUE (32'd0)
  ) mscratch_csr_i (
    .clk      (clk),
    .rst_n     (rst_n),
    .wr_data_i  (mscratch_n),
    .wr_en_i    (mscratch_we),
    .rd_data_o  (mscratch_q),
    .rd_error_o (mscratch_rd_error)
  );

  cv32e40x_csr #(
    .WIDTH      (32),
    .SHADOWCOPY (1'b0),
    .RESETVALUE (32'd0)
  ) mie_csr_i (
    .clk      (clk),
    .rst_n     (rst_n),
    .wr_data_i  (mie_n),
    .wr_en_i    (mie_we),
    .rd_data_o  (mie_q),
    .rd_error_o (mie_rd_error)
  );

  cv32e40x_csr #(
    .WIDTH      (32),
    .SHADOWCOPY (1'b0),
    .RESETVALUE (MSTATUS_RESET_VAL)
  ) mstatus_csr_i (
    .clk      (clk),
    .rst_n     (rst_n),
    .wr_data_i  (mstatus_n),
    .wr_en_i    (mstatus_we),
    .rd_data_o  (mstatus_q),
    .rd_error_o (mstatus_rd_error)
  );

  cv32e40x_csr #(
    .WIDTH      (32),
    .SHADOWCOPY (1'b0),
    .RESETVALUE (32'd0)
  ) mcause_csr_i (
    .clk      (clk),
    .rst_n     (rst_n),
    .wr_data_i  (mcause_n),
    .wr_en_i    (mcause_we),
    .rd_data_o  (mcause_q),
    .rd_error_o (mcause_rd_error)
  );

  

  cv32e40x_csr #(
    .WIDTH      (32),
    .SHADOWCOPY (1'b0),
    .RESETVALUE (MTVEC_RESET_VAL)
  ) mtvec_csr_i (
    .clk      (clk),
    .rst_n     (rst_n),
    .wr_data_i  (mtvec_n),
    .wr_en_i    (mtvec_we),
    .rd_data_o  (mtvec_q),
    .rd_error_o (mtvec_rd_error)
  );

  generate
    if (SMCLIC) begin
      cv32e40x_csr #(
        .WIDTH      (32),
        .SHADOWCOPY (1'b0),
        .RESETVALUE (MTVT_RESET_VAL)
      ) mtvt_csr_i (
        .clk        (clk),
        .rst_n      (rst_n),
        .wr_data_i  (mtvt_n),
        .wr_en_i    (mtvt_we),
        .rd_data_o  (mtvt_q),
        .rd_error_o (mtvt_rd_error)
      );

      assign mnxti_q = 32'h0;

      cv32e40x_csr #(
        .WIDTH      (32),
        .SHADOWCOPY (1'b0),
        .RESETVALUE (MINTSTATUS_RESET_VAL)
      ) mintstatus_csr_i (
        .clk        (clk),
        .rst_n      (rst_n),
        .wr_data_i  (mintstatus_n),
        .wr_en_i    (mintstatus_we),
        .rd_data_o  (mintstatus_q),
        .rd_error_o (mintstatus_rd_error)
      );
      cv32e40x_csr #(
        .WIDTH      (32),
        .SHADOWCOPY (1'b0),
        .RESETVALUE (32'h0)
      ) mintthresh_csr_i (
        .clk        (clk),
        .rst_n      (rst_n),
        .wr_data_i  (mintthresh_n),
        .wr_en_i    (mintthresh_we),
        .rd_data_o  (mintthresh_q),
        .rd_error_o (mintthresh_rd_error)
      );
      cv32e40x_csr #(
        .WIDTH      (32),
        .SHADOWCOPY (1'b0),
        .RESETVALUE (32'h0)
      ) mscratchcsw_csr_i (
        .clk        (clk),
        .rst_n      (rst_n),
        .wr_data_i  (mscratchcsw_n),
        .wr_en_i    (mscratchcsw_we),
        .rd_data_o  (mscratchcsw_q),
        .rd_error_o (mscratchcsw_rd_error)
      );
      cv32e40x_csr #(
        .WIDTH      (32),
        .SHADOWCOPY (1'b0),
        .RESETVALUE (32'h0)
      ) mscratchcswl_csr_i (
        .clk        (clk),
        .rst_n      (rst_n),
        .wr_data_i  (mscratchcswl_n),
        .wr_en_i    (mscratchcswl_we),
        .rd_data_o  (mscratchcswl_q),
        .rd_error_o (mscratchcswl_rd_error)
      );
      cv32e40x_csr #(
        .WIDTH      (32),
        .SHADOWCOPY (1'b0),
        .RESETVALUE (32'h0)
      ) mclicbase_csr_i (
        .clk        (clk),
        .rst_n      (rst_n),
        .wr_data_i  (mclicbase_n),
        .wr_en_i    (mclicbase_we),
        .rd_data_o  (mclicbase_q),
        .rd_error_o (mclicbase_rd_error)
      );

    end else begin
      assign mtvt_q              = 32'h0;
      assign mtvt_rd_error       = 1'b0;
      assign mnxti_q             = 32'h0;
      assign mintstatus_q        = 32'h0;
      assign mintstatus_rd_error = 1'b0;
      assign mintthresh_q        = 32'h0;
      assign mintthresh_rd_error = 1'b0;
      assign mscratchcsw_q       = 32'h0;
      assign mscratchcswl_q      = 32'h0;
      assign mclicbase_q         = 32'h0;
    end
  endgenerate

  assign csr_rdata_o = csr_rdata_int;

  // IRQ enable
  assign m_irq_enable_o  = mstatus_q.mie;
  
  assign mtvec_addr_o    = mtvec_q.addr;
  assign mtvec_mode_o    = mtvec_q.mode;
  
  assign mepc_o          = mepc_q;
  assign dpc_o           = dpc_q;
  assign dcsr_o          = dcsr_q;

  assign mie_o = mie_q;
  
  // dcsr_rdata factors in the flop outputs and the nmip bit from the controller
  assign dcsr_rdata = {dcsr_q[31:4], ctrl_fsm_i.pending_nmi, dcsr_q[2:0]};

 ////////////////////////////////////////////////////////////////////////
 //  ____       _                   _____     _                        //
 // |  _ \  ___| |__  _   _  __ _  |_   _| __(_) __ _  __ _  ___ _ __  //
 // | | | |/ _ \ '_ \| | | |/ _` |   | || '__| |/ _` |/ _` |/ _ \ '__| //
 // | |_| |  __/ |_) | |_| | (_| |   | || |  | | (_| | (_| |  __/ |    //
 // |____/ \___|_.__/ \__,_|\__, |   |_||_|  |_|\__, |\__, |\___|_|    //
 //                         |___/               |___/ |___/            //
 ////////////////////////////////////////////////////////////////////////

  
  // Write select
  assign tmatch_control_we = csr_we_int && ctrl_fsm_i.debug_mode && (csr_waddr == CSR_TDATA1);
  assign tmatch_value_we   = csr_we_int && ctrl_fsm_i.debug_mode && (csr_waddr == CSR_TDATA2);

  // All supported trigger types
  assign tinfo_types = 1 << TTYPE_MCONTROL;

  // Assign write data
  // TDATA0 - only support simple address matching
  assign tmatch_control_n =
              {
              TTYPE_MCONTROL,        // type    : address/data match
              1'b1,                  // dmode   : access from D mode only
              6'h00,                 // maskmax : exact match only
              1'b0,                  // hit     : not supported
              1'b0,                  // select  : address match only
              1'b0,                  // timing  : match before execution
              2'b00,                 // sizelo  : match any access
              4'h1,                  // action  : enter debug mode
              1'b0,                  // chain   : not supported
              4'h0,                  // match   : simple match
              1'b1,                  // m       : match in m-mode
              1'b0,                  // 0       : zero
              1'b0,                  // s       : not supported
              1'b0,                  // u       : match in u-mode
              csr_wdata_int[2],      // execute : match instruction address
              1'b0,                  // store   : not supported
              1'b0};                 // load    : not supported

  assign tmatch_value_n = csr_wdata_int; 

  cv32e40x_csr #(
    .WIDTH      (32),
    .SHADOWCOPY (1'b0),
    .RESETVALUE (TMATCH_CONTROL_RST_VAL)
  ) tmatch_control_csr_i (
    .clk      (clk),
    .rst_n     (rst_n),
    .wr_data_i  (tmatch_control_n),
    .wr_en_i    (tmatch_control_we),
    .rd_data_o  (tmatch_control_q),
    .rd_error_o (tmatch_control_rd_error)
  );   
  
  cv32e40x_csr #(
    .WIDTH      (32),
    .SHADOWCOPY (1'b0),
    .RESETVALUE (32'd0)
  ) tmatch_value_csr_i (
    .clk      (clk),
    .rst_n     (rst_n),
    .wr_data_i  (tmatch_value_n),
    .wr_en_i    (tmatch_value_we),
    .rd_data_o  (tmatch_value_q),
    .rd_error_o (tmatch_value_rd_error)
  );  


  // Breakpoint matching
  // We match against the next address, as the breakpoint must be taken before execution
  // Matching is disabled when ctrl_fsm_i.debug_mode == 1'b1
  // Trigger CSRs can only be written from debug mode, writes from any other privilege level are ignored.
  //   Thus we do not have an issue where a write to the tdata2 CSR immediately before the matched instruction
  //   could be missed since we must write in debug mode, then dret to machine mode (kills pipeline) before
  //   returning to dpc.
  assign trigger_match_o = tmatch_control_q[2] && !ctrl_fsm_i.debug_mode &&
                           (pc_if_i[31:0] == tmatch_value_q[31:0]);


  /////////////////////////////////////////////////////////////////
  //   ____            __     ____                  _            //
  // |  _ \ ___ _ __ / _|   / ___|___  _   _ _ __ | |_ ___ _ __  //
  // | |_) / _ \ '__| |_   | |   / _ \| | | | '_ \| __/ _ \ '__| //
  // |  __/  __/ |  |  _|  | |__| (_) | |_| | | | | ||  __/ |    //
  // |_|   \___|_|  |_|(_)  \____\___/ \__,_|_| |_|\__\___|_|    //
  //                                                             //
  /////////////////////////////////////////////////////////////////

  // Cycle Count Output Signal
  assign mcycle_o = mhpmcounter_q[0];

  // Flop certain events to ease timing
  localparam bit [15:0] HPM_EVENT_FLOP     = 16'b1111_1111_1100_0000;
  localparam bit [31:0] MCOUNTINHIBIT_MASK = {{(29-NUM_MHPMCOUNTERS){1'b0}},{(NUM_MHPMCOUNTERS){1'b1}},3'b101};
  
  logic [15:0]          hpm_events_raw;
  logic                 all_counters_disabled;
  
  assign all_counters_disabled = &(mcountinhibit_n | ~MCOUNTINHIBIT_MASK);

  genvar                hpm_idx;
  generate
    for(hpm_idx=0; hpm_idx<16; hpm_idx++) begin
      if(HPM_EVENT_FLOP[hpm_idx]) begin: hpm_event_flop

        always_ff @(posedge clk, negedge rst_n) begin
          if (rst_n == 1'b0) begin
            hpm_events[hpm_idx] <= 1'b0;
          end else begin
            if(!all_counters_disabled) begin
              hpm_events[hpm_idx] <= hpm_events_raw[hpm_idx];
            end
          end
        end

      end
      else begin: hpm_even_no_flop
        assign hpm_events[hpm_idx] = hpm_events_raw[hpm_idx];
      end
    end
  endgenerate

  // ------------------------
  // Events to count
  assign hpm_events_raw[0]  = 1'b1;                               // Cycle counter
  assign hpm_events_raw[1]  = ctrl_fsm_i.mhpmevent.minstret;      // Instruction counter
  assign hpm_events_raw[2]  = ctrl_fsm_i.mhpmevent.compressed;    // Compressed instruction counter
  assign hpm_events_raw[3]  = ctrl_fsm_i.mhpmevent.jump;          // Nr of jumps (unconditional)
  assign hpm_events_raw[4]  = ctrl_fsm_i.mhpmevent.branch;        // Nr of branches (conditional)
  assign hpm_events_raw[5]  = ctrl_fsm_i.mhpmevent.branch_taken;  // Nr of taken branches (conditional)
  assign hpm_events_raw[6]  = ctrl_fsm_i.mhpmevent.intr_taken;    // Nr of interrupts taken (excluding NMI)
  assign hpm_events_raw[7]  = ctrl_fsm_i.mhpmevent.data_read;     // Data read. Nr of read transactions on the OBI data interface
  assign hpm_events_raw[8]  = ctrl_fsm_i.mhpmevent.data_write;    // Data write. Nr of write transactions on the OBI data interface
  assign hpm_events_raw[9]  = ctrl_fsm_i.mhpmevent.if_invalid;    // IF invalid (No valid output from IF when ID stage is ready)
  assign hpm_events_raw[10] = ctrl_fsm_i.mhpmevent.id_invalid;    // ID invalid (No valid output from ID when EX stage is ready)
  assign hpm_events_raw[11] = ctrl_fsm_i.mhpmevent.ex_invalid;    // EX invalid (No valid output from EX when WB stage is ready)
  assign hpm_events_raw[12] = ctrl_fsm_i.mhpmevent.wb_invalid;    // WB invalid (No valid output from WB)
  assign hpm_events_raw[13] = ctrl_fsm_i.mhpmevent.id_ld_stall;   // Nr of load use hazards
  assign hpm_events_raw[14] = ctrl_fsm_i.mhpmevent.id_jalr_stall; // Nr of jump (and link) register hazards
  assign hpm_events_raw[15] = ctrl_fsm_i.mhpmevent.wb_data_stall; // Nr of stall cycles caused in the WB stage by loads/stores

  // ------------------------
  // address decoder for performance counter registers
  logic mcountinhibit_we;
  logic mhpmevent_we;

  assign mcountinhibit_we = csr_we_int & (  csr_waddr == CSR_MCOUNTINHIBIT);
  assign mhpmevent_we     = csr_we_int & ( (csr_waddr == CSR_MHPMEVENT3  )||
                                           (csr_waddr == CSR_MHPMEVENT4  ) ||
                                           (csr_waddr == CSR_MHPMEVENT5  ) ||
                                           (csr_waddr == CSR_MHPMEVENT6  ) ||
                                           (csr_waddr == CSR_MHPMEVENT7  ) ||
                                           (csr_waddr == CSR_MHPMEVENT8  ) ||
                                           (csr_waddr == CSR_MHPMEVENT9  ) ||
                                           (csr_waddr == CSR_MHPMEVENT10 ) ||
                                           (csr_waddr == CSR_MHPMEVENT11 ) ||
                                           (csr_waddr == CSR_MHPMEVENT12 ) ||
                                           (csr_waddr == CSR_MHPMEVENT13 ) ||
                                           (csr_waddr == CSR_MHPMEVENT14 ) ||
                                           (csr_waddr == CSR_MHPMEVENT15 ) ||
                                           (csr_waddr == CSR_MHPMEVENT16 ) ||
                                           (csr_waddr == CSR_MHPMEVENT17 ) ||
                                           (csr_waddr == CSR_MHPMEVENT18 ) ||
                                           (csr_waddr == CSR_MHPMEVENT19 ) ||
                                           (csr_waddr == CSR_MHPMEVENT20 ) ||
                                           (csr_waddr == CSR_MHPMEVENT21 ) ||
                                           (csr_waddr == CSR_MHPMEVENT22 ) ||
                                           (csr_waddr == CSR_MHPMEVENT23 ) ||
                                           (csr_waddr == CSR_MHPMEVENT24 ) ||
                                           (csr_waddr == CSR_MHPMEVENT25 ) ||
                                           (csr_waddr == CSR_MHPMEVENT26 ) ||
                                           (csr_waddr == CSR_MHPMEVENT27 ) ||
                                           (csr_waddr == CSR_MHPMEVENT28 ) ||
                                           (csr_waddr == CSR_MHPMEVENT29 ) ||
                                           (csr_waddr == CSR_MHPMEVENT30 ) ||
                                           (csr_waddr == CSR_MHPMEVENT31 ) );

  // ------------------------
  // Increment value for performance counters
  genvar incr_gidx;
  generate
    for (incr_gidx=0; incr_gidx<32; incr_gidx++) begin : gen_mhpmcounter_increment
      assign mhpmcounter_increment[incr_gidx] = mhpmcounter_q[incr_gidx] + 1;
    end
  endgenerate

  // ------------------------
  // next value for performance counters and control registers
  always_comb
    begin
      mcountinhibit_n = mcountinhibit_q;
      mhpmevent_n     = mhpmevent_q;

      
      // Inhibit Control
      if(mcountinhibit_we)
        mcountinhibit_n = csr_wdata_int & MCOUNTINHIBIT_MASK;

      // Event Control
      if(mhpmevent_we)
        mhpmevent_n[csr_waddr[4:0]] = csr_wdata_int;
    end

  genvar wcnt_gidx;
  generate
    for (wcnt_gidx=0; wcnt_gidx<32; wcnt_gidx++) begin : gen_mhpmcounter_write

      // Write lower counter bits
      assign mhpmcounter_write_lower[wcnt_gidx] = csr_we_int && (csr_waddr == (CSR_MCYCLE + wcnt_gidx));

      // Write upper counter bits
      assign mhpmcounter_write_upper[wcnt_gidx] = !mhpmcounter_write_lower[wcnt_gidx] &&
                                                  csr_we_int && (csr_waddr == (CSR_MCYCLEH + wcnt_gidx)) && (MHPMCOUNTER_WIDTH == 64);

      // Increment counter
      
      if (wcnt_gidx == 0) begin : gen_mhpmcounter_mcycle
        // mcycle = mhpmcounter[0] : count every cycle (if not inhibited)
        assign mhpmcounter_write_increment[wcnt_gidx] = !mhpmcounter_write_lower[wcnt_gidx] &&
                                                        !mhpmcounter_write_upper[wcnt_gidx] &&
                                                        !mcountinhibit_q[wcnt_gidx];
      end else if (wcnt_gidx == 2) begin : gen_mhpmcounter_minstret
        // minstret = mhpmcounter[2]  : count every retired instruction (if not inhibited)
        assign mhpmcounter_write_increment[wcnt_gidx] = !mhpmcounter_write_lower[wcnt_gidx] &&
                                                        !mhpmcounter_write_upper[wcnt_gidx] &&
                                                        !mcountinhibit_q[wcnt_gidx] &&
                                                        hpm_events[1];
      end else if( (wcnt_gidx>2) && (wcnt_gidx<(NUM_MHPMCOUNTERS+3))) begin : gen_mhpmcounter
        // add +1 if any event is enabled and active
        assign mhpmcounter_write_increment[wcnt_gidx] = !mhpmcounter_write_lower[wcnt_gidx] &&
                                                        !mhpmcounter_write_upper[wcnt_gidx] &&
                                                        !mcountinhibit_q[wcnt_gidx] &&
                                                        |(hpm_events & mhpmevent_q[wcnt_gidx][NUM_HPM_EVENTS-1:0]);
      end else begin : gen_mhpmcounter_not_implemented
        assign mhpmcounter_write_increment[wcnt_gidx] = 1'b0;
      end
       
    end
  endgenerate

  // ------------------------
  // HPM Registers
  // next value
  genvar nxt_gidx;
  generate
    for (nxt_gidx = 0; nxt_gidx < 32; nxt_gidx++) begin : gen_mhpmcounter_nextvalue
      // mcyclce  is located at index 0
      // there is no counter at index 1
      // minstret is located at index 2
      // Programable HPM counters start at index 3
      if( (nxt_gidx == 1) ||
          (nxt_gidx >= (NUM_MHPMCOUNTERS+3) ) )
        begin : gen_non_implemented
          assign mhpmcounter_n[nxt_gidx]  = 'b0;
          assign mhpmcounter_we[nxt_gidx] = 2'b0;
      end
      else begin : gen_implemented_nextvalue
        always_comb begin
          mhpmcounter_we[nxt_gidx] = 2'b0;
          mhpmcounter_n[nxt_gidx]  = mhpmcounter_q[nxt_gidx];
          if (mhpmcounter_write_lower[nxt_gidx]) begin
            mhpmcounter_n[nxt_gidx][31:0] = csr_wdata_int;
            mhpmcounter_we[nxt_gidx][0] = 1'b1;
          end else if (mhpmcounter_write_upper[nxt_gidx]) begin
            mhpmcounter_n[nxt_gidx][63:32] = csr_wdata_int;
            mhpmcounter_we[nxt_gidx][1] = 1'b1;
          end else if (mhpmcounter_write_increment[nxt_gidx]) begin
            mhpmcounter_we[nxt_gidx] = 2'b11;
            mhpmcounter_n[nxt_gidx] = mhpmcounter_increment[nxt_gidx];
          end
        end // always_comb
      end
    end
  endgenerate
  //  Counter Registers: mhpcounter_q[]
  genvar cnt_gidx;
  generate
    for (cnt_gidx = 0; cnt_gidx < 32; cnt_gidx++) begin : gen_mhpmcounter
      // mcyclce  is located at index 0
      // there is no counter at index 1
      // minstret is located at index 2
      // Programable HPM counters start at index 3
      if( (cnt_gidx == 1) ||
          (cnt_gidx >= (NUM_MHPMCOUNTERS+3) ) )
        begin : gen_non_implemented
        assign mhpmcounter_q[cnt_gidx] = 'b0;
      end
      else begin : gen_implemented
        always_ff @(posedge clk, negedge rst_n)
          if (!rst_n) begin
            mhpmcounter_q[cnt_gidx] <= 'b0;
          end else begin
            if (mhpmcounter_we[cnt_gidx][0]) begin
              mhpmcounter_q[cnt_gidx][31:0] <= mhpmcounter_n[cnt_gidx][31:0];
            end
            if (mhpmcounter_we[cnt_gidx][1]) begin
              mhpmcounter_q[cnt_gidx][63:32] <= mhpmcounter_n[cnt_gidx][63:32];
            end
          end
      end
    end
  endgenerate

  //  Event Register: mhpevent_q[]
  genvar evt_gidx;
  generate
    for (evt_gidx = 0; evt_gidx < 32; evt_gidx++) begin : gen_mhpmevent
      // programable HPM events start at index3
      if( (evt_gidx < 3) ||
          (evt_gidx >= (NUM_MHPMCOUNTERS+3) ) )
        begin : gen_non_implemented
        assign mhpmevent_q[evt_gidx] = 'b0;
      end
      else begin : gen_implemented
        if (NUM_HPM_EVENTS < 32) begin : gen_tie_off
             assign mhpmevent_q[evt_gidx][31:NUM_HPM_EVENTS] = 'b0;
        end
        always_ff @(posedge clk, negedge rst_n)
            if (!rst_n)
                mhpmevent_q[evt_gidx][NUM_HPM_EVENTS-1:0]  <= 'b0;
            else
                mhpmevent_q[evt_gidx][NUM_HPM_EVENTS-1:0]  <= mhpmevent_n[evt_gidx][NUM_HPM_EVENTS-1:0] ;
      end
    end
  endgenerate

  //  Inhibit Regsiter: mcountinhibit_q
  //  Note: implemented counters are disabled out of reset to save power
  always_ff @(posedge clk, negedge rst_n) begin
    if (!rst_n) begin
      mcountinhibit_q <= MCOUNTINHIBIT_MASK; // default disable
    end else begin
      mcountinhibit_q <= mcountinhibit_n;
    end
  end

endmodule // cv32e40x_cs_registers
