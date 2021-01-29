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
// Engineer:       Matthias Baer - baermatt@student.ethz.ch                   //
//                                                                            //
// Additional contributions by:                                               //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                                                                            //
//                                                                            //
// Design Name:    RISC-V processor core                                      //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Defines for various constants used by the processor core.  //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

package cv32e40x_pkg;

////////////////////////////////////////////////
//    ___         ____          _             //
//   / _ \ _ __  / ___|___   __| | ___  ___   //
//  | | | | '_ \| |   / _ \ / _` |/ _ \/ __|  //
//  | |_| | |_) | |__| (_) | (_| |  __/\__ \  //
//   \___/| .__/ \____\___/ \__,_|\___||___/  //
//        |_|                                 //
////////////////////////////////////////////////

parameter OPCODE_SYSTEM    = 7'h73;
parameter OPCODE_FENCE     = 7'h0f;
parameter OPCODE_OP        = 7'h33;
parameter OPCODE_OPIMM     = 7'h13;
parameter OPCODE_STORE     = 7'h23;
parameter OPCODE_LOAD      = 7'h03;
parameter OPCODE_BRANCH    = 7'h63;
parameter OPCODE_JALR      = 7'h67;
parameter OPCODE_JAL       = 7'h6f;
parameter OPCODE_AUIPC     = 7'h17;
parameter OPCODE_LUI       = 7'h37;
parameter OPCODE_OP_FP     = 7'h53;
parameter OPCODE_OP_FMADD  = 7'h43;
parameter OPCODE_OP_FNMADD = 7'h4f;
parameter OPCODE_OP_FMSUB  = 7'h47;
parameter OPCODE_OP_FNMSUB = 7'h4b;
parameter OPCODE_STORE_FP  = 7'h27;
parameter OPCODE_LOAD_FP   = 7'h07;
parameter OPCODE_AMO       = 7'h2F;

parameter REGC_S1   = 2'b10;
parameter REGC_S4   = 2'b00;
parameter REGC_RD   = 2'b01;
parameter REGC_ZERO = 2'b11;


//////////////////////////////////////////////////////////////////////////////
//      _    _    _   _    ___                       _   _                  //
//     / \  | |  | | | |  / _ \ _ __   ___ _ __ __ _| |_(_) ___  _ __  ___  //
//    / _ \ | |  | | | | | | | | '_ \ / _ \ '__/ _` | __| |/ _ \| '_ \/ __| //
//   / ___ \| |__| |_| | | |_| | |_) |  __/ | | (_| | |_| | (_) | | | \__ \ //
//  /_/   \_\_____\___/   \___/| .__/ \___|_|  \__,_|\__|_|\___/|_| |_|___/ //
//                             |_|                                          //
//////////////////////////////////////////////////////////////////////////////

parameter ALU_OP_WIDTH = 5;

typedef enum logic [ALU_OP_WIDTH-1:0]
{

 ALU_ADD   = 5'b11000,
 ALU_SUB   = 5'b11001,
 
 ALU_XOR   = 5'b01111,
 ALU_OR    = 5'b01110,
 ALU_AND   = 5'b10101,

// Shifts
 ALU_SRA   = 5'b00100,
 ALU_SRL   = 5'b00101,
 ALU_SLL   = 5'b00111,

// Comparisons
 ALU_LTS   = 5'b00000,
 ALU_LTU   = 5'b00001,
 ALU_GES   = 5'b01010,
 ALU_GEU   = 5'b01011,
 ALU_EQ    = 5'b01100,
 ALU_NE    = 5'b01101,

// Set Lower Than operations
 ALU_SLTS  = 5'b00010,
 ALU_SLTU  = 5'b00011,

// div/rem
 ALU_DIVU  = 5'b10000,
 ALU_DIV   = 5'b10001,
 ALU_REMU  = 5'b10010,
 ALU_REM   = 5'b10011
 
} alu_opcode_e;
  
parameter MUL_OP_WIDTH = 1;

typedef enum logic [MUL_OP_WIDTH-1:0]
{

 MUL_M32   = 1'b0,
 MUL_H     = 1'b1

 } mul_opcode_e;

// vector modes
parameter VEC_MODE32 = 2'b00;
parameter VEC_MODE16 = 2'b10;
parameter VEC_MODE8  = 2'b11;


// FSM state encoding
typedef enum logic [4:0] { RESET, BOOT_SET, SLEEP, WAIT_SLEEP, FIRST_FETCH,
                   DECODE, FLUSH_EX, FLUSH_WB, XRET_JUMP,
                   DBG_TAKEN_ID, DBG_TAKEN_IF, DBG_FLUSH, DBG_WAIT_BRANCH} ctrl_state_e;

// Debug FSM state encoding
// State encoding done one-hot to ensure that debug_havereset_o, debug_running_o, debug_halted_o
// will come directly from flip-flops. *_INDEX and debug_state_e encoding must match

parameter HAVERESET_INDEX = 0;
parameter RUNNING_INDEX = 1;
parameter HALTED_INDEX = 2;

typedef enum logic [2:0] { HAVERESET = 3'b001, RUNNING = 3'b010, HALTED = 3'b100 } debug_state_e;

typedef enum logic {IDLE, BRANCH_WAIT} prefetch_state_e;

typedef enum logic [2:0] {IDLE_MULT, STEP0, STEP1, STEP2, FINISH} mult_state_e;

// ALU divider FSM state encoding
typedef enum logic [1:0] {DIV_IDLE, DIV_DIVIDE, DIV_FINISH} div_state_e;


/////////////////////////////////////////////////////////
//    ____ ____    ____            _     _             //
//   / ___/ ___|  |  _ \ ___  __ _(_)___| |_ ___ _ __  //
//  | |   \___ \  | |_) / _ \/ _` | / __| __/ _ \ '__| //
//  | |___ ___) | |  _ <  __/ (_| | \__ \ ||  __/ |    //
//   \____|____/  |_| \_\___|\__, |_|___/\__\___|_|    //
//                           |___/                     //
/////////////////////////////////////////////////////////

// CSRs mnemonics
typedef enum logic[11:0] {

  ///////////////////////////////////////////////////////
  // User CSRs
  ///////////////////////////////////////////////////////

  // None

  ///////////////////////////////////////////////////////
  // User Custom CSRs
  ///////////////////////////////////////////////////////

  // None

  ///////////////////////////////////////////////////////
  // Machine CSRs
  ///////////////////////////////////////////////////////

  // Machine trap setup
  CSR_MSTATUS        = 12'h300,
  CSR_MISA           = 12'h301,
  CSR_MIE            = 12'h304,
  CSR_MTVEC          = 12'h305,

  // Performance counters
  CSR_MCOUNTEREN     = 12'h306,
  CSR_MCOUNTINHIBIT  = 12'h320,
  CSR_MHPMEVENT3     = 12'h323,
  CSR_MHPMEVENT4     = 12'h324,
  CSR_MHPMEVENT5     = 12'h325,
  CSR_MHPMEVENT6     = 12'h326,
  CSR_MHPMEVENT7     = 12'h327,
  CSR_MHPMEVENT8     = 12'h328,
  CSR_MHPMEVENT9     = 12'h329,
  CSR_MHPMEVENT10    = 12'h32A,
  CSR_MHPMEVENT11    = 12'h32B,
  CSR_MHPMEVENT12    = 12'h32C,
  CSR_MHPMEVENT13    = 12'h32D,
  CSR_MHPMEVENT14    = 12'h32E,
  CSR_MHPMEVENT15    = 12'h32F,
  CSR_MHPMEVENT16    = 12'h330,
  CSR_MHPMEVENT17    = 12'h331,
  CSR_MHPMEVENT18    = 12'h332,
  CSR_MHPMEVENT19    = 12'h333,
  CSR_MHPMEVENT20    = 12'h334,
  CSR_MHPMEVENT21    = 12'h335,
  CSR_MHPMEVENT22    = 12'h336,
  CSR_MHPMEVENT23    = 12'h337,
  CSR_MHPMEVENT24    = 12'h338,
  CSR_MHPMEVENT25    = 12'h339,
  CSR_MHPMEVENT26    = 12'h33A,
  CSR_MHPMEVENT27    = 12'h33B,
  CSR_MHPMEVENT28    = 12'h33C,
  CSR_MHPMEVENT29    = 12'h33D,
  CSR_MHPMEVENT30    = 12'h33E,
  CSR_MHPMEVENT31    = 12'h33F,

  // Machine trap handling
  CSR_MSCRATCH       = 12'h340,
  CSR_MEPC           = 12'h341,
  CSR_MCAUSE         = 12'h342,
  CSR_MTVAL          = 12'h343,
  CSR_MIP            = 12'h344,

  // Physical memory protection (PMP)
  CSR_PMPCFG0        = 12'h3A0,         // Not included (USE_PMP = 0)
  CSR_PMPCFG1        = 12'h3A1,         // Not included (USE_PMP = 0)
  CSR_PMPCFG2        = 12'h3A2,         // Not included (USE_PMP = 0)
  CSR_PMPCFG3        = 12'h3A3,         // Not included (USE_PMP = 0)
  CSR_PMPADDR0       = 12'h3B0,         // Not included (USE_PMP = 0)
  CSR_PMPADDR1       = 12'h3B1,         // Not included (USE_PMP = 0)
  CSR_PMPADDR2       = 12'h3B2,         // Not included (USE_PMP = 0)
  CSR_PMPADDR3       = 12'h3B3,         // Not included (USE_PMP = 0)
  CSR_PMPADDR4       = 12'h3B4,         // Not included (USE_PMP = 0)
  CSR_PMPADDR5       = 12'h3B5,         // Not included (USE_PMP = 0)
  CSR_PMPADDR6       = 12'h3B6,         // Not included (USE_PMP = 0)
  CSR_PMPADDR7       = 12'h3B7,         // Not included (USE_PMP = 0)
  CSR_PMPADDR8       = 12'h3B8,         // Not included (USE_PMP = 0)
  CSR_PMPADDR9       = 12'h3B9,         // Not included (USE_PMP = 0)
  CSR_PMPADDR10      = 12'h3BA,         // Not included (USE_PMP = 0)
  CSR_PMPADDR11      = 12'h3BB,         // Not included (USE_PMP = 0)
  CSR_PMPADDR12      = 12'h3BC,         // Not included (USE_PMP = 0)
  CSR_PMPADDR13      = 12'h3BD,         // Not included (USE_PMP = 0)
  CSR_PMPADDR14      = 12'h3BE,         // Not included (USE_PMP = 0)
  CSR_PMPADDR15      = 12'h3BF,         // Not included (USE_PMP = 0)

  // Trigger
  CSR_TSELECT        = 12'h7A0,
  CSR_TDATA1         = 12'h7A1,
  CSR_TDATA2         = 12'h7A2,
  CSR_TDATA3         = 12'h7A3,
  CSR_TINFO          = 12'h7A4,
  CSR_MCONTEXT       = 12'h7A8,
  CSR_SCONTEXT       = 12'h7AA,

  // Debug/trace
  CSR_DCSR           = 12'h7B0,
  CSR_DPC            = 12'h7B1,

  // Debug
  CSR_DSCRATCH0      = 12'h7B2,
  CSR_DSCRATCH1      = 12'h7B3,

  // Hardware Performance Monitor
  CSR_MCYCLE         = 12'hB00,
  CSR_MINSTRET       = 12'hB02,
  CSR_MHPMCOUNTER3   = 12'hB03,
  CSR_MHPMCOUNTER4   = 12'hB04,
  CSR_MHPMCOUNTER5   = 12'hB05,
  CSR_MHPMCOUNTER6   = 12'hB06,
  CSR_MHPMCOUNTER7   = 12'hB07,
  CSR_MHPMCOUNTER8   = 12'hB08,
  CSR_MHPMCOUNTER9   = 12'hB09,
  CSR_MHPMCOUNTER10  = 12'hB0A,
  CSR_MHPMCOUNTER11  = 12'hB0B,
  CSR_MHPMCOUNTER12  = 12'hB0C,
  CSR_MHPMCOUNTER13  = 12'hB0D,
  CSR_MHPMCOUNTER14  = 12'hB0E,
  CSR_MHPMCOUNTER15  = 12'hB0F,
  CSR_MHPMCOUNTER16  = 12'hB10,
  CSR_MHPMCOUNTER17  = 12'hB11,
  CSR_MHPMCOUNTER18  = 12'hB12,
  CSR_MHPMCOUNTER19  = 12'hB13,
  CSR_MHPMCOUNTER20  = 12'hB14,
  CSR_MHPMCOUNTER21  = 12'hB15,
  CSR_MHPMCOUNTER22  = 12'hB16,
  CSR_MHPMCOUNTER23  = 12'hB17,
  CSR_MHPMCOUNTER24  = 12'hB18,
  CSR_MHPMCOUNTER25  = 12'hB19,
  CSR_MHPMCOUNTER26  = 12'hB1A,
  CSR_MHPMCOUNTER27  = 12'hB1B,
  CSR_MHPMCOUNTER28  = 12'hB1C,
  CSR_MHPMCOUNTER29  = 12'hB1D,
  CSR_MHPMCOUNTER30  = 12'hB1E,
  CSR_MHPMCOUNTER31  = 12'hB1F,

  CSR_MCYCLEH        = 12'hB80,
  CSR_MINSTRETH      = 12'hB82,
  CSR_MHPMCOUNTER3H  = 12'hB83,
  CSR_MHPMCOUNTER4H  = 12'hB84,
  CSR_MHPMCOUNTER5H  = 12'hB85,
  CSR_MHPMCOUNTER6H  = 12'hB86,
  CSR_MHPMCOUNTER7H  = 12'hB87,
  CSR_MHPMCOUNTER8H  = 12'hB88,
  CSR_MHPMCOUNTER9H  = 12'hB89,
  CSR_MHPMCOUNTER10H = 12'hB8A,
  CSR_MHPMCOUNTER11H = 12'hB8B,
  CSR_MHPMCOUNTER12H = 12'hB8C,
  CSR_MHPMCOUNTER13H = 12'hB8D,
  CSR_MHPMCOUNTER14H = 12'hB8E,
  CSR_MHPMCOUNTER15H = 12'hB8F,
  CSR_MHPMCOUNTER16H = 12'hB90,
  CSR_MHPMCOUNTER17H = 12'hB91,
  CSR_MHPMCOUNTER18H = 12'hB92,
  CSR_MHPMCOUNTER19H = 12'hB93,
  CSR_MHPMCOUNTER20H = 12'hB94,
  CSR_MHPMCOUNTER21H = 12'hB95,
  CSR_MHPMCOUNTER22H = 12'hB96,
  CSR_MHPMCOUNTER23H = 12'hB97,
  CSR_MHPMCOUNTER24H = 12'hB98,
  CSR_MHPMCOUNTER25H = 12'hB99,
  CSR_MHPMCOUNTER26H = 12'hB9A,
  CSR_MHPMCOUNTER27H = 12'hB9B,
  CSR_MHPMCOUNTER28H = 12'hB9C,
  CSR_MHPMCOUNTER29H = 12'hB9D,
  CSR_MHPMCOUNTER30H = 12'hB9E,
  CSR_MHPMCOUNTER31H = 12'hB9F,

  CSR_CYCLE          = 12'hC00,
  CSR_INSTRET        = 12'hC02,
  CSR_HPMCOUNTER3    = 12'hC03,
  CSR_HPMCOUNTER4    = 12'hC04,
  CSR_HPMCOUNTER5    = 12'hC05,
  CSR_HPMCOUNTER6    = 12'hC06,
  CSR_HPMCOUNTER7    = 12'hC07,
  CSR_HPMCOUNTER8    = 12'hC08,
  CSR_HPMCOUNTER9    = 12'hC09,
  CSR_HPMCOUNTER10   = 12'hC0A,
  CSR_HPMCOUNTER11   = 12'hC0B,
  CSR_HPMCOUNTER12   = 12'hC0C,
  CSR_HPMCOUNTER13   = 12'hC0D,
  CSR_HPMCOUNTER14   = 12'hC0E,
  CSR_HPMCOUNTER15   = 12'hC0F,
  CSR_HPMCOUNTER16   = 12'hC10,
  CSR_HPMCOUNTER17   = 12'hC11,
  CSR_HPMCOUNTER18   = 12'hC12,
  CSR_HPMCOUNTER19   = 12'hC13,
  CSR_HPMCOUNTER20   = 12'hC14,
  CSR_HPMCOUNTER21   = 12'hC15,
  CSR_HPMCOUNTER22   = 12'hC16,
  CSR_HPMCOUNTER23   = 12'hC17,
  CSR_HPMCOUNTER24   = 12'hC18,
  CSR_HPMCOUNTER25   = 12'hC19,
  CSR_HPMCOUNTER26   = 12'hC1A,
  CSR_HPMCOUNTER27   = 12'hC1B,
  CSR_HPMCOUNTER28   = 12'hC1C,
  CSR_HPMCOUNTER29   = 12'hC1D,
  CSR_HPMCOUNTER30   = 12'hC1E,
  CSR_HPMCOUNTER31   = 12'hC1F,

  CSR_CYCLEH         = 12'hC80,
  CSR_INSTRETH       = 12'hC82,
  CSR_HPMCOUNTER3H   = 12'hC83,
  CSR_HPMCOUNTER4H   = 12'hC84,
  CSR_HPMCOUNTER5H   = 12'hC85,
  CSR_HPMCOUNTER6H   = 12'hC86,
  CSR_HPMCOUNTER7H   = 12'hC87,
  CSR_HPMCOUNTER8H   = 12'hC88,
  CSR_HPMCOUNTER9H   = 12'hC89,
  CSR_HPMCOUNTER10H  = 12'hC8A,
  CSR_HPMCOUNTER11H  = 12'hC8B,
  CSR_HPMCOUNTER12H  = 12'hC8C,
  CSR_HPMCOUNTER13H  = 12'hC8D,
  CSR_HPMCOUNTER14H  = 12'hC8E,
  CSR_HPMCOUNTER15H  = 12'hC8F,
  CSR_HPMCOUNTER16H  = 12'hC90,
  CSR_HPMCOUNTER17H  = 12'hC91,
  CSR_HPMCOUNTER18H  = 12'hC92,
  CSR_HPMCOUNTER19H  = 12'hC93,
  CSR_HPMCOUNTER20H  = 12'hC94,
  CSR_HPMCOUNTER21H  = 12'hC95,
  CSR_HPMCOUNTER22H  = 12'hC96,
  CSR_HPMCOUNTER23H  = 12'hC97,
  CSR_HPMCOUNTER24H  = 12'hC98,
  CSR_HPMCOUNTER25H  = 12'hC99,
  CSR_HPMCOUNTER26H  = 12'hC9A,
  CSR_HPMCOUNTER27H  = 12'hC9B,
  CSR_HPMCOUNTER28H  = 12'hC9C,
  CSR_HPMCOUNTER29H  = 12'hC9D,
  CSR_HPMCOUNTER30H  = 12'hC9E,
  CSR_HPMCOUNTER31H  = 12'hC9F,

  // Machine information
  CSR_MVENDORID      = 12'hF11,
  CSR_MARCHID        = 12'hF12,
  CSR_MIMPID         = 12'hF13,
  CSR_MHARTID        = 12'hF14
} csr_num_e;

// CSR operations

parameter CSR_OP_WIDTH = 2;

typedef enum logic [CSR_OP_WIDTH-1:0]
{
 CSR_OP_READ  = 2'b00,
 CSR_OP_WRITE = 2'b01,
 CSR_OP_SET   = 2'b10,
 CSR_OP_CLEAR = 2'b11
} csr_opcode_e;

// CSR interrupt pending/enable bits
parameter int unsigned CSR_MSIX_BIT      = 3;
parameter int unsigned CSR_MTIX_BIT      = 7;
parameter int unsigned CSR_MEIX_BIT      = 11;
parameter int unsigned CSR_MFIX_BIT_LOW  = 16;
parameter int unsigned CSR_MFIX_BIT_HIGH = 31;

// SPR for debugger, not accessible by CPU
parameter SP_DVR0       = 16'h3000;
parameter SP_DCR0       = 16'h3008;
parameter SP_DMR1       = 16'h3010;
parameter SP_DMR2       = 16'h3011;

parameter SP_DVR_MSB = 8'h00;
parameter SP_DCR_MSB = 8'h01;
parameter SP_DMR_MSB = 8'h02;
parameter SP_DSR_MSB = 8'h04;

// Privileged mode
typedef enum logic[1:0] {
  PRIV_LVL_M = 2'b11,
  PRIV_LVL_H = 2'b10,
  PRIV_LVL_S = 2'b01,
  PRIV_LVL_U = 2'b00
} PrivLvl_t;

// Machine Vendor ID - OpenHW JEDEC ID is '2 decimal (bank 13)'
parameter MVENDORID_OFFSET = 7'h2;      // Final byte without parity bit
parameter MVENDORID_BANK = 25'hC;       // Number of continuation codes

// Machine Architecture ID (https://github.com/riscv/riscv-isa-manual/blob/master/marchid.md)
parameter MARCHID = 32'h4;

parameter MTVEC_MODE        = 2'b01;
parameter NUM_HPM_EVENTS    =   16;

parameter MAX_N_PMP_ENTRIES = 16;
parameter MAX_N_PMP_CFG     =  4;


parameter MSTATUS_UIE_BIT      = 0;
parameter MSTATUS_SIE_BIT      = 1;
parameter MSTATUS_MIE_BIT      = 3;
parameter MSTATUS_UPIE_BIT     = 4;
parameter MSTATUS_SPIE_BIT     = 5;
parameter MSTATUS_MPIE_BIT     = 7;
parameter MSTATUS_SPP_BIT      = 8;
parameter MSTATUS_MPP_BIT_HIGH = 12;
parameter MSTATUS_MPP_BIT_LOW  = 11;
parameter MSTATUS_MPRV_BIT     = 17;

// misa
parameter logic [1:0] MXL = 2'd1; // M-XLEN: XLEN in M-Mode for RV32

parameter MHPMCOUNTER_WIDTH  = 64;
// Types for packed struct CSRs
typedef struct packed {
  logic [31:18] zero4; // Reserved, hardwired zero
  logic         mprv; // hardwired zero
  logic [16:13] zero3; // Unimplemented, hardwired zero
  logic [12:11] mpp; // Hardwire to 2'b11 when user mode is not enabled
  logic [10:8]  zero2;
  logic         mpie;
  logic [6:5]   zero1;
  logic         upie; // Tie to zero
  logic         mie;
  logic [2:1]   zero0; // Unimplemented, hardwired zero
  logic         uie; // Tie to zero when user mode is not enabled

} Status_t;
  
// Debug Cause
parameter DBG_CAUSE_NONE       = 3'h0;
parameter DBG_CAUSE_EBREAK     = 3'h1;
parameter DBG_CAUSE_TRIGGER    = 3'h2;
parameter DBG_CAUSE_HALTREQ    = 3'h3;
parameter DBG_CAUSE_STEP       = 3'h4;
parameter DBG_CAUSE_RSTHALTREQ = 3'h5;

// Debug module
parameter DBG_SETS_W = 6;

parameter DBG_SETS_IRQ    = 5;
parameter DBG_SETS_ECALL  = 4;
parameter DBG_SETS_EILL   = 3;
parameter DBG_SETS_ELSU   = 2;
parameter DBG_SETS_EBRK   = 1;
parameter DBG_SETS_SSTE   = 0;

parameter DBG_CAUSE_HALT   = 6'h1F;

// Constants for the dcsr.xdebugver fields
typedef enum logic[3:0] {
   XDEBUGVER_NO     = 4'd0, // no external debug support
   XDEBUGVER_STD    = 4'd4, // external debug according to RISC-V debug spec
   XDEBUGVER_NONSTD = 4'd15 // debug not conforming to RISC-V debug spec
} x_debug_ver_e;

// Trigger types
typedef enum logic [3:0] {
  TTYPE_MCONTROL = 4'h2,
  TTYPE_ICOUNT = 4'h3,
  TTYPE_ITRIGGER = 4'h4,
  TTYPE_ETRIGGER = 4'h5
} trigger_type_e;

typedef struct packed{
    logic [31:28] xdebugver;
    logic [27:16] zero2;
    logic         ebreakm;
    logic         zero1;
    logic         ebreaks;
    logic         ebreaku;
    logic         stepie;
    logic         stopcount;
    logic         stoptime;
    logic [8:6]   cause;
    logic         zero0;
    logic         mprven;
    logic         nmip;
    logic         step;
    PrivLvl_t     prv;
} Dcsr_t;

typedef struct packed {
  logic           interrupt;
  logic [30:5]    zero0;
  logic [4:0]     exception_code;
} Mcause_t;

typedef struct packed {
  logic [31:8] addr;
  logic [7:2]  zero0;
  logic [1:0]  mode;
} Mtvec_t;


parameter Dcsr_t DCSR_RESET_VAL = '{
  xdebugver : XDEBUGVER_STD,
  cause:      DBG_CAUSE_NONE,
  prv:        PRIV_LVL_M,
  default:    '0}; 

parameter Mtvec_t MTVEC_RESET_VAL = '{
  addr: 'd0,
  zero0: 'd0,
  mode:  MTVEC_MODE};

parameter Status_t MSTATUS_RESET_VAL = '{
  zero4: 'b0, // Reserved, hardwired zero
  mprv: 1'b0, // hardwired zero
  zero3: 'b0, // Unimplemented, hardwired zero
  mpp: PRIV_LVL_M, // Hardwire to 2'b11 when user mode is not enabled
  zero2: 'b0,
  mpie: 1'b0,
  zero1: 'b0,
  upie: 1'b0, // Tie to zero
  mie: 1'b0,
  zero0: 'b0, // Unimplemented, hardwired zero
  uie: 1'b0, // Tie to zero when user mode is not enabled
  default: 'b0};

parameter logic [31:0] TMATCH_CONTROL_RST_VAL = {
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
  1'b0,      // execute : match instruction address
  1'b0,                  // store   : not supported
  1'b0};                 // load    : not supported 


///////////////////////////////////////////////
//   ___ ____    ____  _                     //
//  |_ _|  _ \  / ___|| |_ __ _  __ _  ___   //
//   | || | | | \___ \| __/ _` |/ _` |/ _ \  //
//   | || |_| |  ___) | || (_| | (_| |  __/  //
//  |___|____/  |____/ \__\__,_|\__, |\___|  //
//                              |___/        //
///////////////////////////////////////////////

// Register file read/write ports
parameter REGFILE_NUM_READ_PORTS  = 2;
parameter REGFILE_NUM_WRITE_PORTS = 2;

// Address width of register file
parameter REGFILE_ADDR_WIDTH = 5;

// Data width of register file
parameter REGFILE_DATA_WIDTH = 32;

// Number of regfile integer registers
parameter REGFILE_NUM_WORDS = 2**(REGFILE_ADDR_WIDTH);

// Register file address type
typedef logic [REGFILE_ADDR_WIDTH-1:0] rf_addr_t;

// Register file data type
typedef logic [REGFILE_DATA_WIDTH-1:0] rf_data_t;

// forwarding operand mux
parameter SEL_REGFILE      = 2'b00;
parameter SEL_FW_EX        = 2'b01;
parameter SEL_FW_WB        = 2'b10;

// operand a selection
parameter OP_A_REGA_OR_FWD = 3'b000;
parameter OP_A_CURRPC      = 3'b001;
parameter OP_A_IMM         = 3'b010;
parameter OP_A_REGB_OR_FWD = 3'b011;
parameter OP_A_REGC_OR_FWD = 3'b100;

// immediate a selection
parameter IMMA_Z      = 1'b0;
parameter IMMA_ZERO   = 1'b1;

// operand b selection
parameter OP_B_REGB_OR_FWD = 3'b000;
parameter OP_B_REGC_OR_FWD = 3'b001;
parameter OP_B_IMM         = 3'b010;
parameter OP_B_REGA_OR_FWD = 3'b011;

// immediate b selection
parameter IMMB_I      = 4'b0000;
parameter IMMB_S      = 4'b0001;
parameter IMMB_U      = 4'b0010;
parameter IMMB_PCINCR = 4'b0011;
parameter IMMB_CLIP   = 4'b1001;

// bit mask selection
parameter BMASK_A_ZERO = 1'b0;
parameter BMASK_A_S3   = 1'b1;

parameter BMASK_B_S2   = 2'b00;
parameter BMASK_B_S3   = 2'b01;
parameter BMASK_B_ZERO = 2'b10;
parameter BMASK_B_ONE  = 2'b11;

parameter BMASK_A_REG  = 1'b0;
parameter BMASK_A_IMM  = 1'b1;
parameter BMASK_B_REG  = 1'b0;
parameter BMASK_B_IMM  = 1'b1;


// multiplication immediates
parameter MIMM_ZERO    = 1'b0;
parameter MIMM_S3      = 1'b1;

// operand c selection
parameter OP_C_REGC_OR_FWD = 2'b00;
parameter OP_C_REGB_OR_FWD = 2'b01;
parameter OP_C_JT          = 2'b10;

// branch types
parameter BRANCH_NONE = 2'b00;
parameter BRANCH_JAL  = 2'b01;
parameter BRANCH_JALR = 2'b10;
parameter BRANCH_COND = 2'b11; // conditional branches

// jump target mux
parameter JT_JAL  = 2'b01;
parameter JT_JALR = 2'b10;
parameter JT_COND = 2'b11;

// Atomic operations
parameter AMO_LR   = 5'b00010;
parameter AMO_SC   = 5'b00011;
parameter AMO_SWAP = 5'b00001;
parameter AMO_ADD  = 5'b00000;
parameter AMO_XOR  = 5'b00100;
parameter AMO_AND  = 5'b01100;
parameter AMO_OR   = 5'b01000;
parameter AMO_MIN  = 5'b10000;
parameter AMO_MAX  = 5'b10100;
parameter AMO_MINU = 5'b11000;
parameter AMO_MAXU = 5'b11100;

// ID/EX pipeline
typedef struct packed {

  // ALU Control
  logic         alu_en;
  alu_opcode_e  alu_operator;      
  logic [31:0]  alu_operand_a;     
  logic [31:0]  alu_operand_b;     
  logic [31:0]  alu_operand_c;     

  // Multiplier control
  logic         mult_en;           
  mul_opcode_e  mult_operator;     
  logic [31:0]  mult_operand_a;    
  logic [31:0]  mult_operand_b;    
  logic [31:0]  mult_operand_c;    
  logic         mult_sel_subword;  
  logic [ 1:0]  mult_signed_mode;  

  // Register write control
  logic         rf_we;
  rf_addr_t     rf_waddr; 

  logic prepost_useincr;

  // CSR control
  logic         csr_access;
  csr_opcode_e  csr_op;            

  // Data Memory Control:  From ID stage (id-ex pipe) <--> load store unit
  logic         data_req;          
  logic         data_we;           
  logic [1:0]   data_type;         
  logic [1:0]   data_sign_ext;     
  logic [1:0]   data_reg_offset;   
  logic         data_misaligned;   
  logic [5:0]   data_atop;             

  // PC of last executed branch
  logic [31:0]  pc;

  // Branch target
  logic         branch_in_ex;
} id_ex_pipe_t;

// EX/WB pipeline
typedef struct packed {
  logic         rf_we;
  rf_addr_t     rf_waddr;
  logic [31:0]  rf_wdata;
} ex_wb_pipe_t;

///////////////////////////////////////////////
//   ___ _____   ____  _                     //
//  |_ _|  ___| / ___|| |_ __ _  __ _  ___   //
//   | || |_    \___ \| __/ _` |/ _` |/ _ \  //
//   | ||  _|    ___) | || (_| | (_| |  __/  //
//  |___|_|     |____/ \__\__,_|\__, |\___|  //
//                              |___/        //
///////////////////////////////////////////////

// PC mux selector defines
typedef enum logic[2:0] {
  PC_BOOT      = 3'b000,
  PC_JUMP      = 3'b010,
  PC_BRANCH    = 3'b011,
  PC_EXCEPTION = 3'b100,
  PC_FENCEI    = 3'b001,
  PC_MRET      = 3'b101,
  PC_URET      = 3'b110,
  PC_DRET      = 3'b111
} pc_mux_e;


// Exception PC mux selector defines
typedef enum logic[1:0] {
  EXC_PC_EXCEPTION = 2'b00,
  EXC_PC_IRQ       = 2'b01,
  EXC_PC_DBD       = 2'b10,
  EXC_PC_DBE       = 2'b11
} exc_pc_mux_e;

// Exception Cause
parameter EXC_CAUSE_INSTR_FAULT  = 5'h01;
parameter EXC_CAUSE_ILLEGAL_INSN = 5'h02;
parameter EXC_CAUSE_BREAKPOINT   = 5'h03;
parameter EXC_CAUSE_LOAD_FAULT   = 5'h05;
parameter EXC_CAUSE_STORE_FAULT  = 5'h07;
parameter EXC_CAUSE_ECALL_UMODE  = 5'h08;
parameter EXC_CAUSE_ECALL_MMODE  = 5'h0B;

// Interrupt mask
parameter IRQ_MASK = 32'hFFFF0888;

// Instruction aligner FSM state encoding
typedef enum logic [2:0]  {ALIGNED32,
                           MISALIGNED32,
                           MISALIGNED16,
                           BRANCH_MISALIGNED,
                           WAIT_VALID_BRANCH} aligner_state_e;

// IF/ID pipeline
typedef struct packed {

  logic        instr_valid;
  logic [31:0] instr_rdata;
  logic        is_fetch_failed;
  logic [31:0] pc;
  logic        is_compressed;
  logic        illegal_c_insn;
} if_id_pipe_t;
  
  
  ///////////////////////////
  //                       //
  //    /\/\ (_)___  ___   //
  //   /    \| / __|/ __|  //
  //  / /\/\ \ \__ \ (__   //
  //  \/    \/_|___/\___|  //
  //                       //
  ///////////////////////////

  // OBI interface FSM state encoding
  typedef enum logic {TRANSPARENT, REGISTERED} obi_if_state_e;

  
  
  
  // OBI bus and internal data types

  parameter INSTR_ADDR_WIDTH = 32;
  parameter INSTR_DATA_WIDTH = 32;
  parameter DATA_ADDR_WIDTH = 32;
  parameter DATA_DATA_WIDTH = 32;
  
  typedef struct packed {
    logic [INSTR_ADDR_WIDTH-1:0] addr;
  } inst_req_t;

  typedef struct packed {
    logic [INSTR_DATA_WIDTH-1:0] rdata;
    logic                        err;
  } inst_resp_t;

  typedef struct packed {
    logic [DATA_ADDR_WIDTH-1:0]     addr;
    logic [5:0]                     atop;
    logic                           we;
    logic [(DATA_DATA_WIDTH/8)-1:0] be;
    logic [DATA_DATA_WIDTH-1:0]     wdata;
 } data_req_t;

 typedef struct packed {
    logic [DATA_DATA_WIDTH-1:0] rdata;
    logic                       err;
    logic                       exokay;
 } data_resp_t;

endpackage
