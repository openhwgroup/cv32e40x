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

  typedef enum logic [6:0] {
                            OPCODE_SYSTEM    = 7'h73,
                            OPCODE_FENCE     = 7'h0f,
                            OPCODE_OP        = 7'h33,
                            OPCODE_OPIMM     = 7'h13,
                            OPCODE_STORE     = 7'h23,
                            OPCODE_LOAD      = 7'h03,
                            OPCODE_BRANCH    = 7'h63,
                            OPCODE_JALR      = 7'h67,
                            OPCODE_JAL       = 7'h6f,
                            OPCODE_AUIPC     = 7'h17,
                            OPCODE_LUI       = 7'h37,
                            OPCODE_AMO       = 7'h2F
                            } opcode_e;
                                                                       
//////////////////////////////////////////////////////////////////////////////
//      _    _    _   _    ___                       _   _                  //
//     / \  | |  | | | |  / _ \ _ __   ___ _ __ __ _| |_(_) ___  _ __  ___  //
//    / _ \ | |  | | | | | | | | '_ \ / _ \ '__/ _` | __| |/ _ \| '_ \/ __| //
//   / ___ \| |__| |_| | | |_| | |_) |  __/ | | (_| | |_| | (_) | | | \__ \ //
//  /_/   \_\_____\___/   \___/| .__/ \___|_|  \__,_|\__|_|\___/|_| |_|___/ //
//                             |_|                                          //
//////////////////////////////////////////////////////////////////////////////

parameter ALU_OP_WIDTH = 6;

  // TODO:low Could a smarter encoding be used here?
typedef enum logic [ALU_OP_WIDTH-1:0]
{
 ALU_ADD   = 6'b001000,
 ALU_SUB   = 6'b001001,

 ALU_XOR   = 6'b001111,
 ALU_OR    = 6'b001110,
 ALU_AND   = 6'b000110,

 // Shifts
 ALU_SRA   = 6'b000100,
 ALU_SRL   = 6'b000101,
 ALU_SLL   = 6'b000111,

 // Comparisons
 ALU_LTS   = 6'b000000,
 ALU_LTU   = 6'b000001,
 ALU_GES   = 6'b001010,
 ALU_GEU   = 6'b001011,
 ALU_EQ    = 6'b001100,
 ALU_NE    = 6'b001101,

 // Set Lower Than operations
 ALU_SLTS  = 6'b000010,
 ALU_SLTU  = 6'b000011,

 // B, Zba
 ALU_B_SH1ADD   = 6'b100000,
 ALU_B_SH2ADD   = 6'b100001,
 ALU_B_SH3ADD   = 6'b100010,

 // B, Zbb
 ALU_B_CLZ      = 6'b100011,
 ALU_B_CTZ      = 6'b100100,
 ALU_B_CPOP     = 6'b100101,
 ALU_B_MIN      = 6'b100110,
 ALU_B_MINU     = 6'b100111,
 ALU_B_MAX      = 6'b101000,
 ALU_B_MAXU     = 6'b101001,
 ALU_B_SEXT_B   = 6'b101010,
 ALU_B_SEXT_H   = 6'b101011,
 ALU_B_ANDN     = 6'b101100,
 ALU_B_ORN      = 6'b101101,
 ALU_B_XNOR     = 6'b101110,
 ALU_B_ROR      = 6'b101111,
 ALU_B_ROL      = 6'b110000,
 ALU_B_REV8     = 6'b110001,
 ALU_B_ORC_B    = 6'b110010,

 // B, Zbs
 ALU_B_BSET     = 6'b110011,
 ALU_B_BCLR     = 6'b110100,
 ALU_B_BINV     = 6'b110101,
 ALU_B_BEXT     = 6'b110110

} alu_opcode_e;


parameter MUL_OP_WIDTH = 1;

typedef enum logic [MUL_OP_WIDTH-1:0]
{
 MUL_M32 = 1'b0,
 MUL_H   = 1'b1
 } mul_opcode_e;

parameter DIV_OP_WIDTH = 2;

typedef enum logic [DIV_OP_WIDTH-1:0]
{

 DIV_DIVU= 2'b00,
 DIV_DIV = 2'b01,
 DIV_REMU= 2'b10,
 DIV_REM = 2'b11

 } div_opcode_e;

// FSM state encoding
typedef enum logic [2:0] { RESET, BOOT_SET, FUNCTIONAL, SLEEP, DEBUG_TAKEN} ctrl_state_e;



// Debug FSM state encoding
// State encoding done one-hot to ensure that debug_havereset_o, debug_running_o, debug_halted_o
// will come directly from flip-flops. *_INDEX and debug_state_e encoding must match

parameter HAVERESET_INDEX = 0;
parameter RUNNING_INDEX = 1;
parameter HALTED_INDEX = 2;

typedef enum logic [2:0] { HAVERESET = 3'b001, RUNNING = 3'b010, HALTED = 3'b100 } debug_state_e;

typedef enum logic {IDLE, BRANCH_WAIT} prefetch_state_e;

typedef enum logic [1:0] {MUL_ALBL, MUL_ALBH, MUL_AHBL, MUL_AHBH} mul_state_e;

// ALU divider FSM state encoding
typedef enum logic [1:0] {DIV_IDLE, DIV_DIVIDE, DIV_DUMMY, DIV_FINISH} div_state_e;


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
parameter MARCHID = 32'h14;

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


  typedef struct packed {
    logic        rotate;
    logic        rshift;
    logic        arithmetic;
    logic        operand_tieoff;
  } Alu_shifter_t;

// Debug Cause
parameter DBG_CAUSE_NONE       = 3'h0;
parameter DBG_CAUSE_EBREAK     = 3'h1;
parameter DBG_CAUSE_TRIGGER    = 3'h2;
parameter DBG_CAUSE_HALTREQ    = 3'h3;
parameter DBG_CAUSE_STEP       = 3'h4;
parameter DBG_CAUSE_RSTHALTREQ = 3'h5;

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
parameter REGFILE_NUM_WRITE_PORTS = 1;

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
typedef enum logic[1:0] {
                         SEL_REGFILE = 2'b00,
                         SEL_FW_EX   = 2'b01,
                         SEL_FW_WB   = 2'b10
                         } op_fw_mux_e;

typedef enum logic {
                         SELJ_REGFILE = 1'b0,
                         SELJ_FW_WB   = 1'b1
                         } jalr_fw_mux_e;

// operand a selection
typedef enum logic[1:0] {
                         OP_A_REGA_OR_FWD = 2'b00,
                         OP_A_CURRPC      = 2'b01,
                         OP_A_IMM         = 2'b10,
                         OP_A_REGB_OR_FWD = 2'b11
                         } alu_op_a_mux_e;


// immediate a selection
typedef enum logic {
                    IMMA_Z      = 1'b0,
                    IMMA_ZERO   = 1'b1
                    } imm_a_mux_e;


// operand b selection
typedef enum logic[1:0] {
                         OP_B_REGB_OR_FWD = 2'b00,
                         OP_B_IMM         = 2'b10,
                         OP_B_REGA_OR_FWD = 2'b11
                         } alu_op_b_mux_e;

// immediate b selection
typedef enum logic[1:0] {
                         IMMB_I      = 2'b00,
                         IMMB_S      = 2'b01,
                         IMMB_U      = 2'b10,
                         IMMB_PCINCR = 2'b11
                         } imm_b_mux_e;
  
// operand c selection
typedef enum logic[1:0] {
                         OP_C_FWD         = 2'b00,
                         OP_C_REGB_OR_FWD = 2'b01,
                         OP_C_BCH         = 2'b10
                         } op_c_mux_e;

// branch types
parameter BRANCH_NONE = 2'b00;
parameter BRANCH_JAL  = 2'b01;
parameter BRANCH_JALR = 2'b10;
parameter BRANCH_COND = 2'b11; // conditional branches

// jump target mux
typedef enum logic[1:0] {
                         JT_JAL  = 2'b01,
                         JT_JALR = 2'b10,
                         JT_COND = 2'b11
                         } jt_mux_e;


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


// Decoder control signals
typedef struct packed {
  logic [1:0]                        ctrl_transfer_insn;
  jt_mux_e                           ctrl_transfer_target_mux_sel;
  logic                              alu_en;
  alu_opcode_e                       alu_operator;
  alu_op_a_mux_e                     alu_op_a_mux_sel;
  alu_op_b_mux_e                     alu_op_b_mux_sel;
  op_c_mux_e                         op_c_mux_sel;
  imm_a_mux_e                        imm_a_mux_sel;
  imm_b_mux_e                        imm_b_mux_sel;
  Alu_shifter_t                      alu_shifter;
  logic                              mul_en;
  mul_opcode_e                       mul_operator;
  logic [1:0]                        mul_signed_mode;
  logic                              div_en;
  div_opcode_e                       div_operator;
  logic [REGFILE_NUM_READ_PORTS-1:0] rf_re;
  logic                              rf_we;
  logic                              csr_en;
  csr_opcode_e                       csr_op;
  logic                              lsu_en;
  logic                              lsu_we;
  logic [1:0]                        lsu_type;
  logic                              lsu_sign_ext;
  logic [1:0]                        lsu_reg_offset;
  logic [5:0]                        lsu_atop;
  logic                              lsu_prepost_useincr;
  logic                              mret_insn;
  logic                              dret_insn;
  logic                              illegal_insn;
  logic                              ebrk_insn;
  logic                              ecall_insn;
  logic                              wfi_insn;
  logic                              fencei_insn;
} decoder_ctrl_t;

  parameter decoder_ctrl_t DECODER_CTRL_ILLEGAL_INSN =  '{ctrl_transfer_insn           : BRANCH_NONE,
                                                          ctrl_transfer_target_mux_sel : JT_JAL,
                                                          alu_en                       : 1'b0,
                                                          alu_operator                 : ALU_SLTU,
                                                          alu_op_a_mux_sel             : OP_A_REGA_OR_FWD,
                                                          alu_op_b_mux_sel             : OP_B_REGB_OR_FWD,
                                                          op_c_mux_sel                 : OP_C_FWD,
                                                          imm_a_mux_sel                : IMMA_ZERO,
                                                          imm_b_mux_sel                : IMMB_I,
                                                          alu_shifter                  : 4'b0000,
                                                          mul_en                       : 1'b0,
                                                          mul_operator                 : MUL_M32,
                                                          mul_signed_mode              : 2'b00,
                                                          div_en                       : 1'b0,
                                                          div_operator                 : DIV_DIVU,
                                                          rf_re                        : 2'b00,
                                                          rf_we                        : 1'b0,
                                                          csr_en                       : 1'b0,
                                                          csr_op                       : CSR_OP_READ,
                                                          lsu_en                       : 1'b0,
                                                          lsu_we                       : 1'b0,
                                                          lsu_type                     : 2'b00,
                                                          lsu_sign_ext                 : 1'b0,
                                                          lsu_reg_offset               : 2'b00,
                                                          lsu_atop                     : 6'b000000,
                                                          lsu_prepost_useincr          : 1'b1,
                                                          mret_insn                    : 1'b0,
                                                          dret_insn                    : 1'b0,
                                                          illegal_insn                 : 1'b1,
                                                          ebrk_insn                    : 1'b0,
                                                          ecall_insn                   : 1'b0,
                                                          wfi_insn                     : 1'b0,
                                                          fencei_insn                  : 1'b0
                                                          };

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
parameter EXC_CAUSE_INSTR_FAULT     = 5'h01;
parameter EXC_CAUSE_ILLEGAL_INSN    = 5'h02;
parameter EXC_CAUSE_BREAKPOINT      = 5'h03;
parameter EXC_CAUSE_LOAD_FAULT      = 5'h05;
parameter EXC_CAUSE_STORE_FAULT     = 5'h07;
parameter EXC_CAUSE_ECALL_UMODE     = 5'h08;
parameter EXC_CAUSE_ECALL_MMODE     = 5'h0B;
parameter EXC_CAUSE_INSTR_BUS_FAULT = 5'h18;

// Interrupt mask
parameter IRQ_MASK = 32'hFFFF0888;
  

////////////////////////////
//                        //
//    /\/\    / _ \/\ /\  //
//   /    \  / /_)/ / \ \ //
//  / /\/\ \/ ___/\ \_/ / //
//  \/    \/\/     \___/  //
//                        //
////////////////////////////

// PMA region config
// word_addr_low/high: Address boundaries, containing word aligned 34-bit address (address[33:2])
// main:               Region is defined as main memory (as opposed to I/O memory)
// bufferable:         Transfers in this region are bufferable
// cacheable:          Transfers in this region are cacheable
// atomic:             This region supports atomic transfers
typedef struct packed {
  logic [31:0] word_addr_low;
  logic [31:0] word_addr_high;
  logic        main;
  logic        bufferable;
  logic        cacheable;
  logic        atomic;
} pma_region_t;

// Default attribution when PMA is not configured (PMA_NUM_REGIONS=0) (Address is don't care)
parameter pma_region_t NO_PMA_R_DEFAULT = '{word_addr_low   : 0, 
                                            word_addr_high  : 0,
                                            main            : 1'b1,
                                            bufferable      : 1'b0,
                                            cacheable       : 1'b0,
                                            atomic          : 1'b1};
  
// Default attribution when PMA is configured (Address is don't care)
parameter pma_region_t PMA_R_DEFAULT = '{word_addr_low   : 0, 
                                         word_addr_high  : 0,
                                         main            : 1'b0,
                                         bufferable      : 1'b0,
                                         cacheable       : 1'b0,
                                         atomic          : 1'b0};

// MPU status. Used for PMA and PMP
typedef enum logic [1:0] {
                          MPU_OK       = 2'h0,
                          MPU_RE_FAULT = 2'h1,
                          MPU_WR_FAULT = 2'h2
                          } mpu_status_e;

typedef enum logic [2:0] {MPU_IDLE, MPU_RE_ERR_RESP, MPU_RE_ERR_WAIT, MPU_WR_ERR_RESP, MPU_WR_ERR_WAIT} mpu_state_e;
  
// OBI bus and internal data types

parameter INSTR_ADDR_WIDTH = 32;
parameter INSTR_DATA_WIDTH = 32;
parameter DATA_ADDR_WIDTH = 32;
parameter DATA_DATA_WIDTH = 32;

typedef struct packed {
  logic        req;
} obi_req_t;

typedef struct packed {
  logic        gnt;
} obi_gnt_t;

typedef struct packed {
  logic        rvalid;
} obi_rvalid_t;

typedef struct packed {
  logic [INSTR_ADDR_WIDTH-1:0] addr;
  logic [1:0]                  memtype;
  logic [2:0]                  prot;
} obi_inst_req_t;

typedef struct packed {
  logic [INSTR_DATA_WIDTH-1:0] rdata;
  logic                        err;
} obi_inst_resp_t;

typedef struct packed {
  logic [DATA_ADDR_WIDTH-1:0]     addr;
  logic [5:0]                     atop;
  logic                           we;
  logic [(DATA_DATA_WIDTH/8)-1:0] be;
  logic [DATA_DATA_WIDTH-1:0]     wdata;
  logic [1:0]                     memtype;
  logic [2:0]                     prot;
} obi_data_req_t;

typedef struct packed {
  logic [DATA_DATA_WIDTH-1:0] rdata;
  logic                       err;
  logic                       exokay;
} obi_data_resp_t;

// Data/instruction transfer bundeled with MPU status
typedef struct packed {
 obi_inst_resp_t             bus_resp;
 mpu_status_e                mpu_status;
} inst_resp_t;

// Reset value for the inst_resp_t type
parameter inst_resp_t INST_RESP_RESET_VAL = '{
  bus_resp    : '{rdata: 32'h0, err: 1'b0},
  mpu_status  : MPU_OK
}; 

// Reset value for the obi_inst_req_t type
parameter obi_inst_req_t OBI_INST_REQ_RESET_VAL = '{
  addr    : 'h0,
  memtype : 'h0,
  prot    : {PRIV_LVL_M, 1'b0}
};
  
// Data transfer bundeled with MPU status
typedef struct packed {
  obi_data_resp_t             bus_resp;
  mpu_status_e                mpu_status;
} data_resp_t;
  
// IF/ID pipeline
typedef struct packed {
  logic        instr_valid;
  inst_resp_t  instr;
  logic [31:0] pc;
  logic        is_compressed;
  logic [15:0] compressed_instr;
  logic        illegal_c_insn;
} if_id_pipe_t;

// ID/EX pipeline
typedef struct packed {

  // ALU Control
  logic         alu_en;
  alu_opcode_e  alu_operator;
  Alu_shifter_t alu_shifter;
  logic [31:0]  alu_operand_a;
  logic [31:0]  alu_operand_b;
  logic [31:0]  operand_c; // Gated with alu_en but not used by ALU

  // Multiplier control
  logic         mul_en;
  mul_opcode_e  mul_operator;
  logic [31:0]  mul_operand_a;
  logic [31:0]  mul_operand_b;
  logic [ 1:0]  mul_signed_mode;

  // Divider control
  logic         div_en;
  div_opcode_e  div_operator;
  
  // Register write control
  logic         rf_we;
  rf_addr_t     rf_waddr;

  // CSR
  logic         csr_en;
  csr_opcode_e  csr_op;

  // LSU
  logic         lsu_en;
  logic         lsu_we;
  logic [1:0]   lsu_type;
  logic         lsu_sign_ext;
  logic [1:0]   lsu_reg_offset;
  logic         lsu_misaligned;
  logic [5:0]   lsu_atop;
  logic         lsu_prepost_useincr;

  // Branch target
  logic         branch_in_ex;

  // Trigger match on insn
  logic         trigger_match;

  // Signals for exception handling etc passed on for evaluation in WB stage
  logic [31:0]  pc;
  inst_resp_t   instr;            // Contains instruction word (may be compressed),bus error status and MPU status
  logic         instr_valid;      // instruction in EX is valid
  logic         illegal_insn;
  logic         ebrk_insn;
  logic         wfi_insn;
  logic         ecall_insn;
  logic         fencei_insn;
  logic         mret_insn;
  logic         dret_insn;
} id_ex_pipe_t;

// EX/WB pipeline
typedef struct packed {
  logic         rf_we;
  rf_addr_t     rf_waddr;
  logic [31:0]  rf_wdata;

  // CSR
  logic         csr_en;
  csr_opcode_e  csr_op;
  logic [11:0]  csr_addr;
  logic [31:0]  csr_wdata;

  // LSU
  logic         lsu_en;
  mpu_status_e  lsu_mpu_status; // MPU timing on gnt, ready in EX

  // Trigger match on insn
  logic         trigger_match;

  // Signals for exception handling etc
  logic [31:0]  pc;
  inst_resp_t   instr;            // Contains instruction word (may be compressed), bus error status and MPU status
  logic         instr_valid;      // instruction in WB is valid
  logic         illegal_insn;
  logic         ebrk_insn;
  logic         wfi_insn;
  logic         ecall_insn;
  logic         fencei_insn;
  logic         mret_insn;
  logic         dret_insn;
} ex_wb_pipe_t;

// Performance counter events
typedef struct packed {
  logic                              minstret;
  logic                              load;
  logic                              store;
  logic                              jump;
  logic                              branch;
  logic                              branch_taken;
  logic                              compressed;
  logic                              jr_stall;
  logic                              imiss;
  logic                              ld_stall;
} mhpmevent_t;

// Controller Bypass outputs
typedef struct packed {
  op_fw_mux_e  operand_a_fw_mux_sel;  // Operand A forward mux sel
  op_fw_mux_e  operand_b_fw_mux_sel;  // Operand B forward mux sel
  jalr_fw_mux_e jalr_fw_mux_sel;      // Jump target forward mux sel
  logic        misaligned_stall;      // Stall due to misaligned load/store
  logic        jr_stall;              // Stall due to JR hazard (JR used result from EX or LSU result in WB)
  logic        load_stall;            // Stall due to load operation
  logic        csr_stall;
  logic        wfi_stall;
  logic        minstret_stall;        // Stall due to minstret/h read in EX
  logic        deassert_we;           // Deassert write enable for next instruction
  logic        deassert_we_special;   // Deassert write enable and special insn bits
} ctrl_byp_t;

// Controller FSM outputs
typedef struct packed {
  logic        ctrl_busy;             // Core is busy processing instructions

  // to IF stage
  logic        instr_req;             // Start fetching instructions
  logic        pc_set;                // jump to address set by pc_mux
  pc_mux_e     pc_mux;                // Selector in the Fetch stage to select the rigth PC (normal, jump ...)
  exc_pc_mux_e exc_pc_mux;            // Selects target PC for exception

  // To WB stage
  logic        block_data_addr;       // To LSU to prevent data_addr_wb_i updates between error and taken NMI
  logic        irq_ack;               // irq has been taken 
  logic [4:0]  irq_id;                // id of taken irq (to toplevel pins)
  logic [4:0]  m_exc_vec_pc_mux;      // id of taken irq (to IF, EXC_PC_MUX, zeroed if mtvec_mode==0)

  // Debug outputs
  logic        debug_mode;           // Flag signalling we are in debug mode
  logic [2:0]  debug_cause;          // cause of debug entry
  logic        debug_csr_save;       // Update debug CSRs
  logic        debug_wfi_no_sleep;   // Debug prevents core from sleeping after WFI
  logic        debug_havereset;      // Signal to external debugger that we have reset
  logic        debug_running;        // Signal to external debugger that we are running (not in debug)
  logic        debug_halted;         // Signal to external debugger that we are halted (in debug mode)

  // Wakeup Signal to sleep unit
  logic        wake_from_sleep;       // Wakeup (due to irq or debug)

  // CSR signals
  logic        csr_save_if;         // Save PC from IF stage
  logic        csr_save_id;         // Save PC from ID stage
  logic        csr_save_ex;         // Save PC from EX stage (currently unused)
  logic        csr_save_wb;         // Save PC from WB stage
  logic [5:0]  csr_cause;           // CSR cause (saves to mcause CSR)
  logic        csr_restore_mret; // Restore CSR due to mret
  logic        csr_restore_dret; // Restore CSR due to dret
  logic        csr_save_cause;      // Update CSRs

  // Performance counter events
  mhpmevent_t  mhpmevent;

  // Halt signals
  logic        halt_if; // Halt IF stage
  logic        halt_id; // Halt ID stage
  logic        halt_ex; // Halt EX stage
  logic        halt_wb; // Halt WB stage

  // Kill signals
  logic        kill_if; // Kill IF stage
  logic        kill_id; // Kill ID stage
  logic        kill_ex; // Kill EX stage
  logic        kill_wb; // Kill WB stage
} ctrl_fsm_t;

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

  // Enum used for configuration of B extension
  typedef enum logic [1:0] {NONE, ZBA_ZBB_ZBS, ZBA_ZBB_ZBC_ZBS} b_ext_e;
endpackage
