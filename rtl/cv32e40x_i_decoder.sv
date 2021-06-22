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
// Engineer        Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                                                                            //
// Additional contributions by:                                               //
//                 Matthias Baer - baermatt@student.ethz.ch                   //
//                 Igor Loi - igor.loi@unibo.it                               //
//                 Sven Stucki - svstucki@student.ethz.ch                     //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                 Oivind Ekelund - oivind.ekelund@silabs.com                 //
//                                                                            //
// Design Name:    I Decoder                                                  //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Decoder for the RV32I Base Instruction set                 //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_i_decoder import cv32e40x_pkg::*;
  #(
    parameter DEBUG_TRIGGER_EN  = 1
    )
  (
   // from IF/ID pipeline
   input logic [31:0] instr_rdata_i,

   input  ctrl_fsm_t     ctrl_fsm_i,
   output decoder_ctrl_t decoder_ctrl_o
   );
  
  always_comb
  begin

    // Set default values
    decoder_ctrl_o              = DECODER_CTRL_ILLEGAL_INSN;
    decoder_ctrl_o.illegal_insn = 1'b0;
    decoder_ctrl_o.alu_en       = 1'b1;

    unique case (instr_rdata_i[6:0])

      //////////////////////////////////////
      //      _ _   _ __  __ ____  ____   //
      //     | | | | |  \/  |  _ \/ ___|  //
      //  _  | | | | | |\/| | |_) \___ \  //
      // | |_| | |_| | |  | |  __/ ___) | //
      //  \___/ \___/|_|  |_|_|   |____/  //
      //                                  //
      //////////////////////////////////////

      OPCODE_JAL: begin // Jump and Link
        decoder_ctrl_o.ctrl_transfer_target_mux_sel = JT_JAL;
        decoder_ctrl_o.ctrl_transfer_insn           = BRANCH_JAL;
        // Calculate and store PC+4
        decoder_ctrl_o.alu_op_a_mux_sel = OP_A_CURRPC;
        decoder_ctrl_o.alu_op_b_mux_sel = OP_B_IMM;
        decoder_ctrl_o.imm_b_mux_sel    = IMMB_PCINCR;
        decoder_ctrl_o.alu_operator     = ALU_ADD;
        decoder_ctrl_o.rf_we            = 1'b1;
        // Calculate jump target (= PC + UJ imm)
      end

      OPCODE_JALR: begin // Jump and Link Register

        if (instr_rdata_i[14:12] != 3'b0) begin
          decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
        end
        else begin
          decoder_ctrl_o.ctrl_transfer_target_mux_sel = JT_JALR;
          decoder_ctrl_o.ctrl_transfer_insn           = BRANCH_JALR;
          // Calculate and store PC+4
          decoder_ctrl_o.alu_op_a_mux_sel             = OP_A_CURRPC;
          decoder_ctrl_o.alu_op_b_mux_sel             = OP_B_IMM;
          decoder_ctrl_o.imm_b_mux_sel                = IMMB_PCINCR;
          decoder_ctrl_o.alu_operator                 = ALU_ADD;
          decoder_ctrl_o.rf_we                        = 1'b1;
          // Calculate jump target (                  = RS1 + I imm)
          decoder_ctrl_o.rf_re[0]                     = 1'b1;
        end

      end

      OPCODE_BRANCH: begin // Branch
        decoder_ctrl_o.ctrl_transfer_target_mux_sel = JT_COND;
        decoder_ctrl_o.ctrl_transfer_insn           = BRANCH_COND;
        decoder_ctrl_o.op_c_mux_sel                 = OP_C_BCH;
        decoder_ctrl_o.rf_re[0]                     = 1'b1;
        decoder_ctrl_o.rf_re[1]                     = 1'b1;
        
        unique case (instr_rdata_i[14:12])
          3'b000: decoder_ctrl_o.alu_operator = ALU_EQ;
          3'b001: decoder_ctrl_o.alu_operator = ALU_NE;
          3'b100: decoder_ctrl_o.alu_operator = ALU_LTS;
          3'b101: decoder_ctrl_o.alu_operator = ALU_GES;
          3'b110: decoder_ctrl_o.alu_operator = ALU_LTU;
          3'b111: decoder_ctrl_o.alu_operator = ALU_GEU;
          default: begin
            decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
          end
        endcase
      end

      //////////////////////////////////
      //  _     ____    ______ _____  //
      // | |   |  _ \  / / ___|_   _| //
      // | |   | | | |/ /\___ \ | |   //
      // | |___| |_| / /  ___) || |   //
      // |_____|____/_/  |____/ |_|   //
      //                              //
      //////////////////////////////////

      OPCODE_STORE: begin
        decoder_ctrl_o.lsu_en       = 1'b1;
        decoder_ctrl_o.lsu_we       = 1'b1;
        decoder_ctrl_o.rf_re[0]     = 1'b1;
        decoder_ctrl_o.rf_re[1]     = 1'b1;
        decoder_ctrl_o.alu_operator = ALU_ADD;
        // pass write data through ALU operand c
        decoder_ctrl_o.op_c_mux_sel = OP_C_REGB_OR_FWD;

        decoder_ctrl_o.imm_b_mux_sel    = IMMB_S;
        decoder_ctrl_o.alu_op_b_mux_sel = OP_B_IMM;

        // Data type encoded in instr_rdata_i[13:12]:
        // 2'b00: SB, 2'b01: SH, 2'10: SW
        decoder_ctrl_o.lsu_type = instr_rdata_i[13:12];
        
        if ((instr_rdata_i[14] == 1'b1) || (instr_rdata_i[13:12] == 2'b11)) begin
          decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
        end
      end

      OPCODE_LOAD: begin
        decoder_ctrl_o.lsu_en            = 1'b1;
        decoder_ctrl_o.rf_we             = 1'b1;
        decoder_ctrl_o.rf_re[0]          = 1'b1;
        // offset from immediate
        decoder_ctrl_o.alu_operator      = ALU_ADD;
        decoder_ctrl_o.alu_op_b_mux_sel  = OP_B_IMM;
        decoder_ctrl_o.imm_b_mux_sel     = IMMB_I;
        
        // sign/zero extension
        decoder_ctrl_o.lsu_sign_ext = !instr_rdata_i[14];

        // Data type encoded in instr_rdata_i[13:12]:
        // 2'b00: LB, 2'b01: LH, 2'10: LW
        decoder_ctrl_o.lsu_type = instr_rdata_i[13:12];

        // Reserved or RV64
        if ((instr_rdata_i[14:12] == 3'b111) || (instr_rdata_i[14:12] == 3'b110) || (instr_rdata_i[14:12] == 3'b011)) begin
          decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
        end
      end

      //////////////////////////
      //     _    _    _   _  //
      //    / \  | |  | | | | //
      //   / _ \ | |  | | | | //
      //  / ___ \| |__| |_| | //
      // /_/   \_\_____\___/  //
      //                      //
      //////////////////////////

      OPCODE_LUI: begin  // Load Upper Immediate
        decoder_ctrl_o.alu_op_a_mux_sel = OP_A_IMM;
        decoder_ctrl_o.alu_op_b_mux_sel = OP_B_IMM;
        decoder_ctrl_o.imm_a_mux_sel    = IMMA_ZERO;
        decoder_ctrl_o.imm_b_mux_sel    = IMMB_U;
        decoder_ctrl_o.alu_operator     = ALU_ADD;
        decoder_ctrl_o.rf_we            = 1'b1;
      end

      OPCODE_AUIPC: begin  // Add Upper Immediate to PC
        decoder_ctrl_o.alu_op_a_mux_sel = OP_A_CURRPC;
        decoder_ctrl_o.alu_op_b_mux_sel = OP_B_IMM;
        decoder_ctrl_o.imm_b_mux_sel    = IMMB_U;
        decoder_ctrl_o.alu_operator     = ALU_ADD;
        decoder_ctrl_o.rf_we            = 1'b1;
      end

      OPCODE_OPIMM: begin // Register-Immediate ALU Operations
        decoder_ctrl_o.alu_op_b_mux_sel = OP_B_IMM;
        decoder_ctrl_o.imm_b_mux_sel    = IMMB_I;
        decoder_ctrl_o.rf_we            = 1'b1;
        decoder_ctrl_o.rf_re[0]         = 1'b1;

        unique case (instr_rdata_i[14:12])
          3'b000: decoder_ctrl_o.alu_operator = ALU_ADD;  // Add Immediate
          3'b010: decoder_ctrl_o.alu_operator = ALU_SLTS; // Set to one if Lower Than Immediate
          3'b011: decoder_ctrl_o.alu_operator = ALU_SLTU; // Set to one if Lower Than Immediate Unsigned
          3'b100: decoder_ctrl_o.alu_operator = ALU_XOR;  // Exclusive Or with Immediate
          3'b110: decoder_ctrl_o.alu_operator = ALU_OR;   // Or with Immediate
          3'b111: decoder_ctrl_o.alu_operator = ALU_AND;  // And with Immediate

          3'b001: begin
            decoder_ctrl_o.alu_operator   = ALU_SLL;  // Shift Left Logical by Immediate
            if (instr_rdata_i[31:25] != 7'b0) begin
              decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
            end
          end

          3'b101: begin
            if (instr_rdata_i[31:25] == 7'b0)
              decoder_ctrl_o.alu_operator = ALU_SRL;  // Shift Right Logical by Immediate
            else if (instr_rdata_i[31:25] == 7'b010_0000)
              decoder_ctrl_o.alu_operator = ALU_SRA;  // Shift Right Arithmetically by Immediate
            else begin
              decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
            end
          end


        endcase
      end

      OPCODE_OP: begin  // Register-Register ALU operation

        if ((instr_rdata_i[31:30] == 2'b11) || (instr_rdata_i[31:30] == 2'b10)) begin
          decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
        end else begin

          decoder_ctrl_o.rf_we    = 1'b1;
          decoder_ctrl_o.rf_re[0] = 1'b1;
          
          if (~instr_rdata_i[28]) decoder_ctrl_o.rf_re[1] = 1'b1;

          unique case ({instr_rdata_i[30:25], instr_rdata_i[14:12]})
            // RV32I ALU operations
            {6'b00_0000, 3'b000}: decoder_ctrl_o.alu_operator = ALU_ADD;   // Add
            {6'b10_0000, 3'b000}: decoder_ctrl_o.alu_operator = ALU_SUB;   // Sub
            {6'b00_0000, 3'b010}: decoder_ctrl_o.alu_operator = ALU_SLTS;  // Set Lower Than
            {6'b00_0000, 3'b011}: decoder_ctrl_o.alu_operator = ALU_SLTU;  // Set Lower Than Unsigned
            {6'b00_0000, 3'b100}: decoder_ctrl_o.alu_operator = ALU_XOR;   // Xor
            {6'b00_0000, 3'b110}: decoder_ctrl_o.alu_operator = ALU_OR;    // Or
            {6'b00_0000, 3'b111}: decoder_ctrl_o.alu_operator = ALU_AND;   // And
            {6'b00_0000, 3'b001}: decoder_ctrl_o.alu_operator = ALU_SLL;   // Shift Left Logical
            {6'b00_0000, 3'b101}: decoder_ctrl_o.alu_operator = ALU_SRL;   // Shift Right Logical
            {6'b10_0000, 3'b101}: decoder_ctrl_o.alu_operator = ALU_SRA;   // Shift Right Arithmetic

            default: begin
              decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
            end
          endcase
        end
      end

      ////////////////////////////////////////////////
      //  ____  ____  _____ ____ ___    _    _      //
      // / ___||  _ \| ____/ ___|_ _|  / \  | |     //
      // \___ \| |_) |  _|| |    | |  / _ \ | |     //
      //  ___) |  __/| |__| |___ | | / ___ \| |___  //
      // |____/|_|   |_____\____|___/_/   \_\_____| //
      //                                            //
      ////////////////////////////////////////////////

      OPCODE_FENCE: begin

        decoder_ctrl_o.alu_operator = ALU_SLTU;
        
        unique case (instr_rdata_i[14:12])
          3'b000: begin // FENCE (FENCE.I instead, a bit more conservative)
            // flush pipeline
            decoder_ctrl_o.fencei_insn = 1'b1;
          end

          3'b001: begin // FENCE.I
            // flush prefetch buffer, flush pipeline
            decoder_ctrl_o.fencei_insn = 1'b1;
          end

          default: begin
            decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
          end
        endcase
      end

      OPCODE_SYSTEM: begin

        decoder_ctrl_o.alu_operator = ALU_SLTU;
        
        if (instr_rdata_i[14:12] == 3'b000)
        begin
          // non CSR related SYSTEM instructions
          if ( {instr_rdata_i[19:15], instr_rdata_i[11:7]} == '0)
          begin
            unique case (instr_rdata_i[31:20])
              12'h000:  // ECALL
              begin
                // environment (system) call
                decoder_ctrl_o.ecall_insn  = 1'b1;
              end

              12'h001:  // ebreak
              begin
                // debugger trap
                decoder_ctrl_o.ebrk_insn = 1'b1;
              end

              12'h302:  // mret
              begin
                decoder_ctrl_o.mret_insn = 1'b1;
              end

              12'h7b2:  // dret
                begin
                  if(ctrl_fsm_i.debug_mode) begin
                    decoder_ctrl_o.dret_insn    =  1'b1;
                  end
                  else begin
                    decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
                  end
              end

              12'h105:  // wfi
              begin
                decoder_ctrl_o.wfi_insn = 1'b1;
                if (ctrl_fsm_i.debug_wfi_no_sleep) begin
                  // Treat as NOP (do not cause sleep mode entry)
                  // Using decoding similar to ADDI, but without register reads/writes, i.e.
                  // keep rf_we = 0, rf_re[0] = 0
                  decoder_ctrl_o.alu_op_b_mux_sel = OP_B_IMM;
                  decoder_ctrl_o.imm_b_mux_sel    = IMMB_I;
                  decoder_ctrl_o.alu_operator     = ALU_ADD;
                end
              end

              default:
                begin
                  decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
              end
            endcase
          end else begin // if ( {instr_rdata_i[19:15], instr_rdata_i[11:7]} == '0)
            decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
          end
        end // if (instr_rdata_i[14:12] == 3'b000)
        else
        begin
          // instruction to read/modify CSR
          decoder_ctrl_o.csr_en           = 1'b1;
          decoder_ctrl_o.rf_we            = 1'b1;
          decoder_ctrl_o.alu_op_b_mux_sel = OP_B_IMM;
          decoder_ctrl_o.imm_a_mux_sel    = IMMA_Z;
          decoder_ctrl_o.imm_b_mux_sel    = IMMB_I;    // CSR address is encoded in I imm
          decoder_ctrl_o.alu_operator     = ALU_SLTU;
          
          if (instr_rdata_i[14] == 1'b1) begin
            // rs1 field is used as immediate
            decoder_ctrl_o.alu_op_a_mux_sel = OP_A_IMM;
          end else begin
            decoder_ctrl_o.rf_re[0]         = 1'b1;
            decoder_ctrl_o.alu_op_a_mux_sel = OP_A_REGA_OR_FWD;
          end

          // instr_rdata_i[19:14] = rs or immediate value
          //   if set or clear with rs==x0 or imm==0,
          //   then do not perform a write action
          unique case (instr_rdata_i[13:12])
            2'b01:   decoder_ctrl_o.csr_op = CSR_OP_WRITE;
            2'b10:   decoder_ctrl_o.csr_op = instr_rdata_i[19:15] == 5'b0 ? CSR_OP_READ : CSR_OP_SET;
            2'b11:   decoder_ctrl_o.csr_op = instr_rdata_i[19:15] == 5'b0 ? CSR_OP_READ : CSR_OP_CLEAR;
            default: decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
          endcase

          
          // Determine if CSR access is illegal
          case (instr_rdata_i[31:20])
            //  Writes to read only CSRs results in illegal instruction
            CSR_MVENDORID,
              CSR_MARCHID,
              CSR_MIMPID,
              CSR_MHARTID :
                if(decoder_ctrl_o.csr_op != CSR_OP_READ) begin
                  decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
                end

            // These are valid CSR registers
            CSR_MSTATUS,
              CSR_MEPC,
              CSR_MTVEC,
              CSR_MCAUSE : begin
                ; // do nothing, not illegal
              end
            // These are valid CSR registers
            CSR_MISA,
              CSR_MIE,
              CSR_MSCRATCH,
              CSR_MTVAL,
              CSR_MIP : begin
                ; // do nothing, not illegal
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
              CSR_MCOUNTINHIBIT,
              CSR_MHPMEVENT3,
              CSR_MHPMEVENT4,  CSR_MHPMEVENT5,  CSR_MHPMEVENT6,  CSR_MHPMEVENT7,
              CSR_MHPMEVENT8,  CSR_MHPMEVENT9,  CSR_MHPMEVENT10, CSR_MHPMEVENT11,
              CSR_MHPMEVENT12, CSR_MHPMEVENT13, CSR_MHPMEVENT14, CSR_MHPMEVENT15,
              CSR_MHPMEVENT16, CSR_MHPMEVENT17, CSR_MHPMEVENT18, CSR_MHPMEVENT19,
              CSR_MHPMEVENT20, CSR_MHPMEVENT21, CSR_MHPMEVENT22, CSR_MHPMEVENT23,
              CSR_MHPMEVENT24, CSR_MHPMEVENT25, CSR_MHPMEVENT26, CSR_MHPMEVENT27,
              CSR_MHPMEVENT28, CSR_MHPMEVENT29, CSR_MHPMEVENT30, CSR_MHPMEVENT31 : begin
                ; // do nothing, not illegal
              end

            // Hardware Performance Monitor (unprivileged read-only mirror CSRs)
            // Removal of these is not SEC equivalent
            CSR_CYCLE,
              CSR_INSTRET,
              CSR_HPMCOUNTER3,
              CSR_HPMCOUNTER4,  CSR_HPMCOUNTER5,  CSR_HPMCOUNTER6,  CSR_HPMCOUNTER7,
              CSR_HPMCOUNTER8,  CSR_HPMCOUNTER9,  CSR_HPMCOUNTER10, CSR_HPMCOUNTER11,
              CSR_HPMCOUNTER12, CSR_HPMCOUNTER13, CSR_HPMCOUNTER14, CSR_HPMCOUNTER15,
              CSR_HPMCOUNTER16, CSR_HPMCOUNTER17, CSR_HPMCOUNTER18, CSR_HPMCOUNTER19,
              CSR_HPMCOUNTER20, CSR_HPMCOUNTER21, CSR_HPMCOUNTER22, CSR_HPMCOUNTER23,
              CSR_HPMCOUNTER24, CSR_HPMCOUNTER25, CSR_HPMCOUNTER26, CSR_HPMCOUNTER27,
              CSR_HPMCOUNTER28, CSR_HPMCOUNTER29, CSR_HPMCOUNTER30, CSR_HPMCOUNTER31,
              CSR_CYCLEH,
              CSR_INSTRETH,
              CSR_HPMCOUNTER3H,
              CSR_HPMCOUNTER4H,  CSR_HPMCOUNTER5H,  CSR_HPMCOUNTER6H,  CSR_HPMCOUNTER7H,
              CSR_HPMCOUNTER8H,  CSR_HPMCOUNTER9H,  CSR_HPMCOUNTER10H, CSR_HPMCOUNTER11H,
              CSR_HPMCOUNTER12H, CSR_HPMCOUNTER13H, CSR_HPMCOUNTER14H, CSR_HPMCOUNTER15H,
              CSR_HPMCOUNTER16H, CSR_HPMCOUNTER17H, CSR_HPMCOUNTER18H, CSR_HPMCOUNTER19H,
              CSR_HPMCOUNTER20H, CSR_HPMCOUNTER21H, CSR_HPMCOUNTER22H, CSR_HPMCOUNTER23H,
              CSR_HPMCOUNTER24H, CSR_HPMCOUNTER25H, CSR_HPMCOUNTER26H, CSR_HPMCOUNTER27H,
              CSR_HPMCOUNTER28H, CSR_HPMCOUNTER29H, CSR_HPMCOUNTER30H, CSR_HPMCOUNTER31H :
                // Read-only and readable from user mode only if the bit of mcounteren is set
                if((decoder_ctrl_o.csr_op != CSR_OP_READ)) begin
                  decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
                end else begin
                  ; // do nothing, not illegal
                end

            // Debug register access
            CSR_DCSR,
              CSR_DPC,
              CSR_DSCRATCH0,
              CSR_DSCRATCH1 :
                if(!ctrl_fsm_i.debug_mode) begin
                  decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
              end else begin
                ; // do nothing, not illegal
              end

            // Debug Trigger register access
            CSR_TSELECT,
              CSR_TDATA1,
              CSR_TDATA2,
              CSR_TDATA3,
              CSR_TINFO,
              CSR_MCONTEXT,
              CSR_SCONTEXT :
                if(DEBUG_TRIGGER_EN != 1) begin
                  decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
                end

                  default : decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;

          endcase // case (instr_rdata_i[31:20])

          if (decoder_ctrl_o.illegal_insn) begin
            decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
          end

        end
      end

      default: begin
        decoder_ctrl_o = DECODER_CTRL_ILLEGAL_INSN;
      end
    endcase
    
  end // always_comb

endmodule : cv32e40x_i_decoder
