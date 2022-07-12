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
// Engineer:       Igor Loi - igor.loi@unibo.it                               //
//                                                                            //
// Additional contributions by:                                               //
//                 Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                 Øystein Knauserud - oystein.knauserud@silabs.com           //
//                 Michael Platzer - michael.platzer@tuwien.ac.at             //
//                                                                            //
// Design Name:    Load Store Unit                                            //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Load Store Unit, used to eliminate multiple access during  //
//                 processor stalls, and to align bytes and halfwords         //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_load_store_unit import cv32e40x_pkg::*;
#(
  parameter bit          A_EXT = 0,
  parameter bit          X_EXT = 0,
  parameter int          X_ID_WIDTH = 4,
  parameter int          PMA_NUM_REGIONS = 0,
  parameter pma_cfg_t    PMA_CFG[PMA_NUM_REGIONS-1:0] = '{default:PMA_R_DEFAULT}
)
(
  input  logic        clk,
  input  logic        rst_n,

  // From controller FSM
  input  ctrl_fsm_t   ctrl_fsm_i,

  // output to data memory
  if_c_obi.master     m_c_obi_data_if,

  // ID/EX pipeline
  input id_ex_pipe_t  id_ex_pipe_i,

  // Control outputs
  output logic        busy_o,
  output logic        interruptible_o,

  // Stage 0 outputs (EX)
  output logic        lsu_split_0_o,            // Misaligned access is split in two transactions (to controller)
  output logic        lsu_first_op_0_o,         // First operation is active in EX
  output logic        lsu_last_op_0_o,          // Last operation is active in EX

  // Stage 1 outputs (WB)
  output logic [1:0]  lsu_err_1_o,
  output logic [31:0] lsu_rdata_1_o,            // LSU read data
  output mpu_status_e lsu_mpu_status_1_o,       // MPU (PMA) status, response/WB timing. To controller and wb_stage

  // Handshakes
  input  logic        valid_0_i,                // Handshakes for first LSU stage (EX)
  output logic        ready_0_o,                // LSU ready for new data in EX stage
  output logic        valid_0_o,
  input  logic        ready_0_i,

  input  logic        valid_1_i,                // Handshakes for second LSU stage (WB)
  output logic        ready_1_o,                // LSU ready for new data in WB stage
  output logic        valid_1_o,
  input  logic        ready_1_i,

  // eXtension interface
  if_xif.cpu_mem        xif_mem_if,
  if_xif.cpu_mem_result xif_mem_result_if
);

  localparam DEPTH = 2;                         // Maximum number of outstanding transactions

  // Transaction request (before aligner)
  trans_req_t     trans;

  // Aligned transaction request (to cv32e40x_mpu)
  logic           trans_valid; // todo: consider renaming to align_trans_valid, align_trans_ready (if so, do we need trans_valid, trans_ready as well?)
  logic           trans_ready;
  obi_data_req_t  align_trans;

  // Transaction response interface (from cv32e40x_mpu)
  logic           resp_valid;
  logic [31:0]    resp_rdata;
  data_resp_t     resp;

  // Transaction request (from cv32e40x_mpu to cv32e40x_write_buffer)
  logic           buffer_trans_valid;
  logic           buffer_trans_ready;
  obi_data_req_t  buffer_trans;

  logic           filter_trans_valid;
  logic           filter_trans_ready;
  obi_data_req_t  filter_trans;
  logic           filter_resp_valid;
  obi_data_resp_t filter_resp;
  logic [1:0]     filter_err;

  // Transaction request (from cv32e40x_write_buffer to cv32e40x_data_obi_interface)
  logic           bus_trans_valid;
  logic           bus_trans_ready;
  obi_data_req_t  bus_trans;

  // Transaction response (from cv32e40x_data_obi_interface to cv32e40x_mpu)
  logic           bus_resp_valid;
  obi_data_resp_t bus_resp;

  // Counter to count maximum number of outstanding transactions
  logic [1:0]     cnt_q;                // Transaction counter
  logic [1:0]     next_cnt;             // Next value for cnt_q
  logic           count_up;             // Increment outstanding transaction count by 1 (can happen at same time as count_down)
  logic           count_down;           // Decrement outstanding transaction count by 1 (can happen at same time as count_up)
  logic           cnt_is_one_next;

  logic           ctrl_update;          // Update load/store control info in WB stage

  // registers for data_rdata alignment and sign extension
  logic [1:0]     lsu_size_q;
  logic           lsu_sext_q;
  logic           lsu_we_q;
  logic [1:0]     rdata_offset_q;
  logic           last_q;               // Last transfer of load/store (only 0 for first part of split transfer)

  logic [3:0]     be;                   // Byte enables
  logic [31:0]    wdata;

  logic           split_q;              // Currently performing the second address phase of a split misaligned load/store
  logic           misaligned_halfword;  // Halfword is not naturally aligned, but no split is needed
  logic           misaligned_access;    // Access is not naturally aligned

  logic           filter_resp_busy;     // Response filter busy

  logic [31:0]    rdata_q;

  logic           done_0;               // First stage (EX) is done

  logic           trans_valid_q;        // trans_valid got clocked without trans_ready

  logic                  xif_req;       // The ongoing memory request comes from the XIF interface
  logic                  xif_mpu_err;   // The ongoing memory request caused an MPU error
  logic                  xif_ready_1;   // The LSU second stage is ready for an XIF transaction
  logic                  xif_res_q;     // The next memory result is for the XIF interface
  logic [X_ID_WIDTH-1:0] xif_id_q;      // Instruction ID of an XIF memory transaction

  assign xif_req = X_EXT && xif_mem_if.mem_valid;

  // Transaction (before aligner)
  // Generate address from operands (atomic memory transactions do not use an address offset computation)
  always_comb begin
    if (xif_req) begin
      trans.addr  = xif_mem_if.mem_req.addr;
      trans.we    = xif_mem_if.mem_req.we;
      trans.size  = 2'b10;                    // XIF memory requests always use maximum size
      trans.wdata = xif_mem_if.mem_req.wdata;
      trans.mode  = xif_mem_if.mem_req.mode;  // TODO use mode from XIF request or force machine mode?
      trans.dbg   = '0;                       // TODO setup debug triggers

      trans.atop  = '0;
      trans.sext  = '0;
    end else begin
      trans.addr  = id_ex_pipe_i.lsu_atop[5] ? id_ex_pipe_i.alu_operand_a : (id_ex_pipe_i.alu_operand_a + id_ex_pipe_i.alu_operand_b);
      trans.we    = id_ex_pipe_i.lsu_we;
      trans.size  = id_ex_pipe_i.lsu_size;
      trans.wdata = id_ex_pipe_i.operand_c;
      trans.mode  = PRIV_LVL_M; // Machine mode
      trans.dbg   = ctrl_fsm_i.debug_mode;

      trans.atop  = id_ex_pipe_i.lsu_atop;
      trans.sext  = id_ex_pipe_i.lsu_sext;
    end
  end

  ///////////////////////////////// BE generation ////////////////////////////////
  always_comb
  begin
    case (trans.size) // Data type 00 byte, 01 halfword, 10 word
      2'b00: begin // Writing a byte
        case (trans.addr[1:0])
          2'b00: be = 4'b0001;
          2'b01: be = 4'b0010;
          2'b10: be = 4'b0100;
          2'b11: be = 4'b1000;
        endcase; // case (trans.addr[1:0])
      end
      2'b01:
      begin // Writing a half word
        if (split_q == 1'b0)
        begin // non-misaligned case
          case (trans.addr[1:0])
            2'b00: be = 4'b0011;
            2'b01: be = 4'b0110;
            2'b10: be = 4'b1100;
            2'b11: be = 4'b1000;
          endcase; // case (trans.addr[1:0])
        end
        else
        begin // misaligned case
          be = 4'b0001;
        end
      end
      default:
      begin // Writing a word (note: XIF memory requests always write a word)
        if (split_q == 1'b0)
        begin // non-misaligned case
          case (trans.addr[1:0])
            2'b00: be = xif_req ?  xif_mem_if.mem_req.be[3:0]        : 4'b1111;
            2'b01: be = xif_req ? {xif_mem_if.mem_req.be[2:0], 1'b0} : 4'b1110;
            2'b10: be = xif_req ? {xif_mem_if.mem_req.be[1:0], 2'b0} : 4'b1100;
            2'b11: be = xif_req ? {xif_mem_if.mem_req.be[0:0], 3'b0} : 4'b1000;
          endcase; // case (trans.addr[1:0])
        end
        else
        begin // misaligned case
          case (trans.addr[1:0])
            2'b00: be = 4'b0000; // this is not used, but included for completeness
            2'b01: be = xif_req ? {3'b0, xif_mem_if.mem_req.be[3:3]} : 4'b0001;
            2'b10: be = xif_req ? {2'b0, xif_mem_if.mem_req.be[3:2]} : 4'b0011;
            2'b11: be = xif_req ? {1'b0, xif_mem_if.mem_req.be[3:1]} : 4'b0111;
          endcase; // case (trans.addr[1:0])
        end
      end
    endcase; // case (trans.size)
  end

  // Prepare data to be written to the memory. We handle misaligned (split) accesses,
  // half word and byte accesses and register offsets here.

  always_comb
  begin
    case (trans.addr[1:0])
      2'b00: wdata = trans.wdata[31:0];
      2'b01: wdata = {trans.wdata[23:0], trans.wdata[31:24]};
      2'b10: wdata = {trans.wdata[15:0], trans.wdata[31:16]};
      2'b11: wdata = {trans.wdata[ 7:0], trans.wdata[31: 8]};
    endcase; // case (trans.addr[1:0])
  end

  // FF for rdata alignment and sign-extension
  // Signals used in WB stage
  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0) begin
      lsu_size_q       <= 2'b0;
      lsu_sext_q       <= 1'b0;
      lsu_we_q         <= 1'b0;
      rdata_offset_q   <= 2'b0;
      last_q           <= 1'b0;
    end else if (ctrl_update) begin     // request was granted, we wait for rvalid and can continue to WB
      lsu_size_q       <= trans.size;
      lsu_sext_q       <= trans.sext;
      lsu_we_q         <= trans.we;
      rdata_offset_q   <= trans.addr[1:0];
      // If we currently signal split from first stage (EX), WB stage will not see the last transfer for this update.
      // Otherwise we are on the last. For non-split accesses we always mark as last.
      last_q           <= lsu_split_0_o ? 1'b0 : 1'b1;
    end
  end

  // Tracking split (misaligned) state
  // This signals has EX timing, and indicates that the second
  // address phase of a split transfer is taking place
  // Reset/killed on !valid_0_i to ensure it is zero for the
  // first phase of the next instruction. Otherwise it could stick at 1 after a killed
  // split, causing next LSU instruction to calculate wrong _be.
  // todo: add assertion that it is zero for the first phase (regardless of alignment)
  always_ff @(posedge clk, negedge rst_n) begin
    if (rst_n == 1'b0) begin
      split_q    <= 1'b0;
    end else begin
      if(!valid_0_i && !xif_req) begin
        split_q <= 1'b0; // Reset split_st when no valid instructions
      end else if (ctrl_update) begin // EX done, update split_q for next address phase
        split_q <= lsu_split_0_o;
      end
    end
  end

  generate
    if (X_EXT) begin : x_ext_regs
      always_ff @(posedge clk, negedge rst_n) begin
        if (rst_n == 1'b0) begin
          xif_res_q <= '0;
          xif_id_q  <= '0;
        end else if (ctrl_update) begin       // request was granted
          xif_res_q <= xif_req;               // expect an XIF result if we did an XIF request
          xif_id_q  <= xif_mem_if.mem_req.id; // save XIF instruction ID for result
        end
      end
    end else begin : no_x_ext_regs
      assign xif_res_q = 1'b0;
      assign xif_id_q  = '0;
    end
  endgenerate

  ////////////////////////////////////////////////////////////////////////
  //  ____  _               _____      _                 _              //
  // / ___|(_) __ _ _ __   | ____|_  _| |_ ___ _ __  ___(_) ___  _ __   //
  // \___ \| |/ _` | '_ \  |  _| \ \/ / __/ _ \ '_ \/ __| |/ _ \| '_ \  //
  //  ___) | | (_| | | | | | |___ >  <| ||  __/ | | \__ \ | (_) | | | | //
  // |____/|_|\__, |_| |_| |_____/_/\_\\__\___|_| |_|___/_|\___/|_| |_| //
  //          |___/                                                     //
  ////////////////////////////////////////////////////////////////////////

  logic [31:0] rdata_ext;
  logic [63:0] rdata_full;
  logic [63:0] rdata_aligned; // [63:32] unsused
  logic        rdata_is_split;

  // Check if rdata is split over two accesses
  assign rdata_is_split = ((lsu_size_q == 2'b10) && (rdata_offset_q != 2'b00)) || // Split word
                          ((lsu_size_q == 2'b01) && (rdata_offset_q == 2'b11));   // Split halfword

  // Assemble full rdata
  assign rdata_full  = rdata_is_split ? {resp_rdata, rdata_q} :   // Use lsb data from previous access if split
                                        {resp_rdata, resp_rdata}; // Set up data for shifting resp_data LSBs into MSBs of rdata_aligned

  // Realign rdata
  assign rdata_aligned = rdata_full >> (8*rdata_offset_q);

  // Sign-extend aligned rdata
  always_comb begin
    case (lsu_size_q)
      2'b00:   rdata_ext = {{24{lsu_sext_q && rdata_aligned[ 7]}},  rdata_aligned[ 7:0]}; // Byte
      2'b01:   rdata_ext = {{16{lsu_sext_q && rdata_aligned[ 15]}}, rdata_aligned[15:0]}; // Halfword
      default: rdata_ext =                                          rdata_aligned[31:0];  // Word
    endcase
  end



  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0) begin
      rdata_q <= '0;
    end else if (resp_valid && !lsu_we_q) begin
      // if we have detected a split access, and we are
      // currently doing the first part of this access, then
      // store the data coming from memory in rdata_q.
      // In all other cases, rdata_q gets the value that we are
      // writing to the register file
      if (split_q || lsu_split_0_o) begin
        rdata_q <= resp_rdata;
      end else begin
        rdata_q <= rdata_ext;
      end
    end
  end

  // output to register file
  // Always rdata_ext regardless of split accesses
  // Output will be valid (valid_1_o) only for the last phase of split access.
  assign lsu_rdata_1_o = rdata_ext;

  // misaligned_access is high for both transfers of a misaligned transfer
  assign misaligned_access = split_q || lsu_split_0_o || misaligned_halfword;

  // Check for misaligned accesses that need a second memory access
  // If one is detected, this is signaled with lsu_split_0_o.
  // This is used to gate off ready_0_o to avoid instructions into
  // the EX stage while the LSU is handling the second phase of the split access.
  // Also detecting misaligned halfwords that don't need a second transfer
  always_comb
  begin
    lsu_split_0_o = 1'b0;
    misaligned_halfword = 1'b0;
    if ((valid_0_i || xif_req) && !split_q)
    begin
      case (trans.size)
        2'b10: // word
        begin
          if (trans.addr[1:0] != 2'b00)
            lsu_split_0_o = 1'b1;
        end
        2'b01: // half word
        begin
          if (trans.addr[1:0] == 2'b11)
            lsu_split_0_o = 1'b1;
          if (trans.addr[0] != 1'b0)
            misaligned_halfword = 1'b1;
        end
        default: begin end
      endcase // case (trans.size)
    end
  end

  // Set flags for first and last op
  // Only valid when id_ex_pipe.lsu_en == 1
  assign lsu_last_op_0_o = !lsu_split_0_o;
  assign lsu_first_op_0_o = !split_q;

  // Busy if there are ongoing (or potentially outstanding) transfers
  // In the case of mpu errors, the LSU control logic can have outstanding transfers not seen by the response filter.
  assign busy_o = filter_resp_busy || (cnt_q > 0) || trans_valid;

  //////////////////////////////////////////////////////////////////////////////
  // Transaction request generation
  //
  // Assumes that corresponding response is at least 1 cycle after request
  //
  // - Only request transaction when EX stage requires data transfer and
  // - maximum number of outstanding transactions will not be exceeded (cnt_q < DEPTH)
  //////////////////////////////////////////////////////////////////////////////

  // For last phase of misaligned/split transfer the address needs to be word aligned (as LSB of be will be set)

  // todo: As part of the fix for https://github.com/openhwgroup/cv32e40x/issues/388 the following should be used as well:
  // assign align_trans.addr    = split_q ? {trans.addr[31:2], 2'b00} + 'h4 : trans.addr;

  assign align_trans.addr    = trans.atop[5] ? trans.addr : (split_q ? {trans.addr[31:2], 2'b00} + 'h4 : trans.addr);
  assign align_trans.we      = trans.we;
  assign align_trans.be      = be;
  assign align_trans.wdata   = wdata;
  assign align_trans.atop    = trans.atop;
  assign align_trans.prot    = {trans.mode, 1'b1};      // Transfers from LSU are data transfers
  assign align_trans.dbg     = trans.dbg;
  assign align_trans.memtype = 2'b00;                   // Memory type is assigned in MPU

  // Transaction request generation
  // OBI compatible (avoids combinatorial path from data_rvalid_i to data_req_o). Multiple trans_* transactions can be
  // issued (and accepted) before a response (resp_*) is received.
  assign trans_valid = (valid_0_i || xif_req) && (cnt_q < DEPTH);

  // LSU second stage is ready if it is not being used (i.e. no outstanding transfers, cnt_q = 0),
  // or if it is being used and the awaited response arrives (resp_rvalid).
  // XIF transactions bypass the pipeline, hence ready_1_i is not required for the second stage to
  // be ready for XIF transactions.
  assign ready_1_o   = ((cnt_q == 2'b00) ? 1'b1 : resp_valid) && ready_1_i;
  assign xif_ready_1 = ((cnt_q == 2'b00) ? 1'b1 : resp_valid);

  // LSU second stage is valid when resp_valid (typically data_rvalid_i) is received. Both parts of a misaligned transfer will signal valid_1_o.
  assign valid_1_o                          = resp_valid && valid_1_i && !xif_res_q;
  assign xif_mem_result_if.mem_result_valid = last_q && resp_valid && xif_res_q; // todo: last_q or not?

  // LSU EX stage readyness requires two criteria to be met:
  //
  // - A data request has been forwarded/accepted (trans_valid && trans_ready)
  // - The LSU WB stage is available such that EX and WB can be updated in lock step
  //
  // Default (if there is not even a data request) LSU EX is signaled to be ready, else
  // if there are no outstanding transactions the EX stage is ready again once the transaction
  // request is accepted (at which time this load/store will move to the WB stage), else
  // in case there is already at least one outstanding transaction (so WB is full) the EX
  // and WB stage can only signal readiness in lock step.

  // Internal signal used in ctrl_update.
  // Indicates that address phase in EX is complete.
  // XIF request bypasses pipeline, ignores ready_0_i but requires xif_ready_1 instead.
  assign done_0    = (
                      !(valid_0_i || xif_req) ? 1'b1 :
                      (cnt_q == 2'b00)        ? (trans_valid && trans_ready) :
                      (cnt_q == 2'b01)        ? (trans_valid && trans_ready) :
                      1'b1
                     ) && (ready_0_i || (xif_req && xif_ready_1));

  // XIF request bypasses pipeline (does not assert valid_0_o) and takes precedence over regular
  // requests, hence inhibits a concurrent request from EX stage
  assign valid_0_o =  (
                       (cnt_q == 2'b00) ? (trans_valid && trans_ready) :
                       (cnt_q == 2'b01) ? (trans_valid && trans_ready) :
                       1'b1
                      ) && valid_0_i && !xif_req;


  // External (EX) ready only when not handling multi cycle split accesses
  // otherwise we may let a new instruction into EX, overwriting second phase of split access..
  // XIF transactions take precedence, thus the LSU is not ready for EX in case of an XIF request.
  assign ready_0_o = done_0 && !lsu_split_0_o && !xif_req;

  generate
    if (X_EXT) begin : x_ext_mem_ready
      assign xif_mem_if.mem_ready = done_0 && !lsu_split_0_o;
    end else begin : no_x_ext_mem_ready
      assign xif_mem_if.mem_ready = 1'b0;
    end
  endgenerate

  // Export mpu status to WB stage/controller
  assign lsu_mpu_status_1_o = resp.mpu_status;

  // Update signals for EX/WB registers (when EX has valid data itself and is ready for next)
  assign ctrl_update = done_0 && (valid_0_i || xif_req);


  //////////////////////////////////////////////////////////////////////////////
  // Counter (cnt_q, next_cnt) to count number of outstanding OBI transactions
  // (maximum = DEPTH)
  //
  // Counter overflow is prevented by limiting the number of outstanding transactions
  // to DEPTH. Counter underflow is prevented by the assumption that resp_valid = 1
  // will only occur in response to accepted transfer request (as per the OBI protocol).
  //////////////////////////////////////////////////////////////////////////////

  assign count_up = trans_valid && trans_ready;         // Increment upon accepted transfer request
  assign count_down = resp_valid;                       // Decrement upon accepted transfer response

  always_comb begin
    unique case ({count_up, count_down})
      2'b00 : begin
        next_cnt = cnt_q;
      end
      2'b01 : begin
        next_cnt = cnt_q - 1'b1;
      end
      2'b10 : begin
        next_cnt = cnt_q + 1'b1;
      end
      2'b11 : begin
        next_cnt = cnt_q;
      end
    endcase
  end

  // Indicate that counter will be one in the next cycle
  assign cnt_is_one_next = next_cnt == 2'h1;

  //////////////////////////////////////////////////////////////////////////////
  // Counter (cnt_q) to count number of outstanding OBI transactions
  //////////////////////////////////////////////////////////////////////////////

  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0) begin
      cnt_q <= '0;
    end else begin
      cnt_q <= next_cnt;
    end
  end

  //////////////////////////////////////////////////////////////////////////////
  // Check if LSU is interruptible
  //////////////////////////////////////////////////////////////////////////////
  // OBI protocol should not be violated. For non-buffered writes, the trans_
  // signals are fed directly through to the OBI interface. Buffered writes that have
  // been accepted by the write buffer will complete regardless of interrupts,
  // debug and killing of stages.
  //
  // A trans_valid that has been high for at least one clock cycle is not
  // allowed to retract.
  //
  // LSU instructions shall not be interrupted/killed if the address phase is
  // already done, the instruction must finish with resp_valid=1 in WB
  // stage (cnt_q > 0 until resp_valid becomes 1)
  //
  // For misaligned split instructions, we may interrupt during the first
  // cycle of the first half. If the first half stays in EX for more than one
  // cycle, we cannot interrupt it (trans_valid_q == 1). When the first half
  // goes to WB, cnt_q != 0 will block interrupts. If the first half finishes
  // in WB before the second half gets grant, trans_valid_q will again be
  // 1 and block interrupts, and cnt_q will block the last half while it is in
  // WB.

  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0) begin
      trans_valid_q <= 1'b0;
    end else begin
      if (trans_valid && !ctrl_update) begin
        trans_valid_q <= 1'b1;
      end else if (ctrl_update) begin
        trans_valid_q <= 1'b0;
      end
    end
  end

  assign interruptible_o = !trans_valid_q && (cnt_q == '0);


  //////////////////////////////////////////////////////////////////////////////
  // Handle bus errors
  //////////////////////////////////////////////////////////////////////////////

  // Validate bus_error on rvalid from the bus (WB stage)
  // For bufferable transfers, this can happen many cycles after the pipeline control logic has seen the filtered resp_valid
  // Todo: This bypasses the MPU, could be merged with mpu_status_e and passed through the MPU instead
  assign lsu_err_1_o = xif_res_q ? '0 : filter_err;

  //////////////////////////////////////////////////////////////////////////////
  // MPU
  //////////////////////////////////////////////////////////////////////////////

  cv32e40x_mpu
  #(
    .IF_STAGE           ( 0                    ),
    .A_EXT              ( A_EXT                ),
    .CORE_RESP_TYPE     ( data_resp_t          ),
    .BUS_RESP_TYPE      ( obi_data_resp_t      ),
    .CORE_REQ_TYPE      ( obi_data_req_t       ),
    .PMA_NUM_REGIONS    ( PMA_NUM_REGIONS      ),
    .PMA_CFG            ( PMA_CFG              )
  )
  mpu_i
  (
    .clk                  ( clk                ),
    .rst_n                ( rst_n              ),
    .atomic_access_i      ( 1'b0               ), // TODO:OE update to support atomic PMA checks
    .misaligned_access_i  ( misaligned_access  ),

    .core_if_data_access_i( 1'b0               ), // Only applicable for IF stage
    .core_one_txn_pend_n  ( cnt_is_one_next    ),
    .core_mpu_err_wait_i  ( !xif_req           ),
    .core_mpu_err_o       ( xif_mpu_err        ),
    .core_trans_valid_i   ( trans_valid        ),
    .core_trans_ready_o   ( trans_ready        ),
    .core_trans_i         ( align_trans        ),
    .core_resp_valid_o    ( resp_valid         ),
    .core_resp_o          ( resp               ),

    .bus_trans_valid_o    ( filter_trans_valid ),
    .bus_trans_ready_i    ( filter_trans_ready ),
    .bus_trans_o          ( filter_trans       ),
    .bus_resp_valid_i     ( filter_resp_valid  ),
    .bus_resp_i           ( filter_resp        )
  );

  // Extract rdata and err from response struct
  assign resp_rdata = resp.bus_resp.rdata;


  //////////////////////////////////////////////////////////////////////////////
  // Response Filter
  //////////////////////////////////////////////////////////////////////////////

  cv32e40x_lsu_response_filter
    response_filter_i
      (.clk          ( clk                ),
       .rst_n        ( rst_n              ),
       .busy_o       ( filter_resp_busy   ),

       .valid_i      ( filter_trans_valid ),
       .ready_o      ( filter_trans_ready ),
       .trans_i      ( filter_trans       ),
       .resp_valid_o ( filter_resp_valid  ),
       .resp_o       ( filter_resp        ),
       .err_o        ( filter_err         ),

       .valid_o      ( buffer_trans_valid ),
       .ready_i      ( buffer_trans_ready ),
       .trans_o      ( buffer_trans       ),
       .resp_valid_i ( bus_resp_valid     ),
       .resp_i       ( bus_resp           )

     );


  //////////////////////////////////////////////////////////////////////////////
  // Write Buffer
  //////////////////////////////////////////////////////////////////////////////

  cv32e40x_write_buffer
  #(
    .PMA_NUM_REGIONS    ( PMA_NUM_REGIONS    ),
    .PMA_CFG            ( PMA_CFG            )
  )
  write_buffer_i
  (
    .clk                ( clk                ),
    .rst_n              ( rst_n              ),

    .valid_i            ( buffer_trans_valid ),
    .ready_o            ( buffer_trans_ready ),
    .trans_i            ( buffer_trans       ),

    .valid_o            ( bus_trans_valid    ),
    .ready_i            ( bus_trans_ready    ),
    .trans_o            ( bus_trans          )
  );

  //////////////////////////////////////////////////////////////////////////////
  // OBI interface
  //////////////////////////////////////////////////////////////////////////////

  cv32e40x_data_obi_interface
  data_obi_i
  (
    .clk                ( clk             ),
    .rst_n              ( rst_n           ),

    .trans_valid_i      ( bus_trans_valid ),
    .trans_ready_o      ( bus_trans_ready ),
    .trans_i            ( bus_trans       ),

    .resp_valid_o       ( bus_resp_valid  ),
    .resp_o             ( bus_resp        ),

    .m_c_obi_data_if    ( m_c_obi_data_if )
  );

  //////////////////////////////////////////////////////////////////////////////
  // XIF interface response and result data
  //////////////////////////////////////////////////////////////////////////////

  generate
    if (X_EXT) begin : x_ext
      // XIF memory response: convert MPU errors to exception codes
      assign xif_mem_if.mem_resp.exc     = xif_mpu_err;
      assign xif_mem_if.mem_resp.exccode = xif_mpu_err ? (
                                            trans.we ? EXC_CAUSE_STORE_FAULT : EXC_CAUSE_LOAD_FAULT
                                           ) : '0;
      assign xif_mem_if.mem_resp.dbg     = '0; // TODO forward debug triggers

      // XIF memory result
      assign xif_mem_result_if.mem_result.id    = xif_id_q;
      assign xif_mem_result_if.mem_result.rdata = rdata_ext;
      assign xif_mem_result_if.mem_result.err   = filter_err[0]; // forward bus errors to coprocessor
      assign xif_mem_result_if.mem_result.dbg   = '0;            // TODO forward debug triggers
    end else begin : no_x_ext
      assign xif_mem_if.mem_resp.exc            = '0;
      assign xif_mem_if.mem_resp.exccode        = '0;
      assign xif_mem_if.mem_resp.dbg            = '0;
      assign xif_mem_result_if.mem_result.id    = '0;
      assign xif_mem_result_if.mem_result.rdata = '0;
      assign xif_mem_result_if.mem_result.err   = '0;
      assign xif_mem_result_if.mem_result.dbg   = '0;
    end
  endgenerate

endmodule
