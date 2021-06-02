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
  #(parameter bit          A_EXTENSION = 0,
    parameter int unsigned PMA_NUM_REGIONS = 0,
    parameter pma_region_t PMA_CFG[(PMA_NUM_REGIONS ? (PMA_NUM_REGIONS-1) : 0):0] = '{default:PMA_R_DEFAULT})
(
    input  logic         clk,
    input  logic         rst_n,

    input  logic         kill_ex_i,
    // output to data memory
    if_c_obi.master      m_c_obi_data_if,

    // ID/EX pipeline
    input id_ex_pipe_t   id_ex_pipe_i,

    // EX/WB pipeline
    output logic [31:0]  data_addr_wb_o,
    output logic         data_err_wb_o,

    // Block updates of ex_wb_pipe_o.data_addr (from controller)
    input  logic         block_data_addr_i,

    output logic [31:0]  lsu_rdata_o,          // LSU read data
    output logic         lsu_misaligned_o,     // Misaligned access was detected (to controller)

    // stall signal
    output logic         lsu_ready_ex_o,       // LSU ready for new data in EX stage
    output logic         lsu_ready_wb_o,       // LSU ready for new data in WB stage

    // halt signals to EX/WB portion of LSU
    input  logic         halt_ex_i,
    input  logic         halt_wb_i,

    output logic         busy_o
);

  localparam DEPTH = 2;                 // Maximum number of outstanding transactions

  // Transaction request (to cv32e40x_mpu)
  logic          trans_valid;
  logic          trans_ready;
  obi_data_req_t trans;

  // Transaction response interface (from cv32e40x_mpu)
  logic         resp_valid;
  logic [31:0]  resp_rdata;
  logic         resp_err;               // Unused for now
  data_resp_t   resp;
  
  // Transaction request (from cv32e40x_mpu to cv32e40x_data_obi_interface)
  logic          bus_trans_valid;
  logic          bus_trans_ready;
  obi_data_req_t bus_trans;

  // Transaction response (from cv32e40x_data_obi_interface to cv32e40x_mpu)
  logic           bus_resp_valid;
  obi_data_resp_t bus_resp;
  
  // Counter to count maximum number of outstanding transactions
  logic [1:0]   cnt_q;                  // Transaction counter
  logic [1:0]   next_cnt;               // Next value for cnt_q
  logic         count_up;               // Increment outstanding transaction count by 1 (can happen at same time as count_down)
  logic         count_down;             // Decrement outstanding transaction count by 1 (can happen at same time as count_up)
  logic         cnt_is_one_next;

  logic         ctrl_update;            // Update load/store control info in WB stage

  logic [31:0]  data_addr_int;

  // registers for data_rdata alignment and sign extension
  logic [1:0]   data_type_q;
  logic [1:0]   rdata_offset_q;
  logic         data_sign_ext_q;
  logic         data_we_q;

  logic [1:0]   wdata_offset;           // mux control for data to be written to memory

  logic [3:0]   data_be;
  logic [31:0]  data_wdata;

  logic         misaligned_st;          // high if we are currently performing the second part of a misaligned store
  logic         load_err_o, store_err_o;

  logic [31:0]  rdata_q;

  // Signal to block external data_req
  logic         block_data_req;

  // Internally gated data_req
  logic         data_req_valid;

  assign block_data_req = kill_ex_i || id_ex_pipe_i.instr.bus_resp.err ||
                          !(id_ex_pipe_i.instr.mpu_status == MPU_OK);

  assign data_req_valid = id_ex_pipe_i.data_req && id_ex_pipe_i.instr_valid && !block_data_req;

  ///////////////////////////////// BE generation ////////////////////////////////
  always_comb
  begin
    case (id_ex_pipe_i.data_type) // Data type 00 byte, 01 halfword, 10 word
      2'b00: begin // Writing a byte
        case (data_addr_int[1:0])
          2'b00: data_be = 4'b0001;
          2'b01: data_be = 4'b0010;
          2'b10: data_be = 4'b0100;
          2'b11: data_be = 4'b1000;
        endcase; // case (data_addr_int[1:0])
      end
      2'b01:
      begin // Writing a half word
        if (misaligned_st == 1'b0)
        begin // non-misaligned case
          case (data_addr_int[1:0])
            2'b00: data_be = 4'b0011;
            2'b01: data_be = 4'b0110;
            2'b10: data_be = 4'b1100;
            2'b11: data_be = 4'b1000;
          endcase; // case (data_addr_int[1:0])
        end
        else
        begin // misaligned case
          data_be = 4'b0001;
        end
      end
      default:
      begin // Writing a word
        if (misaligned_st == 1'b0)
        begin // non-misaligned case
          case (data_addr_int[1:0])
            2'b00: data_be = 4'b1111;
            2'b01: data_be = 4'b1110;
            2'b10: data_be = 4'b1100;
            2'b11: data_be = 4'b1000;
          endcase; // case (data_addr_int[1:0])
        end
        else
        begin // misaligned case
          case (data_addr_int[1:0])
            2'b00: data_be = 4'b0000; // this is not used, but included for completeness
            2'b01: data_be = 4'b0001;
            2'b10: data_be = 4'b0011;
            2'b11: data_be = 4'b0111;
          endcase; // case (data_addr_int[1:0])
        end
      end
    endcase; // case (id_ex_pipe_i.data_type)
  end

  // prepare data to be written to the memory
  // we handle misaligned accesses, half word and byte accesses and
  // register offsets here
  assign wdata_offset = data_addr_int[1:0] - id_ex_pipe_i.data_reg_offset[1:0];
  always_comb
  begin
    case (wdata_offset)
      2'b00: data_wdata = id_ex_pipe_i.operand_c[31:0];
      2'b01: data_wdata = {id_ex_pipe_i.operand_c[23:0], id_ex_pipe_i.operand_c[31:24]};
      2'b10: data_wdata = {id_ex_pipe_i.operand_c[15:0], id_ex_pipe_i.operand_c[31:16]};
      2'b11: data_wdata = {id_ex_pipe_i.operand_c[ 7:0], id_ex_pipe_i.operand_c[31: 8]};
    endcase; // case (wdata_offset)
  end


  // FF for rdata alignment and sign-extension
  always_ff @(posedge clk, negedge rst_n)
  begin
    if(rst_n == 1'b0)
    begin
      data_type_q       <= '0;
      rdata_offset_q    <= '0;
      data_sign_ext_q   <= 1'b0;
      data_we_q         <= 1'b0;
    end
    else if (ctrl_update) // request was granted, we wait for rvalid and can continue to WB
    begin
      data_type_q       <= id_ex_pipe_i.data_type;
      rdata_offset_q    <= data_addr_int[1:0];
      data_sign_ext_q   <= id_ex_pipe_i.data_sign_ext;
      data_we_q         <= id_ex_pipe_i.data_we;
    end
  end

  ////////////////////////////////////////////////////////////////////////
  //  ____  _               _____      _                 _              //
  // / ___|(_) __ _ _ __   | ____|_  _| |_ ___ _ __  ___(_) ___  _ __   //
  // \___ \| |/ _` | '_ \  |  _| \ \/ / __/ _ \ '_ \/ __| |/ _ \| '_ \  //
  //  ___) | | (_| | | | | | |___ >  <| ||  __/ | | \__ \ | (_) | | | | //
  // |____/|_|\__, |_| |_| |_____/_/\_\\__\___|_| |_|___/_|\___/|_| |_| //
  //          |___/                                                     //
  ////////////////////////////////////////////////////////////////////////

  logic [31:0] data_rdata_ext;

  logic [31:0] rdata_w_ext; // sign extension for words, actually only misaligned assembly
  logic [31:0] rdata_h_ext; // sign extension for half words
  logic [31:0] rdata_b_ext; // sign extension for bytes

  // take care of misaligned words
  always_comb
  begin
    case (rdata_offset_q)
      2'b00: rdata_w_ext = resp_rdata[31:0];
      2'b01: rdata_w_ext = {resp_rdata[ 7:0], rdata_q[31:8]};
      2'b10: rdata_w_ext = {resp_rdata[15:0], rdata_q[31:16]};
      2'b11: rdata_w_ext = {resp_rdata[23:0], rdata_q[31:24]};
    endcase
  end

  // sign extension for half words
  always_comb
  begin
    case (rdata_offset_q)
      2'b00:
      begin
        if (data_sign_ext_q == 1'b0)
          rdata_h_ext = {16'h0000, resp_rdata[15:0]};
        else
          rdata_h_ext = {{16{resp_rdata[15]}}, resp_rdata[15:0]};
      end

      2'b01:
      begin
        if (data_sign_ext_q == 1'b0)
          rdata_h_ext = {16'h0000, resp_rdata[23:8]};
        else
          rdata_h_ext = {{16{resp_rdata[23]}}, resp_rdata[23:8]};
      end

      2'b10:
      begin
        if (data_sign_ext_q == 1'b0)
          rdata_h_ext = {16'h0000, resp_rdata[31:16]};
        else
          rdata_h_ext = {{16{resp_rdata[31]}}, resp_rdata[31:16]};
      end

      2'b11:
      begin
        if (data_sign_ext_q == 1'b0)
          rdata_h_ext = {16'h0000, resp_rdata[7:0], rdata_q[31:24]};
        else
          rdata_h_ext = {{16{resp_rdata[7]}}, resp_rdata[7:0], rdata_q[31:24]};
      end
    endcase // case (rdata_offset_q)
  end

  // sign extension for bytes
  always_comb
  begin
    case (rdata_offset_q)
      2'b00:
      begin
        if (data_sign_ext_q == 1'b0)
          rdata_b_ext = {24'h00_0000, resp_rdata[7:0]};
        else
          rdata_b_ext = {{24{resp_rdata[7]}}, resp_rdata[7:0]};
      end

      2'b01: begin
        if (data_sign_ext_q == 1'b0)
          rdata_b_ext = {24'h00_0000, resp_rdata[15:8]};
        else
          rdata_b_ext = {{24{resp_rdata[15]}}, resp_rdata[15:8]};
      end

      2'b10:
      begin
        if (data_sign_ext_q == 1'b0)
          rdata_b_ext = {24'h00_0000, resp_rdata[23:16]};
        else
          rdata_b_ext = {{24{resp_rdata[23]}}, resp_rdata[23:16]};
      end

      2'b11:
      begin
        if (data_sign_ext_q == 1'b0)
          rdata_b_ext = {24'h00_0000, resp_rdata[31:24]};
        else
          rdata_b_ext = {{24{resp_rdata[31]}}, resp_rdata[31:24]};
      end
    endcase // case (rdata_offset_q)
  end

  // select word, half word or byte sign extended version
  always_comb
  begin
    case (data_type_q)
      2'b00:   data_rdata_ext = rdata_b_ext;
      2'b01:   data_rdata_ext = rdata_h_ext;
      default: data_rdata_ext = rdata_w_ext;
    endcase
  end

  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0)
    begin
      rdata_q <= '0;
    end
    else
    begin
      if (resp_valid && !data_we_q)
      begin
        // if we have detected a misaligned access, and we are
        // currently doing the first part of this access, then
        // store the data coming from memory in rdata_q.
        // In all other cases, rdata_q gets the value that we are
        // writing to the register file
        if (id_ex_pipe_i.data_misaligned || lsu_misaligned_o)
          rdata_q <= resp_rdata;
        else
          rdata_q <= data_rdata_ext;
      end
    end
  end

  // output to register file
  assign lsu_rdata_o = (resp_valid == 1'b1) ? data_rdata_ext : rdata_q;

  assign misaligned_st = id_ex_pipe_i.data_misaligned;

  // Note: PMP is not fully supported at the moment (not even if USE_PMP = 1)
  assign load_err_o      = 1'b0; // Not currently used
  assign store_err_o     = 1'b0; // Not currently used


  // check for misaligned accesses that need a second memory access
  // If one is detected, this is signaled with lsu_misaligned_o to
  // the controller which selectively stalls the pipeline
  always_comb
  begin
    lsu_misaligned_o = 1'b0;

    if (data_req_valid && !id_ex_pipe_i.data_misaligned)
    begin
      case (id_ex_pipe_i.data_type)
        2'b10: // word
        begin
          if (data_addr_int[1:0] != 2'b00)
            lsu_misaligned_o = 1'b1;
        end
        2'b01: // half word
        begin
          if (data_addr_int[1:0] == 2'b11)
            lsu_misaligned_o = 1'b1;
        end
      endcase // case (id_ex_pipe_i.data_type)
    end
  end

  // generate address from operands
  assign data_addr_int = (id_ex_pipe_i.prepost_useincr) ? (id_ex_pipe_i.alu_operand_a + id_ex_pipe_i.alu_operand_b) : id_ex_pipe_i.alu_operand_a;

  // Busy if there are ongoing (or potentially outstanding) transfers
  assign busy_o = (cnt_q != 2'b00) || trans_valid;

  //////////////////////////////////////////////////////////////////////////////
  // Transaction request generation
  //
  // Assumes that corresponding response is at least 1 cycle after request
  //
  // - Only request transaction when EX stage requires data transfer (id_ex_pipe_i.data_req), and
  // - maximum number of outstanding transactions will not be exceeded (cnt_q < DEPTH)
  //////////////////////////////////////////////////////////////////////////////

  // For last phase of misaligned transfer the address needs to be word aligned (as LSB of data_be will be set)
  assign trans.addr  = id_ex_pipe_i.data_misaligned ? {data_addr_int[31:2], 2'b00} : data_addr_int;
  assign trans.we    = id_ex_pipe_i.data_we;
  assign trans.be    = data_be;
  assign trans.wdata = data_wdata;
  assign trans.atop  = id_ex_pipe_i.data_atop;

  // Transaction request generation
  // OBI compatible (avoids combinatorial path from data_rvalid_i to data_req_o). Multiple trans_* transactions can be
  // issued (and accepted) before a response (resp_*) is received.
  assign trans_valid = data_req_valid && (cnt_q < DEPTH);


  // LSU WB stage is ready if it is not being used (i.e. no outstanding transfers, cnt_q = 0),
  // or if it WB stage is being used and the awaited response arrives (resp_rvalid).
  assign lsu_ready_wb_o = (cnt_q == 2'b00) ? !halt_wb_i : resp_valid && !halt_wb_i; //TODO:OK is this ok or not?

  // LSU EX stage readyness requires two criteria to be met:
  // 
  // - A data request (id_ex_pipe_i.data_req) has been forwarded/accepted (trans_valid && trans_ready)
  // - The LSU WB stage is available such that EX and WB can be updated in lock step
  //
  // Default (if there is not even a data request) LSU EX is signaled to be ready, else
  // if there are no outstanding transactions the EX stage is ready again once the transaction
  // request is accepted (at which time this load/store will move to the WB stage), else
  // in case there is already at least one outstanding transaction (so WB is full) the EX 
  // and WB stage can only signal readiness in lock step (so resp_valid is used as well).

  assign lsu_ready_ex_o =                !data_req_valid  ?                                              !halt_ex_i :
                                         (cnt_q == 2'b00) ? (              trans_valid && trans_ready && !halt_ex_i) : 
                                         (cnt_q == 2'b01) ? (resp_valid && trans_valid && trans_ready && !halt_ex_i) : 
                                                            resp_valid && !halt_ex_i; // TODO:OK is this ok or not?

  // Update signals for EX/WB registers (when EX has valid data itself and is ready for next)
  assign ctrl_update = lsu_ready_ex_o && data_req_valid;


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
      2'b00  : begin
        next_cnt = cnt_q;
      end
      2'b01  : begin
          next_cnt = cnt_q - 1'b1;
      end
      2'b10  : begin
          next_cnt = cnt_q + 1'b1;
      end
      2'b11  : begin
        next_cnt = cnt_q;
      end
    endcase
  end

  // Indicate that counter will be one in the next cycle
  assign cnt_is_one_next = next_cnt == 2'h1;

  //////////////////////////////////////////////////////////////////////////////
  // Registers
  //////////////////////////////////////////////////////////////////////////////

  always_ff @(posedge clk, negedge rst_n)
  begin
    if(rst_n == 1'b0)
    begin
      cnt_q <= '0;
    end
    else
    begin
      cnt_q <= next_cnt;
    end
  end

  //////////////////////////////////////////////////////////////////////////////
  // Handle bus errors
  //////////////////////////////////////////////////////////////////////////////

  // Propagate last trans.addr to WB stage (in case of bus_errors in WB this is needed for mtval)
  // In case of a detected error, updates to data_addr_wb_o will be
  // blocked by the controller until the NMI is taken.
  // TODO:OK: If a store following a load with bus error has dependencies on the load result,
    // it may use use an unspecified address and should be avoided for security reasons.
    // The NMI should be taken before this store.
  
  // Folowing block is within the EX stage
  always_ff @(posedge clk, negedge rst_n)
  begin
    if(rst_n == 1'b0) begin
      data_addr_wb_o <= 32'h0;
    end else begin
      // Update for valid addresses if not blocked by controller
      if(!block_data_addr_i && (trans_valid && trans_ready)) begin
        data_addr_wb_o <= trans.addr;
      end
    end
  end

  // Validate bus_error on rvalid (WB stage)
  assign data_err_wb_o = resp_valid && resp_err;


  //////////////////////////////////////////////////////////////////////////////
  // MPU
  //////////////////////////////////////////////////////////////////////////////

  assign trans.prot[0]   = 1'b1;  // Transfers from LSU are data transfers
  assign trans.prot[2:1] = PRIV_LVL_M; // Machine mode
  assign trans.memtype   = 2'b00; // memtype is assigned in the MPU, tie off.
  
  cv32e40x_mpu
    #(.IF_STAGE(0),
      .A_EXTENSION(A_EXTENSION),
      .CORE_RESP_TYPE(data_resp_t),
      .BUS_RESP_TYPE(obi_data_resp_t),
      .CORE_REQ_TYPE(obi_data_req_t),
      .PMA_NUM_REGIONS(PMA_NUM_REGIONS),
      .PMA_CFG(PMA_CFG))
  mpu_i
    (
     .clk                  ( clk             ),
     .rst_n                ( rst_n           ),
     .speculative_access_i ( 1'b0            ), // Load/stores are not speculative
     .atomic_access_i      ( 1'b0            ), // TODO:OE update to support atomic PMA checks
     .execute_access_i     ( 1'b0            ), // No accesses are intended for execution

     .core_one_txn_pend_n  ( cnt_is_one_next ),
     .core_trans_valid_i   ( trans_valid     ),
     .core_trans_ready_o   ( trans_ready     ),
     .core_trans_i         ( trans           ),
     .core_resp_valid_o    ( resp_valid      ),
     .core_resp_o          ( resp            ),

     .bus_trans_valid_o    ( bus_trans_valid ),
     .bus_trans_ready_i    ( bus_trans_ready ),
     .bus_trans_o          ( bus_trans       ),
     .bus_resp_valid_i     ( bus_resp_valid  ),
     .bus_resp_i           ( bus_resp        ));

  // Extract rdata and err from response struct
  assign resp_rdata = resp.bus_resp.rdata;
  assign resp_err   = resp.bus_resp.err;
  
  //////////////////////////////////////////////////////////////////////////////
  // OBI interface
  //////////////////////////////////////////////////////////////////////////////

  
  cv32e40x_data_obi_interface
  data_obi_i
  (
    .clk                   ( clk               ),
    .rst_n                 ( rst_n             ),

    .trans_valid_i         ( bus_trans_valid   ),
    .trans_ready_o         ( bus_trans_ready   ),
    .trans_i               ( bus_trans         ),

    .resp_valid_o          ( bus_resp_valid    ),
    .resp_o                ( bus_resp          ),

    .m_c_obi_data_if       ( m_c_obi_data_if   )
  );

endmodule
