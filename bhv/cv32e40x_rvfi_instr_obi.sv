// Copyright (c) 2022 OpenHW Group
//
// Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// https://solderpad.org/licenses/
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//
// SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0

// CV32E40X RVFI instruction OBI interface (aligns instruction OBI signals to IF timing)
//
// Contributors: Arjan Bink <arjan.bink@silabs.com>

module cv32e40x_rvfi_instr_obi import cv32e40x_pkg::*; import cv32e40x_rvfi_pkg::*;
(
  input  logic                          clk,
  input  logic                          rst_n,

  input  logic                          prefetch_valid_i,
  input  logic                          prefetch_ready_i,
  input  logic [31:0]                   prefetch_addr_i,
  input  logic                          prefetch_compressed_i,
  input  logic                          kill_if_i,

  if_c_obi.monitor                      m_c_obi_instr_if,

  output rvfi_obi_instr_t               obi_instr                               // OBI address and response phase packet aligned to IF timing
);

  // DEPTH of the instruction buffer (at least depth of alignment buffer)
  localparam DEPTH = 4;                                                         // Needs to be power of 2 (due to used pointer arithmetic)
  localparam int unsigned PTR_WIDTH = $clog2(DEPTH);

  // FIFO
  rvfi_obi_instr_t [0:DEPTH-1]  fifo_q;                                         // FIFO with OBI address phase and response phase signals
  rvfi_obi_instr_t              fifo_req_n, fifo_resp_n;                        // FIFO with OBI address phase and response phase signals

  // Read/write pointers
  logic [PTR_WIDTH-1:0]         rptr_q, rptr_n;                                 // Pointer to FIFO entry to be read
  logic [PTR_WIDTH-1:0]         rptr_q_inc;                                     // Next read pointer (needed if instruction word is split over two entries) 
  logic [PTR_WIDTH-1:0]         wptr_req_q, wptr_req_n;                         // Pointer to FIFO (address phase) entry to be written
  logic [PTR_WIDTH-1:0]         wptr_resp_q, wptr_resp_n;                       // Pointer to FIFO (response phase) entry to be written
  logic [PTR_WIDTH:0]           cnt_q, cnt_n;                                   // Number of FIFO entries including incoming entries

  logic                         fifo_req_push;                                  // Push FIFO when receiving OBI address phase signals
  logic                         fifo_resp_push;                                 // Push FIFO when receiving OBI response phase signals
  logic                         fifo_pop;                                       // Pop FIFO when entry has been fully used

  // Outstanding and started OBI transactions
  logic [PTR_WIDTH-1:0]         outstanding_cnt_n, outstanding_cnt_q;
  logic                         outstanding_count_up;
  logic                         outstanding_count_down;

  logic                         started_q, started_n;                           // OBI transaction started (but not yet outstanding)

  logic [PTR_WIDTH-1:0]         flush_cnt;                                      // Number of FIFO entries to be flushed upon IF kill

  //////////////////////////////////////////////////////////////////////////////
  // Count number of outstanding OBI transactions
  //////////////////////////////////////////////////////////////////////////////

  assign outstanding_count_up   = m_c_obi_instr_if.s_req.req && m_c_obi_instr_if.s_gnt.gnt;
  assign outstanding_count_down = m_c_obi_instr_if.s_rvalid.rvalid;

  always_comb begin
    outstanding_cnt_n = outstanding_cnt_q;

    case ({outstanding_count_up, outstanding_count_down})
      2'b00 : begin
        outstanding_cnt_n = outstanding_cnt_q;
      end
      2'b01 : begin
        outstanding_cnt_n = outstanding_cnt_q - 1'b1;
      end
      2'b10 : begin
        outstanding_cnt_n = outstanding_cnt_q + 1'b1;
      end
      2'b11 : begin
        outstanding_cnt_n = outstanding_cnt_q;
      end
    endcase

    started_n = (m_c_obi_instr_if.s_req.req && !m_c_obi_instr_if.s_gnt.gnt) ? 1'b1 : 1'b0;
  end


  //////////////////////////////////////////////////////////////////////////////
  // Number of FIFO entries to be flushed
  //////////////////////////////////////////////////////////////////////////////

  // If an OBI transavyion has been started (req = 1), but not yet acceppted (gnt = 1),
  // then it is not yet counted as outstanding, but it should be flushed nonetheless upon
  // an IF kill.
  
  assign flush_cnt = started_q ? outstanding_cnt_q + 1'b1 : outstanding_cnt_q;

  // The RVFI instruction OBI FIFO tracks reads, writes and flushes of the alignment
  // buffer. As its size is at least the size of the alignment buffer, this FIFO
  // should never overflow. As the OBI response phase is at least a cycle after
  // the address phase acceptance, the address phase FIFO push will always be
  // to a different FIFO entry than the response phase FIFO push.

  // Push OBI address phase signals into FIFO when OBI address phase is accepted
  assign fifo_req_push = m_c_obi_instr_if.s_req.req && m_c_obi_instr_if.s_gnt.gnt;

  // Push OBI response phase signals into FIFO when OBI response phase is accepted
  assign fifo_resp_push = m_c_obi_instr_if.s_rvalid.rvalid;

  // Pop FIFO when reading word or when reading upper halfword
  always_comb
  begin
    if (prefetch_compressed_i) begin
      // Only pop FIFO when using upper halfword
      fifo_pop = prefetch_valid_i && prefetch_ready_i && (prefetch_addr_i[1:0] == 2'b10);
    end else begin
      fifo_pop = prefetch_valid_i && prefetch_ready_i;
    end
  end

  //////////////////////////////////////////////////////////////////////////////
  // FIFO reads/writes
  //////////////////////////////////////////////////////////////////////////////

  assign rptr_n = rptr_q + 1'b1;

  // Next address phase signals to FIFO
  always_comb
  begin
    fifo_req_n = fifo_q[wptr_req_q];
    fifo_req_n.req_payload = m_c_obi_instr_if.req_payload;
    wptr_req_n = wptr_req_q + 1'b1; 
  end

  // Next response phase signals to FIFO
  always_comb
  begin
    fifo_resp_n = fifo_q[wptr_resp_q];
    fifo_resp_n.resp_payload = m_c_obi_instr_if.resp_payload;
    wptr_resp_n = wptr_resp_q + 1'b1; 
  end

  //////////////////////////////////////////////////////////////////////////////
  // Registers
  //////////////////////////////////////////////////////////////////////////////

  always_ff @(posedge clk, negedge rst_n)
  begin
    if (rst_n == 1'b0) begin
      cnt_q                   <= 'b0;
      rptr_q                  <= 'b0;
      wptr_req_q              <= 'b0;
      wptr_resp_q             <= 'b0;
      fifo_q                  <= 'b0;
      outstanding_cnt_q       <= 'b0;
      started_q               <= 1'b0;
    end else begin
      // FIFO reads
      if (kill_if_i) begin
        cnt_q                 <= '0;                                    // No more entries in FIFO
        rptr_q                <= PTR_WIDTH'(wptr_resp_q + flush_cnt);   // Flush/skip existing + incoming entries (assumes rptr_q is power of 2)
      end else begin
        if (fifo_pop) begin
          rptr_q              <= rptr_n;
        end
      end

      // FIFO writes
      if (fifo_req_push) begin                                          // Will not push to same FIFO entry as response phase signals
        fifo_q[wptr_req_q]  <= fifo_req_n;
        wptr_req_q          <= wptr_req_n;
      end
      if (fifo_resp_push) begin                                         // Will not push to same FIFO entry as address phase signals
        fifo_q[wptr_resp_q] <= fifo_resp_n;
        wptr_resp_q         <= wptr_resp_n;
      end

      // OBI transaction outstanding or started
      outstanding_cnt_q     <= outstanding_cnt_n;
      started_q             <= started_n;

    end
  end

  assign rptr_q_inc = rptr_q + 1'b1;                                    // Next read pointer

  //////////////////////////////////////////////////////////////////////////////
  // Transform FIFO content into compressed / uncompressed instructions plus meta data
  //////////////////////////////////////////////////////////////////////////////

  // The FIFO can have at most 3 entries full (because the alignment buffer has that depth); so,
  // if rptr_q == wptr_resp_q, then the FIFO is empty and OBI response phase payload gets passed
  // on directly from OBI. OBI address phase payload is available earlier and will therefore always
  // be present in the FIFO.

  always_comb
  begin
    if (prefetch_compressed_i) begin
      if (prefetch_addr_i[1:0] == 2'b00) begin
        // Compressed instruction in LSBs of 1 rdata item
        obi_instr.req_payload               =  fifo_q[rptr_q].req_payload;
        obi_instr.resp_payload.rdata[31:16] =  16'h0;
        obi_instr.resp_payload.rdata[15:0]  =  (rptr_q     == wptr_resp_q) ? fifo_resp_n.resp_payload.rdata[15:0]  : fifo_q[rptr_q].resp_payload.rdata[15:0];
        obi_instr.resp_payload.err          =  (rptr_q     == wptr_resp_q) ? fifo_resp_n.resp_payload.err          : fifo_q[rptr_q].resp_payload.err;
      end else begin
        // Compressed instruction in MSBs of 1 rdata item
        obi_instr.req_payload               =  fifo_q[rptr_q].req_payload;
        obi_instr.resp_payload.rdata[31:16] =  16'h0;
        obi_instr.resp_payload.rdata[15:0]  =  (rptr_q     == wptr_resp_q) ? fifo_resp_n.resp_payload.rdata[31:16] : fifo_q[rptr_q].resp_payload.rdata[31:16];
        obi_instr.resp_payload.err          =  (rptr_q     == wptr_resp_q) ? fifo_resp_n.resp_payload.err          : fifo_q[rptr_q].resp_payload.err;
      end
    end else begin
      if (prefetch_addr_i[1:0] == 2'b00) begin
        // Uncompressed instruction (or pointer) in 1 rdata item
        obi_instr.req_payload               =  fifo_q[rptr_q].req_payload;
        obi_instr.resp_payload.rdata[31:16] =  (rptr_q     == wptr_resp_q) ? fifo_resp_n.resp_payload.rdata[31:16] : fifo_q[rptr_q].resp_payload.rdata[31:16];
        obi_instr.resp_payload.rdata[15:0]  =  (rptr_q     == wptr_resp_q) ? fifo_resp_n.resp_payload.rdata[15:0]  : fifo_q[rptr_q].resp_payload.rdata[15:0];
        obi_instr.resp_payload.err          =  (rptr_q     == wptr_resp_q) ? fifo_resp_n.resp_payload.err          : fifo_q[rptr_q].resp_payload.err;
      end else begin
        // Uncompressed instruction (or pointer) in 2 rdata items
        obi_instr.req_payload               =  fifo_q[rptr_q].req_payload;
        obi_instr.resp_payload.rdata[31:16] =  (rptr_q_inc == wptr_resp_q) ? fifo_resp_n.resp_payload.rdata[15:0]  : fifo_q[rptr_q_inc].resp_payload.rdata[15:0];
        obi_instr.resp_payload.rdata[15:0]  =                                                                        fifo_q[rptr_q].resp_payload.rdata[31:16];
        obi_instr.resp_payload.err          = ((rptr_q_inc == wptr_resp_q) ? fifo_resp_n.resp_payload.err          : fifo_q[rptr_q_inc].resp_payload.err) ||
                                                                                                                     fifo_q[rptr_q].resp_payload.err;
      end
    end
  end

endmodule
