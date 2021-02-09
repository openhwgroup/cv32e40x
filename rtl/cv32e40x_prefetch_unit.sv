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
// Engineer:       Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                                                                            //
// Design Name:    Prefetcher Buffer for 32 bit memory interface              //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Prefetch Buffer that caches instructions. This cuts overly //
//                 long critical paths to the instruction cache               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

// input port: send address one cycle before the data
// clear_i clears the FIFO for the following cycle. in_addr_i can be sent in
// this cycle already

module cv32e40x_prefetch_unit
(
  input  logic        clk,
  input  logic        rst_n,

  input  logic        prefetch_en_i,
  input  logic        branch_i,
  input  logic [31:0] branch_addr_i,

  input  logic        prefetch_ready_i,
  output logic        prefetch_valid_o,
  output logic [31:0] prefetch_instr_o,
  output logic [31:0] prefetch_addr_o,

  // Transaction interface to obi interface
  output logic        trans_valid_o,
  input  logic        trans_ready_i,
  output logic [31:0] trans_addr_o,

  input  logic        resp_valid_i,
  input  logic [31:0] resp_rdata_i,
  input  logic        resp_err_i,

  output logic perf_imiss_o,

  // Prefetch Buffer Status
  output logic        prefetch_busy_o
);
  
  // FIFO_DEPTH set to 3 as the alignment_buffer will need 3 to function correctly
  localparam FIFO_DEPTH                     = 3; //must be greater or equal to 3
  localparam int unsigned FIFO_ADDR_DEPTH   = $clog2(FIFO_DEPTH);

  

  logic fetch_valid;
  logic fetch_ready;

  logic        fetch_branch;
  logic [31:0] fetch_branch_addr;


  

  //////////////////////////////////////////////////////////////////////////////
  // Prefetcher
  //////////////////////////////////////////////////////////////////////////////

  cv32e40x_prefetcher
  prefetcher_i
  (
    .clk                      ( clk                  ),
    .rst_n                    ( rst_n                ),

    .fetch_branch_i           ( fetch_branch         ),
    .fetch_branch_addr_i      ( fetch_branch_addr    ),
    .fetch_valid_i            ( fetch_valid          ),
    .fetch_ready_o            ( fetch_ready          ),

    .trans_valid_o            ( trans_valid_o        ),
    .trans_ready_i            ( trans_ready_i        ),
    .trans_addr_o             ( trans_addr_o         )

  );


  cv32e40x_alignment_buffer
  #(
      .DEPTH (FIFO_DEPTH),
      .FIFO_ADDR_DEPTH (FIFO_ADDR_DEPTH)
  )
  alignment_buffer_i
  (
    .clk                  ( clk                    ),
    .rst_n                ( rst_n                  ),

    .branch_addr_i        ( branch_addr_i          ),
    .branch_i             ( branch_i               ),
    .prefetch_en_i        ( prefetch_en_i          ),
    .prefetch_busy_o      ( prefetch_busy_o        ),

    // prefetch unit
    .fetch_valid_o        ( fetch_valid            ),
    .fetch_ready_i        ( fetch_ready            ),
    .fetch_branch_o       ( fetch_branch           ),
    .fetch_branch_addr_o  ( fetch_branch_addr      ),

    .resp_valid_i         ( resp_valid_i           ),
    .resp_rdata_i         ( resp_rdata_i           ),

    // Instruction interface
    .instr_valid_o        ( prefetch_valid_o       ),
    .instr_ready_i        ( prefetch_ready_i       ),
    .instr_instr_o        ( prefetch_instr_o       ),
    .instr_addr_o         ( prefetch_addr_o        ),

    .perf_imiss_o         ( perf_imiss_o           )

  );

  //----------------------------------------------------------------------------
  // Assertions
  //----------------------------------------------------------------------------

`ifdef ASSERT_ON
  `include "cv32e40x_prefetch_buffer.svh"
`endif

endmodule // cv32e40x_prefetch_unit
