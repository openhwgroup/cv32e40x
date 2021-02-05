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

module cv32e40x_prefetch_buffer
(
  input  logic        clk,
  input  logic        rst_n,

  input  logic        req_i,
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
  output logic        busy_o
);
  // FIFO_DEPTH controls also the number of outstanding memory requests
  // FIFO_DEPTH must be greater than 1 to respect assertion in prefetch controller
  // FIFO_DEPTH set to 3 to not get additional stalls compared to separate aligner + fifo
  localparam FIFO_DEPTH                     = 3; //must be greater or equal to 2 //Set at least to 3 to avoid stalls compared to the master branch
  localparam int unsigned FIFO_ADDR_DEPTH   = $clog2(FIFO_DEPTH);

  logic  [FIFO_ADDR_DEPTH:0] fifo_cnt; // fifo_cnt should count from 0 to FIFO_DEPTH!

  logic [31:0] fetch_rdata;

  logic fetch_valid;


  assign perf_imiss_o = !fetch_valid && !branch_i;
  //////////////////////////////////////////////////////////////////////////////
  // Prefetch Controller
  //////////////////////////////////////////////////////////////////////////////

  cv32e40x_prefetch_controller
  #(
    .DEPTH          ( FIFO_DEPTH    )   
  )
  prefetch_controller_i
  (
    .clk                      ( clk                  ),
    .rst_n                    ( rst_n                ),

    .req_i                    ( req_i                ),
    .branch_i                 ( branch_i             ),
    .branch_addr_i            ( branch_addr_i        ),
    .busy_o                   ( busy_o               ),

    .trans_valid_o            ( trans_valid_o        ),
    .trans_ready_i            ( trans_ready_i        ),
    .trans_addr_o             ( trans_addr_o         ),

    .resp_valid_i             ( resp_valid_i         ),

    .fetch_valid_o            ( fetch_valid          ),
    .fifo_cnt_i               ( fifo_cnt             )
  );

  // Feed data to alignment_buffer directly from OBI response data
  assign fetch_rdata = resp_rdata_i;

  cv32e40x_alignment_buffer
  #(
      .DEPTH (FIFO_DEPTH),
      .FIFO_ADDR_DEPTH (FIFO_ADDR_DEPTH)
  )
  alignment_buffer_i
  (
    .clk               ( clk                                ),
    .rst_n             ( rst_n                              ),

    // prefetch controller
    .fetch_valid_i     ( fetch_valid                        ),
    .fetch_rdata_i     ( fetch_rdata                        ),
    .fifo_cnt_o        ( fifo_cnt                           ),

    // If stage
    .instr_valid_o     ( prefetch_valid_o                   ),
    .instr_ready_i     ( prefetch_ready_i                   ),
    .instr_aligned_o   ( prefetch_instr_o                   ),
    .instr_addr_o      ( prefetch_addr_o                    ),

    .branch_addr_i     ( branch_addr_i                      ),
    .branch_i          ( branch_i                           )
    
  );

  //----------------------------------------------------------------------------
  // Assertions
  //----------------------------------------------------------------------------

`ifdef CV32E40P_ASSERT_ON

  // FIFO_DEPTH must be greater than 1. Otherwise, the property
  // p_hwlp_end_already_gnt_when_hwlp_branch in cv32e40x_prefetch_controller
  // is not verified, since the prefetcher cannot ask for HWLP_END the cycle
  // in which HWLP_END-4 is being absorbed by ID.
  property p_fifo_depth_gt_1;
     @(posedge clk) (FIFO_DEPTH > 1);
  endproperty

  a_fifo_depth_gt_1 : assert property(p_fifo_depth_gt_1);

  // Check that branch target address is half-word aligned (RV32-C)
  property p_branch_halfword_aligned;
     @(posedge clk) (branch_i) |-> (branch_addr_i[0] == 1'b0);
  endproperty

  a_branch_halfword_aligned : assert property(p_branch_halfword_aligned);

  // Check that a taken branch can only occur if fetching is requested
  property p_branch_implies_req;
     @(posedge clk) (branch_i) |-> (req_i);
  endproperty

  a_branch_implies_req : assert property(p_branch_implies_req);

  // Check that after a taken branch the initial FIFO output is not accepted
  property p_branch_invalidates_fifo;
     @(posedge clk) (branch_i) |-> (!(fetch_valid && prefetch_ready_i));
  endproperty

  a_branch_invalidates_fifo : assert property(p_branch_invalidates_fifo);

`endif

endmodule // cv32e40x_prefetch_buffer
