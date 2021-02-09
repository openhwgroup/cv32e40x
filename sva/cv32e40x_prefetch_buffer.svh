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
//                                                                            //
// Authors:        Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                 Halfdan Bechmann - halfdan.bechmann@silabs.com             //
//                                                                            //
// Description:    RTL assertions for the prefetch_buffer module              //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

import uvm_pkg::*;

// FIFO_DEPTH must be greater than 1. Otherwise, the property
// p_hwlp_end_already_gnt_when_hwlp_branch in cv32e40x_prefetch_controller
// is not verified, since the prefetcher cannot ask for HWLP_END the cycle
// in which HWLP_END-4 is being absorbed by ID.
property p_fifo_depth_gt_1;
   @(posedge clk) (FIFO_DEPTH > 1);
endproperty

a_fifo_depth_gt_1 : assert property(p_fifo_depth_gt_1) else `uvm_error("controller", "Assertion a_fifo_depth_gt_1 failed")

// Check that branch target address is half-word aligned (RV32-C)
property p_branch_halfword_aligned;
   @(posedge clk) (branch_i) |-> (branch_addr_i[0] == 1'b0);
endproperty

a_branch_halfword_aligned : assert property(p_branch_halfword_aligned)
  else `uvm_error("controller", "Assertion a_branch_halfword_aligned failed")

// Check that a taken branch can only occur if fetching is requested
property p_branch_implies_req;
   @(posedge clk) (branch_i) |-> (req_i);
endproperty

a_branch_implies_req : assert property(p_branch_implies_req)
  else `uvm_error("controller", "Assertion a_branch_implies_req failed")

// Check that after a taken branch the initial FIFO output is not accepted
property p_branch_invalidates_fifo;
   @(posedge clk) (branch_i) |-> (!(fetch_valid && prefetch_ready_i));
endproperty

a_branch_invalidates_fifo : assert property(p_branch_invalidates_fifo)
  else `uvm_error("controller", "Assertion a_branch_invalidates_fifo failed")

