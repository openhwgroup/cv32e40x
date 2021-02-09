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
// Authors    : Lukas Mueller    - lukasmue@student.ethz.ch                   //
//              Michael Gautschi - gautschi@iis.ee.ethz.ch                    //
//              Halfdan Bechmann - halfdan.bechmann@silabs.com                //
//                                                                            //
// Description: RTL assertions for the apu_disp module                        //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

import uvm_pkg::*;

assert property (@(posedge clk_i)
                 (apu_rvalid_i) |-> (valid_req | valid_inflight | valid_waiting))
  else `uvm_warning("apu_disp", "[APU Dispatcher] instruction returned while no instruction is in-flight")


