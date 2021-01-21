// Copyright 2020 Silicon Labs, Inc.
//
// This file, and derivatives thereof are licensed under the
// Solderpad License, Version 2.0 (the "License").
//
// Use of this file means you agree to the terms and conditions
// of the license and are in full compliance with the License.
//
// You may obtain a copy of the License at:
//
//     https://solderpad.org/licenses/SHL-2.0/
//
// Unless required by applicable law or agreed to in writing, software
// and hardware implementations thereof distributed under the License
// is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS
// OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
//
// See the License for the specific language governing permissions and
// limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Øystein Knauserud - oystein.knauserud@silabs.com           //
//                                                                            //
// Design Name:    Register file wrapper                                      //
// Project Name:   CV32E40X                                                   //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Wrapper for the register file                              //
////////////////////////////////////////////////////////////////////////////////

module cv32e40x_register_file_wrapper
    #(
        parameter ADDR_WIDTH      = 5,
        parameter DATA_WIDTH      = 32,
        parameter NUM_READ_PORTS  = 2,
        parameter NUM_WRITE_PORTS = 2
    )
    (
        // Clock and Reset
        input  logic         clk,
        input  logic         rst_n,
    
        input  logic         scan_cg_en_i,
    
        // Read ports
        input  logic [NUM_READ_PORTS-1:0][ADDR_WIDTH-1:0] raddr_i,
        output logic [NUM_READ_PORTS-1:0][DATA_WIDTH-1:0] rdata_o,
    
        // Write ports
        input logic [NUM_WRITE_PORTS-1:0] [ADDR_WIDTH-1:0] waddr_i,
        input logic [NUM_WRITE_PORTS-1:0] [DATA_WIDTH-1:0] wdata_i,
        input logic [NUM_WRITE_PORTS-1:0] we_i
    
        
    );
    
    cv32e40x_register_file
    #(
      .ADDR_WIDTH         ( ADDR_WIDTH             ),
      .DATA_WIDTH         ( DATA_WIDTH             ),
      .NUM_READ_PORTS     ( NUM_READ_PORTS ),
      .NUM_WRITE_PORTS    ( NUM_WRITE_PORTS)
    )
    register_file_i
    (
      .clk                ( clk                ),
      .rst_n              ( rst_n              ),
    
      .scan_cg_en_i       ( scan_cg_en_i       ),
    
      // Read ports
      .raddr_i            ( raddr_i            ),
      .rdata_o            ( rdata_o            ),
    
      // Write ports
      .waddr_i            ( waddr_i            ),
      .wdata_i            ( wdata_i            ),
      .we_i               ( we_i               )
                 
    ); 
    
    endmodule
    