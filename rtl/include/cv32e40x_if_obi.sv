/*
 Copyright 2020 Silicon Labs, Inc.
  
 This file, and derivatives thereof are licensed under the
 Solderpad License, Version 2.0 (the "License");
 Use of this file means you agree to the terms and conditions
 of the license and are in full compliance with the License.
 You may obtain a copy of the License at
  
 https://solderpad.org/licenses/SHL-2.0/
  
 Unless required by applicable law or agreed to in writing, software
 and hardware implementations thereof
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, EITHER EXPRESSED OR IMPLIED.
 See the License for the specific language governing permissions and
 limitations under the License.
 */


  // OBI interface definition for instruction bus
interface if_obi_instr; import cv32e40x_pkg::*;

    // A channel signals
    logic                      req;
    logic                      gnt;
    inst_req_t                 req_payload;
    // R channel signals
    logic                      rvalid;
    inst_resp_t                resp_payload;
  
    modport master
       (
       output req, req_payload,
       input  gnt, rvalid, resp_payload
       );
  
endinterface : if_obi_instr
  

// OBI interface definitions for data bus
interface if_obi_data; import cv32e40x_pkg::*;

    // A channel signals
    logic                      req;
    logic                      gnt;
    data_req_t                 req_payload;


    // R channel signals
    logic                      rvalid;
    data_resp_t                resp_payload;

    modport master
        (
        output req, req_payload,
        input  gnt, rvalid, resp_payload
        );

endinterface : if_obi_data
