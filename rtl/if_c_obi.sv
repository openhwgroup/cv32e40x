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


// OBI interface definition for instruction and data
// The two parameters set the types for payload 
// as these are different for instruction and data
interface if_c_obi import cv32e40x_pkg::*;
#(
    parameter type REQ_TYPE  = inst_req_t,
    parameter type RESP_TYPE = inst_resp_t
);
    // A channel signals
    logic                      req;
    logic                      gnt;
    REQ_TYPE                   req_payload;
    // R channel signals
    logic                      rvalid;
    RESP_TYPE                  resp_payload;
  
    modport master
       (
       output req, req_payload,
       input  gnt, rvalid, resp_payload
       );
  
endinterface : if_c_obi
