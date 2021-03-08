module cv32e40x_mpu_sva import cv32e40x_pkg::*; import uvm_pkg::*;
  #(parameter bit          IF_STAGE = 1,
    parameter type         RESP_TYPE = inst_resp_t,
    parameter int unsigned MAX_IN_FLIGHT = 2,
    parameter int unsigned PMA_NUM_REGIONS = 1,
    parameter pma_region_t PMA_CFG[PMA_NUM_REGIONS-1:0] = '{PMA_R_DEFAULT})
  (
   input logic         clk,
   input logic         rst_n,
   
   input logic         speculative_access_i,
   input logic         atomic_access_i,

   // Interface towards bus interface
   input logic                       obi_if_trans_ready_i,
   input logic [31:0]                obi_if_trans_addr_o,
   input logic                       obi_if_trans_valid_o,
   input logic                       obi_if_resp_valid_i,
   input obi_inst_resp_t             obi_if_resp_i,

   // Interface towards core
   input logic [31:0]                core_trans_addr_i,
   input logic                       core_trans_we_i,
   input logic                       core_trans_valid_i,
   input logic                       core_trans_ready_o,
   input logic                       core_resp_valid_o,
   input inst_resp_t                 core_inst_resp_o,

   input logic [$clog2(MAX_IN_FLIGHT+1)-1:0] in_flight_q,
   input mpu_status_e                        mpu_status,
   input logic                               mpu_block_core,
   input logic                               mpu_block_obi,
   input mpu_state_e                         state_q,
   input logic                               mpu_err
   );
  
  // Checks for illegal PMA region configuration
  initial begin : p_mpu_assertions

    assert (PMA_NUM_REGIONS == $size(PMA_CFG)) else `uvm_error("mpu", "PMA_CFG must contain PMA_NUM_REGION entries")

    for(int i=0; i<PMA_NUM_REGIONS; i++) begin
      if (PMA_CFG[i].main) begin
        assert (PMA_CFG[i].atomic) else `uvm_error("mpu", "PMA regions configured as main must also support atomic operations")
      end

      if (!PMA_CFG[i].main) begin
        assert (!PMA_CFG[i].cacheable) else `uvm_error("mpu", "PMA regions configured as I/O cannot be defined as cacheable")
      end
    end
    
  end
  
  // MPU should never see misaligned transfers
  a_mpu_misaligned :
    assert property (@(posedge clk)
                     (core_trans_addr_i[1:0] == 2'b00) )
      else `uvm_error("mpu", "MPU does not supprot misaligned transfers")

  
  // Should never receive OBI response when no transfers are in flight
  a_mpu_cnt_uf :
    assert property (@(posedge clk)
                     (obi_if_resp_valid_i) |-> (in_flight_q > 0) )
      else `uvm_error("mpu", "in_flight_q underflow")
    
  // Never initiate OBI transfer while in flight counter is maxed out
  a_mpu_cnt_of :
    assert property (@(posedge clk)
                     (obi_if_trans_valid_o && obi_if_trans_ready_i) |-> (in_flight_q != MAX_IN_FLIGHT) )
      else `uvm_error("mpu", "in_flight_q overflow")

  
  // Only give error response when there are no OBI transfers in flight
  a_mpu_status_no_in_flight :
    assert property (@(posedge clk)
                     (mpu_status != MPU_OK) |-> (in_flight_q == 0) )
      else `uvm_error("mpu", "MPU error while transactions in flight")

  // Should never give MPU error response in the same cycle as OBI response
  a_mpu_status_no_obi_rvalid :
    assert property (@(posedge clk)
                     (mpu_status != MPU_OK) |-> (!obi_if_resp_valid_i) )
      else `uvm_error("mpu", "MPU error while OBI rvalid")

  // Should only block core side while waiting to give MPU error response
  a_mpu_block_core_iff_wait :
    assert property (@(posedge clk)
                     (mpu_block_core) |-> ((state_q == MPU_RE_ERR_WAIT) || (state_q == MPU_WR_ERR_WAIT)) )
      else `uvm_error("mpu", "MPU blocking core side when not needed")

  // Should only block OBI side upon MPU error, and while waiting to give MPU error response
  a_mpu_block_obi_iff_err :
    assert property (@(posedge clk)
                     (mpu_block_obi) |-> (mpu_err || (state_q == MPU_RE_ERR_WAIT) || (state_q == MPU_WR_ERR_WAIT)) )
      else `uvm_error("mpu", "MPU blocking OBI side when not needed")

endmodule : cv32e40x_mpu_sva

