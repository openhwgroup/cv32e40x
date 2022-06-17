package cv32e40x_sequencer_pkg;

  //todo: check and remove unused
  typedef logic [4:0] regnum_t;
  typedef logic [4:0] seq_i;

  localparam REG_ZERO = 5'd0;
  localparam REG_RA = 5'd1;
  localparam REG_SP = 5'd2;

  typedef enum logic [3:0] {
    INVALID_INST,
    PUSH,
    POP,
    POPRET,
    POPRETZ,
    MVA01S,
    MVSA01
  } seq_instr_e;

  typedef enum logic [3:0] {
    R_NONE    = 4'd0,
    //RA        = 4'h0,
    RA_S0     = 4'd1,
    RA_S0_S1  = 4'd2,
    RA_S0_S2  = 4'd3,
    RA_S0_S3  = 4'd4,
    RA_S0_S4  = 4'd5,
    RA_S0_S5  = 4'd6,
    RA_S0_S6  = 4'd7,
    RA_S0_S7  = 4'd8,
    RA_S0_S8  = 4'd9,
    RA_S0_S9  = 4'd10,
    RA_S0_S11 = 4'd12
  } pushpop_rlist_e;

  typedef struct packed {
    //logic [4:0] complete_seq_len;
    logic [11:0] register_stack_adj;
    pushpop_rlist_e registers_saved;
    logic [11:0] additional_stack_adj;
    logic [11:0] total_stack_adj;  //Redundant
    logic [11:0] current_stack_adj;
    regnum_t sreg;
  } pushpop_decode_s;


  function automatic regnum_t sn_to_regnum(regnum_t snum);
    case (snum)
      0, 1: sn_to_regnum = regnum_t'(snum + 8);
      default: sn_to_regnum = regnum_t'(snum + 16);
    endcase
  endfunction

  function automatic logic [11:0] align_16(logic [11:0] number);
    align_16 = 12'((number + 12'hF) & 12'hFF0);
  endfunction

  function automatic pushpop_rlist_e pushpop_reg_length(logic [3:0] rlist4);
    case (rlist4)
      'd0:     pushpop_reg_length = R_NONE;
      'd1:     pushpop_reg_length = R_NONE;
      'd2:     pushpop_reg_length = R_NONE;
      'd3:     pushpop_reg_length = R_NONE;
      'd4:     pushpop_reg_length = R_NONE;
      'd5:     pushpop_reg_length = RA_S0;
      'd6:     pushpop_reg_length = RA_S0_S1;
      'd7:     pushpop_reg_length = RA_S0_S2;
      'd8:     pushpop_reg_length = RA_S0_S3;
      'd9:     pushpop_reg_length = RA_S0_S4;
      'd10:    pushpop_reg_length = RA_S0_S5;
      'd11:    pushpop_reg_length = RA_S0_S6;
      'd12:    pushpop_reg_length = RA_S0_S7;
      'd13:    pushpop_reg_length = RA_S0_S8;
      'd14:    pushpop_reg_length = RA_S0_S9;
      'd15:    pushpop_reg_length = RA_S0_S11;
      default: pushpop_reg_length = R_NONE;
    endcase
  endfunction

  // State machine definition
  typedef enum logic [3:0] { S_IDLE, S_PUSH, S_POP, S_DMOVE, S_RA, S_SP, S_A0, S_RET} seq_state_e;

endpackage