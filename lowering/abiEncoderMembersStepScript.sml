(* Both child branches establish the same next-member state and execution contract. *)
Theory abiEncoderMembersStep
Ancestors
  abiEncoderMembersStatic abiEncoderMembersDynamic abiEncoderMembersContract abiEncoderCorrect
  abiEncoderChildInputs abiDecoderEffect abiDecoderLoop fragExec compileEnv valueEncoding venomState

Theorem abi_encoder_members_child_advance:
  abi_encoder_correct ei /\ compile_abi_encode_child dst elem_src ei dyn ho dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_members_inv ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  abi_encoder_buffer_pre ei ty av st elem_src dst (sb+so) mem_sz d output_size b cap initial /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?actual. abi_encoder_members_inv infos tys avs (pre++[ty]) (pvs++[av]) active dyn_ptr site slot
      first last lo end_st limit_st src dst sb (so+mem_sz) (ho+abi_sz) d hl output_size b cap actual /\
    abi_decoder_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\ abi_decode_sim ctx func initial actual
Proof
  Cases_on `dyn` >| [ACCEPT_TAC abi_encoder_members_dynamic_advance,
    ACCEPT_TAC abi_encoder_members_static_advance]
QED
