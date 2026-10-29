(* Enter the current child by executing its real source-address instruction. *)
Theory abiEncoderMembersPrepare
Ancestors
  abiEncoderMemberSourcePhase
  abiEncoderMembersContract abiEncoderMembersDefs abiEncoderMembersSource abiEncoderAddressReach
  abiEncoderTuple abiEncoderChildInputs abiEncoderInput abiCanonicalWindows
  abiDecoderArrayInitExec abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderContract
  abiDecoderLoop fragExec emitHelperProps compileEnv valueEncoding venomState words list
  arithmetic

Theorem abi_encoder_members_prepare:
  emit_op ADD [src;Lit (n2w so)] st = (elem_src,prepared) /\ fn_has_code st prepared func /\
  abi_encoder_members_inv ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  prepared.cs_next_var <= limit_st.cs_next_var ==>
  ?ready. abi_encoder_members_inv ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
      pre pvs active dyn_ptr site slot first last lo prepared limit_st
      src dst sb so ho d hl output_size b cap ready /\
    abi_encoder_buffer_pre ei ty av prepared elem_src dst (sb+so) mem_sz d output_size b cap ready /\
    abi_decoder_address_frame st.cs_next_var initial ready /\ abi_decode_sim ctx func initial ready
Proof
  MATCH_ACCEPT_TAC abi_encoder_members_prepare_raw_compat
QED
