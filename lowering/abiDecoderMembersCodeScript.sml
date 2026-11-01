(* Recover code and endpoint conditions for each nonempty member-list phase. *)
Theory abiDecoderMembersCode
Ancestors
  abiDecoderMemberCons abiDecoderMemberCode abiDecoderMemberInfos abiDecoderContract
  abiDecoderMemberSetup abiDecoderDynamic abiDecoderLoop fragExec abiEncoder compileEnv
  venomState venomInst list arithmetic

Theorem abi_decoder_members_cons_code:
  compile_abi_decode_complex_elems dst src opc hi (abi_decoder_member_infos sf ce (ty::tys))
    ao vo st = ((),final) /\ abi_decode_source_opcode opc /\ fn_has_code st final func /\
  (st.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) ==>
  ?ops middle end_st.
    abi_decode_member_setup dst src opc hi (dec_info_needs_offset (type_to_abi_dec_info sf ce ty))
      ao vo st = (ops,middle) /\
    compile_abi_decode_to_buf (SND ops) (FST ops) opc hi
      (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
    compile_abi_decode_complex_elems dst src opc hi (abi_decoder_member_infos sf ce tys)
      (ao + abi_embedded_static_size ce.ce_struct_fields ty)
      (vo + type_memory_bytes ce ty) end_st = ((),final) /\
    fn_has_code st end_st func /\ fn_has_code end_st final func /\
    (middle.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    (end_st.cs_blocks = final.cs_blocks \/
      !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    st.cs_next_id <= end_st.cs_next_id /\ end_st.cs_next_id <= final.cs_next_id /\
    st.cs_next_var <= end_st.cs_next_var /\ end_st.cs_next_var <= final.cs_next_var
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_member_cons_trace >> strip_tac >>
  rename1 `abi_decode_member_setup dst src opc hi _ ao vo st = (ops,middle)` >>
  rename1 `compile_abi_decode_to_buf _ _ opc hi _ middle = ((),end_st)` >>
  drule_all abi_decoder_member_cons_code >> strip_tac >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  drule_all abi_decoder_members_child_phi >> disch_then assume_tac >>
  mp_tac abi_decoder_members_tail_phi >> impl_tac >- asm_simp_tac bool_ss [] >>
  disch_then assume_tac >>
  qexistsl_tac [`ops`, `middle`, `end_st`] >> asm_simp_tac bool_ss [] >> decide_tac
QED
