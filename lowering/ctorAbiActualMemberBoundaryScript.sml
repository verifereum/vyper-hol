Theory ctorAbiActualMemberBoundary
Ancestors
  ctorAbiActualNarrowWord ctorAbiActualMemberSetup abiDecoderMemberBody
  abiDecoderContract abiDecoderReentry abiEncoderRegisteredEffect abiDecoderReentryPointer abiDecoderDynamicLoopSetup
  abiEncoder fragExec compileEnv valueEncoding contractABI words list arithmetic

Theorem ctor_actual_member_setup_narrow:
  abi_decoder_members ce env sf pretys pretvs preavs prevs /\
  abi_decoder_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  mem_bytes_at sb (LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs)))) initial.vs_data_section =
    enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))) (ListV (preavs ++ av::avs)) /\
  sb + LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) (pretys ++ ty::tys)))
    (ListV (preavs ++ av::avs))) < dimword (:256) /\
  abi_decode_member_setup dst src DLOAD (Lit 0w) hi (dec_info_needs_offset (type_to_abi_dec_info sf ce ty))
    (SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys)))
    (SUM (MAP (type_memory_bytes ce) pretys)) st = (ops,middle) /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  middle.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st middle (\s. s = initial)
    (\t. eval_operand (FST ops) t = SOME (n2w (sb +
        if type_to_abi_dec_info sf ce ty = DecComplex T [] then
          SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) pretys))
        else abi_tuple_child_offset (MAP (vyper_to_abi_type env) (pretys ++ ty::tys))
          (preavs ++ av::avs) (LENGTH pretys))) /\
      eval_operand (SND ops) t = SOME (n2w (d + SUM (MAP (type_memory_bytes ce) pretys))) /\
      fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var initial t /\
      abi_encoder_registered_effect {} [] initial t /\
      t.vs_memory = initial.vs_memory /\ t.vs_allocas = initial.vs_allocas /\
      t.vs_alloca_next = initial.vs_alloca_next) (K F)
Proof
  strip_tac >> drule_all ctor_actual_member_setup >>
  disch_then (qspec_then `ctx` assume_tac) >>
  irule frag_exec_conseq >> goal_assum (drule_at Any) >> simp[Excl "enc_def"] >>
  rpt strip_tac >>
  `abi_encoder_registered_effect {} [] initial s` by
    (irule ctor_actual_address_empty_effect >> conj_tac >>
     goal_assum (drule_at Any)) >>
  gvs[abi_decoder_address_frame_def, Excl "enc_def"]
QED
