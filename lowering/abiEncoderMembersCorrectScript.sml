(* Execute every actual remaining member, composing the recursive child contracts. *)
Theory abiEncoderMembersCorrect
Ancestors
  abiEncoderSourceMembersInterpret abiEncoderSourceMembersIndex abiEncoderMemberSpine
  abiEncoderMembersStep abiEncoderMembersContract abiEncoderMembersDefs abiEncoderMembersPrepare
  abiEncoderMemberCode abiEncoderChildCompose abiEncoderInput abiDecoderMemberPhases
  abiDecoderDynamicLoopSetup abiDecoderEffect abiDecoderLoop abiDecoderContract fragExec
  compileEnv valueEncoding contractABI venomState list arithmetic

Theorem abi_encoder_members_inv_nonempty:
  abi_encoder_members_inv ((ei,abi_sz,mem_sz,dyn)::infos) tys avs pre pvs active dyn_ptr site slot
    first last lo st limit_st src dst sb so ho d hl output_size b cap initial ==>
  tys <> [] /\ avs <> []
Proof
  strip_tac >> qpat_x_assum `abi_encoder_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_encoder_members_inv_def]) >>
  disch_then (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_encoder_members_pre_def]) >>
  simp_tac bool_ss [abi_encoder_complex_input_iff] >> rpt strip_tac >>
  Cases_on `tys` >> Cases_on `avs` >> gvs[abi_encoder_tuple_type_def]
QED

Theorem abi_encoder_members_correct_from_spine[local]:
  !infos. abi_encoder_members_correct infos
Proof
  gen_tac >> simp_tac bool_ss [abi_encoder_members_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_encoder_spine_code func limit_st end_st.cs_next_id (dst,src,dyn_ptr)
    infos (st,so,ho) (out,end_st)` by
    (simp_tac bool_ss [abi_encoder_spine_code_def] >> asm_simp_tac (srw_ss()) []) >>
  drule_all abi_encoder_source_members_index_initial >>
  disch_then (qspecl_then [`end_st.cs_next_id`,`func`,`ctx`] assume_tac) >>
  drule_all abi_encoder_source_members_generate >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac []
QED

Theorem abi_encoder_members_correct_cons:
  abi_encoder_members_correct infos ==>
  abi_encoder_members_correct ((ei,abi_sz,mem_sz,dyn)::infos)
Proof
  strip_tac >> MATCH_ACCEPT_TAC abi_encoder_members_correct_from_spine
QED

Theorem abi_encoder_members_correct_all:
  !infos. abi_encoder_members_correct infos
Proof
  MATCH_ACCEPT_TAC abi_encoder_members_correct_from_spine
QED
