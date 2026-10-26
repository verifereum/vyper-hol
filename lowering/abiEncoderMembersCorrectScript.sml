(* Execute every actual remaining member, composing the recursive child contracts. *)
Theory abiEncoderMembersCorrect
Ancestors
  abiEncoderMembersStep abiEncoderMembersContract abiEncoderMembersDefs abiEncoderMembersPrepare
  abiEncoderMemberCode abiEncoderChildCompose abiEncoderInput abiEncoderInputLayout
  abiDecoderMemberPhases abiDecoderDynamicLoopSetup abiDecoderEffect abiDecoderLoop
  abiDecoderContract fragExec compileEnv valueEncoding contractABI venomState list arithmetic

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

Theorem abi_encoder_members_correct_cons:
  abi_encoder_members_correct infos ==>
  abi_encoder_members_correct ((ei,abi_sz,mem_sz,dyn)::infos)
Proof
  strip_tac >> simp_tac bool_ss [abi_encoder_members_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_members_inv_nonempty >> strip_tac >>
  Cases_on `tys` >- fs[] >> Cases_on `avs` >- fs[] >>
  rename1 `abi_encoder_members_inv ((ei,abi_sz,mem_sz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs active dyn_ptr site slot first last lo st limit_st src dst sb so ho d hl output_size b cap initial` >>
  qpat_x_assum `EVERY _ (_::_)`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE (srw_ss()) [EVERY_DEF]) >>
  qpat_assum `abi_encoder_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_inv_def]) >>
  drule_all abi_encoder_member_cons_context >> strip_tac >>
  `prepared.cs_next_var <= limit_st.cs_next_var /\ child_end.cs_next_var <= limit_st.cs_next_var /\
    child_end.cs_next_id <= last /\ st.cs_next_var <= prepared.cs_next_var /\
    st.cs_next_var <= child_end.cs_next_var` by decide_tac >>
  `cs_extends st child_end` by
    (irule cs_extends_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`end_st` |-> `child_end`, `final` |-> `end_st`] abi_decoder_members_tail_phi) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`child_src` |-> `elem_src`, `so` |-> `so+mem_sz`,
    `next_ho` |-> `ho+abi_sz`, `final` |-> `end_st`] abi_encoder_members_child_phi) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac abi_encoder_members_prepare >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  `fresh_vars_wrt limit_st ready` by
    (qpat_assum `abi_encoder_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ready`
       (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_inv_def]) >>
     first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`st` |-> `prepared`, `end_st` |-> `child_end`, `out` |-> `child_len`,
    `initial` |-> `ready:venom_state`] abi_encoder_members_child_advance) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func ready encoded` >>
  mp_tac (Q.INST [`st` |-> `child_end`, `initial` |-> `encoded:venom_state`,
    `so` |-> `so+mem_sz`, `ho` |-> `ho+abi_sz`, `pre` |-> `pre++[ty]`, `pvs` |-> `pvs++[av]`]
    abi_encoder_members_run) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func encoded actual` >>
  mp_tac (Q.INST [`child_lo` |-> `lo:num`, `child_hi` |-> `child_end.cs_next_id`,
    `child_next` |-> `prepared.cs_next_var`, `suffix_next` |-> `child_end.cs_next_var`,
    `child_d` |-> `d:num`, `child_sz` |-> `output_size:num`, `sz` |-> `output_size:num`,
    `next` |-> `st.cs_next_var`, `hi` |-> `end_st.cs_next_id`] abi_encoder_child_compose) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  qpat_assum `hl = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  qpat_assum `ho = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  RULE_ASSUM_TAC (SIMP_RULE bool_ss [GSYM APPEND_ASSOC, APPEND, abi_encoder_member_span_def,
    MAP, SUM, pairTheory.UNCURRY_DEF, ADD_ASSOC]) >>
  simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND, abi_encoder_member_span_def,
    MAP, SUM, pairTheory.UNCURRY_DEF, ADD_ASSOC] >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_members_correct_all:
  !infos. abi_encoder_members_correct infos
Proof
  Induct >> simp[abi_encoder_members_correct_empty] >>
  qx_gen_tac `entry` >> PairCases_on `entry` >>
  irule abi_encoder_members_correct_cons >> first_assum ACCEPT_TAC
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_MEMBERS_CORRECT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder members correctness not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderMembersCorrect");
