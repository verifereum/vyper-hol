(* Finite-site constructor assembly around the single member interpreter. *)
Theory abiSiteEncoderComplex
Ancestors
  abiScratchMembersInterpret abiScratchMembersIndex abiScratchMembers
  abiEncoderChildCapability abiEncoderChildContext abiSiteEncoderContract abiEncoderMemberSpine
  abiSiteEncoderBoundary abiEncoderComplexCode abiEncoderComplexDynamic
  abiEncoderComplexPrefix abiEncoderMembersInput abiEncoderTuple abiEncoderInput
  abiEncoderMemberCode abiEncoderMembersDefs
  abiScratchAddress abiScratchEffect abiDecoderLoop abiDecoderContract
  compileEnv valueEncoding contractABI venomState list arithmetic

Theorem abi_site_members_run:
  EVERY (\(ei,_,_,_). abi_site_encoder ei) infos /\
  compile_abi_encode_complex_elems dst src infos so ho dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_site_members_inv infos tys avs pre pvs active dyn_ptr site slot A lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  abi_decoder_emitted_sites st.cs_next_id end_st.cs_next_id st end_st SUBSET A /\
  end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?t. abi_site_members_inv [] [] [] (pre++tys) (pvs++avs) active dyn_ptr site slot A lo
      end_st limit_st src dst sb (so+abi_encoder_member_span infos)
      (ho+SUM (MAP (\(_,abi_sz,_,_). abi_sz) infos)) d hl output_size b cap t /\
    abi_site_encoder_effect A lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial t /\ abi_decode_sim ctx func initial t
Proof
  strip_tac >>
  `EVERY (\(ei,_,_,_). abi_encoder_child_capability A
    (\st en. abi_decoder_emitted_sites st.cs_next_id en.cs_next_id st en SUBSET A) ei) infos` by
    (irule EVERY_MONOTONIC >> goal_assum (drule_at Any) >>
     simp_tac bool_ss [pairTheory.FORALL_PROD, pairTheory.UNCURRY_DEF] >>
     metis_tac[abi_encoder_child_capability_site]) >>
  drule_all (Q.INST [`hi` |-> `end_st.cs_next_id`] abi_site_members_index_initial) >>
  disch_then (qspecl_then [`func`,`end_st`,`ctx`] assume_tac) >>
  `abi_encoder_spine_code func limit_st end_st.cs_next_id (dst,src,dyn_ptr)
    infos (st,so,ho) (out,end_st)` by simp[abi_encoder_spine_code_def] >>
  drule_all (SRULE [abi_encoder_hereditary_guard_sites] (Q.INST
    [`guard` |-> `\st en. abi_decoder_emitted_sites st.cs_next_id en.cs_next_id st en SUBSET A`]
    abi_site_members_generate)) >> strip_tac >>
  qexists_tac `t` >> asm_rewrite_tac []
QED

Theorem abi_site_encoder_complex_static:
  EVERY (\(ei,_,_,_). abi_site_encoder ei) infos /\
  ~EXISTS (\(_,_,_,dyn). dyn) infos ==>
  abi_site_encoder (AbiComplex infos)
Proof
  strip_tac >> simp_tac bool_ss [abi_site_encoder_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_site_encoder_input _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_site_encoder_input_def]) >>
  disch_then (qx_choose_then `tys` (qx_choose_then `avs`
    (MAP_EVERY assume_tac o CONJUNCTS)) o REWRITE_RULE [abi_encoder_complex_input_iff]) >>
  qpat_x_assum `av = ListV avs` SUBST_ALL_TAC >>
  drule_all abi_site_members_root_pre >> strip_tac >>
  qpat_assum `enc at (ListV avs) = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  qpat_assum `abi_site_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_site_members_pre_def]) >> strip_tac >>
  drule_all abi_encoder_complex_static_length >> disch_tac >>
  drule abi_encoder_complex_static_flags >> disch_tac >>
  drule_all abi_encoder_complex_static_trace >> strip_tac >>
  drule abi_encoder_members_bounds >> strip_tac >>
  `start.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`active` |-> `F`, `dyn_ptr` |-> `Lit 0w`, `site` |-> `0:num`,
    `slot` |-> `0:num`, `lo` |-> `start.cs_next_id`, `st` |-> `start`,
    `hl` |-> `head_lengths tys 0`, `output_size` |-> `LENGTH (enc (Tuple tys) (ListV avs))`]
    abi_site_members_initial_inv) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_encoder_cursor_def, Excl "enc_def"] >> disch_tac >>
  drule_all abi_site_members_run >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_assum `abi_site_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t`
    (assume_tac o SIMP_RULE bool_ss [APPEND, ADD_CLAUSES]) >>
  drule abi_site_members_final_output >> strip_tac >>
  qpat_assum `abi_site_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_site_members_inv_def]) >>
  qexists_tac `t` >> asm_simp_tac (srw_ss()) [eval_operand_def, Excl "enc_def"]
QED

val _ = List.app (fn (name,th) =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th) in
    if not (null (Thm.hyp th)) orelse not (null axs) orelse
       List.exists (fn s => s <> "DISK_THM") ors
    then raise Fail ("Finite-site complex dependency: " ^ name) else ()
  end) (DB.thms "abiSiteEncoderComplex");
