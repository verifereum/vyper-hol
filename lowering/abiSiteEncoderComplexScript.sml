(* Finite-site constructor assembly around the single member interpreter. *)
Theory abiSiteEncoderComplex
Ancestors
  abiScratchMembersInterpret abiScratchMembersIndex abiScratchMembers
  abiEncoderChildCapability abiEncoderChildContext abiSiteEncoderContract abiEncoderMemberSpine
  abiSiteEncoderBoundary abiEncoderComplexCode abiEncoderComplexDynamic
  abiEncoderComplexPrefix abiEncoderMembersInput abiEncoderTuple abiEncoderInput
  abiEncoderMemberCode abiEncoderMembersDefs
  abiScratchAddress abiScratchEffect abiDecoderLoop abiDecoderContract abiEncoderLoadReach
  abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderReentryAddress emitHelperProps
  abiSiteAllocation abiEncoderAddressReach abiDecoderSiteMembership compilerOccurrences
  compileEnv valueEncoding contractABI venomState pred_set words list arithmetic

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

Theorem abi_site_complex_finish:
  abi_site_members_inv [] [] [] tys avs T dyn_ptr site slot A lo st limit_st
    src dst sb so ho d hl output_size b cap encoded /\
  emit_op MLOAD [dyn_ptr] st = (out,end_st) /\ fn_has_code st end_st func /\
  end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?actual.
    mem_bytes_at d (LENGTH (enc (Tuple tys) (ListV avs))) actual.vs_memory =
      enc (Tuple tys) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple tys) (ListV avs)))) /\
    abi_site_encoder_effect A lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap encoded actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func encoded actual
Proof
  strip_tac >> drule abi_site_members_final_output >> strip_tac >>
  qpat_assum `abi_site_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ encoded`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_site_members_inv_def]) >>
  qpat_x_assum `abi_encoder_cursor T _ _ _ _ _ _ (LENGTH _) _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  `site IN A` by (qpat_x_assum `T ==> site IN A` mp_tac >> simp[]) >>
  drule_all abi_site_budget_site_bounds >> strip_tac >>
  `slot < dimword (:256)` by decide_tac >>
  mp_tac (Q.INST [`src` |-> `dyn_ptr`, `p` |-> `n2w slot:bytes32`,
    `w` |-> `n2w (LENGTH (enc (Tuple tys) (ListV avs))):bytes32`, `st'` |-> `end_st`,
    `initial` |-> `encoded:venom_state`] abi_encoder_load_reach) >>
  impl_tac >- asm_simp_tac (srw_ss()) [w2n_n2w] >> strip_tac >>
  rename1 `abi_decode_sim ctx func encoded actual` >>
  `abi_site_encoder_effect A lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap encoded actual` by
    (irule abi_site_address_effect >> asm_rewrite_tac[]) >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
Theorem abi_site_complex_prepare:
  abi_site_members_pre infos tys avs st src dst sb 0 d output_size A b cap initial /\
  abi_encode_complex_prefix infos st = (dyn_ptr,prepared) /\ fn_has_code st prepared func /\
  abi_site_budget A b cap initial /\ st.cs_next_id IN A /\
  prepared.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  LENGTH (enc (Tuple tys) (ListV avs)) <= output_size /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ready slot.
    abi_site_members_inv infos tys avs [] [] T dyn_ptr st.cs_next_id slot A st.cs_next_id
      prepared limit_st src dst sb 0 0 d (head_lengths tys 0) output_size b cap ready /\
    abi_site_encoder_effect A st.cs_next_id prepared.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial ready /\ abi_decode_sim ctx func initial ready
Proof
  strip_tac >> drule_all abi_site_complex_prefix_reach >>
  disch_then (qspecl_then [`output_size`, `d`, `ctx`] strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  qpat_x_assum `abi_site_complex_prefix_post _ _ _ _ _ _ _ _ _ _ _ _`
    (qx_choose_then `slot` strip_assume_tac o
     PURE_REWRITE_RULE [abi_site_complex_prefix_post_def]) >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  drule_all abi_site_members_pre_effect >> strip_tac >>
  `st.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  `abi_site_members_pre infos tys avs prepared src dst sb 0 d output_size A b cap ready` by
    (drule_all abi_site_members_pre_mono >> simp[]) >>
  qpat_assum `abi_site_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _ initial`
    (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_site_members_pre_def]) >> strip_tac >>
  drule abi_encoder_complex_input_metadata >> strip_tac >>
  qpat_assum `abi_site_encoder_effect _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_site_encoder_effect_def]) >>
  `abi_encoder_cursor T dyn_ptr st.cs_next_id slot 0 st.cs_next_id prepared
      (head_lengths tys 0) ready` by
    (simp_tac bool_ss [abi_encoder_cursor_def] >> asm_simp_tac (srw_ss()) [] >>
     simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     qexists_tac `st.cs_next_var` >> simp[]) >>
  qexistsl_tac [`ready`, `slot`] >> asm_rewrite_tac[] >>
  irule abi_site_members_initial_inv >> asm_simp_tac (srw_ss()) [] >> gvs[]
QED

Theorem abi_site_complex_phase_sites:
  abi_encode_complex_prefix infos st = (dyn_ptr,prepared) /\
  compile_abi_encode_complex_elems dst src infos 0 0 dyn_ptr prepared = (ignored,middle) /\
  emit_op MLOAD [dyn_ptr] middle = (out,end_st) /\
  abi_decoder_emitted_sites st.cs_next_id end_st.cs_next_id st end_st SUBSET A ==>
  st.cs_next_id IN A /\
  abi_decoder_emitted_sites prepared.cs_next_id middle.cs_next_id prepared middle SUBSET A
Proof
  strip_tac >> drule abi_encoder_complex_prefix_shape >> strip_tac >>
  drule abi_encoder_members_bounds >> strip_tac >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `cs_extends st prepared` by
    (irule cs_extends_same_block >> fs[inst_extends_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `cs_extends prepared end_st` by
    (irule cs_extends_trans >> qexists_tac `middle` >> asm_rewrite_tac[]) >>
  `st.cs_next_id <= prepared.cs_next_id /\ middle.cs_next_id <= end_st.cs_next_id /\
   prepared.cs_next_id <= end_st.cs_next_id` by decide_tac >>
  `abi_decoder_emitted_sites prepared.cs_next_id middle.cs_next_id prepared middle SUBSET
    abi_decoder_emitted_sites st.cs_next_id end_st.cs_next_id st end_st` by
    (irule abi_decoder_emitted_sites_subsegment >> asm_rewrite_tac[]) >>
  `abi_decoder_emitted_sites st.cs_next_id prepared.cs_next_id st prepared SUBSET
    abi_decoder_emitted_sites st.cs_next_id end_st.cs_next_id st end_st` by
    (irule abi_decoder_emitted_sites_subsegment >> simp[cs_extends_refl]) >>
  drule abi_site_complex_prefix_sites >> strip_tac >>
  `abi_decoder_emitted_sites st.cs_next_id prepared.cs_next_id st prepared SUBSET A /\
   abi_decoder_emitted_sites prepared.cs_next_id middle.cs_next_id prepared middle SUBSET A`
    by metis_tac[SUBSET_TRANS] >>
  conj_tac >- (
    qpat_x_assum `abi_decoder_emitted_sites st.cs_next_id prepared.cs_next_id st prepared SUBSET A`
      mp_tac >>
    qpat_x_assum `abi_decoder_emitted_sites st.cs_next_id prepared.cs_next_id st prepared = _`
      (fn th => rewrite_tac[th]) >> simp[]) >> asm_rewrite_tac[]
QED


val _ = List.app (fn (name,th) =>
  let val (ors,axs) = Tag.dest_tag (Thm.tag th) in
    if not (null (Thm.hyp th)) orelse not (null axs) orelse
       List.exists (fn s => s <> "DISK_THM") ors
    then raise Fail ("Finite-site complex dependency: " ^ name) else ()
  end) (DB.thms "abiSiteEncoderComplex");
