(* Closure-facing rich member execution, from the uniform generator only. *)
Theory abiEncoderSharedMembersCorrect
Ancestors
  abiEncoderSharedMembersInterpret abiEncoderSharedMembersIndex abiEncoderSharedMembersInput
  abiEncoderSharedContract abiEncoderOpenInput abiEncoderTuple abiEncoderMembersDefs
  abiEncoderMemberSpine abiScratchEffect abiEncoderRegisteredEffect abiEncoderExtendSim
  abiEncoderInput abiEncoderBufferFrame abiDecoderFootprint abiEncoderZeroFrame
  abiEncoderOpenInputFrame abiEncoderArrayFrame
  abiCanonicalWindows abiDecodeRanges abiDecoderDynamicLoopSetup abiDecoderContract abiDecoderLoop
  compileEnv valueEncoding contractABI venomState list arithmetic

Theorem abi_encoder_shared_members_root_pre:
  abi_encoder_shared_input (AbiComplex infos,at,ListV avs) (st,src,dst) (sb,source_cap)
    (d,output_size) (first,last,b,cap) initial /\ abi_encoder_tuple_type at tys ==>
  abi_encoder_shared_members_pre infos tys avs st src dst sb 0 d output_size first last b cap initial /\
  LIST_REL abi_encoder_structural_valid tys avs /\
  enc at (ListV avs) = enc (Tuple tys) (ListV avs)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_shared_input _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_input_def]) >>
  qpat_assum `abi_encoder_open_input (AbiComplex infos) at _ _ _ _`
    (qx_choose_then `layout` (qx_choose_then `values` strip_assume_tac) o
      REWRITE_RULE [abi_encoder_open_complex_iff]) >>
  `layout = tys` by
    (irule abi_encoder_tuple_type_unique >> qexists_tac `at` >> asm_simp_tac bool_ss []) >>
  gvs[Excl "enc_def"] >> rename1 `abi_encoder_tuple_type at tys` >>
  `LIST_REL abi_encoder_structural_valid tys avs` by
    (simp[LIST_REL_EL_EQN] >> rpt strip_tac >> rename1 `n < LENGTH avs` >>
     first_x_assum (qspec_then `n` mp_tac) >> simp[] >>
     Cases_on `EL n infos` >> PairCases_on `r` >>
     metis_tac[abi_encoder_open_input_valid]) >>
  `enc at (ListV avs) = enc (Tuple tys) (ListV avs)` by
    (gvs[abi_encoder_tuple_type_def] >> simp[Once enc_def, LET_THM]) >>
  `abi_encoder_open_input (AbiComplex infos) (Tuple tys) (ListV avs)
    sb (abi_encoder_member_span infos) initial.vs_memory` by
    (simp[abi_encoder_open_complex_iff, abi_encoder_tuple_type_def] >> metis_tac[]) >>
  `abi_footprint_disjoint sb (abi_encoder_member_span infos)
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial)` by
    (irule abi_footprint_disjoint_subwindow >> qexistsl_tac [`sb`,`source_cap`] >> simp[]) >>
  `regions_disjoint (sb,abi_encoder_member_span infos) (d,output_size)` by
    (gvs[abi_encoder_zero_aware_separation] >> decide_tac) >>
  asm_simp_tac bool_ss [abi_encoder_shared_members_pre_def, ADD_CLAUSES] >> decide_tac
QED

Theorem abi_encoder_shared_members_initial_inv:
  abi_encoder_shared_members_pre infos tys avs st src dst sb 0 d output_size first last b cap initial /\
  LIST_REL abi_encoder_structural_valid tys avs /\
  hl = head_lengths tys 0 /\ LENGTH (enc (Tuple tys) (ListV avs)) <= output_size /\
  abi_encoder_cursor active dyn_ptr site slot first lo st hl initial /\
  (active \/ EVERY (\(_,_,_,dyn). ~dyn) infos) /\
  abi_decoder_budget first last b cap initial /\ first <= lo /\ lo <= st.cs_next_id /\
  st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_encoder_shared_members_inv infos tys avs [] [] active dyn_ptr site slot first last lo st limit_st
    src dst sb 0 0 d hl output_size b cap initial
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `hl = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  asm_simp_tac (srw_ss()) [abi_encoder_shared_members_inv_def, abi_tuple_tails_def, Excl "enc_def"]
QED

Theorem abi_encoder_open_tuple_prefix_complete:
  LIST_REL abi_encoder_layout_valid tys avs /\
  abi_encoder_tuple_prefix (head_lengths tys 0) tys avs d mem ==>
  mem_bytes_at d (LENGTH (enc (Tuple tys) (ListV avs))) mem = enc (Tuple tys) (ListV avs)
Proof
  strip_tac >>
  `LENGTH tys = LENGTH avs` by metis_tac[LIST_REL_LENGTH] >>
  `enc (Tuple tys) (ListV avs) = FLAT (abi_tuple_heads (head_lengths tys 0) 0 tys avs) ++
    FLAT (abi_tuple_tails tys avs)` by simp[Once enc_def, enc_tuple_parts, LET_THM] >>
  `LENGTH (FLAT (abi_tuple_heads (head_lengths tys 0) 0 tys avs)) = head_lengths tys 0`
    by (drule abi_encoder_open_heads_length >> simp[head_lengths_acc]) >>
  qpat_assum `abi_encoder_tuple_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_tuple_prefix_def]) >>
  qpat_assum `enc (Tuple tys) (ListV avs) = _` (fn th => PURE_REWRITE_TAC [th]) >>
  irule abi_encoder_memory_append >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_shared_members_final_output:
  abi_encoder_shared_members_inv [] [] [] tys avs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap actual ==>
  mem_bytes_at d (LENGTH (enc (Tuple tys) (ListV avs))) actual.vs_memory =
    enc (Tuple tys) (ListV avs) /\
  abi_encoder_cursor active dyn_ptr site slot first lo st
    (LENGTH (enc (Tuple tys) (ListV avs))) actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS o
    SIMP_RULE bool_ss [abi_encoder_shared_members_inv_def, APPEND_NIL]) >>
  drule abi_encoder_structural_list_layout >> strip_tac >>
  `LENGTH (enc (Tuple tys) (ListV avs)) = hl+LENGTH (FLAT (abi_tuple_tails tys avs))` by
    (`LENGTH tys = LENGTH avs` by metis_tac[LIST_REL_LENGTH] >>
     simp[Once enc_def, enc_tuple_parts, LET_THM] >>
     drule abi_encoder_open_heads_length >> simp[head_lengths_acc]) >>
  conj_tac
  >- (qpat_assum `hl = _`
        (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
      irule abi_encoder_open_tuple_prefix_complete >> asm_simp_tac bool_ss []) >>
  qpat_assum `LENGTH (enc (Tuple tys) (ListV avs)) = _`
    (fn th => PURE_REWRITE_TAC [th]) >> first_assum ACCEPT_TAC
QED

Theorem abi_encoder_shared_members_correct:
  EVERY (\(ei,_,_,_). abi_encoder_shared ei) infos /\
  compile_abi_encode_complex_elems dst src infos so ho dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_shared_members_inv infos tys avs pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?t. abi_encoder_shared_members_inv [] [] [] (pre++tys) (pvs++avs) active dyn_ptr site slot first last lo
      end_st limit_st src dst sb (so+abi_encoder_member_span infos)
      (ho+SUM (MAP (\(_,abi_sz,_,_). abi_sz) infos)) d hl output_size b cap t /\
    abi_scratch_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial t /\
    abi_encoder_registered_effect (abi_decoder_ids lo end_st.cs_next_id) [(d,output_size)] initial t /\
    (alloca_inv initial ==> alloca_inv t) /\ abi_encoder_extend_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all (Q.INST [`hi` |-> `end_st.cs_next_id`] abi_encoder_shared_members_index_initial) >>
  disch_then (qspecl_then [`func`,`end_st`,`ctx`] assume_tac) >>
  `abi_encoder_spine_code func limit_st end_st.cs_next_id (dst,src,dyn_ptr)
    infos (st,so,ho) (out,end_st)` by simp[abi_encoder_spine_code_def] >>
  drule_all abi_encoder_shared_members_generate >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> asm_rewrite_tac []
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "shared closure admission, axiom or hypothesis"
  end) [abi_encoder_shared_members_root_pre, abi_encoder_shared_members_initial_inv,
    abi_encoder_open_tuple_prefix_complete, abi_encoder_shared_members_final_output,
    abi_encoder_shared_members_correct];
