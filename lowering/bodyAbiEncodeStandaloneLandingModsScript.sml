(* Move the fixed singleton row through setup, then interpret its one payload run. *)
Theory bodyAbiEncodeStandaloneLandingMods
Ancestors
  bodyAbiEncodePayloadLandingMods bodyAbiEncodeSingleSetupViewMods
  bodyAbiEncodeStandaloneMods bodyAbiEncodePackedPostMods
  exprBodyPreProps exprSimHypsDefs typedMemoryCopy exprSimProps exprSimWordArgs
  wordArgsPtr stateRelProj vyperStorageFootprint freshWrites
  loweringPosts loweringStateRelDefs venomState finite_map list pair words arithmetic
Libs horizonTypeLib

Theorem singleton_saved_cuts[local]:
  abi_encode_saved_row_mods lo ce cx sa ready e sv v si sm ss vv copy (H:(bool # bytes32 # type_value) list # num list) ee G tn s /\
  (?si' sm' ss' vv' copy'.
     abi_encode_saved_row_mods lo ce cx sa ready e sv v si' sm' ss' vv' copy' H' ee G tn s) ==>
  abi_encode_saved_row_mods lo ce cx sa ready e sv v si sm ss vv copy H' ee G tn s
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `vv_storage_live H' cx sv ee s` by
    (qpat_assum `abi_encode_saved_row_mods _ _ _ _ _ _ _ _ _ _ _ _ _ H' _ _ _ _`
       (mp_tac o PURE_REWRITE_RULE [abi_encode_saved_row_mods_def]) >>
     simp_tac bool_ss []) >>
  qpat_x_assum `abi_encode_saved_row_mods _ _ _ _ _ _ _ _ _ _ _ _ _ H _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encode_saved_row_mods_def]) >>
  asm_rewrite_tac[abi_encode_saved_row_mods_def]
QED

Theorem singleton_memory_layout[local]:
  expr_body_pre_mods mods ce cx env e es ==>
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv)
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_inv >>
  qpat_x_assum `expr_sim_inv_mods _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> disch_tac >> irule typed_copy_memory_size >>
  qexists_tac `get_tenv cx` >> asm_rewrite_tac[] >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==> _`
    (drule_then (ACCEPT_TAC o CONJUNCT2))
QED

Theorem abi_encode_standalone_landing_mods:
  LENGTH args = 1 /\ ~ensure /\ ~is_word_type (lowered_value_type ce (HD args)) /\
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  eval_exprs cx args (es with gas_obs := gs) = (INL vs,ee) /\
  stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list) ctx func ce cx es s0 /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_encode_packed_post_mods mods DF lo d ctx func ce cx env
      args svs sa st es s0 G0 tn0 H (INL vs : value list + 'err) ee G tn s) /\
  compile_abi_encode_payload ce (LENGTH args = 1 /\ ~ensure) svs
    (MAP (lowered_value_type ce) args) (Var dp) ready = (len,body_end) /\
  fn_has_code ready body_end func /\ fn_inst_ids_distinct func /\
  k = LENGTH (abi_encode_method_id_bytes mid) /\
  cap = 32 + 32 * word_size (abi_size_bound ce.ce_struct_fields (lowered_value_type ce (HD args)) + k) /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce st /\
  sa.cs_next_var <= st.cs_next_var /\ sa.cs_next_id <= st.cs_next_id /\
  st.cs_next_var <= allocated.cs_next_var /\ st.cs_next_var <= ready.cs_next_var /\
  st.cs_next_id < ready.cs_next_id /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP pre.vs_allocas aid = SOME entry) /\
  (!aid b n. aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,n) ==>
    regions_disjoint p cap b n) /\
  (!name b n. local_region ce ee.scopes u name b n ==> regions_disjoint p cap b n) /\
  (!x. not_fresh_at st x ==> lookup_var x pre = lookup_var x s /\
     FLOOKUP Gpre x = FLOOKUP G x /\ op_taint tnpre (Var x) = op_taint tn (Var x)) /\
  lo <= s.vs_alloca_next /\ s.vs_alloca_next <= pre.vs_alloca_next /\
  lo <= p /\ 32+write_len <= cap /\
  typed_copy_state_frame allocated (p+32) write_len u pre /\
  (!b n. b+n <= p+32 \/ p+32+write_len <= b ==>
     mem_bytes_at b n pre.vs_memory = mem_bytes_at b n s.vs_memory) /\
  (!i. i IN tu.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < p+cap)) /\
  tnpre.t_mem = tu.t_mem DIFF {i | p+32 <= i /\ i < p+32+write_len} /\
  tnpre.t_stor = tn.t_stor /\ tnpre.t_trans = tn.t_trans /\
  pre.vs_accounts = s.vs_accounts /\ pre.vs_transient = s.vs_transient /\
  pre.vs_call_ctx = s.vs_call_ctx /\ pre.vs_labels = s.vs_labels /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w cap)] [root]) (fn_insts func) /\
  not_local_ptr ce ee.scopes root /\
  not_fresh_at ready root /\ not_fresh_at ready dp /\
  eval_operand (Var root) pre = SOME (n2w p) /\ ptr_covers Gpre tnpre root pre cap /\
  eval_operand (Var dp) pre = SOME (n2w (p+32+k)) /\ ptr_covers Gpre tnpre dp pre (cap-(32+k)) /\
  FLOOKUP pre.vs_allocas st.cs_next_id = SOME (p,cap) /\
  read_memory (p+32) k pre = abi_encode_method_id_bytes mid /\
  (!i. p+32 <= i /\ i < p+32+k ==> i NOTIN tnpre.t_mem) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee pre /\ immutable_frame_mods func ce cx ee pre /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gpre tnpre pre) /\
  return_buf_frame d ce ready pre /\ alloca_history func pre /\ ~pre.vs_halted /\
  pre.vs_current_bb = ready.cs_current_bb /\ pre.vs_inst_idx = LENGTH ready.cs_current_insts /\
  wb_frame ce es ee sa s0 pre /\ ghost_kept_at lo ce es sa G0 tn0 s0 Gpre tnpre /\
  (~EXISTS expr_has_effect args ==> pure_frame ce func es sa s0 pre) /\
  MAP FDOM ee.scopes = MAP FDOM es.scopes /\ s0.vs_alloca_next <= pre.vs_alloca_next ==>
  ?bytes limit q Gq tq.
    abi_encode_payload_landing_mods ctx func ce cx st0 DF lo d explicit PG
      ann ensure mid target args vs (es,sa,s0,G0,tn0) ee (pre,Gpre,tnpre)
      (body_end,st.cs_next_id,p,cap,root,len) (bytes,limit,q,Gq,tq)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `LENGTH args = 1`
    (qx_choose_then `e` SUBST_ALL_TAC o REWRITE_RULE [LENGTH_EQ_1]) >>
  `ensure = F` by simp[] >> pop_assum SUBST_ALL_TAC >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    (qpat_assum `storage_trace_domain _ _ _` (ACCEPT_TAC o REWRITE_RULE [storage_trace_domain_def])) >>
  `?sv v. svs = [sv] /\ vs = [v]` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> abi_encode_packed_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _ _ _ _ _`
       (drule_then (strip_assume_tac o REWRITE_RULE [abi_encode_packed_post_mods_def])) >>
     `LENGTH svs = 1` by fs[] >>
     qpat_x_assum `LENGTH svs = 1`
       (qx_choose_then `sv` SUBST_ALL_TAC o REWRITE_RULE [LENGTH_EQ_1]) >>
     simp[] >> qpat_assum `LIST_REL _ _ _` (mp_tac o MATCH_MP LIST_REL_LENGTH) >>
     fs[LENGTH_EQ_1]) >>
  qpat_x_assum `svs = [_]` SUBST_ALL_TAC >> qpat_x_assum `vs = [_]` SUBST_ALL_TAC >>
  rename1 `eval_exprs cx [e] _ = (INL [v],ee)` >>
  rename1 `compile_abi_encode_payload ce _ [sv] _ _ _ = _` >>
  qpat_x_assum `~is_word_type _` (assume_tac o SIMP_RULE list_ss [HD]) >>
  qpat_x_assum `cap = _` (assume_tac o REWRITE_RULE [HD]) >>
  qpat_x_assum `compile_abi_encode_payload _ _ _ _ _ _ = _`
    (assume_tac o SIMP_RULE list_ss [MAP, LENGTH]) >>
  `st.cs_next_id <= ready.cs_next_id` by decide_tac >>
  suspend "row"
QED

Resume abi_encode_standalone_landing_mods[row]:
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    ?si sm ss vv copy.
      abi_encode_saved_row_mods lo ce cx sa st e sv v si sm ss vv copy H ee G tn s /\
      abi_encode_saved_row_mods lo ce cx sa ready e sv v si sm ss vv copy H ee Gpre tnpre pre /\
      (!x. vv_operand sv = Var x ==> not_fresh_at ready x)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> abi_encode_packed_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _ _ _ _ _`
       (drule_then assume_tac) >>
     drule_all (SIMP_RULE bool_ss [] (Q.INST [`single` |-> `T`] abi_encode_single_setup_view_mods)) >>
     disch_then (qx_choosel_then [`si`,`sm`,`ss`,`vv`,`copy`,`raw`] strip_assume_tac) >>
     qexistsl_tac [`si`,`sm`,`ss`,`vv`,`copy`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  pop_assum (fn th => assume_tac th >>
    drule_then (qx_choosel_then [`si`,`sm`,`ss`,`vv`,`copy`] strip_assume_tac) th) >>
  `ss.cs_next_id <= st.cs_next_id` by
    (qpat_assum `abi_encode_saved_row_mods _ _ _ _ st _ _ _ _ _ ss _ _ _ _ _ _ _`
       (mp_tac o PURE_REWRITE_RULE [abi_encode_saved_row_mods_def]) >> simp_tac bool_ss []) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_encode_saved_row_mods lo ce cx sa ready e sv v si sm ss vv copy H ee Gpre tnpre pre /\
    stmt_state_rel H ctx func ce cx ee pre /\ immutable_frame_mods func ce cx ee pre /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gpre tnpre pre` by
    (gen_tac >> disch_tac >> conj_tac
     >- (irule singleton_saved_cuts >>
         conj_tac
         >- (qpat_assum `!H. valid_horizon _ _ H _ ==> ?si sm ss vv copy. _`
               (drule_then (qx_choosel_then [`a`,`b`,`c`,`vv'`,`copy'`] strip_assume_tac)) >>
             qexistsl_tac [`a`,`b`,`c`,`vv'`,`copy'`] >> first_assum ACCEPT_TAC) >>
         qexists_tac `storage_trace_horizon ee.storage_trace` >> first_assum ACCEPT_TAC) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ pre /\ _`
       (drule_then ACCEPT_TAC)) >>
  suspend "run"
QED

Resume abi_encode_standalone_landing_mods[run]:
  drule_then strip_assume_tac singleton_memory_layout >>
  `get_tenv cx SUBMAP get_tenv cx` by simp[] >>
  mp_tac (Q.INST [`front` |-> `st`, `aid` |-> `st.cs_next_id`,
    `s` |-> `pre`, `G` |-> `Gpre`, `tn` |-> `tnpre`, `saved` |-> `sv`,
    `dst` |-> `dp`, `E0` |-> `get_tenv cx`] abi_encode_nonword_payload_mods) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp_tac arith_ss []))) >>
  disch_then (qx_choosel_then [`bytes`,`limit`,`q`,`Gq`,`tq`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  suspend "frames"
QED

Resume abi_encode_standalone_landing_mods[frames]:
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by (sym_tac >> first_assum ACCEPT_TAC) >>
  `wb_frame ce es ee sa s0 q` by
    (match_mp_tac (Q.INST [`H` |-> `H0`,`s1` |-> `st`,`t` |-> `pre`,`es1` |-> `ee`]
       (SPEC_ALL (horizonTypeLib.at_horizon_named "H" wb_frame_trans))) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_kept_at lo ce es sa G0 tn0 s0 Gq tq` by
    (irule (horizonTypeLib.at_horizon_named "H" ghost_kept_at_wb_trans) >>
     qpat_assum `stmt_state_rel H0 ctx func ce cx es s0` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo ce es sa G0 tn0 s0 Gpre tnpre` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo ce ee st Gpre tnpre pre Gq tq` (irule_at Any) >>
     qexists_tac `ee` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `~EXISTS expr_has_effect [e] ==> pure_frame ce func es sa s0 q` by
    (disch_tac >>
     `pure_frame ce func es sa s0 pre` by
       (qpat_assum `~EXISTS expr_has_effect [e] ==> _` (drule_then ACCEPT_TAC)) >>
     irule pure_frame_trans >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`ee`,`st`,`pre`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (qpat_assum `wb_frame ce es ee sa s0 pre`
           (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [wb_frame_def])) >>
     qpat_assum `wb_frame ce ee ee st pre q`
       (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [wb_frame_def])) >>
  suspend "finish"
QED

Resume abi_encode_standalone_landing_mods[finish]:
  `local_ptrs_rel func ce ee.scopes q` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ q /\ _`
       (drule_then (strip_assume_tac o CONJUNCT1)) >>
     drule_then (ACCEPT_TAC o CONJUNCT1) stmt_state_rel_local_ptrs_alloca) >>
  `sa.cs_next_var <= body_end.cs_next_var /\ s0.vs_alloca_next <= q.vs_alloca_next` by decide_tac >>
  `!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at body_end x` by
    (rpt gen_tac >> disch_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `st` >> conj_tac >- first_assum ACCEPT_TAC >> first_assum (drule_then ACCEPT_TAC)) >>
  `!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at body_end x` by
    (rpt gen_tac >> disch_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `st` >> conj_tac >- first_assum ACCEPT_TAC >> first_assum (drule_then ACCEPT_TAC)) >>
  `32 + LENGTH (abi_encode_method_id_bytes mid ++ bytes) <= cap` by
    (rewrite_tac [LENGTH_APPEND] >> decide_tac) >>
  qexistsl_tac [`bytes`,`limit`,`q`,`Gq`,`tq`] >>
  simp_tac bool_ss [abi_encode_payload_landing_mods_def, LET_THM, MAP, loweringPostsTheory.expr_has_effect_thm] >>
  qpat_assum `k = LENGTH _` (fn th => REWRITE_TAC [GSYM th]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise abi_encode_standalone_landing_mods
