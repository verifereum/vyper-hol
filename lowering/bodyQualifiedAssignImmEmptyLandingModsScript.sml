(* The empty immutable route starts at the actual target exit. *)
Theory bodyQualifiedAssignImmEmptyLandingMods
Ancestors
  bodyAssignQualifiedStageJoinMods bodyQualifiedPlaceTargetEntryMods
  bodyQualifiedPlaceRhsPostMods bodyQualifiedPlaceImmScalarMods
  bodyPlaceWriteTailAdmissibleMods bodyImmutableAugAssignStore
  bodyWriteTargetStageMods bodyFullTargetDefs bodyFullShared gasContext
  gasOutcomeFullPostMods memoryLocalRhsProps stmtSimLogCompose
  bodyInvCodeProps bodyInvSplit loweringPosts bodySimFull vyperStorageFootprint
  exprLoweringProps bodyFullPredsMods vyperState stmtLoweringMono ptrDiscipline

val store_post =
  ``\(H : (bool # bytes32 # type_value) list # num list) res ef Gf tf t.
      ?ce. stmt_lands lctx sb res t /\ ~t.vs_halted /\
        (res = INL () ==> ~block_is_terminated sb /\ ce = cenv) /\
        cenv_top_ext cenv ce ef.scopes /\ stmt_state_rel H ctx func ce cx ef t /\
        immutable_frame_mods func ce cx ef t /\ storage_well_formed_on cx ef (FST H) /\
        return_buf_frame d ce sb t /\ alloca_history func t /\ return_buf_sep d ce ef t /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s0.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at_mods (DF H) lo d ce cx ef Gf tf t /\
        (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
        (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
        (!x. not_fresh_at sa x ==>
          FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
        alloca_frame cenv es sa s0 ce ef t /\
        (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
          (!n b len. local_region cenv es.scopes s0 n b len ==> off + sz <= b \/ b + len <= off) /\
          off <= i /\ i < off + sz /\ i IN tf.t_mem ==> i IN tn0.t_mem)``;

Theorem reached_imm_empty_write_normal[local]:
  gas_admissible (write_place cx (ImmutablePlace owner id path) v) (stmt_res_ok lctx) ee /\
  ee.gas_obs = [] /\
  ALOOKUP ee.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables owner imms) id = SOME (itv,iv) /\
  evaluate_subscripts itv iv path = INL old ==>
  ?ef. write_place cx (ImmutablePlace owner id path) v ee = (INL (),ef)
Proof
  strip_tac >>
  Cases_on `write_place cx (ImmutablePlace owner id path) v ee` >>
  rename1 `write_place _ _ _ _ = (wr,ef)` >>
  `stmt_res_ok lctx wr` by
    (qpat_x_assum `gas_admissible _ _ _`
       (qspec_then `[]` mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
     simp[]) >>
  drule_all_then strip_assume_tac immutable_augassign_path_write_source >> simp[]
QED

Theorem qualified_assign_imm_empty_landing_mods:
  target_root bt = TopLevelNameTarget key /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  type_place_target env bt = SOME (Type dty) /\
  type_widens_to env.type_defs (expr_type e) dty /\
  (!i se. MEM i (target_indices bt) /\ expr_sim_inv_mods mods cenv cx env se ==>
     expr_body_pre_mods mods cenv cx env i se) /\
  local_ptrs_reserved cenv sa /\ return_buf_sep d cenv es s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  fn_inst_ids_distinct func /\ fn_has_code st sb func /\
  gas_admissible (eval_stmt cx (Assign (BaseTarget bt) e)) (stmt_res_ok lctx) es /\
  qualified_assign_code_mods cenv bt e sa sb shadow_sa shadow_sb saved sr st
    shadow_sr shadow_st dst /\
  qualified_assign_rhs_reached_mods cx st0 e es s0
    (qualified_place_rhs_post_mods (DF,lo,d,ctx,func) mods cenv cx env bt e dty
       es sa shadow_sa sr shadow_sr saved s0 G0 tn0) ms v mid Gu tu u /\
  qualified_assign_target_reached_mods (DF,lo,d,ctx,func) cenv cx st0 bt dty
    mid sr st dst u Gu tu marks p ee Gz tz z /\
  qualified_assign_route_mods AssignImmEmpty key p saved dty dst /\
  (!bw capacity. d = SOME (bw,capacity) ==> allocas_from (w2n bw + capacity) z) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (write_place cx p v) (ee,z,Gz,tz) ^store_post
    (assign_qualified_exit_mods ctx cx RetQ)
Proof
  PairCases_on `key` >> strip_tac >>
  qpat_x_assum `qualified_assign_route_mods _ _ _ _ _ _`
    (strip_assume_tac o SRULE [qualified_assign_route_mods_def]) >>
  gvs[] >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[qualified_assign_target_reached_mods_def,storage_trace_domain_def] >>
  drule_all_then strip_assume_tac qualified_place_store_frame_mods >>
  gvs[] >>
  drule_then strip_assume_tac write_target_immutable_view_mods >>
  qpat_assum `qualified_assign_rhs_reached_mods _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_rhs_reached_mods_def]) >>
  qpat_assum `qualified_assign_target_reached_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_target_reached_mods_def]) >>
  drule_all_then assume_tac assign_reached_write_admissible_mods >>
  drule_all_then strip_assume_tac reached_imm_empty_write_normal >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then (mp_tac o MATCH_MP qualified_place_rhs_saved_view_mods)) >>
  simp[] >> strip_tac >> gvs[] >>
  `has_length_word dty` by
    (irule type_widens_to_has_length_word >> qexistsl_tac [`expr_type e`,`env.type_defs`] >> simp[]) >>
  `ALOOKUP cenv.ce_modules cenv.ce_module = SOME tops` by
    (drule_then assume_tac contract_inv_cenv_modules >> fs[module_body_inv_def]) >>
  qpat_assum `qualified_assign_code_mods _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_code_mods_def]) >>
  `sa.cs_next_var <= st.cs_next_var` by
    (qspecl_then [`bt`,`cenv`,`sa`] mp_tac ci_mono_compile_get_target_ptr >> simp[ci_mono_def]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx es s0` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _` (drule_then ACCEPT_TAC)) >>
  `alloca_frame cenv es sa s0 cenv ee z` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ es s0`
       (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule log_wb_alloca_frame) >>
     simp[EQ_SYM_EQ] >> qexists_tac `ee` >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    dead_lo_ok_mods H (DF H) lo cenv cx /\ stmt_state_rel H ctx func cenv cx ee z /\
    immutable_frame_mods func cenv cx ee z /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee Gz tz z` by
    (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
       (drule_then (strip_assume_tac o MATCH_MP write_target_post_view_mods)) >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> write_target_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (strip_assume_tac o MATCH_MP write_target_post_view_mods) >>
  `op_taint tz (FST dst) = {}` by fs[target_ptr_ok_def] >>
  `return_buf_sep d cenv ee z` by
    (qpat_assum `return_buf_sep d cenv es s0`
       (mp_then (Pat `return_buf_sep _ _ _ _`) irule return_buf_sep_transport) >>
     simp[arithmeticTheory.ADD_COMM]) >>
  qpat_assum `wb_frame cenv es ee sa s0 z` (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
  qpat_assum `dst = (FST dst,_,_)` (fn eq =>
    qpat_assum `assign_place_store_code_mods cenv e NONE dst st = _`
      (assume_tac o ONCE_REWRITE_RULE [eq])) >>
  `eval_operand (FST dst) z = SOME (n2w (off+k))` by fs[arithmeticTheory.ADD_COMM] >>
  irule gas_outcome_full_mods_post_source >>
  irule_at Any qualified_place_imm_empty_mods >>
  qpat_assum `contract_inv mods exps ctx cenv cx` (irule_at Any) >>
  qpat_assum `expr_sim_inv_mods mods cenv cx env ee` (irule_at Any) >>
  qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 Gz tz` (irule_at Any) >>
  qpat_assum `fn_has_code st sb func` (irule_at Any) >>
  qpat_assum `return_buf_sep d cenv ee z` (irule_at Any) >>
  qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `FLOOKUP (get_source_immutables _ _) _ = _` (irule_at Any) >>
  qpat_assum `mem_path_offset _ _ = _` (irule_at Any) >>
  qpat_assum `eval_operand (FST dst) z = SOME (n2w (off+k))` (irule_at Any) >>
  qpat_assum `assign_place_store_code_mods cenv e NONE (FST dst,_,_) st = _` (irule_at Any) >>
  qpat_assum `ALOOKUP cenv.ce_modules cenv.ce_module = SOME tops` (irule_at Any) >>
  qexistsl_tac [`lctx`,`assign_qualified_exit_mods ctx cx RetQ`] >>
  BETA_TAC >> simp[] >>
  rpt gen_tac >> strip_tac >> first_assum ACCEPT_TAC
QED
