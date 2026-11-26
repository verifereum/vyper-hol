(* The empty assignment emits a zero into the observed destination slot.
   Only the RHS code is skipped: its reached source value is still used. *)
Theory bodyQualifiedAssignSlotEmptyLandingMods
Ancestors
  bodyQualifiedPlaceSlotScalarMods bodyQualifiedPlaceRhsPostMods
  stmtLoweringMono stmtSimLogCompose memoryLocalRhsProps
  vyperFiniteStoragePreservation vyperStoragePlaceObserved
  vyperEvalExprPreservesScopesDom vyperStorageFootprint
  bodyFullPostsMods exprSimWordArgs
  bodyAssignQualifiedStageJoinMods bodyWriteTargetStageMods exprLoweringProps
  loweringPosts bodyPtrDefs

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

val rhs_post =
  ``qualified_place_rhs_post_mods (DF,lo,d,ctx,func) mods cenv cx env bt e dty
      es sa shadow_sa sr shadow_sr saved s0 G0 tn0``;

Theorem assign_slot_empty_observed[local]:
  eval_target_place cx bt s = (INL (StoragePlace tr w tv),ee) /\
  valid_horizon cx st0 H ee.storage_trace ==>
  storage_place_observed H (StoragePlace tr w tv)
Proof
  strip_tac >> drule_then strip_assume_tac eval_target_place_observed_region >>
  `storage_observations_ok cx H ee.storage_trace` by fs[valid_horizon_def] >>
  drule_all_then assume_tac storage_observations_ok_root >>
  rename1 `MEM (StorageRoot tr offset root_ty) ee.storage_trace` >>
  simp[storage_place_observed_def] >>
  qexistsl_tac [`n2w offset`,`root_ty`,`path`,`delta`] >> simp[]
QED

Theorem qualified_assign_slot_empty_landing_mods:
  qualified_assign_rhs_reached_mods cx st0 e es s0 ^rhs_post ms v mid Gu tu u /\
  qualified_assign_target_reached_mods (DF,lo,d,ctx,func) cenv cx st0 bt dty
    mid sr st dst u Gu tu marks p ee Gz tz z /\
  qualified_assign_route_mods AssignSlotEmpty (owner,id) p saved dty dst /\
  qualified_assign_code_mods cenv bt e sa sb shadow_sa shadow_sb saved sr st
    shadow_sr shadow_st dst /\
  type_widens_to env.type_defs (expr_type e) dty /\
  fn_has_code st sb func /\ fn_inst_ids_distinct func /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  local_ptrs_reserved cenv sa /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  return_buf_frame d cenv st z /\ return_buf_sep d cenv ee z ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (write_place cx p v) (ee,z,Gz,tz)
    ^store_post (assign_qualified_exit_mods ctx cx RetQ)
Proof
  simp[qualified_assign_route_mods_def] >> strip_tac >> gvs[] >>
  qpat_assum `qualified_assign_rhs_reached_mods _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_rhs_reached_mods_def]) >>
  qpat_assum `qualified_assign_target_reached_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_target_reached_mods_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then (strip_assume_tac o MATCH_MP qualified_place_rhs_saved_view_mods)) >>
  gvs[] >>
  qpat_assum `qualified_assign_code_mods _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_code_mods_def]) >>
  `has_length_word dty` by drule_all_then ACCEPT_TAC type_widens_to_has_length_word >>
  `sa.cs_next_var <= st.cs_next_var` by
    (qspecl_then [`bt`,`cenv`,`sa`] mp_tac ci_mono_compile_get_target_ptr >> simp[ci_mono_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then (strip_assume_tac o MATCH_MP write_target_storage_view_mods)) >>
  qpat_assum `!tail. eval_target_place _ _ _ = _`
    (qspec_then `[]` (assume_tac o SRULE [listTheory.APPEND_NIL])) >>
  `ee with gas_obs := [] = ee` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  fs[] >>
  drule_then (assume_tac o SRULE []) eval_target_place_preserves_scopes_dom >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then (strip_assume_tac o MATCH_MP write_target_post_view_mods)) >>
  `wb_frame cenv es ee sa s0 z` by
    (qpat_x_assum `wb_frame _ _ _ _ _ _` mp_tac >>
     rewrite_tac[wb_frame_def,locals_kept_def,popped_kept_def,
                 vyperStateTheory.evaluation_state_accfupds]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gz tz` by
    (qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[ghost_kept_at_def,vyperStateTheory.evaluation_state_accfupds]) >>
  `alloca_frame cenv es sa s0 cenv ee z` by
    (irule (INST_TYPE [``:'a`` |-> ``:256``] log_wb_alloca_frame) >> simp[] >> conj_tac
     >- (qexists_tac `ee` >> simp[]) >>
     qexistsl_tac [`storage_trace_horizon es.storage_trace`,`ctx`,`cx`,`func`] >>
     first_assum irule >> first_assum ACCEPT_TAC) >>
  `assign_place_store_code_mods cenv e NONE (FST dst,SOME (slot_loc tr),SOME (ValPT dty)) st =
    ((),sb)` by
    (qpat_assum `dst = (FST dst,_,_)` (rewrite_tac o single o GSYM) >>
     first_assum ACCEPT_TAC) >>
  irule qualified_place_slot_empty_mods >> simp[] >>
  rpt conj_tac
  >- (rpt strip_tac >> drule_all_then ACCEPT_TAC wb_frame_vars)
  >- fs[wb_frame_def]
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> write_target_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
        (qspec_then `H` (drule_then (strip_assume_tac o MATCH_MP write_target_post_view_mods))) >> simp[])
  >- (rpt strip_tac >> drule_all_then ACCEPT_TAC assign_slot_empty_observed) >>
  qexistsl_tac [`FST dst`,`dty`,`e`,`st`] >> simp[]
QED
