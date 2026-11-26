(* Compose the target/read frames at the normal Append store cursor. *)
Theory bodyAppendReachedFrameMods
Ancestors
  bodyAppendStageJoinMods bodyWriteTargetStageMods bodyFullPostsMods
  bodyFullShared bodyMemoryDefs wordArgsPtr exprSimWordArgs stmtSimLogCompose
  vyperEvalExprPreservesScopesDom vyperStorageTrace vyperStorageFootprint
  exprLoweringProps freshWrites loweringPosts stmtSimDefs ptrDiscipline
  vyperState venomState finite_map
Libs monadsyntax

Theorem append_reached_target_source[local]:
  eval_target_place cx bt (es with gas_obs := reads) =
    (INL p,mid with gas_obs := []) ==>
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace)
Proof
  strip_tac >> conj_tac
  >- (drule eval_target_place_preserves_scopes_dom >> simp[]) >>
  `storage_trace_frame (eval_target_place cx bt)` by simp[evaluate_storage_trace_frame] >>
  drule_all storage_trace_frame_prefix >> simp[] >>
  strip_tac >> gen_tac >> simp[] >>
  disch_then (ACCEPT_TAC o MATCH_MP gasOutcomeFullTheory.valid_horizon_append)
QED

Theorem append_reached_rhs_source[local]:
  bind (eval_expr cx e) (read_result cx) (mid with gas_obs := reads) =
    (INL v,ee with gas_obs := []) ==>
  MAP FDOM mid.scopes = MAP FDOM ee.scopes /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       valid_horizon cx st0 H mid.storage_trace)
Proof
  strip_tac >> conj_tac
  >- (qpat_x_assum `bind _ _ _ = _` mp_tac >> simp[bind_def,AllCaseEqs()] >>
      strip_tac >> drule vyperScopePreservationTheory.read_result_scopes >>
      simp[] >> disch_tac >> drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    simp[storage_trace_frame_bind,evaluate_storage_trace_frame,storage_trace_frame_read_result] >>
  drule_all storage_trace_frame_prefix >> simp[] >>
  strip_tac >> gen_tac >> simp[] >>
  disch_then (ACCEPT_TAC o MATCH_MP gasOutcomeFullTheory.valid_horizon_append)
QED

Theorem append_rhs_code_view_mods:
  append_rhs_code_mods cenv e elem sp sm shadow_sp shadow_sm op func shadow_func ==>
  lower_value compile_expr cenv elem e sp = (op,sm) /\
  lower_value compile_expr (gas_shadow_env T cenv) elem (gas_shadow_expr e)
    shadow_sp = (op,shadow_sm) /\
  gas_shadow_state sp shadow_sp /\ gas_shadow_state sm shadow_sm /\
  fn_has_code sp sm func /\ fn_has_code shadow_sp shadow_sm shadow_func /\
  ci_mono sp sm
Proof
  simp[append_rhs_code_mods_def] >> strip_tac >>
  qspecl_then [`cenv`,`elem`,`e`,`sp`] mp_tac ci_mono_lower_value_compile_expr >> simp[]
QED

Theorem append_reached_frames[local]:
  stmt_state_rel H ctx func cenv cx es s0 /\
  stmt_state_rel H ctx func cenv cx mid t /\
  local_ptrs_reserved cenv sa /\ ci_mono sa sp /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  MAP FDOM mid.scopes = MAP FDOM ee.scopes /\
  wb_frame cenv es mid sa s0 t /\ wb_frame cenv mid ee sp t u /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gm tm /\
  ghost_kept_at lo cenv mid sp Gm tm t G tn ==>
  (!n b sz. local_region cenv es.scopes s0 n b sz <=>
            local_region cenv mid.scopes t n b sz) /\
  (!n b sz. local_region cenv mid.scopes t n b sz <=>
            local_region cenv ee.scopes u n b sz) /\
  wb_frame cenv es ee sa s0 u /\
  alloca_frame cenv es sa s0 cenv ee u /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn
Proof
  strip_tac >> fs[ci_mono_def] >>
  `local_ptrs_reserved cenv sp` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `!n b sz. local_region cenv es.scopes s0 n b sz <=>
             local_region cenv mid.scopes t n b sz` by
    (irule (GEN_ALL wb_frame_local_regions) >>
     conj_tac >- simp[] >> conj_tac >- (qexistsl_tac [`mid`,`sa`] >> simp[]) >>
     goal_assum (drule_at Any)) >>
  `!n b sz. local_region cenv mid.scopes t n b sz <=>
             local_region cenv ee.scopes u n b sz` by
    (irule (GEN_ALL wb_frame_local_regions) >>
     conj_tac >- simp[] >> conj_tac >- (qexistsl_tac [`ee`,`sp`] >> simp[]) >>
     goal_assum (drule_at Any)) >>
  `wb_frame cenv es ee sa s0 u` by
    (irule wb_frame_trans >> simp[] >>
     conj_tac >- (qexistsl_tac [`mid`,`sp`,`t`] >> simp[]) >>
     goal_assum (drule_at Any)) >>
  simp[] >> conj_tac
  >- (irule log_wb_alloca_frame >> simp[] >>
      conj_tac >- (qexists_tac `ee` >> simp[]) >> goal_assum (drule_at Any)) >>
  irule ghost_kept_at_trans >> qexistsl_tac [`Gm`,`mid`,`t`,`sp`,`tm`] >>
  fs[wb_frame_def]
QED

(* allocas_from at the return-buffer bound is a fact about the same reached
   run (gas_outcome_full_mods_return_buf_allocas), not a consequence of wb_frame. *)
Theorem append_reached_store_frame_mods:
  write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx bt es st0 sa sp shadow_sa shadow_sp dst s0 G0 tn0 /\
  append_rhs_code_mods cenv e elem sp sm shadow_sp shadow_sm op func shadow_func /\
  ci_mono sa sp /\
  return_buf_sep d cenv es s0 /\
  (!bw capacity. d = SOME (bw,capacity) ==> allocas_from (w2n bw + capacity) u) /\
  (!tail. eval_target_place cx bt
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
     (INL p,mid with gas_obs := tail)) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
     (mid with gas_obs := gas_explicit rhsmarks t.vs_gas_readings ++ tail) =
     (INL v,ee with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    write_target_post_mods H (DF H) lo d ctx func cenv cx bt es sa sp s0
      mid (PlaceR p) (Type (ArrayT elem (Dynamic cap))) dst G0 tn0 Gm tm t) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    append_rhs_post_mods DF lo d ctx func cenv cx e mid sp sm t op Gm tm H v ee G tn u) /\
  ~u.vs_halted /\ valid_horizon cx st0 H ee.storage_trace ==>
  write_target_post_mods H (DF H) lo d ctx func cenv cx bt es sa sp s0
    mid (PlaceR p) (Type (ArrayT elem (Dynamic cap))) dst G0 tn0 Gm tm t /\
  append_rhs_post_mods DF lo d ctx func cenv cx e mid sp sm t op Gm tm H v ee G tn u /\
  stmt_state_rel H ctx func cenv cx ee u /\ immutable_frame_mods func cenv cx ee u /\
  storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G tn u /\
  ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts /\
  fn_inst_ids_distinct func /\ alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  return_buf_frame d cenv sm u /\ return_buf_sep d cenv ee u /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!n b sz. local_region cenv es.scopes s0 n b sz <=> local_region cenv ee.scopes u n b sz) /\
  (!n b sz. local_region cenv mid.scopes t n b sz <=> local_region cenv ee.scopes u n b sz) /\
  wb_frame cenv es ee sa s0 u /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x u = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
  alloca_frame cenv es sa s0 cenv ee u /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn
Proof
  strip_tac >>
  qpat_assum `!tail. eval_target_place _ _ _ = _`
    (qspec_then `[]` (strip_assume_tac o MATCH_MP append_reached_target_source)) >>
  qpat_assum `!tail. bind _ _ _ = _`
    (qspec_then `[]` (strip_assume_tac o MATCH_MP append_reached_rhs_source)) >>
  `valid_horizon cx st0 H mid.storage_trace` by simp[] >>
  `valid_horizon cx st0 H es.storage_trace` by simp[] >>
  conj_asm1_tac >- simp[] >>
  conj_asm1_tac >- simp[] >>
  qhdtm_assum `write_target_post_mods` (strip_assume_tac o MATCH_MP write_target_post_view_mods) >>
  qhdtm_assum `append_rhs_post_mods` (strip_assume_tac o REWRITE_RULE [append_rhs_post_mods_def]) >>
  qhdtm_assum `expr_post_mods` (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  qhdtm_assum `expr_post` (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `wb_frame cenv mid ee sp t u` by
    (pure_rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qhdtm_assum `write_target_entry_mods` (strip_assume_tac o REWRITE_RULE [write_target_entry_mods_def]) >>
  qpat_assum `!H. _ ==> stmt_state_rel H _ _ _ _ _ _ /\ _` (drule_then strip_assume_tac) >>
  drule_all_then strip_assume_tac append_reached_frames >>
  drule_then strip_assume_tac append_rhs_code_view_mods >>
  `ci_mono sa sm` by drule_all_then ACCEPT_TAC ci_mono_trans >> fs[ci_mono_def] >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by decide_tac >>
  `return_buf_sep d cenv ee u` by
    (irule return_buf_sep_transport >> conj_tac >- (rpt strip_tac >> fs[]) >>
     qexistsl_tac [`cenv`,`es`,`s0`] >> conj_tac
     >- (qpat_assum `!n b sz. local_region _ es.scopes s0 n b sz <=> local_region _ ee.scopes u n b sz`
          (fn th => simp[NoAsms,th])) >>
     first_assum ACCEPT_TAC) >>
  `return_buf_frame d cenv sm u` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> fs[wb_frame_def]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (gen_tac >> disch_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  qpat_assum `wb_frame cenv es ee sa s0 u`
    (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sm x` irule >>
  first_x_assum (drule_then ACCEPT_TAC)
QED
