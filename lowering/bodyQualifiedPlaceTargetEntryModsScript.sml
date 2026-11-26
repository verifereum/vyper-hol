(* The reached target of a qualified Assign starts at the saved RHS's
   actual cursor. The frames below stop at the target, before any unwrap. *)
Theory bodyQualifiedPlaceTargetEntryMods
Ancestors
  bodyQualifiedPlaceRhsPostMods bodyAssignQualifiedStageJoinMods bodyAssignLocalPlaceRoutesMods
  bodyWritePlaceRunMods bodyPlaceWriteSourceMods bodyWriteTargetStageMods
  bodyPlaceWriteRootReadyMods bodyExprPreFacts stmtLoweringMono exprLoweringProps
  fragExec compileEnv wordArgsPtr exprSimWordArgs bodyMemoryDefs freshWrites
  vyperStorageFootprint vyperEvalExprPreservesScopesDom vyperScopePreservation
  allocLimits vyperSubscriptOverlap option list vyperStorageTrace vyperState
Libs monadsyntax

Theorem qualified_rhs_ci_mono[local]:
  ci_mono sa (SND (assign_place_rhs_code_mods cenv bt e sa))
Proof
  simp[assign_place_rhs_code_mods_def] >> IF_CASES_TAC >- simp[ci_mono_comp_return] >>
  irule ci_mono_bind >> simp[ci_mono_compile_expr_sa] >> gen_tac >> BETA_TAC >>
  irule ci_mono_bind >> simp[ci_mono_comp_return] >>
  IF_CASES_TAC >> simp[ci_mono_compile_snapshot_vv,ci_mono_comp_return]
QED

Theorem qualified_store_ci_mono[local]:
  ci_mono st (SND (assign_place_store_code_mods cenv e saved dst st))
Proof
  Cases_on `saved` >> simp[assign_place_store_code_mods_def,ci_mono_stmt_helpers] >>
  irule ci_mono_bind >> simp[ci_mono_unwrap_value] >> rpt gen_tac >>
  Cases_on `FST (SND dst)` >> simp[ci_mono_emit_void,ci_mono_stmt_helpers]
QED

Theorem qualified_assign_code_cuts[local]:
  assign_place_rhs_code_mods cenv bt e sa = (saved,sr) /\
  compile_get_target_ptr compile_expr cenv bt sr = (dst,st) /\
  assign_place_store_code_mods cenv e saved dst st = ((),sb) /\
  fn_has_code sa sb func ==>
  fn_has_code sa sr func /\ fn_has_code sr st func /\ fn_has_code st sb func
Proof
  strip_tac >>
  `cs_extends sa sr` by
    (mp_tac (SPEC_ALL qualified_rhs_ci_mono) >>
     simp[ci_mono_def]) >>
  `cs_extends sr st` by
    (qspecl_then [`bt`,`cenv`,`sr`] mp_tac ci_mono_compile_get_target_ptr >> simp[ci_mono_def]) >>
  `cs_extends st sb` by
    (mp_tac (SPEC_ALL qualified_store_ci_mono) >>
     simp[ci_mono_def]) >>
  `cs_extends sr sb` by (irule cs_extends_trans >> qexists_tac `st` >> simp[]) >>
  `fn_has_code sa sr func /\ fn_has_code sr sb func` by
    (irule fn_has_code_split >> simp[]) >>
  simp[] >> irule fn_has_code_split >> simp[]
QED

Theorem qualified_place_code_intervals_mods:
  qualified_assign_code_mods cenv bt e sa sb shadow_sa shadow_sb saved sr st
    shadow_sr shadow_st dst /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func ==>
  fn_has_code sa sr func /\ fn_has_code shadow_sa shadow_sr shadow_func /\
  fn_has_code sr st func /\ fn_has_code shadow_sr shadow_st shadow_func /\
  fn_has_code st sb func /\ fn_has_code shadow_st shadow_sb shadow_func
Proof
  simp[qualified_assign_code_mods_def] >> strip_tac >>
  `fn_has_code sa sr func /\ fn_has_code sr st func /\ fn_has_code st sb func` by
    (irule qualified_assign_code_cuts >> rpt (first_assum (irule_at Any))) >>
  `fn_has_code shadow_sa shadow_sr shadow_func /\
   fn_has_code shadow_sr shadow_st shadow_func /\ fn_has_code shadow_st shadow_sb shadow_func` by
    (irule qualified_assign_code_cuts >> rpt (first_assum (irule_at Any))) >>
  simp[]
QED

Theorem qualified_place_target_entry_mods:
  target_root bt = TopLevelNameTarget key /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  supported_stmt tops bindings (Assign (BaseTarget bt) e) /\
  type_stmt env ret_ty (Assign (BaseTarget bt) e) = SOME env' /\
  type_place_target env bt = SOME (Type dty) /\
  stmt_exprs_ok cenv (Assign (BaseTarget bt) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget bt) e)) /\
  EVERY (source_body_call_supported cx) (int_calls_stmt (Assign (BaseTarget bt) e)) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env)
    (Assign (BaseTarget bt) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget bt) e) ==> EXISTS (occurs_abi_decode_target target o SND) mods) /\
  (!k. MEM (WriteAcc (StateRef k)) (accesses_stmt (Assign (BaseTarget bt) e)) /\
       IS_SOME (FLOOKUP env.bare_global_assignable k) ==>
       IS_SOME (FLOOKUP cenv.ce_module_vars k)) /\
  body_base_target_full_ok_mods mods exps cx bt /\
  qualified_assign_code_mods cenv bt e sa sb shadow_sa shadow_sb saved sr st
    shadow_sr shadow_st dst /\
  qualified_assign_rhs_reached_mods cx st0 e es s0
    (qualified_place_rhs_post_mods (DF,lo,d,ctx,func) mods cenv cx env bt e dty
       es sa shadow_sa sr shadow_sr saved s0 G0 tn0) ms v mid Gu tu u /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_inst_ids_distinct func /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) ==>
  write_place_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env bt mid /\
  write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx bt mid st0 sr st shadow_sr shadow_st dst u Gu tu
Proof
  strip_tac >> drule_then strip_assume_tac qualified_place_rhs_entry_view_mods >>
  drule_all_then strip_assume_tac qualified_place_code_intervals_mods >>
  reverse conj_tac
  >- (qpat_assum `qualified_assign_code_mods _ _ _ _ _ _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [qualified_assign_code_mods_def]) >>
      simp[write_target_entry_mods_def] >> conj_tac
      >- (rpt strip_tac >> qpat_assum `!fn inst t. frag_reachable _ _ _ _ _ _ ==> _`
        (drule_then ACCEPT_TAC)) >>
      rpt gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
        (drule_then (strip_assume_tac o BETA_RULE)) >> simp[]) >>
  `alloc_limits_target cenv bt` by
    (qpat_x_assum `stmt_exprs_ok _ _` mp_tac >>
     simp[stmt_exprs_ok_flat,alloc_limits_stmt_def,alloc_limits_assignment_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `!i se. MEM i (target_indices bt) /\ expr_sim_inv_mods mods cenv cx env se ==>
     expr_body_pre_mods mods cenv cx env i se` by
    (mp_tac (Q.INST [`s` |-> `Assign (BaseTarget bt) e`] (SPEC_ALL place_write_index_pre_mods)) >>
     simp[]) >>
  `immutable_root cx bt ==>
     ?owner id off. target_root bt = TopLevelNameTarget (owner,id) /\
        cenv.ce_is_ctor /\ FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off)` by
    (mp_tac (Q.INST [`s` |-> `Assign (BaseTarget bt) e`, `es` |-> `mid`]
                    (SPEC_ALL place_write_immutable_root_ready_mods)) >> simp[]) >>
  irule write_target_place_run_mods >> rpt (first_assum (irule_at Any)) >> simp[]
QED

Theorem qualified_rhs_preserves_scope_domains[local]:
  bind (eval_expr cx e) (read_result cx) es = (INL v,mid) ==>
  MAP FDOM es.scopes = MAP FDOM mid.scopes
Proof
  simp[vyperStateTheory.bind_def,AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule_then assume_tac eval_expr_preserves_scopes_dom >>
  drule_then (fn th => simp[th]) read_result_scopes
QED

(* Compose from the statement origin. The second frame also preserves
   the return resources and local-region identities at the RHS cursor. *)
Theorem qualified_place_compose_frames[local]:
  stmt_state_rel (H : (bool # bytes32 # type_value) list # num list) ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel H ctx func cenv cx mid u /\ local_ptrs_reserved cenv sr /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\ MAP FDOM mid.scopes = MAP FDOM ee.scopes /\
  ci_mono sa sr /\ ci_mono sr st /\ u.vs_alloca_next <= z.vs_alloca_next /\
  wb_frame cenv es mid sa s0 u /\ wb_frame cenv mid ee sr u z /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tu /\
  ghost_kept_at lo cenv mid sr Gu tu u Gz tz /\
  return_buf_frame d cenv sr u /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sr x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sr x) ==>
  wb_frame cenv es ee sa s0 z /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gz tz /\
  return_buf_frame d cenv st z /\ local_ptrs_reserved cenv st /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at st x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at st x) /\
  (!n b sz. local_region cenv mid.scopes u n b sz <=> local_region cenv ee.scopes z n b sz)
Proof
  simp[ci_mono_def] >> strip_tac >>
  conj_tac
  >- (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
        (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule wb_frame_trans) >>
      rpt (first_assum (irule_at Any)) >> simp[]) >>
  conj_tac
  >- (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
        (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule ghost_kept_at_wb_trans) >>
      rpt (first_assum (irule_at Any)) >> simp[]) >>
  conj_tac
  >- (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`u`,`sr`] >> simp[] >>
      drule_then ACCEPT_TAC wb_frame_vars) >>
  conj_tac >- (irule local_ptrs_reserved_next_var >> qexists_tac `sr` >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sr` >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sr` >> simp[]) >>
  drule_all_then ACCEPT_TAC wb_frame_local_regions
QED

Theorem qualified_place_store_frame_mods:
  target_root bt = TopLevelNameTarget (owner,id) /\
  type_place_target env bt = SOME (Type dty) /\
  (!i se. MEM i (target_indices bt) /\ expr_sim_inv_mods mods cenv cx env se ==>
     expr_body_pre_mods mods cenv cx env i se) /\
  local_ptrs_reserved cenv sa /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  qualified_assign_code_mods cenv bt e sa sb shadow_sa shadow_sb saved sr st
    shadow_sr shadow_st dst /\
  qualified_assign_rhs_reached_mods cx st0 e es s0
    (qualified_place_rhs_post_mods (DF,lo,d,ctx,func) mods cenv cx env bt e dty
       es sa shadow_sa sr shadow_sr saved s0 G0 tn0) ms v mid Gu tu u /\
  qualified_assign_target_reached_mods (DF,lo,d,ctx,func) cenv cx st0 bt dty
    mid sr st dst u Gu tu marks p ee Gz tz z /\
  valid_horizon cx st0 H ee.storage_trace ==>
  valid_horizon cx st0 H mid.storage_trace /\ valid_horizon cx st0 H es.storage_trace /\
  expr_sim_inv_mods mods cenv cx env ee /\ body_const_cells_agree_mods mods cx env ee /\
  value_runtime_typed env (expr_type e) v /\
  write_target_post_mods H (DF H) lo d ctx func cenv cx bt mid sr st u
    ee (PlaceR p) (Type dty) dst Gu tu Gz tz z /\
  ((?tr slot tv. p = StoragePlace tr slot tv /\
       dst = (FST dst,SOME (slot_loc tr),SOME (ValPT dty))) \/
   (?path. p = ImmutablePlace owner id path /\
       dst = (FST dst,SOME LocCode,SOME (ValPT dty)))) /\
  s0.vs_alloca_next <= z.vs_alloca_next /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\ MAP FDOM mid.scopes = MAP FDOM ee.scopes /\
  wb_frame cenv es ee sa s0 z /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gz tz /\
  return_buf_frame d cenv st z /\ local_ptrs_reserved cenv st /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at st x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at st x) /\
  (!n b sz. local_region cenv mid.scopes u n b sz <=> local_region cenv ee.scopes z n b sz)
Proof
  strip_tac >> drule_then strip_assume_tac qualified_place_rhs_entry_view_mods >>
  qpat_assum `qualified_assign_rhs_reached_mods _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_rhs_reached_mods_def]) >>
  qpat_x_assum `qualified_assign_target_reached_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_target_reached_mods_def]) >>
  qpat_assum `!tail. eval_target_place _ _ _ = _`
    (qspec_then `[]` (assume_tac o SRULE [APPEND_NIL])) >>
  qpat_assum `!tail. bind (eval_expr _ _) _ _ = _`
    (qspec_then `[]` (assume_tac o SRULE [APPEND_NIL])) >>
  `mid with gas_obs := [] = mid /\ ee with gas_obs := [] = ee` by
    simp[evaluation_state_component_equality] >>
  fs[] >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `eval_target_place _ _ _ = _`
       (mp_then (Pat `_ _ = (_,_)`) mp_tac valid_horizon_frame) >>
     simp[evaluate_storage_trace_frame]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `bind (eval_expr _ _) _ _ = _`
       (mp_then (Pat `_ _ = (_,_)`) mp_tac valid_horizon_frame) >>
     simp[storage_trace_frame_bind,evaluate_storage_trace_frame,storage_trace_frame_read_result]) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _` (drule_then assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _` (drule_then assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule_then strip_assume_tac write_target_post_view_mods >>
  drule_all_then assume_tac qualified_assign_destination_mods >>
  drule_then (assume_tac o SRULE []) qualified_rhs_preserves_scope_domains >>
  drule_then (assume_tac o SRULE []) eval_target_place_preserves_scopes_dom >>
  `expr_sim_inv_mods mods cenv cx env ee /\ body_const_cells_agree_mods mods cx env ee` by
    (irule place_write_reached_source_mods >>
     qpat_assum `eval_target_place _ _ _ = _` (irule_at Any) >> simp[]) >>
  qpat_x_assum `qualified_assign_code_mods _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_code_mods_def]) >>
  `ci_mono sa sr` by (mp_tac (SPEC_ALL qualified_rhs_ci_mono) >> simp[]) >>
  `ci_mono sr st` by (qspecl_then [`bt`,`cenv`,`sr`] mp_tac ci_mono_compile_get_target_ptr >> simp[]) >>
  `s0.vs_alloca_next <= z.vs_alloca_next` by decide_tac >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by simp[] >>
  `wb_frame cenv es ee sa s0 z /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gz tz /\
   return_buf_frame d cenv st z /\ local_ptrs_reserved cenv st /\
   (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at st x) /\
   (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at st x) /\
   (!n b sz. local_region cenv mid.scopes u n b sz <=> local_region cenv ee.scopes z n b sz)` by
    (irule qualified_place_compose_frames >> rpt (first_assum (irule_at Any)) >> simp[]) >>
  simp[]
QED
