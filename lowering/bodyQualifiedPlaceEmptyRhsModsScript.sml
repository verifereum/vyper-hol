(* The qualified Assign empty shortcut evaluates only on the source side. *)
Theory bodyQualifiedPlaceEmptyRhsMods
Ancestors
  bodyQualifiedPlaceRhsPostMods gasOutcomeFullPostMods
  bodyWriteSubscriptSourceMods bodyBranchCellFrameMods bodySimStmtFacts
  exprBodyPreProps exprSafeOperand exprSimSource exprSimWordArgs
  memoryLocalRhsProps vyperTypeInvariants option
  exprLoweringProps wordArgsPtr gasShadowCompileStmtBase
  vyperTypeEvalCaseProofs vyperTypeSystem bodyFullShadowBodyInv bodyFullPostsMods
  bodyInvSplit vyperStorageFootprint bodyAssignQualifiedStageJoinMods
  bodyAssignLocalPlaceRoutesMods compileEnv gasShadow fragGasOriginPtr
  loweringPosts vyperState finite_map
Libs
  monadsyntax

Theorem qualified_empty_source_read[local]:
  expr_body_pre_mods mods cenv cx env e es /\
  type_widens_to env.type_defs (expr_type e) dty /\
  has_length_word (expr_type e) /\ is_empty_value_expr e ==>
  ?v. (!dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==> v = default_value dtv) /\
      (!tail. vyperState$bind (eval_expr cx e) (read_result cx) (es with gas_obs := tail) =
         (INL v,es with gas_obs := tail))
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then (assume_tac o MATCH_MP expr_sim_inv_mods_env) expr_body_pre_mods_inv >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
    metis_tac[well_formed_type_def, env_consistent_var_type_evaluates] >>
  drule_all_then assume_tac well_typed_expr_type_well_formed >>
  `well_formed_type env.type_defs dty` by metis_tac[type_widens_to_def] >>
  `?dtv. evaluate_type (get_tenv cx) dty = SOME dtv` by
    metis_tac[well_formed_type_def, IS_SOME_EXISTS] >>
  qexists_tac `default_value dtv` >> simp[] >> gen_tac >>
  irule (REWRITE_RULE [ETA_THM] memory_rhs_empty_read_destination) >>
  simp[] >> qexistsl_tac [`env`,`dty`] >> simp[]
QED

Theorem qualified_empty_horizon_gas_obs[local]:
  stmt_state_rel H ctx func cenv cx es s /\
  immutable_frame_mods func cenv cx es s /\
  storage_well_formed_on cx es (FST H) /\
  ghost_inv_at_mods D lo d cenv cx es G tn s ==>
  stmt_state_rel H ctx func cenv cx (es with gas_obs := []) s /\
  immutable_frame_mods func cenv cx (es with gas_obs := []) s /\
  storage_well_formed_on cx (es with gas_obs := []) (FST H) /\
  ghost_inv_at_mods D lo d cenv cx (es with gas_obs := []) G tn s
Proof
  strip_tac >> simp[stmt_state_rel_start_gas_obs] >>
  conj_tac
  >- (qpat_assum `immutable_frame_mods _ _ _ es _` mp_tac >>
      pure_rewrite_tac[immutable_frame_mods_def, immutables_rel_mods_def,
        immutable_alloca_sep_mods_def, immutable_alloca_sep_def,
        loweringStateRelDefsTheory.immutables_rel_def, evaluation_state_accfupds] >> simp[]) >>
  conj_tac
  >- (`storage_well_formed_on cx (es with gas_obs := []) (FST H) <=>
        storage_well_formed_on cx es (FST H)` suffices_by simp[] >>
      irule storage_well_formed_on_backends >> simp[]) >>
  qpat_assum `ghost_inv_at_mods _ _ _ _ _ es _ _ _` mp_tac >>
  pure_rewrite_tac[ghost_inv_at_mods_def, evaluation_state_accfupds] >>
  disch_then ACCEPT_TAC
QED

Theorem qualified_place_empty_rhs_mods:
  expr_body_pre_mods mods cenv cx env e es /\
  body_const_cells_agree_mods mods cx env es /\
  type_widens_to env.type_defs (expr_type e) dty /\
  has_length_word (expr_type e) /\ is_empty_value_expr e /\
  qualified_assign_code_mods cenv bt e sa sb shadow_sa shadow_sb saved sr st
    shadow_sr shadow_st dst /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved cenv sa /\ return_buf_frame d cenv sa s0 /\
  ret_pc_ok cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst t. frag_reachable ctx func s0 fn inst t ==> dalloca_fmp_headroom inst t) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (vyperState$bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res mid Gu tu u. ?v. res = INL v /\
       qualified_place_rhs_post_mods (DF,lo,d,ctx,func) mods cenv cx env bt e dty
         es sa shadow_sa sr shadow_sr saved s0 G0 tn0 H v mid Gu tu u)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >> drule_all_then strip_assume_tac qualified_empty_source_read >>
  qhdtm_x_assum `qualified_assign_code_mods`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_code_mods_def]) >>
  `assign_place_rhs_code_mods cenv bt e sa = (NONE,sa)` by
    (pure_rewrite_tac[assign_place_rhs_code_mods_def] >> simp[comp_return_def]) >>
  `assign_place_rhs_code_mods (gas_shadow_env T cenv) (gas_shadow_target bt)
     (gas_shadow_expr e) shadow_sa = (NONE,shadow_sa)` by
    (pure_rewrite_tac[assign_place_rhs_code_mods_def] >>
     simp[comp_return_def, gas_shadow_expr_type]) >>
  `saved = NONE /\ sr = sa /\ shadow_sr = shadow_sa` by
    (qpat_assum `assign_place_rhs_code_mods cenv _ _ _ = (saved,sr)` mp_tac >>
     qpat_assum `assign_place_rhs_code_mods (gas_shadow_env _ _) _ _ _ = (saved,shadow_sr)` mp_tac >>
     simp[] >> metis_tac[]) >>
  map_every (fn eq => qpat_x_assum eq SUBST_ALL_TAC)
    [`saved = NONE`,`sr = sa`,`shadow_sr = shadow_sa`] >>
  `expr_sim_inv_mods mods cenv cx env (es with gas_obs := []) /\
   value_runtime_typed env (expr_type e) v` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
     `expr_body_pre_mods mods cenv cx env e (es with gas_obs := [])` by simp[] >>
     drule_all_then strip_assume_tac (REWRITE_RULE [ETA_THM] expr_body_pre_eval_mods) >> simp[]) >>
  `body_const_cells_agree_mods mods cx env (es with gas_obs := [])` by
    (`body_const_cells_agree_mods mods cx env (es with gas_obs := []) <=>
      body_const_cells_agree_mods mods cx env es` suffices_by simp[] >>
     irule body_const_cells_agree_mods_immutables >> simp[]) >>
  irule gas_outcome_full_mods_pure >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G0`,`es`,`INL v`,`s0`,`tn0`] >> simp[] >>
  gen_tac >> strip_tac >>
  conj_tac >- (irule (CONJUNCT1 gas_origin_ptr_path_rules) >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then (strip_assume_tac o MATCH_MP qualified_empty_horizon_gas_obs)) >>
  simp[qualified_place_rhs_post_mods_def, wb_frame_refl, ghost_kept_at_refl] >>
  rpt strip_tac >> fs[ret_pc_ok_def] >>
  qpat_assum `!fn inst t. frag_reachable _ _ _ fn inst t ==> _`
    (drule_then ACCEPT_TAC)
QED
