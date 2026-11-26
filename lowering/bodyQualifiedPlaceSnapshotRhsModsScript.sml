(* Qualified Assign evaluates and snapshots the RHS before the target. *)
Theory bodyQualifiedPlaceSnapshotRhsMods
Ancestors
  bodyQualifiedPlaceRhsPostMods gasShadowCompileStmtHelpers gasShadowState
  gasShadowCompileConvert gasShadowCompileBase exprSimUnwrap exprLoweringProps
  exprLowering fragExec loweringHalt context bodyAssignLocalPlaceRoutesMods
  gasShadowCompileStmtBase gasShadowCompileHelpers gasShadow compileEnv
  bodyQualifiedSnapshotWordMods bodyQualifiedSnapshotReadMods bodyQualifiedSnapshotAggregateMods
  bodyFullPredsMods bodyFullPostsMods bodyFullIfExpReach exprSimMemorySource
  bodySim allocLimits words exprBodyPreProps exprSimIfExpCompat exprSimHypsDefs
  vyperTypeEvalCaseProofs vyperTypeExprSoundness vyperTypeInvariants vyperTypeSystem
  valueCopyBytes vyperAST vyperState bodyAssignQualifiedStageJoinMods exprSimSource
  vyperStorageFootprint

Theorem qualified_place_snapshot_code_mods:
  assign_place_rhs_code_mods ce bt e sa = (saved,sr) /\
  assign_place_rhs_code_mods (gas_shadow_env T ce) (gas_shadow_target bt)
    (gas_shadow_expr e) shadow_sa = (saved,shadow_sr) /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
  expr_can_mutate ce (target_to_expr bt) /\ gas_shadow_state sa shadow_sa /\
  fn_has_code sa sr func /\ fn_has_code shadow_sa shadow_sr shadow_func ==>
  ?raw vv sm shadow_sm.
    saved = SOME vv /\
    compile_expr ce (expr_type e) e sa = (raw,sm) /\
    compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e)
      shadow_sa = (raw,shadow_sm) /\
    gas_shadow_state sm shadow_sm /\ gas_shadow_state sr shadow_sr /\
    compile_snapshot_vv ce T (vv_with_type (lowered_value_type ce e) raw) sm = (vv,sr) /\
    fn_has_code sa sm func /\ fn_has_code sm sr func /\
    fn_has_code shadow_sa shadow_sm shadow_func /\ fn_has_code shadow_sm shadow_sr shadow_func
Proof
  strip_tac >>
  Cases_on `compile_expr ce (expr_type e) e sa` >> rename1 `_ = (raw,sm)` >>
  Cases_on `compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) shadow_sa` >>
  rename1 `_ = (shadow_raw,shadow_sm)` >>
  `shadow_raw = raw /\ gas_shadow_state sm shadow_sm` by
    (mp_tac (Q.INST [`cenv` |-> `ce`, `sd` |-> `T`, `ty` |-> `expr_type e`]
               gas_shadow_stmt_compile_expr_env) >>
     simp[gas_shadow_compiles_def] >> disch_then drule >> simp[]) >>
  gvs[] >>
  Cases_on `compile_snapshot_vv ce T (vv_with_type (lowered_value_type ce e) raw) sm` >>
  rename1 `_ = (vv,m)` >>
  Cases_on `compile_snapshot_vv ce T (vv_with_type (lowered_value_type ce e) raw) shadow_sm` >>
  rename1 `_ = (shadow_vv,shadow_m)` >>
  `shadow_vv = vv /\ gas_shadow_state m shadow_m` by
    (mp_tac (Q.INST [`cenv` |-> `ce`, `copy_flag` |-> `T`,
                    `vv` |-> `vv_with_type (lowered_value_type ce e) raw`]
               gas_shadow_compiles_snapshot_vv) >>
     simp[gas_shadow_compiles_def] >> disch_then drule >> simp[]) >>
  qpat_x_assum `assign_place_rhs_code_mods ce _ _ _ = _` mp_tac >>
  qpat_x_assum `assign_place_rhs_code_mods (gas_shadow_env _ _) _ _ _ = _` mp_tac >>
  simp[assign_place_rhs_code_mods_def,gas_shadow_is_empty_value_expr,
       gas_shadow_expr_type,gas_shadow_expr_can_mutate,
       comp_bind_def,comp_return_def] >> strip_tac >> strip_tac >> gvs[] >>
  `cs_extends sa sm /\ cs_extends shadow_sa shadow_sm` by
    (conj_tac >> irule (cj 1 compile_expr_extends) >> goal_assum (drule_at Any)) >>
  `cs_extends sm m /\ cs_extends shadow_sm shadow_m` by
    (conj_tac >-
       (qspecl_then [`ce`,`T`,`vv_with_type (lowered_value_type ce e) raw`,`sm`]
          mp_tac ci_mono_compile_snapshot_vv >> simp[ci_mono_def]) >>
     qspecl_then [`ce`,`T`,`vv_with_type (lowered_value_type ce e) raw`,`shadow_sm`]
       mp_tac ci_mono_compile_snapshot_vv >> simp[ci_mono_def]) >>
  `fn_has_code sa sm func /\ fn_has_code sm m func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code shadow_sa shadow_sm shadow_func /\ fn_has_code shadow_sm shadow_m shadow_func` by
    (irule fn_has_code_split >> simp[]) >>
  simp[]
QED

Theorem qualified_place_snapshot_rhs_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env e es /\
  body_expr_full_ok_mods mods exps cx e /\
  stmt_exprs_ok cenv (Assign (BaseTarget bt) e) /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
  expr_can_mutate cenv (target_to_expr bt) /\
  qualified_assign_code_mods cenv bt e sa sb shadow_sa shadow_sb saved sr st
    shadow_sr shadow_st dst /\
  gas_shadow_state sa shadow_sa /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sr func /\ fn_has_code shadow_sa shadow_sr shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_admissible (vyperState$bind (eval_expr cx e) (read_result cx)) expr_res_ok es ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (vyperState$bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res mid Gu tu u. ?v. res = INL v /\
      qualified_place_rhs_post_mods (DF,lo,d,ctx,func) mods cenv cx env bt e dty
        es sa shadow_sa sr shadow_sr saved s0 G0 tn0 H v mid Gu tu u)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >> strip_tac >>
  qhdtm_x_assum `qualified_assign_code_mods`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_code_mods_def]) >>
  drule_all_then (qx_choosel_then [`raw`,`vv`,`sm`,`shadow_sm`] strip_assume_tac)
    qualified_place_snapshot_code_mods >>
  qpat_x_assum `saved = SOME vv` SUBST_ALL_TAC >>
  Cases_on `is_word_type (lowered_value_type cenv e)`
  >- (irule qualified_place_snapshot_word_mods >>
      asm_rewrite_tac[] >> conj_tac
      >- (qexistsl_tac [`raw`,`shadow_sm`,`sm`] >> asm_rewrite_tac[]) >>
      conj_tac >- (qexists_tac `shadow_func` >> asm_rewrite_tac[]) >>
      conj_tac >- (qexists_tac `exps` >> asm_rewrite_tac[]) >>
      qexistsl_tac [`src`,`tops`] >> first_assum ACCEPT_TAC) >>
  `type_memory_bytes cenv (lowered_value_type cenv e) < dimword (:256)` by
    (`assign_alloc_ok cenv bt e` by
       fs[stmt_exprs_ok_def,Once alloc_limits_stmt_def] >>
     `type_memory_bytes cenv (lowered_value_type cenv e) < 2 ** 64` by
       fs[assign_alloc_ok_def,type_alloc_ok_def] >>
     irule arithmeticTheory.LESS_TRANS >> qexists_tac `2 ** 64` >> simp[dimword_def]) >>
  `expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (qpat_assum `body_expr_full_ok_mods _ _ _ _`
       (mp_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
     strip_tac >>
     qpat_assum `!DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
                  _ ==> _ /\ expr_vv_sim_full_mods _ _ _ _ _ _`
       (drule_all_then (mp_tac o SIMP_RULE bool_ss [FORALL_AND_THM])) >> simp[]) >>
  drule_then assume_tac forced_expr_admissible_raw >>
  qhdtm_x_assum `expr_vv_sim_full_mods`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`raw`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (mk_asm "open_run") >>
  irule qualified_snapshot_read_lift_mods >>
  qexistsl_tac [`cenv`,`d`,`sa`,`sm`,`raw`] >> BETA_TAC >>
  reverse conj_tac >- asm "open_run" ACCEPT_TAC >>
  asm_x "open_run" kall_tac >>
  suspend "suffix"
QED

Resume qualified_place_snapshot_rhs_mods[suffix]:
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `contract_inv _ _ _ _ _`
       (mp_then Any (qspec_then `func` mp_tac) body_inv_no_phi_mods) >>
     simp[]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (drule_then (ACCEPT_TAC o cj 1))) >>
  `~is_word_type (expr_type e)` by suspend "annotation" >>
  rpt gen_tac >> strip_tac >>
  rename1 `gas_origin_ptr_path _ _ _ (OK t,G,tn)` >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (s0,G0,tn0) marks (OK t,G,tn) /\
     vv_post_mods H ctx func cenv cx e es sa sm s0 mid pv raw t /\
     ghost_inv_at_mods (DF H) lo d cenv cx mid G tn t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` (drule_then (map_every assume_tac o CONJUNCTS))) >>
     asm_rewrite_tac[]) >>
  drule_all qualified_place_snapshot_aggregate_suffix_mods >>
  simp[]
QED

Resume qualified_place_snapshot_rhs_mods[annotation]:
  strip_tac >> drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
    (rpt strip_tac >> drule_all env_consistent_var_type_evaluates >> simp[well_formed_type_def]) >>
  `sfields_tenv_consistent cenv.ce_struct_fields env.type_defs` by
    (qpat_assum `expr_sim_inv_mods _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >> simp[]) >>
  `!fid sg. FLOOKUP env.fn_sigs fid = SOME sg ==>
    cenv.ce_func_return_type (nsid_to_string fid) = sg.ret_ty` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC expr_sim_inv_mods_return_type) >>
  drule_all ifexp_lowered_type_classify >>
  disch_then (DISJ_CASES_THEN2 assume_tac (DISJ_CASES_THEN2 strip_assume_tac strip_assume_tac))
  >- fs[]
  >- fs[is_bytestring_word_type] >>
  qpat_x_assum `e = Call _ (IntCall _) _ _` SUBST_ALL_TAC >>
  PairCases_on `fid` >>
  qpat_x_assum `well_typed_expr env _`
    (strip_assume_tac o ONCE_REWRITE_RULE [well_typed_expr_def]) >>
  drule_all_then assume_tac expr_sim_inv_mods_return_type >>
  fs[lowered_value_type_def,expr_type_def] >>
  metis_tac[type_widens_to_word]
QED

Finalise qualified_place_snapshot_rhs_mods
