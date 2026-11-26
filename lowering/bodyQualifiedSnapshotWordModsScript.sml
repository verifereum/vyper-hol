(* The forced word snapshot is the scalar child's full paired interval. *)
Theory bodyQualifiedSnapshotWordMods
Ancestors
  bodyQualifiedPlaceRhsPostMods bodyNormalHeadTailMods bodyBranchCellFrameMods
  bodySimStmtFacts bodyFullIfExpReach gasOutcomeFullPostMods
  exprBodyPreProps exprBodyPreTypingProps exprReasonOperand exprOperandVar
  exprSimWordArgs exprSimUnwrap exprLoweringProps gasShadowCompileStmtHelpers
  bodyMemoryDefs vyperTypeArgFits vyperTypeEvalCaseProofs valueEncodingTyping
  exprLowering vyperTypeSystem vyperAST compileEnv context exprSimHypsDefs
  vyperState vyperInterpreter bodyFullPredsMods bodyFullPostsMods loweringPosts
  gasShadowCompileBase gasOutcomeFullMods fragExec freshWrites vyperTypeExprSoundness
  gasShadowState gasShadowCompilePure bodyAssignLocalPlaceRoutesMods gasShadow
  gasShadowCompileStmtBase gasShadowCompileHelpers

Theorem snapshot_word_type[local]:
  !cenv e. expr_sim_inv_mods mods cenv cx env es /\ well_typed_expr env e /\
    is_word_type (lowered_value_type cenv e) ==>
    lowered_value_type cenv e = expr_type e
Proof
  ho_match_mp_tac lowered_value_type_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`IntCall`]
  >- (strip_tac >> rename1 `IntCall fid` >> PairCases_on `fid` >>
      fs[Once well_typed_expr_def] >>
      drule_all expr_sim_inv_mods_return_type >>
      strip_tac >> gvs[lowered_value_type_def, expr_type_def, type_widens_to_def,
         vyperEventArgCompatTheory.event_arg_compatible_alias_def] >>
      metis_tac[aggregateEvaluatedLayoutTheory.arg_type_fits_word_type,
                abiEncodeArgsSimTheory.abi_args_word_fits_eq])
  >~ [`Concat`]
  >- (Cases_on `ty` >> simp[lowered_value_type_def, concat_buffer_type_def, is_word_type_def] >>
      rename1 `BaseT b` >> Cases_on `b` >> simp[is_word_type_def]) >>
  simp[lowered_value_type_def,is_word_type_def,expr_type_def]
QED

Theorem snapshot_word_code[local]:
  expr_sim_inv_mods mods cenv cx env es /\ well_typed_expr env e /\
  is_word_type (expr_type e) /\ lowered_value_type cenv e = expr_type e /\
  compile_expr cenv (expr_type e) e sa = (raw,sm) /\
  compile_snapshot_vv cenv T (vv_with_type (expr_type e) raw) sm = (vv,sr) ==>
  vv_type raw = expr_type e /\ vv_with_type (expr_type e) raw = raw /\
  ?op. lower_value compile_expr cenv (expr_type e) e sa = (op,sr) /\
       vv = StackValue (expr_type e) op /\ sa.cs_next_var <= sr.cs_next_var
Proof
  strip_tac >>
  `reason_uniform_shape compile_expr cenv (expr_type e) e` by
    (irule compile_expr_reason_uniform >> qexists_tac `env` >>
     fs[expr_sim_inv_mods_def]) >>
  `vv_type raw = expr_type e` by
    (fs[reason_uniform_shape_def] >> first_x_assum drule >>
     Cases_on `raw` >> gvs[reason_result_shape_def, vv_type_def]) >>
  drule_then strip_assume_tac compile_expr_extends >>
  `ci_mono sm sr` by
    (qspecl_then [`cenv`,`T`,`vv_with_type (expr_type e) raw`,`sm`]
        mp_tac ci_mono_compile_snapshot_vv >> simp[]) >>
  `vv_with_type (expr_type e) raw = raw` by
    (Cases_on `raw` >> gvs[vv_with_type_def, vv_type_def]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  Cases_on `unwrap_value cenv raw sm` >>
  gvs[lower_value_def, compile_snapshot_vv_def, comp_bind_def, comp_return_def,
      ci_mono_def] >> decide_tac
QED

Theorem snapshot_word_source[local]:
  expr_body_pre_mods mods cenv cx env e es /\
  body_const_cells_agree_mods mods cx env es /\ is_word_type (expr_type e) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,mid) ==>
  expr_sim_inv_mods mods cenv cx env mid /\ body_const_cells_agree_mods mods cx env mid /\
  value_runtime_typed env (expr_type e) v
Proof
  strip_tac >>
  `(expr_body_pre_mods mods cenv cx env e (es with gas_obs := gs) <=>
    expr_body_pre_mods mods cenv cx env e es)` by
    simp_tac (srw_ss()) [expr_body_pre_mods_def,expr_sim_inv_mods_def] >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := gs)` by simp[] >>
  drule_all_then strip_assume_tac (REWRITE_RULE [ETA_AX] expr_body_pre_eval_mods) >>
  simp[] >>
  irule body_const_cells_agree_mods_stmt >>
  qexistsl_tac [`env`,`es with gas_obs := gs`,`INR (ReturnException v)`,
                `expr_type e`,`Return (SOME e)`] >>
  conj_tac
  >- (drule_then assume_tac expr_body_pre_mods_well_typed >>
      Cases_on `expr_type e` >> fs[type_stmt_def,is_word_type_def]) >>
  qpat_x_assum `bind (eval_expr _ _) _ _ = _` mp_tac >>
  simp[Once evaluate_def] >>
  simp[vyperStateTheory.bind_def,AllCaseEqs(),raise_def] >>
  strip_tac >> simp[]
QED

Theorem snapshot_word_headroom[local]:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn) Q R /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst t. frag_reachable ctx func s fn inst t ==> dalloca_fmp_headroom inst t) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn) (\H res ee G' tn' u. Q H res ee G' tn' u /\
      (!fn inst t. frag_reachable ctx func u fn inst t ==> dalloca_fmp_headroom inst t)) R
Proof
  strip_tac >>
  qhdtm_x_assum `gas_outcome_full_mods`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_full_mods_def]) >>
  rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks`
  >- (disj1_tac >> simp[] >>
      qexistsl_tac [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >> simp[])
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[]
      >- (disj1_tac >> simp[] >>
          drule_at (Pat `gas_origin_ptr_path _ _ _ _`) gas_origin_ptr_path_dalloca_fmp_headroom >>
          metis_tac[]) >>
      disj2_tac >> simp[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem qualified_place_snapshot_word_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env e es /\
  body_expr_full_ok_mods mods exps cx e /\
  assign_place_rhs_code_mods cenv bt e sa = (SOME vv,sr) /\
  assign_place_rhs_code_mods (gas_shadow_env T cenv) (gas_shadow_target bt)
    (gas_shadow_expr e) shadow_sa = (SOME vv,shadow_sr) /\
  expr_can_mutate cenv (target_to_expr bt) /\
  is_word_type (lowered_value_type cenv e) /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
  compile_expr cenv (expr_type e) e sa = (raw,sm) /\
  compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e)
    shadow_sa = (raw,shadow_sm) /\
  compile_snapshot_vv cenv T (vv_with_type (lowered_value_type cenv e) raw) sm = (vv,sr) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sr shadow_sr /\
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
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res mid Gu tu u. ?v. res = INL v /\
      qualified_place_rhs_post_mods (DF,lo,d,ctx,func) mods cenv cx env bt e dty
        es sa shadow_sa sr shadow_sr (SOME vv) s0 G0 tn0 H v mid Gu tu u)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_all_then assume_tac snapshot_word_type >>
  `is_word_type (expr_type e)` by fs[] >>
  `compile_snapshot_vv cenv T (vv_with_type (expr_type e) raw) sm = (vv,sr)` by fs[] >>
  drule_all_then strip_assume_tac snapshot_word_code >>
  `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
      (gas_shadow_expr e) shadow_sa = (op,shadow_sr)` by
    (qpat_x_assum `assign_place_rhs_code_mods (gas_shadow_env _ _) _ _ _ = _` mp_tac >>
     simp[assign_place_rhs_code_mods_def, gas_shadow_is_empty_value_expr,
          gas_shadow_expr_type, gas_shadow_expr_can_mutate, lower_value_def,
          comp_bind_def, comp_return_def] >>
     Cases_on `unwrap_value cenv raw shadow_sm` >>
     gvs[compile_snapshot_vv_def, comp_bind_def, comp_return_def]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_full_ok_mods _ _ _ _` mp_tac >>
     rewrite_tac[Once body_expr_full_ok_mods_def] >> strip_tac >>
     qpat_assum `!DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
                    _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ _`
       (qspecl_then [`DF`,`lo`,`d`,`PG`,`src`,`tops`,`ctx`,`shadow_ctx`,
                    `func`,`shadow_func`,`cenv`,`env`,`expr_type e`,`es`] mp_tac) >>
     simp[]) >>
  qhdtm_x_assum `expr_sim_full_mods` (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sr`,`shadow_sa`,`shadow_sr`,`op`,`s0`,`G0`,`tn0`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi_mods] >>
  qmatch_assum_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ ExprQ ExprR` >>
  `gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
      (\H res ee G tn t. ExprQ H res ee G tn t /\
        (!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s)) ExprR` by
    (irule snapshot_word_headroom >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ (\H res ee G tn t. _ /\ _) ExprR` (irule_at Any) >>
  simp[Abbr `ExprQ`,Abbr `ExprR`] >> rpt gen_tac >> strip_tac >>
  suspend "normal"
QED

Resume qualified_place_snapshot_word_mods[normal]:
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := xs) = (INL v,ee)` by
    (qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     asm_rewrite_tac[listTheory.APPEND_NIL]) >>
  drule_all_then strip_assume_tac snapshot_word_source >>
  qhdtm_x_assum `expr_post_mods`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  drule_then assume_tac expr_post_frame >>
  `local_ptrs_reserved cenv sr` by metis_tac[local_ptrs_reserved_next_var] >>
  `return_buf_frame d cenv sr t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >>
     simp[] >> metis_tac[wb_frame_vars]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sr x` by
    metis_tac[not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sr x` by
    metis_tac[not_fresh_at_mono] >>
  `!x. op = Var x ==> not_fresh_at sr x` by metis_tac[compile_lower_value_var] >>
  `env.type_defs = get_tenv cx` by
    metis_tac[expr_sim_inv_mods_env,env_consistent_type_defs_get_tenv] >>
  `post_value_type cenv e = expr_type e` by simp[post_value_type_lowered] >>
  qhdtm_x_assum `expr_post` (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  qhdtm_assum `value_runtime_typed`
    (qx_choose_then `tv` strip_assume_tac o REWRITE_RULE [value_runtime_typed_def]) >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME tv` by
    (qpat_x_assum `env.type_defs = get_tenv cx` (fn th => simp[GSYM th])) >>
  `val_wf tv v` by (irule (cj 1 value_has_type_val_wf) >> simp[]) >>
  `eval_operand op t = SOME (typed_val_to_w256 tv v)` by
    (qhdtm_x_assum `expr_val_rel` mp_tac >> simp[expr_val_rel_def] >>
     disch_then (qx_choose_then `w` strip_assume_tac) >>
     first_x_assum (qspec_then `tv` mp_tac) >> simp[]) >>
  qexists_tac `v` >> simp[qualified_place_rhs_post_mods_def] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC
QED

Finalise qualified_place_snapshot_word_mods
