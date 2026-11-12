(* Expression statements preserve the counted raw-expression outcome. *)
Theory stmtSimExpr
Ancestors
  stmtSimDefs stmtSimProps exprSimDefs exprSimProps loweringPosts
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext
  list rich_list finite_map pred_set fragExec localPtrsProps loweringSlice
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv loweringStateRelDefs valueEncoding vyperInterpreter vyperState vyperValue
  vyperEvalPreservesScopes vyperExprNoControl vyperValueOperation
  venomExecSemantics venomExecProofs venomInst venomState venomMemDefs integer_word
Libs
  monadsyntax intLib

Theorem eval_expr_stmt_success:
  eval_expr cx e s = (INL tv, ee) /\ ~is_HashMapRef tv ==>
  eval_stmt cx (Expr e) s = (INL (), ee)
Proof
  simp[Once evaluate_def, bind_def, type_check_def, assert_def,
       return_def]
QED

Theorem eval_expr_stmt_exception:
  eval_expr cx e s = (INR ex, ee) ==>
  eval_stmt cx (Expr e) s = (INR ex, ee)
Proof
  simp[Once evaluate_def, bind_def]
QED

Theorem expr_stmt_not_hashmap:
  gas_admissible (eval_stmt cx (Expr e)) (stmt_res_ok lctx) es /\
  eval_expr cx e (es with gas_obs := gs) = (INL tv, ee) ==>
  ~is_HashMapRef tv
Proof
  strip_tac >>
  qpat_x_assum `gas_admissible _ _ _`
    (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
  disch_then (qspec_then `gs` mp_tac) >>
  simp[Once evaluate_def, bind_def, type_check_def, assert_def,
       raise_def, stmt_res_ok_def]
QED

Theorem expr_stmt_admissible:
  gas_admissible (eval_stmt cx (Expr e)) (stmt_res_ok lctx) es ==>
  gas_admissible (eval_expr cx e) expr_vv_res_ok es
Proof
  strip_tac >> rw[gas_admissible_def] >>
  Cases_on `res`
  >- (rename1 `INL tv` >>
      `~is_HashMapRef tv` by metis_tac[expr_stmt_not_hashmap] >>
      Cases_on `tv` >> gvs[expr_vv_res_ok_def]) >>
  rename1 `INR ex` >>
  drule eval_expr_stmt_exception >> strip_tac >>
  drule_all gas_admissible_result >> strip_tac >>
  drule (cj 1 eval_expr_no_control) >>
  Cases_on `ex` >>
  gvs[no_control_exc_def, stmt_res_ok_def, expr_vv_res_ok_def]
QED

Theorem expr_stmt_exempt:
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_expr cx e) (return ())) (es,s0)
    marks (err,ee) (leaf,fin) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_stmt cx (Expr e)) (return ())) (es,s0)
    marks (err,ee) (leaf,fin)
Proof
  strip_tac >>
  `ignore_bind (eval_stmt cx (Expr e)) (return ()) =
   bind (eval_expr cx e)
     (\tv. ignore_bind (type_check (~is_HashMapRef tv) "Expr HashMapRef")
                       (return ()))` by
    (simp[Once evaluate_def, ignore_bind_def, FUN_EQ_THM, bind_def] >>
     gen_tac >> Cases_on `eval_expr cx e x` >> Cases_on `q` >> simp[]) >>
  pop_assum SUBST1_TAC >>
  irule gas_exempt_cert_error_result >> simp[]
QED

Theorem expr_stmt_post[local]:
  vv_post H ctx func cenv cx e es sa sb s0 ee tv vv t /\
  ~t.vs_halted /\ ~block_is_terminated sb /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  stmt_state_rel H ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM ee.scopes = MAP FDOM es.scopes ==>
  stmt_post H ctx func cx lctx cenv cenv sa sb es s0 (INL ()) ee t
Proof
  strip_tac >> drule_all vv_post_alloca_frame >> strip_tac >>
  fs[vv_post_def, stmt_post_def, stmt_lands_def, cenv_top_ext_refl] >>
  metis_tac[]
QED

(* The statement's counted run is the expression's, with its value dropped:
   an admissible statement never meets a HashMapRef. *)
Theorem expr_stmt_marked_exec[local]:
  gas_marked_exec memory (ctx,func) (eval_expr cx e) (es,s0) marks res ee r /\
  gas_admissible (eval_stmt cx (Expr e)) (stmt_res_ok lctx) es ==>
  gas_marked_exec memory (ctx,func) (eval_stmt cx (Expr e)) (es,s0) marks
    (case res of INL tv => INL () | INR ex => INR ex) ee r
Proof
  rw[gas_marked_exec_def] >>
  first_x_assum (qspec_then `tail` assume_tac) >>
  Cases_on `res`
  >- (drule_all expr_stmt_not_hashmap >> strip_tac >>
      drule_all eval_expr_stmt_success >> simp[]) >>
  drule eval_expr_stmt_exception >> simp[]
QED

Theorem expr_stmt_bad_storage[local]:
  gas_bad_storage_at cx st0 (eval_expr cx e) es s0 marks /\
  gas_admissible (eval_stmt cx (Expr e)) (stmt_res_ok lctx) es ==>
  gas_bad_storage_at cx st0 (eval_stmt cx (Expr e)) es s0 marks
Proof
  rw[gasStorageTheory.gas_bad_storage_at_def] >>
  first_x_assum (qspec_then `tail` mp_tac) >>
  Cases_on `eval_expr cx e
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail)` >>
  rename1 `_ = (res, ee)` >> Cases_on `res`
  >- (drule_all expr_stmt_not_hashmap >> strip_tac >>
      drule_all eval_expr_stmt_success >> simp[]) >>
  drule eval_expr_stmt_exception >> simp[]
QED

Theorem compile_expr_stmt_frag_ok:
  !ctx func cx lctx RetQ cenv ty e es.
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    (!gs sa vv sb tv es1.
       storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
       eval_expr cx e (es with gas_obs := gs) = (INL tv, es1) /\
       compile_expr cenv (expr_type e) e sa = (vv, sb) /\
       ~block_is_terminated sa ==> ~block_is_terminated sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (Expr e))
      (eval_stmt cx (Expr e)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >> rename1 `_ = (vv, sm)` >>
  simp[] >> strip_tac >> gvs[] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[expr_stmt_admissible] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sb`, `vv`, `s0`] mp_tac) >>
  impl_tac >- gs[] >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> BETA_TAC >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      irule expr_stmt_bad_storage >> simp[] >> metis_tac[])
  >- (qexists_tac `marks` >> disj2_tac >> disj1_tac >>
      drule_all expr_stmt_marked_exec >> strip_tac >>
      first_x_assum (irule_at Any) >> disj1_tac >>
      qexists_tac `t` >> conj_tac >- first_assum ACCEPT_TAC >>
      `~t.vs_halted` by
        (qpat_x_assum `gas_marked_exec _ _ (eval_expr _ _) _ _ _ _ _` mp_tac >>
         simp[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
         metis_tac[fragGasPathTheory.gas_path_normal]) >>
      `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
         (res, es_end with gas_obs := [])` by
        (qpat_x_assum `gas_marked_exec _ _ (eval_expr _ _) _ _ _ _ _` mp_tac >>
         simp[gas_marked_exec_def] >> strip_tac >>
         first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
      rpt strip_tac >>
      `valid_horizon cx st0 H es.storage_trace` by
        (qpat_x_assum `eval_expr cx e _ = (res,_)` assume_tac >>
         drule_at (Pos (el 2)) vyperStorageFootprintTheory.valid_horizon_frame >>
         gs[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> ?tv. _`
        (qspec_then `H` mp_tac) >>
      impl_tac >- gs[] >>
      strip_tac >> gvs[] >>
      `stmt_state_rel H ctx func cenv cx es s0` by metis_tac[] >>
      `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
        fs[vv_post_def, stmt_state_rel_def, state_rel_def] >>
      `~block_is_terminated sb` by metis_tac[] >>
      `MAP FDOM (es_end with gas_obs := []).scopes = MAP FDOM es.scopes` by
        (imp_res_tac vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >>
         fs[]) >>
      irule expr_stmt_post >> simp[] >> metis_tac[])
  >- (qexists_tac `marks` >> disj2_tac >> disj1_tac >>
      drule_all expr_stmt_marked_exec >> strip_tac >>
      first_x_assum (irule_at Any) >> disj2_tac >>
      conj_tac >- first_assum ACCEPT_TAC >>
      Cases_on `res` >> gs[stmt_exit_def] >>
      metis_tac[expr_exit_INR_type]) >>
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  metis_tac[expr_stmt_exempt]
QED

(* The same, with the expression's fragment leaving its block open from
   every start. *)
Theorem compile_expr_stmt_frag:
  !ctx func cx lctx RetQ cenv ty e es.
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    (!sa vv sb. compile_expr cenv (expr_type e) e sa = (vv, sb) /\
                ~block_is_terminated sa ==> ~block_is_terminated sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (Expr e))
      (eval_stmt cx (Expr e)) es
Proof
  rpt strip_tac >> irule compile_expr_stmt_frag_ok >> simp[] >>
  metis_tac[]
QED

