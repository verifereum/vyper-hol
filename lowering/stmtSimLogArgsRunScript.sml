Theory stmtSimLogArgsRun
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts
  stmtSimLogArgs stmtSimLogArgsGrowth exprReasonOperand exprOperandVar
  exprSimWordArgs supportedTypes  exprSimOps
  loweringSlice exprLoweringProps freshWrites fragExec emitHelperProps varsExt compileEnv
  vyperInterpreter vyperState vyperTyping
  vyperEvalExprPreservesScopesDom

Theorem log_scalar_base[local]:
  supported_scalar_type ty ==> ?bt. ty = BaseT bt
Proof
  Cases_on `ty` >> simp[supported_scalar_type_def, supported_word_type_def,
    supported_string_type_def]
QED

Theorem compile_log_eval_all_nil_sim:
  frag_exec ctx sa sa (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
    (\s. log_args_post ctx func cenv cx es sa sa s0 es [] [] s)
    (wb_args_exit (INL []))
Proof
  irule frag_exec_refl >> simp[log_args_post_nil]
QED

Theorem log_args_frag_at_entry[local]:
  (!s. P s ==> s = s0) /\
  ((~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts) ==>
    frag_exec ctx sa sb P Q R) ==>
  frag_exec ctx sa sb P Q R
Proof
  simp[frag_exec_def] >> metis_tac[]
QED

Theorem compile_log_eval_all_safe_sim:
  !args ctx func cenv cx R es sa xs sb rr es' s0 env env0 es0.
    (!e tail es. R (e::tail) es ==>
       expr_sim ctx func cenv cx (expr_type e) e es /\
       !v es1. (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es1) ==>
         R tail es1 /\
         ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
              value_has_type tv v) /\
    R args es /\ EVERY supported_scalar_type (MAP expr_type args) /\
    compile_log_eval_all cenv args sa = (xs,sb) /\
    eval_exprs cx args es = (rr,es') /\
    (case rr of INL vs => T | INR exc => expr_res_ok (INR exc : value + exception)) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    expr_sim_inv cenv cx env0 es0 /\ well_typed_exprs env args /\
    (!id t. FLOOKUP env.var_types id = SOME t ==>
       ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) ==>
    frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. ?vs. rr = INL vs /\
        log_args_post ctx func cenv cx es sa sb s0 es' xs vs s /\
        EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sb z) /\
                   (!lab. FST p <> Label lab)) xs)
      (wb_args_exit rr)
Proof
  Induct
  >- (simp[compile_log_eval_all_nil, eval_exprs_nil] >> rpt strip_tac >>
      irule frag_exec_refl >> simp[log_args_post_nil]) >>
  rpt gen_tac >> strip_tac >>
  reverse (Cases_on `stmt_state_rel ctx func cenv cx es s0`)
  >- (`(\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s) = (\s. F)` by
        (simp[FUN_EQ_THM] >> metis_tac[]) >>
      simp[] >> irule frag_exec_false_pre) >>
  irule log_args_frag_at_entry >> qexists `s0` >>
  conj_tac >- simp[] >> strip_tac >>
  gvs[compile_log_eval_all_cons] >>
  rename1 `lower_value compile_expr cenv (expr_type e) e sa = (x,sm)` >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
   sa.cs_next_id <= sm.cs_next_id /\
   (!z. x = Var z ==> not_fresh_at sm z)` by
    (drule (cj 2 compile_expr_grows) >> strip_tac >>
     simp[] >> metis_tac[compile_lower_value_var]) >>
  `cs_extends sm sb /\ sm.cs_next_var <= sb.cs_next_var /\
   sm.cs_next_id <= sb.cs_next_id` by
    (drule compile_log_eval_all_grows >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `expr_sim ctx func cenv cx (expr_type e) e es` by metis_tac[] >>
  drule eval_exprs_cons_cases >> strip_tac
  >- suspend "head_error" >>
  suspend "head_value"
QED

Resume compile_log_eval_all_safe_sim[head_error]:
  gvs[wb_args_exit_def] >>
  drule_all expr_sim_apply >>
  disch_then (qspec_then `s0` mp_tac) >> simp[] >> strip_tac >>
  irule frag_exec_exit_prefix >> goal_assum (drule_at Any) >> simp[]
QED

Resume compile_log_eval_all_safe_sim[head_value]:
  rename1 `eval_exprs cx args es1 = (tail_res, es')` >>
  `well_typed_expr env e /\ well_typed_exprs env args` by
    fs[vyperTypeSystemTheory.well_typed_expr_def] >>
  `!lab. x <> Label lab` by
    (drule_all lower_compile_expr_not_label >> simp[]) >>
  `R args es1` by metis_tac[] >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `MAP FDOM es.scopes = MAP FDOM es1.scopes` by
    (drule forced_eval_expr_preserves_scopes_dom >> simp[]) >>
  `MAP FDOM es1.scopes = MAP FDOM es'.scopes` by
    (drule eval_exprs_preserves_scopes_dom >> simp[]) >>
  `(case tail_res of INL vs => T | INR exc => expr_res_ok (INR exc : value + exception))` by
    (Cases_on `tail_res` >> gvs[]) >>
  `expr_exit (INL v) = (\r. F)` by simp[FUN_EQ_THM] >>
  `expr_res_ok (INL v)` by simp[expr_res_ok_def] >>
  drule_all expr_sim_apply >> disch_then (qspec_then `s0` mp_tac) >>
  simp[expr_exit_def] >> disch_then (mp_then Any irule wb_frag_then) >> simp[] >>
  qx_gen_tac `t` >> strip_tac >>
  first_x_assum (drule_all_then (qspec_then `t` mp_tac)) >>
  disch_then (mp_then Any irule frag_exec_weaken) >>
  conj_tac >- (Cases_on `tail_res` >> simp[wb_args_exit_def]) >>
  conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[expr_post_state]) >>
  rpt strip_tac >> gvs[] >>
  conj_tac
  >- (drule_all log_scalar_base >> strip_tac >>
      irule log_args_post_cons >> simp[] >>
      conj_tac >- metis_tac[] >>
      goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      simp[]) >>
  metis_tac[not_fresh_at_mono]
QED

Finalise compile_log_eval_all_safe_sim

Theorem compile_log_eval_all_sim:
  !args ctx func cenv cx R es sa xs sb rr es' s0 env env0 es0.
    (!e tail es. R (e::tail) es ==>
       expr_sim ctx func cenv cx (expr_type e) e es /\
       !v es1. (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es1) ==>
         R tail es1 /\
         ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
              value_has_type tv v) /\
    R args es /\ EVERY supported_scalar_type (MAP expr_type args) /\
    compile_log_eval_all cenv args sa = (xs,sb) /\
    eval_exprs cx args es = (rr,es') /\
    (case rr of INL vs => T | INR exc => expr_res_ok (INR exc : value + exception)) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    expr_sim_inv cenv cx env0 es0 /\ well_typed_exprs env args /\
    (!id t. FLOOKUP env.var_types id = SOME t ==>
       ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) ==>
    frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. ?vs. rr = INL vs /\
        log_args_post ctx func cenv cx es sa sb s0 es' xs vs s)
      (wb_args_exit rr)
Proof
  rpt gen_tac >> strip_tac >> drule_all compile_log_eval_all_safe_sim >>
  disch_then (qspec_then `s0` mp_tac) >>
  disch_then (mp_then Any irule frag_exec_weaken) >> simp[] >> metis_tac[]
QED
