(* Counted unary composition source boundaries. *)
Theory exprSimUnopComposeProps
Ancestors
  exprSimUnopProps exprUnopSimDefs exprSimDefs gasContext gasSummary gasOutcome
  gasSummaryCompose gasExemptCert gasNormalPrefix vyperInterpreter vyperState
  loweringPosts exprLoweringProps compileEnv venomExecSemantics

Theorem eval_expr_unop_action_general:
  bi <> Len /\ ~precompile_builtin bi /\ builtin_args_length_ok bi 1 ==>
  (bind (eval_expr cx (Builtin ann bi [e])) (read_result cx) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v es. (unop_result cx ann bi [expr_type e] v es, es)))
Proof
  strip_tac >> pure_rewrite_tac[FUN_EQ_THM] >> gen_tac >>
  Cases_on `bind (eval_expr cx (Builtin ann bi [e])) (read_result cx) x` >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) eval_expr_unop_cases) >>
  strip_tac >> gvs[bind_def]
QED

Theorem unop_result_gas_obs:
  unop_result cx ann bi tys v (es with gas_obs := gs) =
  unop_result cx ann bi tys v es
Proof
  simp[unop_result_def]
QED

Theorem unop_operand_admissible:
  bi <> Len /\ ~precompile_builtin bi /\ builtin_args_length_ok bi 1 /\
  gas_admissible (bind (eval_expr cx (Builtin ann bi [e])) (read_result cx))
    expr_res_ok es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  strip_tac >>
  `bind (eval_expr cx (Builtin ann bi [e])) (read_result cx) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v es. (unop_result cx ann bi [expr_type e] v es,es))` by
    (irule eval_expr_unop_action_general >> simp[]) >>
  gvs[] >>
  gvs[gas_admissible_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `res`
  >- simp[expr_res_ok_def] >>
  first_x_assum (qspec_then `gs` mp_tac) >> simp[bind_def]
QED

Theorem unop_exempt_cert:
  bi <> Len /\ ~precompile_builtin bi /\ builtin_args_length_ok bi 1 /\
  gas_exempt_cert memory tops p
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    start marks out endpoint ==>
  gas_exempt_cert memory tops p
    (ignore_bind (bind (eval_expr cx (Builtin ann bi [e])) (read_result cx))
      (return ())) start marks out endpoint
Proof
  strip_tac >>
  asm_simp_tac (srw_ss()) [eval_expr_unop_action_general] >>
  PairCases_on `p` >> PairCases_on `start` >>
  PairCases_on `out` >> PairCases_on `endpoint` >>
  `ignore_bind
    (bind (bind (eval_expr cx e) (read_result cx))
      (\v es. (unop_result cx ann bi [expr_type e] v es,es))) (return ()) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v. ignore_bind (\es. (unop_result cx ann bi [expr_type e] v es,es))
       (return ()))` by
    (qmatch_goalsub_abbrev_tac `bind a _` >>
     simp[FUN_EQ_THM, ignore_bind_def, bind_def] >> gen_tac >>
     Cases_on `a x` >> Cases_on `q` >> simp[] >>
     Cases_on `unop_result cx ann bi [expr_type e] a' r` >> simp[]) >>
  pop_assum SUBST1_TAC >> irule gas_exempt_cert_error_value >> simp[]
QED

Theorem unop_continuation_summary:
  expr_post ctx func cenv cx e1 es sa s1 s0 (ee with gas_obs := []) v1 x t0 /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t0.vs_halted /\
  evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
  unop_frag ctx func cenv cx f (typed_val_to_w256 tv1 v1) ann
    (unop_result cx ann bi [expr_type e1] v1 ee) (ee with gas_obs := []) /\
  expr_res_ok (unop_result cx ann bi [expr_type e1] v1 ee) /\
  f x s1 = (op,sb) /\ (!z. x = Var z ==> not_fresh_at s1 z) /\
  fn_has_code s1 sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv s1 /\ is_word_type ann /\
  is_word_type (expr_type e1) /\ sa.cs_next_var <= s1.cs_next_var ==>
  gas_summary_at F (ctx,func) []
    (\vs. (unop_result cx ann bi [expr_type e1] v1 vs,vs))
    (ee with gas_obs := [],t0)
    (\res fin t. ?v. res = INL v /\
      expr_post ctx func cenv cx (Builtin ann bi [e1]) es sa sb s0 fin v op t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res fin r. expr_exit res r)
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx (ee with gas_obs := []) t0 /\
   eval_operand x t0 = SOME (typed_val_to_w256 tv1 v1)` by
    gvs[expr_post_def, expr_val_rel_def] >>
  qpat_x_assum `unop_frag _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [unop_frag_def]) >>
  disch_then (qspecl_then [`s1`,`sb`,`x`,`op`,`t0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac
  >- (simp[gas_summary_at_def] >>
      qexistsl_tac [`unop_result cx ann bi [expr_type e1] v1 ee`,`ee`,`r`] >>
      conj_tac
      >- (simp[gas_marked_exec_def, unop_result_gas_obs] >> metis_tac[]) >>
      gvs[] >> irule expr_post_unop >> simp[] >>
      qexistsl_tac [`s1`,`t0`,`v1`,`x`] >> simp[]) >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`unop_result cx ann bi [expr_type e1] v1 ee`,`ee`,`r`] >>
  simp[gas_marked_exec_def, unop_result_gas_obs]
QED
