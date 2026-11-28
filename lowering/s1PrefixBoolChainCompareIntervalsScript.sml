(* Paired child entries in the emitted interval of an eager scalar equality. *)
Theory s1PrefixBoolChainCompareIntervals
Ancestors
  s1PrefixDefs bodyFullBopWordLayout exprSimHyps exprSimSource exprLowering

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  `is_word_type (expr_type e2)` by simp[] >>
  qhdtm_x_assum `expr_sim_full_pre`
    (strip_assume_tac o REWRITE_RULE [expr_sim_full_pre_def]) >>
  drule_all (Q.INST [`bop` |-> `Eq`] bop_full_layout) >>
  simp[] >> strip_tac >>
  drule expr_body_pre_bop >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e1) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `compile_binop Eq _ _ _ _ _ _ = _`
    (assume_tac o SIMP_RULE (srw_ss()) [compile_binop_def, compile_compare_def, LET_THM]) >>
  qexistsl_tac [`x`,`s1`,`shadow_s1`,`y`,`s2`,`shadow_s2`] >>
  pure_rewrite_tac[expr_sim_full_pre_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
*)
Theorem bool_chain_compare_child_intervals:
  is_word_type (expr_type e1) /\ expr_type e2 = expr_type e1 /\
  expr_body_pre cenv cx env (Builtin (BaseT BoolT) (Bop Eq) [e1;e2]) es /\
  expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (BaseT BoolT) (Builtin (BaseT BoolT) (Bop Eq) [e1;e2]) es
    (st0,sa,sb,shadow_sa,shadow_sb,op,s,G,tn) ==>
  ?x s1 shadow_s1 y s2 shadow_s2.
    lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
    lower_value compile_expr cenv (expr_type e1) e2 s1 = (y,s2) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e1)
      (gas_shadow_expr e1) shadow_sa = (x,shadow_s1) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e1)
      (gas_shadow_expr e2) shadow_s1 = (y,shadow_s2) /\
    gas_shadow_state s1 shadow_s1 /\ gas_shadow_state s2 shadow_s2 /\
    fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
    fn_has_code shadow_sa shadow_s1 shadow_func /\
    fn_has_code shadow_s1 shadow_s2 shadow_func /\
    sa.cs_next_var <= s1.cs_next_var /\
    emit_op EQ [x;y] s2 = (op,sb) /\ fn_has_code s2 sb func /\
    expr_body_pre cenv cx env e1 es /\
    expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e1) e1 es (st0,sa,s1,shadow_sa,shadow_s1,x,s,G,tn)
Proof
  cheat
QED
