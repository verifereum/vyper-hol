(* Joint full simulation for account builtins. *)
Theory bodyFullBuiltinEnvAccount
Ancestors
  bodyFullBuiltinEnvAccountRun bodyFullBuiltinEnvAccountCompose
  bodyFullExprGeneric bodyFullPreds bodySimFull exprSimAccounts exprSimSource
  exprSimHypsDefs exprLoweringProps vyperTypeSystem allocLimits
  vyperAST list

Theorem account_builtin_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    (?i. bt = Acc i) /\
    builtin_args_length_ok bt (LENGTH args) /\
    (builtin_args_length_ok bt (LENGTH args) /\ bt <> Len ==>
     body_exprs_full_ok cx args) /\
    (builtin_args_length_ok bt (LENGTH args) /\ bt = Len ==>
     body_expr_full_ok cx (HD args)) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin a bt args) es ==>
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  `i <> Code` by
    (gvs[expr_body_pre_def, alloc_limits_expr_def]) >>
  `?e. args = [e] /\ a = account_item_type i /\
       expr_type e = BaseT AddressT` by
    (gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
     Cases_on `args` >> gvs[] >> rename1 `h::t` >> Cases_on `t` >> gvs[]) >>
  gvs[] >>
  conj_asm1_tac
  >- (irule account_full_from_suffix >>
      conj_tac
      >- (rpt gen_tac >> strip_tac >>
          drule_all account_suffix_full_run >>
          disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
          qexistsl_tac [`t`, `G'`, `tn'`] >> simp[]) >>
      metis_tac[]) >>
  irule expr_vv_sim_stack_full >>
  simp[expr_type_def, account_item_type_word, compile_acc_stack] >>
  rpt strip_tac >> irule exprLoweringPropsTheory.eval_expr_builtin_value >>
  goal_assum (drule_at Any)
QED
