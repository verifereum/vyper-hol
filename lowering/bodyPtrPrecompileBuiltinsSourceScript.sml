Theory bodyPtrPrecompileBuiltinsSource
Ancestors exprSimWordArgs vyperInterpreter vyperState

Theorem precompile_eval_read_action:
 !cx ann bt args.
 (bt = ECRecover \/ bt = ECAdd \/ bt = ECMul) /\
 builtin_args_length_ok bt (LENGTH args) ==>
 bind (eval_expr cx (Builtin ann bt args)) (read_result cx) =
 bind (eval_exprs cx args)
   (\vs st. case exprSimWordArgs$builtin_result cx st.accounts ann bt
                    (MAP expr_type args) vs of
      INR ex => (INR ex,st)
    | INL v => (do precompile_call_success bt; return v od) st)
Proof
  rpt gen_tac >> strip_tac >> pure_rewrite_tac[FUN_EQ_THM] >> gen_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def] >>
  Cases_on `eval_exprs cx args x` >> rename1 `eval_exprs cx args x = (rr,st)` >>
  Cases_on `rr` >> simp[get_accounts_def, bind_def, return_def,
    lift_sum_def, builtin_result_def] >>
  rename1 `evaluate_builtin cx st.accounts ann bi ts vs` >>
  Cases_on `evaluate_builtin cx st.accounts ann bi ts vs` >>
  simp[bind_def, return_def, raise_def, read_result_def, ignore_bind_def] >>
  Cases_on `precompile_call_success bi st` >>
  rename1 `precompile_call_success bi st = (rr,fin)` >> Cases_on `rr` >>
  simp[bind_def, return_def, read_result_def]
QED
