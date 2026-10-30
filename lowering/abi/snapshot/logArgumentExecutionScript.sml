(* TOP-LEVEL: source-order argument execution includes materialisation before
   the suffix and propagates failures at either stage. The composition lemma
   joins actual compiler equations, source evaluation and native fragments. *)
Theory logArgumentExecution
Ancestors
  logArgumentCompile typedLogArgs stmtLowering exprLowering context compileEnv
  fragExec fragBlockPath vyperInterpreter vyperState list
Libs pairLib

Definition eval_argument_def:
  eval_argument cx e = do tv <- eval_expr cx e; materialise cx tv od
End

Theorem eval_argument_value:
  !cx e es v es'. eval_expr cx e es = (INL (Value v),es') ==>
    eval_argument cx e es = (INL v,es')
Proof
  simp[eval_argument_def, bind_def, materialise_def, return_def]
QED

Theorem eval_exprs_cons_argument:
  !cx e suffix.
    eval_exprs cx (e::suffix) =
      do v <- eval_argument cx e; vs <- eval_exprs cx suffix; return (v::vs) od
Proof
  rpt gen_tac >> simp[FUN_EQ_THM, Once evaluate_def, eval_argument_def, bind_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[]) >> rpt CASE_TAC >> simp[]
QED

Theorem eval_exprs_argument_success:
  !cx e suffix es v es1 vs es2.
    eval_argument cx e es = (INL v,es1) /\ eval_exprs cx suffix es1 = (INL vs,es2) ==>
    eval_exprs cx (e::suffix) es = (INL (v::vs),es2)
Proof
  simp[eval_exprs_cons_argument, bind_def, return_def]
QED

Theorem eval_exprs_argument_exception:
  (!cx e suffix es exn es'. eval_argument cx e es = (INR exn,es') ==>
    eval_exprs cx (e::suffix) es = (INR exn,es')) /\
  (!cx e suffix es v es1 exn es2.
    eval_argument cx e es = (INL v,es1) /\ eval_exprs cx suffix es1 = (INR exn,es2) ==>
    eval_exprs cx (e::suffix) es = (INR exn,es2))
Proof
  simp[eval_exprs_cons_argument, bind_def]
QED

Theorem log_argument_execution_cons:
  !cx cenv ctx func e suffix cs arg_op load_cut saved save_cut rest cs' es es1 es2 v vs
    ss middle out prefix ptvs pvs tv tvs.
    lower_value compile_expr cenv (expr_type e) e cs = (arg_op,load_cut) /\
    compile_log_save_arg cenv (lowered_value_type cenv e) arg_op suffix load_cut = (saved,save_cut) /\
    compile_log_eval_all cenv suffix save_cut = (rest,cs') /\
    eval_argument cx e es = (INL v,es1) /\ eval_exprs cx suffix es1 = (INL vs,es2) /\
    fragment_path ctx func ss middle /\ fragment_path ctx func middle out /\
    log_args_rel ((prefix ++ [(saved,lowered_value_type cenv e)]) ++ rest)
      ((ptvs ++ [tv]) ++ tvs) ((pvs ++ [v]) ++ vs) out ==>
    compile_log_eval_all cenv (e::suffix) cs = ((saved,lowered_value_type cenv e)::rest,cs') /\
    eval_exprs cx (e::suffix) es = (INL (v::vs),es2) /\ fragment_path ctx func ss out /\
    log_args_rel (prefix ++ (saved,lowered_value_type cenv e)::rest)
      (ptvs ++ tv::tvs) (pvs ++ v::vs) out
Proof
  rpt gen_tac >> strip_tac >> rpt conj_tac
  >- simp[Once compile_log_eval_all_def, comp_bind_def, comp_return_def, LET_THM]
  >- (drule_all eval_exprs_argument_success >> simp[])
  >- (irule fragment_path_trans >> qexists_tac `middle` >> simp[]) >>
  qpat_x_assum `log_args_rel _ _ _ out` mp_tac >>
  simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]
QED
