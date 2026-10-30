(* TOP-LEVEL: successful source argument execution decomposes in order
   and preserves the typing environment used by the next native step.
   Materialisation is included in eval_argument. *)
Theory logArgumentSourceExecution
Ancestors
  logArgumentExecution vyperTypeEvalSoundness vyperTypeExprSoundness
  vyperTypeSystem vyperTypeInvariants vyperTypeCallGraph vyperTypeCallStackSoundness
  vyperInterpreter vyperState vyperAST list pair

Theorem eval_exprs_cons_success:
  !cx e suffix es values es'.
    eval_exprs cx (e::suffix) es = (INL values,es') <=>
    ?v middle vs. eval_argument cx e es = (INL v,middle) /\
      eval_exprs cx suffix middle = (INL vs,es') /\ values = v::vs
Proof
  rpt gen_tac >> simp_tac bool_ss [eval_exprs_cons_argument, bind_def, return_def] >>
  Cases_on `eval_argument cx e es` >> rename1 `eval_argument cx e es = (result,middle)` >>
  Cases_on `result` >> simp[] >> Cases_on `eval_exprs cx suffix middle` >>
  rename1 `eval_exprs cx suffix middle = (rest_result,last)` >> Cases_on `rest_result` >>
  simp[EQ_SYM_EQ, CONJ_COMM]
QED

Theorem eval_argument_singleton_success:
  !cx e es v es'.
    eval_argument cx e es = (INL v,es') <=> eval_exprs cx [e] es = (INL [v],es')
Proof
  rpt gen_tac >> simp_tac bool_ss [eval_exprs_cons_success] >>
  simp[Once evaluate_def, return_def]
QED

Theorem checked_log_argument_source_state:
  !env cx es e v es'.
    runtime_consistent env cx es /\ functions_well_typed cx /\ well_typed_expr env e /\
    call_evaluation_safe cx (int_calls_expr e) /\ eval_argument cx e es = (INL v,es') ==>
    runtime_consistent env cx es' /\ value_runtime_typed env (expr_type e) v
Proof
  rpt gen_tac >> strip_tac >>
  `eval_exprs cx [e] es = (INL [v],es')` by fs[GSYM eval_argument_singleton_success] >>
  `well_typed_exprs env [e]` by simp[well_typed_expr_def] >>
  `call_evaluation_safe cx (int_calls_exprs [e])` by simp[int_calls_expr_def] >>
  fs[runtime_consistent_def] >>
  qspecl_then [`cx`, `[e]`, `env`, `es`, `INL [v]`, `es'`]
    mp_tac (cj 9 eval_all_type_sound_mutual) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  simp_tac bool_ss [runtime_consistent_def] >>
  rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
    gvs[exprs_runtime_typed_def, LIST_REL_CONS1, value_runtime_typed_def] >>
    goal_assum drule >> simp[]]
QED
