(* Runtime layouts for positional operands read only after the pure tail. *)
Theory exprExtRequestDelayedTyping
Ancestors
  exprExtRequestStagesSource exprExtRequestTyping exprExtRequestSourceFrame
  exprExtRequestReadProbe exprExtRequestSuffix exprExtRequestUnreadCps
  exprSimSource exprSimHyps exprSimHypsDefs
  memoryLocalRhsProps valueEncodingTyping vyperInterpreter vyperState
  vyperCallOutcomeFrame list

Theorem extrequest_delayed_operand_typed:
  expr_body_pre cenv cx env e es /\ ~expr_has_effect e /\
  eval_expr cx e es = (INL r,mid) /\
  extrequest_read_frame cx mid ee /\
  read_result cx r ee = (INL v,ee) ==>
  value_runtime_typed env (expr_type e) v /\
  value_runtime_typed env (lowered_value_type cenv e) v
Proof
  strip_tac >>
  `read_result cx r mid = (INL v,mid)` by
    (drule extrequest_read_result_frame >>
     disch_then (qspec_then `r` mp_tac) >> simp[] >>
     metis_tac[read_result_state, pairTheory.PAIR, pairTheory.FST]) >>
  `vyperState$bind (eval_expr cx e) (read_result cx) es = (INL v,mid)` by
    simp[vyperStateTheory.bind_def] >>
  conj_tac
  >- (irule memory_rhs_read_annotation_typed >> metis_tac[]) >>
  irule memory_rhs_read_lowered_typed_unwidened >>
  conj_tac
  >- metis_tac[extrequest_effect_free_not_call] >>
  metis_tac[]
QED

Theorem extrequest_delayed_results_typed:
  !xs start rs finish ee vs.
  EVERY (\e. !mid. expr_sim_inv cenv cx env mid ==>
    expr_body_pre cenv cx env e mid) xs /\
  EVERY (\e. ~expr_has_effect e) xs /\
  expr_sim_inv cenv cx env start /\
  eval_expr_results cx xs start = (INL rs,finish) /\
  extrequest_read_frame cx finish ee /\
  read_results cx rs ee = (INL vs,ee) ==>
  LIST_REL (\e v. value_runtime_typed env (expr_type e) v /\
    value_runtime_typed env (lowered_value_type cenv e) v) xs vs
Proof
  Induct >> simp[Once evaluate_def, vyperStateTheory.return_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[extrequest_results_cons, vyperStateTheory.bind_def,
      vyperStateTheory.return_def, AllCaseEqs()] >>
  gvs[read_results_def, vyperStateTheory.bind_def,
      vyperStateTheory.return_def, AllCaseEqs()] >>
  drule read_result_state >> disch_then SUBST_ALL_TAC >>
  `expr_body_pre cenv cx env h start` by metis_tac[] >>
  `expr_sim_inv cenv cx env s''` by
    metis_tac[expr_body_pre_eval_result] >>
  `extrequest_read_frame cx s'' finish'` by
    (drule extrequest_pure_results_read_frame >>
     rewrite_tac[state_rel_frame_def] >>
     disch_then (qspecl_then [`cx`, `s''`] mp_tac) >>
     asm_rewrite_tac[] >> simp[]) >>
  `extrequest_read_frame cx s'' ee` by
    metis_tac[extrequest_read_frame_def] >>
  drule_all extrequest_delayed_operand_typed >> strip_tac >>
  simp[] >> first_x_assum irule >> metis_tac[]
QED
