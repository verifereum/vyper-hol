(* Source effects admitted by supported internal-call arguments. *)
Theory bodyIntCallSourceFrame
Ancestors
  supportedExprs supportedExprForms vyperPureExpr vyperInterpreter vyperState
  vyperStatePreservation vyperPlaceFrames

Theorem outcomes_frame_trans[local]:
  s1 = s0 with outcomes := s1.outcomes /\
  s2 = s1 with outcomes := s2.outcomes ==>
  s2 = s0 with outcomes := s2.outcomes
Proof
  simp[evaluation_state_component_equality] >> metis_tac[]
QED

Theorem outcomes_frame_bind[local]:
  (!s r t. f s = (r,t) ==> t = s with outcomes := t.outcomes) /\
  (!x s r t. g x s = (r,t) ==> t = s with outcomes := t.outcomes) /\
  bind f g s = (r,t) ==>
  t = s with outcomes := t.outcomes
Proof
  simp[bind_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  metis_tac[outcomes_frame_trans]
QED

Theorem outcomes_frame_precompile[local]:
  precompile_call_success bt s = (r,t) ==>
  t = s with outcomes := t.outcomes
Proof
  strip_tac >> drule precompile_call_success_state >>
  strip_tac >> gvs[]
QED

Theorem supported_builtin_no_gas_or_len[local]:
  supported_builtin_form tops ty blt es ==>
  blt <> Env MsgGas /\ blt <> Len
Proof
  Cases_on `blt` >> simp[supported_builtin_form_def] >>
  rpt strip_tac >> gvs[] >> Cases_on `es` >> gvs[]
QED

Theorem supported_eval_outcomes_frame:
  (!tops e. supported_pure_expr tops e ==>
    !cx s r t. eval_expr cx e s = (r,t) ==>
      t = s with outcomes := t.outcomes) /\
  (!tops es. supported_pure_exprs tops es ==>
    !cx s r t. eval_exprs cx es s = (r,t) ==>
      t = s with outcomes := t.outcomes) /\
  (!tops fields. supported_pure_fields tops fields ==>
    !cx s r t. eval_exprs cx (MAP SND fields) s = (r,t) ==>
      t = s with outcomes := t.outcomes) /\
  (!tops e. supported_place_expr tops e ==>
    !cx s r t. eval_expr cx e s = (r,t) ==>
      t = s with outcomes := t.outcomes)
Proof
  ho_match_mp_tac supported_pure_expr_ind >>
  simp[supported_pure_expr_def] >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac
  >>~- ([`eval_expr _ (Name _ _) _ = _`],
    drule_at (Pos last) eval_expr_preserves_state >> simp[pure_expr_def] >>
    strip_tac >> gvs[])
  >>~- ([`eval_expr _ (Literal _ _) _ = _`],
    drule_at (Pos last) eval_expr_preserves_state >> simp[pure_expr_def] >>
    strip_tac >> gvs[])
  >>~- ([`eval_expr _ (TopLevelName _ _) _ = _`],
    drule_at (Pos last) eval_expr_preserves_state >> simp[pure_expr_def] >>
    strip_tac >> gvs[])
  >>~- ([`eval_exprs _ [] _ = _`], gvs[Once evaluate_def, return_def])
  >>~- ([`eval_expr _ (Attribute _ _ _) _ = _`],
    gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
    imp_res_tac select_result_state >> gvs[] >> metis_tac[])
  >>~- ([`eval_expr _ (TypeBuiltin _ _ _ _) _ = _`],
    gvs[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(),
        type_check_def, assert_def, return_def, raise_def] >>
    imp_res_tac lift_sum_state >> gvs[] >> metis_tac[])
  >>~- ([`eval_expr _ (StructLit _ _ _) _ = _`],
    rename1 `StructLit ty id fields` >> PairCases_on `id` >>
    gvs[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
    imp_res_tac lift_sum_state >> gvs[] >> metis_tac[])
  >>~- ([`eval_expr _ (Subscript _ _ _) _ = _`],
    gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
    imp_res_tac read_result_state >> imp_res_tac select_result_state >>
    gvs[] >> metis_tac[outcomes_frame_trans])
  >>~- ([`eval_expr _ (IfExp _ _ _ _) _ = _`],
    gvs[Once evaluate_def, bind_def, AllCaseEqs(), switch_BoolV_def, raise_def] >>
    imp_res_tac read_result_state >>
    imp_res_tac conditional_result_state >> gvs[] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[raise_def]) >>
    metis_tac[outcomes_frame_trans])
  >>~- ([`eval_expr _ (Builtin _ _ _) _ = _`],
    drule supported_builtin_no_gas_or_len >> strip_tac >>
    gvs[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(),
        type_check_def, assert_def, return_def, raise_def, get_accounts_def] >>
    imp_res_tac lift_sum_state >> gvs[] >>
    imp_res_tac outcomes_frame_precompile >> metis_tac[outcomes_frame_trans])
  >>~- ([`eval_exprs _ (_::_) _ = _`],
    gvs[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
    imp_res_tac read_result_state >> gvs[] >> metis_tac[outcomes_frame_trans])
QED


Theorem supported_eval_expr_outcomes:
  supported_pure_expr tops e /\ eval_expr cx e s = (r,t) ==>
  t = s with outcomes := t.outcomes
Proof
  metis_tac[CONJUNCT1 supported_eval_outcomes_frame]
QED

Theorem supported_eval_expr_results_outcomes:
  !args s r t.
    EVERY (supported_pure_expr tops) args /\
    eval_expr_results cx args s = (r,t) ==>
    t = s with outcomes := t.outcomes
Proof
  Induct_on `args` >> simp[Once evaluate_def, return_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[bind_def, return_def, AllCaseEqs()] >>
  metis_tac[supported_eval_expr_outcomes, outcomes_frame_trans]
QED
