(* Exact caller scope preservation for non-mutating target walks. *)
Theory targetPureWalkScopes
Ancestors
  stmtLowering exprLowering notMutateExprScopes vyperInterpreter vyperState
  vyperScopePreservation vyperPlaceFrames vyperStatePreservation

Theorem target_walk_scopes:
  !bt cenv cx es pv ee.
    ~expr_can_mutate cenv (target_to_expr bt) /\
    eval_base_place cx bt es = (INL pv,ee) ==>
    ee.scopes = es.scopes
Proof
  qsuff_tac `(!e:expr. T) /\
    !bt cenv cx es pv ee.
      ~expr_can_mutate cenv (target_to_expr bt) /\
      eval_base_place cx bt es = (INL pv,ee) ==>
      ee.scopes = es.scopes`
  >- simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[target_to_expr_def, expr_can_mutate_def] >> rpt conj_tac
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, get_scopes_def, bind_def, ignore_bind_def,
          type_check_def, assert_def, return_def, raise_def, AllCaseEqs()])
  >- (rpt gen_tac >> PairCases_on `p` >> simp[Once evaluate_def] >>
      metis_tac[lookup_global_scopes])
  >- (rpt strip_tac >>
      qpat_x_assum `eval_base_place _ (SubscriptTarget _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      strip_tac >> imp_res_tac read_result_state >>
      imp_res_tac extend_place_state >>
      imp_res_tac not_mutate_expr_scopes >> gvs[] >> metis_tac[])
  >> rpt strip_tac >>
  qpat_x_assum `eval_base_place _ (AttributeTarget _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  strip_tac >> imp_res_tac extend_place_state >> gvs[] >> metis_tac[]
QED
