Theory loweringBudgetOracleConsumption
Ancestors
  list pair option sum extCallOracle vyperState vyperCallOutcome
  vyperInterpreter venomCallOracleDefs

(* These projections relate only the residual oracle.  Requests need not agree:
   value, control, accounts and trace simulation remain separate obligations.
   Errors and computed precompile failure consume just as successful calls do. *)
Theorem lower_budget_call_consumption:
  !es s rq rq' ro rz sr ee w t.
    es.outcomes = SOME s.vs_outcomes /\
    take_request_outcome rq es = (sr,ee) /\
    consume_call_outcome rq' ro rz s = (w,t) ==>
    ee.outcomes = SOME t.vs_outcomes /\
    t.vs_outcomes = DROP 1 s.vs_outcomes
Proof
  rpt strip_tac >>
  gvs[consume_call_outcome_eq, take_request_outcome_def,
      pair_CASE_def, UNCURRY, take_outcome_rest, AllCaseEqs()]
QED

Theorem lower_budget_create_consumption:
  !es s kind value code rq sr ee w t.
    es.outcomes = SOME s.vs_outcomes /\
    take_create_outcome kind value code es = (sr,ee) /\
    consume_create_outcome rq s = (w,t) ==>
    ee.outcomes = SOME t.vs_outcomes /\
    t.vs_outcomes = DROP 1 s.vs_outcomes
Proof
  rpt strip_tac >>
  gvs[consume_create_outcome_eq, take_create_outcome_def,
      pair_CASE_def, UNCURRY, take_outcome_rest, AllCaseEqs()]
QED

Theorem lower_budget_precompile_consumption:
  !bt es s rq ro rz sr ee w t.
    precompile_builtin bt /\ es.outcomes = SOME s.vs_outcomes /\
    precompile_call_success bt es = (sr,ee) /\
    consume_call_outcome rq ro rz s = (w,t) ==>
    ee.outcomes = SOME t.vs_outcomes /\
    t.vs_outcomes = DROP 1 s.vs_outcomes
Proof
  rpt strip_tac >> Cases_on `s.vs_outcomes` >>
  gvs[consume_call_outcome_eq, precompile_call_success_def,
      take_outcome_rest, vyperStateTheory.check_def,
      vyperStateTheory.assert_def, vyperStateTheory.return_def,
      vyperStateTheory.raise_def, vyperStateTheory.bind_def] >>
  rpt (CASE_TAC >> gvs[])
QED
