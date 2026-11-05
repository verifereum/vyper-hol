(* Two facts deploy_unit_execution_correct takes from top-level changes that
 * are not on the branch yet. ADMITTED until those land; each then goes:
 *  - deploy_venom_result_agree_rel: deploy_venom_result_rel takes the agree
 *    form, so this is its definition;
 *  - deploy_call_outcomes_pending: call_outcomes_ok on the call trace becomes
 *    a premise of the top theorem, so the composition takes it from there.
 * Both are false as stated today; they mark the gap, nothing builds on them
 * but the composition.
 *)
Theory ctorDeployLoweringPendingTop
Ancestors
  ctorDeployLoweringAgreeDefs e2eDefs callTrace

Theorem deploy_venom_result_agree_rel:
  !tops runtime_bc am tx src vres.
    deploy_venom_result_agree tops runtime_bc am tx src vres ==>
    deploy_venom_result_rel tops runtime_bc tx src vres
Proof
  cheat
QED

Theorem deploy_call_outcomes_pending:
  !tops deploy_bc am tx es.
    deploy_state_rel tops deploy_bc am tx es ==>
    call_outcomes_ok am tx (MAP SND (call_trace es))
Proof
  cheat
QED
