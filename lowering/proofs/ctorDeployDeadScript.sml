(* deploy_venom_result_rel is preserved by the O1 pipeline's result relation
 * with no dead bytes.
 * TOP-LEVEL: deploy_venom_result_rel_dead (a piece of e2e_deploy_correctness; admitted until proved).
 *)
Theory ctorDeployDead
Ancestors
  ctorDeployDefs

Theorem deploy_venom_result_rel_dead:
  !tops runtime_bc tx src res res'.
    deploy_venom_result_rel tops runtime_bc tx src res /\
    ~deploy_source_exempt tops src /\
    dead_result_rel deploy_dead res res'
    ==>
    deploy_venom_result_rel tops runtime_bc tx src res'
Proof
  cheat
QED
