(* deploy_dead is well formed, and deploy_venom_result_rel is preserved by the
 * O1 pipeline's result relation with deploy_dead's dead bytes.
 * TOP-LEVEL: deploy_dead_wf, deploy_venom_result_rel_dead (pieces of
 * e2e_deploy_correctness; admitted until proved).
 *)
Theory ctorDeployDead
Ancestors
  ctorDeployDefs

Theorem deploy_dead_wf:
  !tops runtime_bc am tx. dead_wf (deploy_dead tops runtime_bc am tx)
Proof
  cheat
QED

Theorem deploy_venom_result_rel_dead:
  !tops runtime_bc am tx gobs src res res'.
    deploy_source_ok tops am tx /\
    src = load_contract NONE gobs am tx [(NONE, tops)] [] /\
    deploy_venom_result_rel tops runtime_bc tx src res /\
    ~deploy_source_exempt tops src /\
    dead_result_rel (deploy_dead tops runtime_bc am tx) res res'
    ==>
    deploy_venom_result_rel tops runtime_bc tx src res'
Proof
  cheat
QED
