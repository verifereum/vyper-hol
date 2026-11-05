(* Initcode size bound needed by codegen_correct's initial_ctx_rel (LENGTH code <= 24576).
 * deploy_state_rel bounds neither deploy_bc nor the appended constructor
 * arguments, so this piece is expected to need a statement decision.
 * TOP-LEVEL: deploy_initcode_bounded (a piece of e2e_deploy_correctness; admitted until proved).
 *)
Theory ctorDeployInitcode
Ancestors
  ctorDeployDefs

Theorem deploy_initcode_bounded:
  !policy tops deploy_bc runtime_bc arts am tx es.
    deploy_phases policy tops (deploy_bc, runtime_bc) arts /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es
    ==>
    LENGTH (FST (HD es.contexts)).msgParams.code <= 24576
Proof
  cheat
QED
