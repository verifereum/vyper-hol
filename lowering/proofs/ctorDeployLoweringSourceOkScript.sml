(* A piece of deploy_unit_execution_correct (ctorDeployLowering).
   ADMITTED until proved. *)
Theory ctorDeployLoweringSourceOk
Ancestors
  ctorDeployLoweringDefs stmtSimDefs

(* The constructor body never ends in a break or a continue. *)
Theorem deploy_ctor_body_source_ok:
  !tops am tx mut nr body am_c es0 gs oc res ee.
    deploy_source_ok tops am tx /\
    deploy_ctor_start tops am tx (mut, nr, body, am_c, es0) /\
    eval_stmts (deploy_evaluation_context tops am tx) body
      (es0 with <| gas_obs := gs; outcomes := oc |>) = (res, ee) ==>
    stmt_res_ok NoLoop res
Proof
  cheat
QED
