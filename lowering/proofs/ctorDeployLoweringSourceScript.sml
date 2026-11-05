(* A piece of deploy_unit_execution_correct (ctorDeployLowering).
   ADMITTED until proved. *)
Theory ctorDeployLoweringSource
Ancestors
  ctorDeployLoweringDefs

(* load_contract is deploy_ctor_finish of the constructor body's run from
   deploy_ctor_start, at any gas observations.  The body is call-free
   (constructor_call_free), so it never reads the call outcomes: a run with
   any outcomes field gives the same result. *)
Theorem deploy_ctor_source_run:
  !tops am tx mut nr body am_c es0 gobs oc res st.
    deploy_source_ok tops am tx /\ tx.function_name = "__init__" /\
    deploy_ctor_start tops am tx (mut, nr, body, am_c, es0) /\
    eval_stmts (deploy_evaluation_context tops am tx) body
      (es0 with <| gas_obs := gobs; outcomes := oc |>) = (res, st) ==>
    load_contract NONE gobs am tx [(NONE, tops)] [] =
      deploy_ctor_finish tops tx (deploy_evaluation_context tops am tx) nr mut am_c res st
Proof
  cheat
QED
