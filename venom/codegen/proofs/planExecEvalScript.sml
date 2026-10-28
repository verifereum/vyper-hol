(* Exact list-constructor boundaries for native stack-plan execution. *)
Theory planExecEval
Ancestors planExec list

Theorem execute_plan_nil:
  execute_plan initial_fmp [] = []
Proof
  simp[execute_plan_def]
QED

Theorem execute_plan_cons:
  execute_plan initial_fmp (operation :: rest) =
    exec_stack_op initial_fmp operation ++ execute_plan initial_fmp rest
Proof
  simp[execute_plan_def]
QED
