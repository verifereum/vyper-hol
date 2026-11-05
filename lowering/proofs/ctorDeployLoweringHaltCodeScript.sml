(* A piece of deploy_unit_execution_correct (ctorDeployLowering).
   ADMITTED until proved. *)
Theory ctorDeployLoweringHaltCode
Ancestors
  fragExec venomExecSemantics

(* A run never changes the code or the labels. *)
Theorem run_from_halt_code:
  !fuel ctx func s final.
    run_from fuel ctx func s = Halt final ==>
    final.vs_code = s.vs_code /\ final.vs_labels = s.vs_labels
Proof
  cheat
QED
