(* Exception results share the same halt obligation at every value type. *)
Theory haltExitProj
Ancestors
  exprSimDefs

Theorem halt_exit_INR_type:
  halt_exit H cx ee (INR exc : 'a + exception) r <=>
  halt_exit H cx ee (INR exc : 'b + exception) r
Proof
  simp[exprSimDefsTheory.halt_exit_def]
QED

Theorem halt_exit_INR_not_halt:
  exc <> HaltException ==> halt_exit H cx ee (INR exc : 'a + exception) r
Proof
  simp[exprSimDefsTheory.halt_exit_def]
QED
