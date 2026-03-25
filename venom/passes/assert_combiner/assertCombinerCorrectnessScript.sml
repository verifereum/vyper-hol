Theory assertCombinerCorrectness
Ancestors
  assertCombinerProofs venomWf

Theorem ac_transform_function_correct:
  !fuel ctx fn s.
    lift_result (state_equiv {}) (execution_equiv {})
      (run_function fuel ctx fn s)
      (run_function fuel ctx (ac_transform_function fn) s)
Proof
  ACCEPT_TAC ac_transform_function_correct_proof
QED

(* ===== Obligations ===== *)

Theorem ac_preserves_ssa_form:
  ∀fn. ssa_form fn ⇒ ssa_form (ac_transform_function fn)
Proof
  cheat
QED

Theorem ac_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (ac_transform_function fn)
Proof
  cheat
QED
