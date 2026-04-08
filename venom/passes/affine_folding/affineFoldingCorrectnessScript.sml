Theory affineFoldingCorrectness
Ancestors
  affineFoldingProofs venomWf

(* Affine folding preserves function execution semantics:
   running a function before and after the transform produces
   equivalent results under state_equiv and execution_equiv. *)
Theorem af_transform_function_correct:
  !fuel ctx fn s.
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (af_transform_function fn) s)
Proof
  ACCEPT_TAC af_transform_function_correct_proof
QED

(* ===== Obligations ===== *)

Theorem af_preserves_ssa_form:
  ∀fn. ssa_form fn ⇒ ssa_form (af_transform_function fn)
Proof
  cheat
QED

Theorem af_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (af_transform_function fn)
Proof
  cheat
QED
