Theory algebraicOptCorrectness
Ancestors
  algebraicOptProofs venomWf

(* Algebraic optimization preserves function execution semantics:
   running a function before and after the transform produces
   equivalent results under state_equiv and execution_equiv. *)
Theorem ao_transform_function_correct:
  !fuel ctx fn s.
    lift_result (state_equiv {}) (execution_equiv {})
      (run_function fuel ctx fn s)
      (run_function fuel ctx (ao_transform_function fn) s)
Proof
  ACCEPT_TAC ao_transform_function_correct_proof
QED

(* ===== Obligations ===== *)

Theorem ao_preserves_ssa_form:
  ∀fn. ssa_form fn ⇒ ssa_form (ao_transform_function fn)
Proof
  cheat
QED

Theorem ao_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (ao_transform_function fn)
Proof
  cheat
QED
