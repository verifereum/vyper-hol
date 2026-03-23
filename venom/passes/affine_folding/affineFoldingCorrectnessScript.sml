Theory affineFoldingCorrectness
Ancestors
  affineFoldingProofs

(* Affine folding preserves function execution semantics:
   running a function before and after the transform produces
   equivalent results under state_equiv and execution_equiv. *)
Theorem af_transform_function_correct:
  !fuel ctx fn s.
    lift_result (state_equiv {}) (execution_equiv {})
      (run_function fuel ctx fn s)
      (run_function fuel ctx (af_transform_function fn) s)
Proof
  ACCEPT_TAC af_transform_function_correct_proof
QED
