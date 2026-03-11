Theory mem2varCorrectness
Ancestors
  mem2varProofs

Theorem m2v_transform_function_correct:
  !fuel ctx fn s.
    lift_result (state_equiv {}) (execution_equiv {})
      (run_function fuel ctx fn s)
      (run_function fuel ctx (m2v_transform_function fn) s)
Proof
  ACCEPT_TAC m2v_transform_function_correct_proof
QED
