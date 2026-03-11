Theory mem2varProofs
Ancestors
  mem2varDefs

Theorem m2v_transform_function_correct_proof:
  !fuel ctx fn s.
    lift_result (state_equiv {}) (execution_equiv {})
      (run_function fuel ctx fn s)
      (run_function fuel ctx (m2v_transform_function fn) s)
Proof
  cheat
QED
