Theory affineFoldingProofs
Ancestors
  affineFoldingDefs

Theorem af_transform_function_correct_proof:
  !fuel ctx fn s.
    lift_result (state_equiv {}) (execution_equiv {})
      (run_function fuel ctx fn s)
      (run_function fuel ctx (af_transform_function fn) s)
Proof
  cheat
QED
