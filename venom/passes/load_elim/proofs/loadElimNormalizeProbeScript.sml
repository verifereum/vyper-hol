Theory loadElimNormalizeProbe
Ancestors
  loadElimPhiProbes dfgDefs finite_map

Definition normalize_cycle_dfg_def:
  normalize_cycle_dfg = (dfg_build_function singleton_probe_fn) with dfg_defs :=
    FEMPTY |++
      [("x", probe_inst 0 ASSIGN [Var "y"] ["x"]);
       ("y", probe_inst 1 ASSIGN [Var "x"] ["y"]);
       ("bad", probe_inst 2 ASSIGN [Lit 1w] ["bad"])]
End

Theorem normalize_cycle_probe:
  normalize_operand normalize_cycle_dfg [] (Var "x") = Var "x" /\
  normalize_operand normalize_cycle_dfg ["x"] (Var "x") = Var "x" /\
  normalize_operand normalize_cycle_dfg [] (Var "absent") = Var "absent" /\
  normalize_operand normalize_cycle_dfg [] (Lit 3w) = Lit 3w
Proof
  EVAL_TAC
QED

