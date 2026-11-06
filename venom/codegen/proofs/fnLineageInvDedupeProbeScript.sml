Theory fnLineageInvDedupeProbe
Ancestors livenessDefs venomInst list

Theorem repeated_add_live_distinct_probe:
  ALL_DISTINCT
    (liveness_transfer [] (mk_inst 0 ADD [Var "x"; Var "x"] ["y"]) [])
Proof
  EVAL_TAC
QED
