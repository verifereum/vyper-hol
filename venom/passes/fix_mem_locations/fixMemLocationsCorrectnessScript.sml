(*
 * Fix Memory Locations Pass — Correctness Statement
 *
 * Replacing FREE_VAR_SPACE literals with pinned alloca+ADD preserves
 * function semantics modulo fresh temporary variables.
 *)

Theory fixMemLocationsCorrectness
Ancestors
  fixMemLocationsProofs

Theorem fix_mem_function_correct:
  !fuel ctx fn s.
    lift_result (state_equiv (fml_fresh_vars_fn fn))
               (execution_equiv (fml_fresh_vars_fn fn))
      (run_function fuel ctx fn s)
      (run_function fuel ctx (fix_mem_function fn) s)
Proof
  ACCEPT_TAC fix_mem_function_correct_proof
QED
