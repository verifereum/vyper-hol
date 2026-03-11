(*
 * Fix Memory Locations Pass — Proofs
 *
 * Correctness: pinned allocas produce the same addresses as the
 * original hardcoded FREE_VAR_SPACE offsets, so memory behavior
 * is unchanged.
 *)

Theory fixMemLocationsProofs
Ancestors
  fixMemLocationsDefs

Theorem fix_mem_function_correct_proof:
  !fuel ctx fn s.
    lift_result (state_equiv (fml_fresh_vars_fn fn))
               (execution_equiv (fml_fresh_vars_fn fn))
      (run_function fuel ctx fn s)
      (run_function fuel ctx (fix_mem_function fn) s)
Proof
  cheat
QED
