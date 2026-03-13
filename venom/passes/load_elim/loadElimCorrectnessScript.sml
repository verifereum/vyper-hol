(*
 * Load Elimination — Correctness Statement
 *
 * Uses fresh vars exclusion for PHI output variables.
 * The existential fresh set is the union of fresh vars from all 5 rounds.
 *)

Theory loadElimCorrectness
Ancestors
  loadElimProofs

Theorem load_elim_function_correct:
  !fuel ir_ctx ctx fn s.
    ?fresh.
    lift_result (state_equiv fresh) (execution_equiv fresh)
      (run_function fuel ctx fn s)
      (run_function fuel ctx (load_elim_function ir_ctx fn) s)
Proof
  ACCEPT_TAC load_elim_function_correct_proof
QED
