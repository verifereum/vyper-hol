(*
 * Lower DLOAD Pass — Correctness Statement
 *
 * Expanding dload/dloadbytes to alloca+add+codecopy+mload preserves
 * semantics modulo fresh temporary variables.
 *)

Theory lowerDloadCorrectness
Ancestors
  lowerDloadProofs

Theorem lower_dload_function_correct:
  !fuel ctx fn s.
    lift_result (state_equiv (ld_fresh_vars_fn fn))
               (execution_equiv (ld_fresh_vars_fn fn))
      (run_function fuel ctx fn s)
      (run_function fuel ctx (lower_dload_function fn) s)
Proof
  ACCEPT_TAC lower_dload_function_correct_proof
QED
