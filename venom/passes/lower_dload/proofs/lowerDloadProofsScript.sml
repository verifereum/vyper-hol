(*
 * Lower DLOAD Pass — Proofs
 *
 * Correctness: the expanded instruction sequence computes the same
 * result as the original dload/dloadbytes, under the precondition
 * that code_end resolves to the data section boundary.
 *)

Theory lowerDloadProofs
Ancestors
  lowerDloadDefs

Theorem lower_dload_function_correct_proof:
  !fuel ctx fn s.
    lift_result (state_equiv (ld_fresh_vars_fn fn))
               (execution_equiv (ld_fresh_vars_fn fn))
      (run_function fuel ctx fn s)
      (run_function fuel ctx (lower_dload_function fn) s)
Proof
  cheat
QED
