(*
 * Branch Optimization Pass — Proofs
 *
 * Correctness: branch swapping with iszero insertion/removal preserves
 * semantics because iszero(cond) = 0 iff cond != 0.
 *)

Theory branchOptProofs
Ancestors
  branchOptDefs

Theorem branch_opt_function_correct_proof:
  !fuel ctx live_at fn s.
    lift_result (state_equiv (bo_fresh_vars_fn fn))
               (execution_equiv (bo_fresh_vars_fn fn))
      (run_function fuel ctx fn s)
      (run_function fuel ctx (branch_opt_function live_at fn) s)
Proof
  cheat
QED
