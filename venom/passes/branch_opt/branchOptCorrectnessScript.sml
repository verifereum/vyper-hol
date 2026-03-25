Theory branchOptCorrectness
Ancestors
  branchOptProofs venomWf

Theorem branch_opt_function_correct:
  !fuel ctx live_at fn s.
    lift_result (state_equiv (bo_fresh_vars_fn fn))
               (execution_equiv (bo_fresh_vars_fn fn))
      (run_function fuel ctx fn s)
      (run_function fuel ctx (branch_opt_function live_at fn) s)
Proof
  ACCEPT_TAC branch_opt_function_correct_proof
QED

(* ===== Obligations ===== *)

Theorem branch_opt_preserves_ssa_form:
  ∀fn live_at. ssa_form fn ⇒ ssa_form (branch_opt_function live_at fn)
Proof
  cheat
QED

Theorem branch_opt_preserves_wf_function:
  ∀fn live_at. wf_function fn ⇒ wf_function (branch_opt_function live_at fn)
Proof
  cheat
QED
