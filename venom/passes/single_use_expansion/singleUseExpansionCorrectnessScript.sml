Theory singleUseExpansionCorrectness
Ancestors
  singleUseExpansionProofs venomWf

Theorem sue_expand_function_correct:
  !fuel ctx fn s.
    lift_result (state_equiv (sue_fresh_vars_fn fn))
               (execution_equiv (sue_fresh_vars_fn fn))
      (run_function fuel ctx fn s)
      (run_function fuel ctx (sue_expand_function fn) s)
Proof
  ACCEPT_TAC sue_expand_function_correct_proof
QED

(* ===== Obligations ===== *)

(* SUE establishes single_use_form *)
Theorem sue_establishes_single_use:
  !fn. single_use_form (sue_expand_function fn)
Proof
  ACCEPT_TAC sue_establishes_single_use_form
QED

Theorem sue_preserves_ssa_form:
  ∀fn. ssa_form fn ⇒ ssa_form (sue_expand_function fn)
Proof
  cheat
QED

Theorem sue_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (sue_expand_function fn)
Proof
  cheat
QED
