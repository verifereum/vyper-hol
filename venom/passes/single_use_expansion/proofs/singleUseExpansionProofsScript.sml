Theory singleUseExpansionProofs
Ancestors
  singleUseExpansionDefs passSharedDefs

Theorem sue_expand_function_correct_proof:
  !fuel ctx fn s.
    lift_result (state_equiv (sue_fresh_vars_fn fn))
               (execution_equiv (sue_fresh_vars_fn fn))
      (run_function fuel ctx fn s)
      (run_function fuel ctx (sue_expand_function fn) s)
Proof
  cheat
QED

(* SingleUseExpansion establishes single_use_form.
   Required by DFT (stack_order analysis needs this for from_to_wf). *)
Theorem sue_establishes_single_use_form:
  !fn. single_use_form (sue_expand_function fn)
Proof
  cheat
QED
