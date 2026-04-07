(*
 * Fix Memory Locations Pass — Correctness Statement
 *
 * Replacing FREE_VAR_SPACE literals with pinned alloca+ADD preserves
 * function semantics modulo fresh temporary variables.
 *)

Theory fixMemLocationsCorrectness
Ancestors
  fixMemLocationsProofs venomWf

Theorem fix_mem_function_correct:
  !fuel ctx fn s.
    lift_result (state_equiv (fml_fresh_vars_fn fn))
               (execution_equiv (fml_fresh_vars_fn fn))
                  (execution_equiv (fml_fresh_vars_fn fn))
      (run_function fuel ctx fn s)
      (run_function fuel ctx (fix_mem_function fn) s)
Proof
  ACCEPT_TAC fix_mem_function_correct_proof
QED

(* ===== Obligations ===== *)

Theorem fix_mem_preserves_ssa_form:
  ∀fn. ssa_form fn ⇒ ssa_form (fix_mem_function fn)
Proof
  cheat
QED

Theorem fix_mem_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (fix_mem_function fn)
Proof
  cheat
QED
