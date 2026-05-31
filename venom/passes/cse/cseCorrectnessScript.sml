(*
 * CSE — Correctness Statement
 *
 * Replacing a redundant computation with ASSIGN from the available
 * expression's result preserves semantics.
 *)

Theory cseCorrectness
Ancestors
  cseProofs venomWf

Theorem cse_function_correct:
  !fuel ctx fn s.
    fn_inst_wf fn /\ s.vs_inst_idx = 0 ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (cse_function fn) s)
Proof
  ACCEPT_TAC cse_function_correct_proof
QED

(* ===== Obligations ===== *)

Theorem cse_preserves_ssa_form:
  ∀fn. ssa_form fn ⇒ ssa_form (cse_function fn)
Proof
  cheat
QED

Theorem cse_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (cse_function fn)
Proof
  cheat
QED
