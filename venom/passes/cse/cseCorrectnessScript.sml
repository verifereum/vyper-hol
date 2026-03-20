(*
 * CSE — Correctness Statement
 *
 * Replacing a redundant computation with ASSIGN from the available
 * expression's result preserves semantics.
 *)

Theory cseCorrectness
Ancestors
  cseProofs

Theorem cse_function_correct:
  !fuel ctx fn s.
    fn_inst_wf fn /\ s.vs_inst_idx = 0 ==>
    (?e. run_function fuel ctx fn s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {})
      (run_function fuel ctx fn s)
      (run_function fuel ctx (cse_function fn) s)
Proof
  ACCEPT_TAC cse_function_correct_proof
QED
