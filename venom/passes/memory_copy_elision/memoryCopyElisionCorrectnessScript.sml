(*
 * Memory Copy Elision — Correctness Statement
 *
 * Eliding redundant memory copies preserves semantics when the
 * destination already contains the expected data.
 *)

Theory memoryCopyElisionCorrectness
Ancestors
  memoryCopyElisionProofs

Theorem copy_elision_function_correct:
  !fuel ctx fn s.
    fn_inst_wf fn /\ s.vs_inst_idx = 0 ==>
    (?e. run_function fuel ctx fn s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {})
      (run_function fuel ctx fn s)
      (run_function fuel ctx (copy_elision_function ctx fn) s)
Proof
  ACCEPT_TAC copy_elision_function_correct_proof
QED
