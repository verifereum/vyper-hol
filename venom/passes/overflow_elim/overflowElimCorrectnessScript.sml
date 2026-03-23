(*
 * Overflow Check Elimination — Correctness Statement
 *
 * Overflow check elimination preserves execution semantics: when
 * range analysis proves an arithmetic operation cannot overflow/underflow,
 * the guarding assert instruction can be safely removed.
 *)

Theory overflowElimCorrectness
Ancestors
  overflowElimProofs

Theorem overflow_elim_function_correct:
  !fuel ctx fn s.
    fn_inst_wf fn /\ s.vs_inst_idx = 0 ==>
    (?e. run_function fuel ctx fn s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {})
      (run_function fuel ctx fn s)
      (run_function fuel ctx (overflow_elim_function fn) s)
Proof
  ACCEPT_TAC overflow_elim_function_correct_proof
QED
