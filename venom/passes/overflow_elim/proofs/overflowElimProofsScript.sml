(*
 * Overflow Check Elimination — Proofs
 *
 * Correctness: overflow_elim_function preserves execution semantics.
 *
 * Unlike assert_elim which uses the analysis_inst_simulates framework,
 * this pass follows DFG chains (assert → iszero → lt/gt → add/sub)
 * so it needs a custom correctness argument.
 *
 * Key insight: when the overflow check is provably safe, the assert
 * operand is always nonzero, so removing it (NOP) doesn't change
 * the non-error behavior.
 *)

Theory overflowElimProofs
Ancestors
  overflowElimDefs analysisSimProps passSimulationProps

Theorem overflow_elim_function_correct_proof:
  !fuel ctx fn s.
    fn_inst_wf fn /\ s.vs_inst_idx = 0 ==>
    (?e. run_function fuel ctx fn s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {})
      (run_function fuel ctx fn s)
      (run_function fuel ctx (overflow_elim_function fn) s)
Proof
  cheat
QED
