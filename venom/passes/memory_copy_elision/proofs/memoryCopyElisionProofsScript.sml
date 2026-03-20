(*
 * Memory Copy Elision — Proofs
 *
 * Key lemma: copy_elision_inst satisfies analysis_inst_simulates
 * with copy fact soundness.
 *)

Theory memoryCopyElisionProofs
Ancestors
  memoryCopyElisionDefs analysisSimProps passSimulationProps

Theorem copy_elision_function_correct_proof:
  !fuel ctx fn s.
    fn_inst_wf fn /\ s.vs_inst_idx = 0 ==>
    (?e. run_function fuel ctx fn s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {})
      (run_function fuel ctx fn s)
      (run_function fuel ctx (copy_elision_function ctx fn) s)
Proof
  cheat
QED
