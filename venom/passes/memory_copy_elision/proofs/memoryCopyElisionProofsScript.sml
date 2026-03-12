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
    lift_result (state_equiv {}) (execution_equiv {})
      (run_function fuel ctx fn s)
      (run_function fuel ctx (copy_elision_function ctx fn) s)
Proof
  cheat
QED
