(*
 * Memory Copy Elision — Proofs
 *
 * Key lemma: copy_elision_inst satisfies analysis_inst_simulates
 * with copy fact soundness.
 *)

Theory memoryCopyElisionProofs
Ancestors
  memoryCopyElisionDefs analysisSimProps passSimulationProps
  basePtrProps

(* bp_ptrs_bounded: copy elision correctness depends on aliasing
 * analysis to determine source and dest don't overlap. *)
Theorem copy_elision_function_correct_proof:
  !fuel ctx fn s bp.
    fn_inst_wf fn /\ s.vs_inst_idx = 0 /\
    bp_ptr_sound bp s /\ bp_ptrs_bounded bp fn s ==>
    (?e. run_function fuel ctx fn s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {})
      (run_function fuel ctx fn s)
      (run_function fuel ctx (copy_elision_function fn) s)
Proof
  cheat
QED
