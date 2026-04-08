(*
 * Load Elimination — Correctness Statement
 *
 * Uses fresh vars exclusion for PHI output variables.
 * The existential fresh set is the union of fresh vars from all 5 rounds.
 *)

Theory loadElimCorrectness
Ancestors
  loadElimProofs venomWf basePtrProps

Theorem load_elim_function_correct:
  !fuel ir_ctx ctx fn s bp.
    fn_inst_wf fn /\ s.vs_inst_idx = 0 /\
    bp_ptr_sound bp s /\ bp_ptrs_bounded bp fn s ==>
    ?fresh.
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (load_elim_function fn) s)
Proof
  ACCEPT_TAC load_elim_function_correct_proof
QED

(* ===== Obligations ===== *)

Theorem load_elim_preserves_ssa_form:
  ∀fn. ssa_form fn ⇒ ssa_form (load_elim_function fn)
Proof
  cheat
QED

Theorem load_elim_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (load_elim_function fn)
Proof
  cheat
QED
