Theory mem2varCorrectness
Ancestors
  mem2varProofs venomWf basePtrProps pointerConfinedDefs

Theorem m2v_transform_function_correct:
  !fuel ctx fn s bp.
    bp_ptr_sound bp s /\ bp_ptrs_bounded bp s /\
    alloca_pointer_confined fn ==>
    lift_result (state_equiv {}) (execution_equiv {})
      (run_function fuel ctx fn s)
      (run_function fuel ctx (m2v_transform_function fn) s)
Proof
  ACCEPT_TAC m2v_transform_function_correct_proof
QED

(* ===== Obligations ===== *)

Theorem m2v_preserves_ssa_form:
  ∀fn. ssa_form fn ⇒ ssa_form (m2v_transform_function fn)
Proof
  cheat
QED

Theorem m2v_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (m2v_transform_function fn)
Proof
  cheat
QED
