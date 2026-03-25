(*
 * SCCP — Correctness Statement
 *
 * Replacing variable operands with known constants and folding
 * constant branches preserves semantics under SSA form.
 * SSA guarantees each variable has a unique definition point,
 * so the dataflow fixpoint correctly characterizes runtime values.
 *
 * Returns NONE on static assertion failure (compile error).
 *)

Theory sccpCorrectness
Ancestors
  sccpProofs venomWf

Theorem sccp_function_correct:
  !fuel ctx fn fn' s.
    ssa_form fn /\
    sccp_function fn = SOME fn' ==>
    lift_result (state_equiv {}) (execution_equiv {})
      (run_function fuel ctx fn s)
      (run_function fuel ctx fn' s)
Proof
  ACCEPT_TAC sccp_function_correct_proof
QED

(* ===== Obligations ===== *)

Theorem sccp_preserves_ssa_form:
  ∀fn fn'. ssa_form fn ∧ sccp_function fn = SOME fn' ⇒ ssa_form fn'
Proof
  cheat
QED

Theorem sccp_preserves_wf_function:
  ∀fn fn'. wf_function fn ∧ sccp_function fn = SOME fn' ⇒ wf_function fn'
Proof
  cheat
QED
