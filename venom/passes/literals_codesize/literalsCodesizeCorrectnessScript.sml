(*
 * Literals Codesize — Correctness Statement
 *
 * The transform preserves semantics: NOT(NOT(x)) = x and
 * (x >>> tz) <<< tz = x when trailing zeros are correct.
 *)

Theory literalsCodesizeCorrectness
Ancestors
  literalsCodesizeProofs venomWf

Theorem lit_codesize_function_correct:
  !fuel ctx fn s.
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (lit_codesize_function fn) s)
Proof
  ACCEPT_TAC lit_codesize_function_correct_proof
QED

(* ===== Obligations ===== *)

Theorem lit_codesize_preserves_ssa_form:
  ∀fn. ssa_form fn ⇒ ssa_form (lit_codesize_function fn)
Proof
  cheat
QED

Theorem lit_codesize_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (lit_codesize_function fn)
Proof
  cheat
QED
