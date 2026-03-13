(*
 * Literals Codesize — Correctness Statement
 *
 * The transform preserves semantics: NOT(NOT(x)) = x and
 * (x >>> tz) <<< tz = x when trailing zeros are correct.
 *)

Theory literalsCodesizeCorrectness
Ancestors
  literalsCodesizeProofs

Theorem lit_codesize_function_correct:
  !fuel ctx fn s.
    lift_result (state_equiv {}) (execution_equiv {})
      (run_function fuel ctx fn s)
      (run_function fuel ctx (lit_codesize_function fn) s)
Proof
  ACCEPT_TAC lit_codesize_function_correct_proof
QED
