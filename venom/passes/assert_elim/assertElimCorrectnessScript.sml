(*
 * Assert Elimination — Correctness Statement
 *
 * Assert elimination preserves execution semantics: if the operand
 * range provably excludes zero, the assert can never fail, so
 * replacing it with NOP is sound.
 *)

Theory assertElimCorrectness
Ancestors
  assertElimProofs

Theorem assert_elim_function_correct:
  !fuel ctx fn s.
    lift_result (state_equiv {}) (execution_equiv {})
      (run_function fuel ctx fn s)
      (run_function fuel ctx (assert_elim_function fn) s)
Proof
  ACCEPT_TAC assert_elim_function_correct_proof
QED
