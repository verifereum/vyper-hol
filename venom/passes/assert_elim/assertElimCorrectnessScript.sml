(*
 * Assert Elimination — Correctness Statement
 *
 * Assert elimination preserves execution semantics: if the operand
 * range provably excludes zero, the assert can never fail, so
 * replacing it with NOP is sound.
 *)

Theory assertElimCorrectness
Ancestors
  assertElimProofs venomWf

Theorem assert_elim_function_correct:
  !fuel ctx fn s.
    fn_inst_wf fn /\ s.vs_inst_idx = 0 ==>
    (?e. run_function fuel ctx fn s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {})
      (run_function fuel ctx fn s)
      (run_function fuel ctx (assert_elim_function fn) s)
Proof
  ACCEPT_TAC assert_elim_function_correct_proof
QED

(* ===== Obligations ===== *)

Theorem assert_elim_preserves_ssa_form:
  ∀fn. ssa_form fn ⇒ ssa_form (assert_elim_function fn)
Proof
  cheat
QED

Theorem assert_elim_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (assert_elim_function fn)
Proof
  cheat
QED
