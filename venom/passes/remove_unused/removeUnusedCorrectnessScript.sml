(*
 * Remove Unused Variables — Correctness Statement
 *
 * NOP'ing a removable instruction with unused outputs preserves
 * semantics: the instruction has no side effects and its outputs
 * are never read. Variables eliminated by the pass are excluded
 * from state equivalence (they are dead).
 *)

Theory removeUnusedCorrectness
Ancestors
  removeUnusedProofs pointerConfinedDefs

Theorem remove_unused_function_correct:
  !fuel ctx fn s.
    venom_wf ctx /\ wf_function fn /\ fn_inst_wf fn /\
    alloca_pointer_confined fn ==>
    let elim = remove_unused_eliminated_vars fn in
    lift_result (state_equiv elim) (execution_equiv elim)
      (run_function fuel ctx fn s)
      (run_function fuel ctx (remove_unused_function fn) s)
Proof
  rpt strip_tac >> irule remove_unused_function_correct_proof >> simp[]
QED

(* ===== Obligations ===== *)

Theorem remove_unused_preserves_ssa_form:
  ∀fn. ssa_form fn ⇒ ssa_form (remove_unused_function fn)
Proof
  cheat
QED

Theorem remove_unused_preserves_wf_function:
  ∀fn. wf_function fn ⇒ wf_function (remove_unused_function fn)
Proof
  cheat
QED
