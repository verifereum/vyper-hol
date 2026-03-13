(*
 * Assign Elimination — Correctness Statement
 *
 * Copy propagation preserves semantics: replacing Var x with Var y
 * where x := assign y gives the same value because copy_sound ensures
 * lookup_var x s = lookup_var y s at every use site.
 *
 * Variables that are outputs of NOP'd ASSIGNs are excluded from
 * equivalence (assign_elim_eliminated_vars). These variables are dead
 * after copy propagation substitutes all their uses with the source.
 *)

Theory assignElimCorrectness
Ancestors
  assignElimProofs

Theorem assign_elim_function_correct:
  !fuel ctx fn s.
    let elim = assign_elim_eliminated_vars fn in
    lift_result (state_equiv elim) (execution_equiv elim)
      (run_function fuel ctx fn s)
      (run_function fuel ctx (assign_elim_function fn) s)
Proof
  ACCEPT_TAC assign_elim_function_correct_proof
QED
