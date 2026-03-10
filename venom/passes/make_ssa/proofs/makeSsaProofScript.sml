(*
 * Make SSA Pass — Correctness Proof (cheated)
 *
 * Proves: SSA construction (PHI insertion + variable renaming +
 * degenerate PHI removal) preserves execution semantics modulo
 * fresh variable names introduced by versioning.
 * Key insight: each variable version corresponds to a unique
 * definition point; PHI nodes correctly select the reaching
 * definition at each join point.
 *)

Theory makeSsaProof
Ancestors
  makeSsaDefs stateEquiv venomExecSemantics

(* Make SSA preserves execution semantics at the function level.
 * The transformation introduces fresh versioned variable names
 * (e.g., x:1, x:2) but preserves the computation. *)
Theorem make_ssa_fn_correct:
  !dom_frontiers dom_children dom_post_order pred_map succ_map live_in
   func s fuel ctx.
    wf_ir_fn func /\
    func.fn_blocks <> [] ==>
    let func' = make_ssa_fn dom_frontiers dom_children dom_post_order
                  pred_map succ_map live_in func in
    ?fresh.
      result_equiv fresh
        (run_function fuel ctx func s)
        (run_function fuel ctx func' s)
Proof
  cheat
QED
