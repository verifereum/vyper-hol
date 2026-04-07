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
 * Preconditions:
 *   - wf_function (well-formed blocks, not SSA — that's the output)
 *   - valid analysis inputs (dominators, CFG, liveness)
 * The transformation introduces fresh versioned variable names
 * (e.g., x:1, x:2) and PHI nodes, which may change fuel requirements.
 * fresh: set of versioned variable names introduced by renaming. *)
Theorem make_ssa_fn_correct:
  !dom_frontiers dtree dom_post_order pred_map succ_map live_in
   func s fuel ctx.
    wf_function func /\
    valid_dom_tree dom_frontiers dtree dom_post_order func /\
    valid_cfg_maps pred_map succ_map func /\
    valid_liveness live_in func ==>
    let func' = make_ssa_fn dom_frontiers dtree dom_post_order
                  pred_map succ_map live_in func in
    ?fresh fuel'.
      result_equiv fresh
        (run_blocks fuel ctx func s)
        (run_blocks fuel' ctx func' s)
Proof
  cheat
QED
