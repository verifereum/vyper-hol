(*
 * Make SSA Pass — Correctness & Obligations
 *
 * Proof in proofs/makeSsaProofScript.sml; re-exported via ACCEPT_TAC.
 *
 * Obligations:
 *   make_ssa_establishes_ssa_form     — output is in SSA form
 *   make_ssa_establishes_wf_ssa       — output is wf_ssa (ssa_form + dominance)
 *   make_ssa_preserves_wf_function    — output is still wf_function
 *)

Theory makeSsaCorrectness
Ancestors
  makeSsaProof

Theorem make_ssa_pass_correct:
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
        (run_function fuel ctx func s)
        (run_function fuel' ctx func' s)
Proof
  ACCEPT_TAC make_ssa_fn_correct
QED

(* ===== Obligations ===== *)

Theorem make_ssa_establishes_ssa_form:
  ∀dom_frontiers dtree dom_post_order pred_map succ_map live_in func.
    wf_function func ∧
    valid_dom_tree dom_frontiers dtree dom_post_order func ∧
    valid_cfg_maps pred_map succ_map func ∧
    valid_liveness live_in func ⇒
    ssa_form (make_ssa_fn dom_frontiers dtree dom_post_order
                pred_map succ_map live_in func)
Proof
  cheat
QED

Theorem make_ssa_establishes_wf_ssa:
  ∀dom_frontiers dtree dom_post_order pred_map succ_map live_in func.
    wf_function func ∧
    valid_dom_tree dom_frontiers dtree dom_post_order func ∧
    valid_cfg_maps pred_map succ_map func ∧
    valid_liveness live_in func ⇒
    wf_ssa (make_ssa_fn dom_frontiers dtree dom_post_order
              pred_map succ_map live_in func)
Proof
  cheat
QED

Theorem make_ssa_preserves_wf_function:
  ∀dom_frontiers dtree dom_post_order pred_map succ_map live_in func.
    wf_function func ∧
    valid_dom_tree dom_frontiers dtree dom_post_order func ∧
    valid_cfg_maps pred_map succ_map func ∧
    valid_liveness live_in func ⇒
    wf_function (make_ssa_fn dom_frontiers dtree dom_post_order
                   pred_map succ_map live_in func)
Proof
  cheat
QED
