(*
 * Make SSA Pass — Correctness Statement
 *
 * Proof in proofs/makeSsaProofScript.sml; re-exported via ACCEPT_TAC.
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
