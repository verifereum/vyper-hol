(*
 * Make SSA Pass — Correctness Statement
 *
 * Proof in proofs/makeSsaProofScript.sml; re-exported via ACCEPT_TAC.
 *)

Theory makeSsaCorrectness
Ancestors
  makeSsaProof

Theorem make_ssa_pass_correct:
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
  ACCEPT_TAC make_ssa_fn_correct
QED
