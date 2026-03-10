(*
 * Tail Merge Pass — Correctness Statement
 *
 * Proof in proofs/tailMergeProofScript.sml; re-exported via ACCEPT_TAC.
 *)

Theory tailMergeCorrectness
Ancestors
  tailMergeProof

Theorem tail_merge_pass_correct:
  !func s fuel ctx.
    wf_ir_fn func /\
    func.fn_blocks <> [] ==>
    let func' = tail_merge_fn func in
    result_equiv {}
      (run_function fuel ctx func s)
      (run_function fuel ctx func' s)
Proof
  ACCEPT_TAC tail_merge_fn_correct
QED
