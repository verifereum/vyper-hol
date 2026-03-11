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
    wf_function func ==>
    let func' = tail_merge_fn func in
    result_equiv UNIV
      (run_function fuel ctx func s)
      (run_function fuel ctx func' s)
Proof
  ACCEPT_TAC tail_merge_fn_correct
QED
