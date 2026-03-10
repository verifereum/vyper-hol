(*
 * CFG Normalization Pass — Correctness Statement
 *
 * Proof in proofs/cfgNormProofScript.sml; re-exported via ACCEPT_TAC.
 *)

Theory cfgNormCorrectness
Ancestors
  cfgNormProof

Theorem cfg_norm_pass_correct:
  !func s fuel ctx.
    wf_ir_fn func /\
    func.fn_blocks <> [] ==>
    let func' = cfg_norm_fn func in
    result_equiv {}
      (run_function fuel ctx func s)
      (run_function fuel ctx func' s)
Proof
  ACCEPT_TAC cfg_norm_fn_correct
QED
