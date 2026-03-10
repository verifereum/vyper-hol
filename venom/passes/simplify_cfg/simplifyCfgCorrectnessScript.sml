(*
 * Simplify CFG Pass — Correctness Statement
 *
 * Proof in proofs/simplifyCfgProofScript.sml; re-exported via ACCEPT_TAC.
 *)

Theory simplifyCfgCorrectness
Ancestors
  simplifyCfgProof

Theorem simplify_cfg_pass_correct:
  !func s fuel ctx.
    wf_ir_fn func /\
    func.fn_blocks <> [] ==>
    let func' = simplify_cfg_fn func in
    result_equiv {}
      (run_function fuel ctx func s)
      (run_function fuel ctx func' s)
Proof
  ACCEPT_TAC simplify_cfg_fn_correct
QED
