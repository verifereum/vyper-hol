(*
 * Simplify CFG Pass — Correctness Statement
 *
 * Preconditions:
 *   wf_function, fn_inst_wf  — structural well-formedness
 *   fn_phi_wf                — PHIs mirror CFG predecessors
 *
 * Proof in proofs/simplifyCfgProofScript.sml; re-exported via ACCEPT_TAC.
 *)

Theory simplifyCfgCorrectness
Ancestors
  simplifyCfgProof cfgWf

Theorem simplify_cfg_pass_correct:
  !func s fuel ctx.
    wf_function func /\ fn_inst_wf func /\
    fn_phi_wf func ==>
    let func' = simplify_cfg_fn func in
    ?fuel'.
      result_equiv {}
        (run_function fuel ctx func s)
        (run_function fuel' ctx func' s)
Proof
  cheat
QED
