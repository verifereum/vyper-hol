(*
 * Simplify CFG Pass — Correctness Statement
 *
 * Proof in proofs/simplifyCfgProofScript.sml; re-exported via ACCEPT_TAC.
 *)

Theory simplifyCfgCorrectness
Ancestors
  simplifyCfgProof cfgWf

Theorem simplify_cfg_pass_correct:
  !func s fuel ctx.
    wf_function func ==>
    let func' = simplify_cfg_fn func in
    ?fuel'.
      result_equiv {}
        (run_blocks fuel ctx func s)
        (run_blocks fuel' ctx func' s)
Proof
  ACCEPT_TAC simplify_cfg_fn_correct
QED

(* ===== Obligations ===== *)

Theorem simplify_cfg_establishes_all_reachable:
  ∀func. wf_function func ⇒ all_reachable (simplify_cfg_fn func)
Proof
  cheat
QED

Theorem simplify_cfg_preserves_ssa_form:
  ∀func. ssa_form func ∧ wf_function func ⇒ ssa_form (simplify_cfg_fn func)
Proof
  cheat
QED

Theorem simplify_cfg_preserves_wf_function:
  ∀func. wf_function func ⇒ wf_function (simplify_cfg_fn func)
Proof
  cheat
QED
