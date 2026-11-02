(*
 * Simplify CFG Pass — Correctness Statement
 *
 * Proof in proofs/simplifyCfgProofScript.sml; re-exported via ACCEPT_TAC.
 *)

Theory simplifyCfgCorrectness
Ancestors
  simplifyCfgProof cfgWf

Theorem simplify_cfg_pass_correct:
  wf_function fn /\ fn_inst_wf fn /\ first_block_no_preds fn /\
  simplify_cfg_fn_ok fn ==>
  fn_bisim fn (simplify_cfg_fn fn)
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
