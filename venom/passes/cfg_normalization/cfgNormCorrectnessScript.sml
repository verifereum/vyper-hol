(*
 * CFG Normalization Pass — Correctness Statement
 *
 * Proof in proofs/cfgNormIterScript.sml; re-exported via ACCEPT_TAC.
 *)

Theory cfgNormCorrectness
Ancestors
  cfgNormIter cfgNormProof cfgWf

Theorem cfg_norm_pass_correct = cfg_norm_fn_correct

(* ===== Obligations ===== *)

Theorem cfg_norm_establishes_normalized_cfg:
  ∀func. wf_function func ⇒ is_normalized_cfg (cfg_norm_fn func)
Proof
  cheat
QED

Theorem cfg_norm_preserves_ssa_form:
  ∀func. ssa_form func ∧ wf_function func ⇒ ssa_form (cfg_norm_fn func)
Proof
  cheat
QED

Theorem cfg_norm_preserves_wf_function:
  ∀func. wf_function func ⇒ wf_function (cfg_norm_fn func)
Proof
  cheat
QED
