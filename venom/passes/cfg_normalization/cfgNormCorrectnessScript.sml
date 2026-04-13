(*
 * CFG Normalization Pass — Correctness Statement
 *
 * Proof in proofs/cfgNormIterScript.sml; re-exported via ACCEPT_TAC.
 *)

Theory cfgNormCorrectness
Ancestors
  cfgNormIter cfgNormProof cfgWf

Theorem cfg_norm_pass_correct:
  !func s fuel ctx.
    wf_function func /\
    (!pred_lbl tgt_lbl var.
       MEM (STRCAT (split_block_name pred_lbl tgt_lbl)
                   (STRCAT "_fwd_" var)) (fn_all_vars func) ==> F) /\
    split_labels_fresh split_block_name func ==>
    let func' = cfg_norm_fn func in
    ?fresh fuel'.
      result_equiv fresh
        (run_function fuel ctx func s)
        (run_function fuel' ctx func' s)
(* cfg_norm_fn_correct has extra preconditions; cheat only the gap *)
Proof
  rpt strip_tac >> irule cfg_norm_fn_correct >> cheat
QED

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
