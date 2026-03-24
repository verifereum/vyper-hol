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
    wf_function func /\
    (!pred_lbl tgt_lbl var.
       MEM (STRCAT (split_block_name pred_lbl tgt_lbl)
                   (STRCAT "_fwd_" var)) (fn_all_vars func) ==> F) ==>
    let func' = cfg_norm_fn func in
    ?fresh fuel'.
      result_equiv fresh
        (run_function fuel ctx func s)
        (run_function fuel' ctx func' s)
Proof
  ACCEPT_TAC cfg_norm_fn_correct
QED

(* ===== Obligations ===== *)

Theorem cfg_norm_establishes_no_critical_edges:
  ∀func. wf_function func ⇒ no_critical_edges (cfg_norm_fn func)
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
