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
    fn_inst_wf func /\
    fn_phi_preds_closed func /\
    fn_phis_non_interfering func /\
    fn_phi_labels_distinct func /\
    (!pred_lbl tgt_lbl var.
       MEM (STRCAT (STRCAT (split_block_name pred_lbl tgt_lbl) "_fwd_") var)
                   (fn_all_vars func) ==> F) /\
    split_labels_fresh split_block_name func /\
    (* split_block_name injective on original labels *)
    (!p1 t1 p2 t2.
       MEM p1 (fn_labels func) /\ MEM t1 (fn_labels func) /\
       MEM p2 (fn_labels func) /\ MEM t2 (fn_labels func) /\
       split_block_name p1 t1 = split_block_name p2 t2 ==>
       p1 = p2 /\ t1 = t2) /\
    (* No self-loop critical edges *)
    (!bb. MEM bb func.fn_blocks ==>
       !lbl. MEM lbl (bb_succs bb) ==> lbl <> bb.bb_label) /\
    (* No original label starts with "split_" *)
    (!L. MEM L (fn_labels func) ==> TAKE 6 L <> "split_") /\
    (* No original label contains "_fwd" (4-char) substring *)
    (!L. MEM L (fn_labels func) ==> !a b. L <> STRCAT a (STRCAT "_fwd" b)) /\
    (* No original label ends with "_split" *)
    (!L. MEM L (fn_labels func) ==> !x. L <> STRCAT x "_split") /\
    fn_entry_label func = SOME s.vs_current_bb /\
    ~s.vs_halted /\
    s.vs_inst_idx = 0 /\
    s.vs_prev_bb = NONE /\
    s.vs_labels = FEMPTY ==>
    let func' = cfg_norm_fn func in
    ?fresh fuel'.
      result_equiv fresh
        (run_function fuel ctx func s)
        (run_function fuel' ctx func' s)
Proof
  ACCEPT_TAC cfg_norm_fn_correct
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
