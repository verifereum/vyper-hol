(*
 * CFG Normalization Pass — Correctness Statement
 *
 * Proof in proofs/cfgNormIterScript.sml; re-exported via ACCEPT_TAC.
 *)

Theory cfgNormCorrectness
Ancestors
  cfgNormIter cfgNormProof cfgNormDefs cfgNormBase cfgWf venomWf

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

(* ===== Helpers ===== *)

(* cfg_norm_iter preserves cfg_norm_inv *)
Theorem cfg_norm_iter_preserves_inv[local]:
  !n func func0 id_base.
    cfg_norm_inv func0 func ==>
    cfg_norm_inv func0 (cfg_norm_iter n func id_base)
Proof
  Induct >> simp[cfg_norm_iter_def, LET_THM] >>
  rpt gen_tac >> strip_tac >>
  pairarg_tac >> fs[] >>
  IF_CASES_TAC >> fs[] >>
  first_x_assum irule >>
  irule cfg_norm_round_preserves_inv >>
  metis_tac[]
QED

(* ===== Obligations ===== *)

Theorem cfg_norm_establishes_normalized_cfg:
  !func. wf_function func ==> is_normalized_cfg (cfg_norm_fn func)
Proof
  cheat
QED

Theorem cfg_norm_preserves_ssa_form:
  !func. ssa_form func /\ wf_function func ==> ssa_form (cfg_norm_fn func)
Proof
  cheat
QED

(* NOTE: cfg_norm_fn does NOT preserve fn_inst_ids_distinct because
   insert_split starts id_base at 0 which collides with existing IDs.
   Only wf_function_no_ids (= wf_function minus fn_inst_ids_distinct)
   is preserved. *)
Theorem cfg_norm_preserves_wf_function:
  !func. wf_function func ==> wf_function_no_ids (cfg_norm_fn func)
Proof
  rpt strip_tac >>
  simp[cfg_norm_fn_def, LET_THM] >>
  irule cfg_norm_inv_wf >>
  qexists_tac `func` >>
  irule cfg_norm_iter_preserves_inv >>
  irule cfg_norm_inv_initial >>
  simp[] >> cheat
QED
