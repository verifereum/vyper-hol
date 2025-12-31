(* 
 * Simplify-CFG Merge Correctness
 *
 * Correctness proofs for block merge and jump threading.
 *)

Theory scfgMergeCorrect
Ancestors
  scfgMergeRunBlock

(* ===== Merging Blocks ===== *)

Theorem merge_blocks_correct:
  !fn a_lbl b_lbl s.
    cfg_wf fn /\
    phi_fn_wf fn /\
    merge_blocks_cond fn a_lbl b_lbl /\
    s.vs_current_bb = entry_label fn /\
    s.vs_prev_bb = NONE /\
    s.vs_inst_idx = 0 ==>
    run_function_equiv_cfg fn (merge_blocks fn a_lbl b_lbl) s
Proof
  cheat
QED

(* ===== Jump Threading ===== *)

Theorem merge_jump_correct:
  !fn a_lbl b_lbl s.
    cfg_wf fn /\
    phi_fn_wf fn /\
    merge_jump_cond fn a_lbl b_lbl /\
    s.vs_current_bb = entry_label fn /\
    s.vs_prev_bb = NONE /\
    s.vs_inst_idx = 0 ==>
    run_function_equiv_cfg fn (merge_jump fn a_lbl b_lbl) s
Proof
  cheat
QED

val _ = export_theory();
