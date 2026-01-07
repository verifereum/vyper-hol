(*
 * Simplify-CFG Merge Correctness
 *
 * Correctness proofs for block merge and jump threading.
 *)

Theory scfgMergeCorrect
Ancestors
  scfgMergeRunBlock
Libs
  scfgMergeRunBlockTheory scfgMergeHelpersTheory scfgDefsTheory
  scfgEquivTheory scfgTransformTheory
  venomSemTheory venomSemPropsTheory venomStateTheory venomInstTheory

(* ===== Lookup Helpers for Merged Function ===== *)

(* Helper: lookup_block returns a block with matching label *)
Theorem lookup_block_label:
  !lbl blocks bb. lookup_block lbl blocks = SOME bb ==> bb.bb_label = lbl
Proof
  Induct_on `blocks` >> simp[lookup_block_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

(* b_lbl is removed from merged function *)
Theorem lookup_block_merge_blocks_b:
  !fn a_lbl b_lbl a b.
    lookup_block a_lbl fn.fn_blocks = SOME a /\
    lookup_block b_lbl fn.fn_blocks = SOME b /\
    a_lbl <> b_lbl ==>
    lookup_block b_lbl (merge_blocks fn a_lbl b_lbl).fn_blocks = NONE
Proof
  rpt strip_tac >> simp[merge_blocks_def, replace_label_fn_def] >>
  sg `a.bb_label = a_lbl` >- metis_tac[lookup_block_label] >>
  irule lookup_block_replace_label_block_none >>
  irule lookup_block_replace_block_none >>
  simp[lookup_block_remove_block_same]
QED

(* a_lbl maps to merged block in merged function *)
Theorem lookup_block_merge_blocks_a:
  !fn a_lbl b_lbl a b.
    lookup_block a_lbl fn.fn_blocks = SOME a /\
    lookup_block b_lbl fn.fn_blocks = SOME b /\
    a_lbl <> b_lbl ==>
    lookup_block a_lbl (merge_blocks fn a_lbl b_lbl).fn_blocks =
    SOME (replace_label_block b_lbl a_lbl
           (a with bb_instructions := FRONT a.bb_instructions ++ b.bb_instructions))
Proof
  rpt strip_tac >> simp[merge_blocks_def, replace_label_fn_def] >>
  sg `a.bb_label = a_lbl` >- metis_tac[lookup_block_label] >>
  irule lookup_block_replace_label_block >>
  sg `lookup_block a_lbl (remove_block b_lbl fn.fn_blocks) = SOME a`
  >- (irule lookup_block_remove_block >> simp[])
  >- (drule lookup_block_replace_block >> strip_tac >>
      first_x_assum (qspec_then `a with bb_instructions :=
        FRONT a.bb_instructions ++ b.bb_instructions` mp_tac) >> simp[])
QED

(* Other blocks map to label-replaced versions *)
Theorem lookup_block_merge_blocks_other:
  !fn a_lbl b_lbl a b c_lbl c.
    lookup_block a_lbl fn.fn_blocks = SOME a /\
    lookup_block b_lbl fn.fn_blocks = SOME b /\
    lookup_block c_lbl fn.fn_blocks = SOME c /\
    a_lbl <> b_lbl /\ c_lbl <> a_lbl /\ c_lbl <> b_lbl ==>
    lookup_block c_lbl (merge_blocks fn a_lbl b_lbl).fn_blocks =
    SOME (replace_label_block b_lbl a_lbl c)
Proof
  rpt strip_tac >> simp[merge_blocks_def, replace_label_fn_def] >>
  sg `a.bb_label = a_lbl` >- metis_tac[lookup_block_label] >>
  irule lookup_block_replace_label_block >>
  sg `lookup_block c_lbl (remove_block b_lbl fn.fn_blocks) = SOME c`
  >- (irule lookup_block_remove_block >> simp[])
  >- (drule lookup_block_replace_block >> strip_tac >>
      first_x_assum (qspec_then `a with bb_instructions :=
        FRONT a.bb_instructions ++ b.bb_instructions` mp_tac) >> simp[])
QED

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
