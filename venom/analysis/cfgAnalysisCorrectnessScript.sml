(*
 * CFG Analysis Correctness (Statements Only)
 *
 * Lightweight correctness statements for the CFG analysis.
 * Proofs are intentionally omitted for now.
 *)

Theory cfgAnalysisCorrectness
Ancestors
  cfgAnalysis list pred_set

(* ==========================================================================
   Well-formedness for CFG results
   ========================================================================== *)

Definition cfg_labels_def:
  cfg_labels fn = MAP (λbb. bb.bb_label) fn.fn_blocks
End

(* cfg_wf: basic shape invariants for a CFG built from fn.fn_blocks.
   - reachable/dfs labels are all drawn from the function's block labels
   - succs/preds only mention labels from the function
   - succs/preds are consistent inverses (edge symmetry) *)
Definition cfg_wf_def:
  cfg_wf cfg fn <=>
    (!lbl.
       cfg_reachable_of cfg lbl ==>
       MEM lbl (cfg_labels fn)) /\
    (!lbl.
       MEM lbl cfg.cfg_dfs_post ==>
       MEM lbl (cfg_labels fn)) /\
    (!lbl.
       MEM lbl cfg.cfg_dfs_pre ==>
       MEM lbl (cfg_labels fn)) /\
    (!lbl succ.
       MEM succ (cfg_succs_of cfg lbl) ==>
       MEM succ (cfg_labels fn)) /\
    (!lbl pred.
       MEM pred (cfg_preds_of cfg lbl) ==>
       MEM pred (cfg_labels fn)) /\
    (!lbl succ.
       MEM succ (cfg_succs_of cfg lbl) ==>
       MEM lbl (cfg_preds_of cfg succ)) /\
    (!lbl pred.
       MEM pred (cfg_preds_of cfg lbl) ==>
       MEM lbl (cfg_succs_of cfg pred))
End

(* ==========================================================================
   Correctness statements (cheated)
   ========================================================================== *)

(* Desiderata: prove the analysis finishes in O(n) time. *)

Theorem cfg_analyze_wf:
  !fn. cfg_wf (cfg_analyze fn) fn
Proof
  cheat
QED

(* ==========================================================================
   Structural correctness statements (cheated)
   ========================================================================== *)

(* cfg_analyze produces succs that match bb_succs on each block. *)
Theorem cfg_analyze_succs_correct:
  !fn bb.
    MEM bb fn.fn_blocks ==>
    cfg_succs_of (cfg_analyze fn) bb.bb_label = bb_succs bb
Proof
  cheat
QED

(* preds are the inverse edge relation of succs. *)
Theorem cfg_analyze_preds_correct:
  !fn bb pred_lbl.
    MEM bb fn.fn_blocks ==>
    (MEM pred_lbl (cfg_preds_of (cfg_analyze fn) bb.bb_label) <=>
     MEM bb.bb_label (cfg_succs_of (cfg_analyze fn) pred_lbl))
Proof
  cheat
QED

(* postorder labels, preorder labels, and reachable labels coincide as sets. *)
Theorem cfg_analyze_reachable_sets:
  !fn.
    set (cfg_dfs_post (cfg_analyze fn)) = set (cfg_dfs_pre (cfg_analyze fn)) /\
    set (cfg_dfs_post (cfg_analyze fn)) =
      {lbl | cfg_reachable_of (cfg_analyze fn) lbl}
Proof
  cheat
QED

(* DFS postorder contains no duplicates. *)
Theorem cfg_analyze_dfs_post_distinct:
  !fn. ALL_DISTINCT (cfg_dfs_post (cfg_analyze fn))
Proof
  cheat
QED

(* DFS preorder contains no duplicates. *)
Theorem cfg_analyze_dfs_pre_distinct:
  !fn. ALL_DISTINCT (cfg_dfs_pre (cfg_analyze fn))
Proof
  cheat
QED


val _ = export_theory();
