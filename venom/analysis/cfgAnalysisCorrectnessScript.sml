(*
 * CFG Analysis Correctness (Statements Only)
 *
 * Lightweight correctness statements for the CFG analysis.
 * Proofs are intentionally omitted for now.
 *)

Theory cfgAnalysisCorrectness
Ancestors
  cfgAnalysis list pred_set

Definition cfg_labels_def:
  cfg_labels fn = MAP (λbb. bb.bb_label) fn.fn_blocks
End

(* ==========================================================================
   Correctness statements (cheated)
   ========================================================================== *)

(* Desiderata: prove the analysis finishes in O(n) time. *)

(* Reachable labels are labels of blocks in the function. *)
Theorem cfg_analyze_reachable_in_labels:
  !fn lbl.
    cfg_reachable_of (cfg_analyze fn) lbl ==>
    MEM lbl (cfg_labels fn)
Proof
  cheat
QED

(* Successor labels are labels of blocks in the function. *)
Theorem cfg_analyze_succ_labels:
  !fn lbl succ.
    MEM succ (cfg_succs_of (cfg_analyze fn) lbl) ==>
    MEM succ (cfg_labels fn)
Proof
  cheat
QED

(* Predecessor labels are labels of blocks in the function. *)
Theorem cfg_analyze_pred_labels:
  !fn lbl pred.
    MEM pred (cfg_preds_of (cfg_analyze fn) lbl) ==>
    MEM pred (cfg_labels fn)
Proof
  cheat
QED

(* ==========================================================================
   Structural correctness statements (cheated)
   ========================================================================== *)

(* cfg_analyze preserves bb_succs on each block. *)
Theorem cfg_analyze_preserves_bb_succs:
  !fn bb.
    MEM bb fn.fn_blocks ==>
    cfg_succs_of (cfg_analyze fn) bb.bb_label = bb_succs bb
Proof
  cheat
QED

(* preds are the inverse edge relation of succs (for block labels). *)
Theorem cfg_analyze_edge_symmetry:
  !fn lbl succ.
    MEM lbl (cfg_labels fn) /\
    MEM succ (cfg_labels fn) ==>
      (MEM succ (cfg_succs_of (cfg_analyze fn) lbl) <=>
       MEM lbl (cfg_preds_of (cfg_analyze fn) succ))
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
