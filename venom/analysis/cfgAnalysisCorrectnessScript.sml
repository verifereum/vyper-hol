(*
 * CFG Analysis Correctness (Statements Only)
 *
 * We structure the statements in three layers:
 *
 * 1) Label-domain and shape invariants
 *    - All reachable/succ/pred labels are drawn from the function's labels.
 *
 * 2) Structural correctness
 *    - succs match block terminator successors.
 *    - preds are the inverse edge relation (within the label domain).
 *
 * 3) Traversal properties
 *    - DFS preorder/postorder enumerate exactly the reachable labels.
 *    - Entry label is the DFS root (first in preorder, last in postorder).
 *
 * 4) Semantic reachability
 *    - Reachability coincides with a path relation over successor edges.
 *
 * Proofs are intentionally omitted for now.
 *)

(* my own analysis of correctness (should shove somewhere else?)
 * we just refactored the theorem statements so they are more cohesive while keeping their strenght
 * so ok we have
 * 1. reachable \subset labels
 * 2. succs \subset labels
 * 3. preds \subset labels
 * 4. for two labels A and B, A succ B iff B pred A
 * 5. dfs_{pre,post} equal each other and reachable as sets
 *   5.1. this together with 1. implies dfs_{pre,post} are a subset of labels
 *   5.2. but they are lists so we add an additional theorem that they contain no duplicates, making set equality imply equality up to reordering
 * 6. entry is first in preorder and last on postorder
 * 7. cfg_reachable_of is compatible with the inductive relation cfg_path
 *)

Theory cfgAnalysisCorrectness
Ancestors
  cfgAnalysis list pred_set

(* ==========================================================================
   1) Label-domain and shape invariants (cheated)
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
    wf_function fn /\
    MEM succ (cfg_succs_of (cfg_analyze fn) lbl) ==>
    MEM succ (cfg_labels fn)
Proof
  cheat
QED

(* Predecessor labels are labels of blocks in the function. *)
Theorem cfg_analyze_pred_labels:
  !fn lbl pred.
    wf_function fn /\
    MEM pred (cfg_preds_of (cfg_analyze fn) lbl) ==>
    MEM pred (cfg_labels fn)
Proof
  cheat
QED

(* ==========================================================================
   2) Structural correctness statements (cheated)
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

(* ==========================================================================
   3) Traversal statements (cheated)
   ========================================================================== *)

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

(* postorder labels, preorder labels, and reachable labels coincide as sets.
 * together with the previous distinctness theorems, implies that pre and postorders
 * are permutations of each other. *)
Theorem cfg_analyze_reachable_sets:
  !fn.
    set (cfg_dfs_post (cfg_analyze fn)) = set (cfg_dfs_pre (cfg_analyze fn)) /\
    set (cfg_dfs_post (cfg_analyze fn)) =
      {lbl | cfg_reachable_of (cfg_analyze fn) lbl}
Proof
  cheat
QED

(* Entry label is the first label in DFS preorder. *)
Theorem cfg_analyze_preorder_entry_first:
  !fn bb.
    entry_block fn = SOME bb ==>
    cfg_dfs_pre (cfg_analyze fn) <> [] /\
    HD (cfg_dfs_pre (cfg_analyze fn)) = bb.bb_label
Proof
  cheat
QED

(* Entry label is the last label in DFS postorder. *)
Theorem cfg_analyze_postorder_entry_last:
  !fn bb.
    entry_block fn = SOME bb /\
    cfg_dfs_post (cfg_analyze fn) <> [] ==>
    LAST (cfg_dfs_post (cfg_analyze fn)) = bb.bb_label
Proof
  cheat
QED

(* ==========================================================================
   4) Semantic reachability (cheated)
   ========================================================================== *)

(* cfg_path inductively defines a relation for which nodes have directed paths between
 * them, from the successor sets *)
Inductive cfg_path:
  (!cfg n. cfg_path cfg n n) /\
  (!cfg x y z.
     MEM y (cfg_succs_of cfg x) /\ cfg_path cfg y z ==> cfg_path cfg x z)
End

(* Reachable labels are exactly those on a CFG path from the entry label. *)
Theorem cfg_analyze_semantic_reachability:
  !fn bb lbl.
    entry_block fn = SOME bb ==>
    (cfg_reachable_of (cfg_analyze fn) lbl <=>
     cfg_path (cfg_analyze fn) bb.bb_label lbl)
Proof
  cheat
QED

val _ = export_theory();
