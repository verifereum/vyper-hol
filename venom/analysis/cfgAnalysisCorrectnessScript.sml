(*
 * CFG Analysis Correctness (Statements Only)
 *
 * We structure the statements in five layers:
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
 * 5) Traversal ordering
 *    - Postorder respects edge direction for non-back-edges.
 *    - Acyclic CFGs yield a clean postorder ordering.
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

(* wf_function captures basic IR well-formedness assumptions
 * needed by CFG analysis and downstream passes. *)
Definition wf_function_def:
  wf_function fn <=>
    ALL_DISTINCT (cfg_labels fn) /\
    fn_wf_entry fn /\
    (!bb. MEM bb fn.fn_blocks ==>
      bb.bb_instructions <> [] /\
      is_terminator (LAST bb.bb_instructions).inst_opcode) /\
    (!bb succ.
      MEM bb fn.fn_blocks /\ MEM succ (bb_succs bb) ==>
      MEM succ (cfg_labels fn))
End

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

(* ==========================================================================
   5) Traversal ordering (cheated)
   ========================================================================== *)

Definition index_of_def:
  index_of x xs =
    case xs of
      [] => 0
    | y::ys => if x = y then 0 else SUC (index_of x ys)
End

(* non-back-edge successors appear earlier than predecessors in postorder.
 * reachable assumption is necessary since otherwise an unreachable node
 * and their successor will have index_of = LENGTH
 *)
Theorem cfg_analyze_postorder_order:
  !fn a b.
    cfg_reachable_of (cfg_analyze fn) a /\
    MEM b (cfg_succs_of (cfg_analyze fn) a) /\
    ~cfg_path (cfg_analyze fn) b a ==>
    index_of b (cfg_dfs_post (cfg_analyze fn)) <
    index_of a (cfg_dfs_post (cfg_analyze fn))
Proof
  cheat
QED

Definition cfg_acyclic_def:
  cfg_acyclic cfg <=>
    !a b. cfg_path cfg a b /\ cfg_path cfg b a ==> a = b
End

(* acyclic CFGs yield a clean postorder ordering for all edges.
 * can be proved from cfg_analyze_postorder_order since cfg_acyclic
 * implies there can be no back-edge b->a if b is a successor of a.
 *)
Theorem cfg_analyze_postorder_order_acyclic:
  !fn a b.
    cfg_reachable_of (cfg_analyze fn) a /\
    cfg_acyclic (cfg_analyze fn) /\
    MEM b (cfg_succs_of (cfg_analyze fn) a) ==>
    index_of b (cfg_dfs_post (cfg_analyze fn)) <
    index_of a (cfg_dfs_post (cfg_analyze fn))
Proof
  cheat
QED

val _ = export_theory();
