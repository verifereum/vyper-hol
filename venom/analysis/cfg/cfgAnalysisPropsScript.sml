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
 *    - Preorder has symmetric property.
 *
 * Proofs live in cfgCorrectnessProofScript.sml; this file re-exports via ACCEPT_TAC.
 *
 * Informal analysis:
 * 1. reachable ⊆ labels
 * 2. succs ⊆ labels
 * 3. preds ⊆ labels
 * 4. for two labels A and B, A succ B iff B pred A
 * 5. dfs_{pre,post} equal each other and reachable as sets
 *   5.1. this together with 1. implies dfs_{pre,post} are a subset of labels
 *   5.2. but they are lists so we add an additional theorem that they contain
 *        no duplicates, making set equality imply equality up to reordering
 * 6. entry is first in preorder and last on postorder
 * 7. cfg_reachable_of is compatible with cfg_path (RTC over successor edges)
 *)

Theory cfgAnalysisProps
Ancestors
  cfgCorrectnessProof

(* ==========================================================================
   1) Label-domain and shape invariants
   ========================================================================== *)

(* Any label marked reachable by cfg_analyze belongs to the function's blocks. *)
Theorem cfg_analyze_reachable_in_labels:
  !fn lbl.
    cfg_reachable_of (cfg_analyze fn) lbl ==>
    MEM lbl (fn_labels fn)
Proof
  ACCEPT_TAC cfg_analyze_reachable_in_labels_proof
QED

(* Every successor computed by cfg_analyze is a label of some block in the function.
 * Requires wf_function (terminators only target existing blocks). *)
Theorem cfg_analyze_succ_labels:
  !fn lbl succ.
    wf_function fn /\
    MEM succ (cfg_succs_of (cfg_analyze fn) lbl) ==>
    MEM succ (fn_labels fn)
Proof
  ACCEPT_TAC cfg_analyze_succ_labels_proof
QED

(* Every predecessor computed by cfg_analyze is a label of some block in the function.
 * Requires wf_function (terminators only target existing blocks). *)
Theorem cfg_analyze_pred_labels:
  !fn lbl pred.
    wf_function fn /\
    MEM pred (cfg_preds_of (cfg_analyze fn) lbl) ==>
    MEM pred (fn_labels fn)
Proof
  ACCEPT_TAC cfg_analyze_pred_labels_proof
QED

(* cfg_analyze only records predecessors for labels in the function:
 * if a label has any predecessors, it must be a block label. *)
Theorem cfg_analyze_preds_domain:
  !fn lbl.
    wf_function fn /\
    cfg_preds_of (cfg_analyze fn) lbl <> [] ==>
    MEM lbl (fn_labels fn)
Proof
  ACCEPT_TAC cfg_analyze_preds_domain_proof
QED

(* ==========================================================================
   2) Structural correctness
   ========================================================================== *)

(* The successors recorded by cfg_analyze for a block match the block's
 * terminator targets (as extracted by bb_succs). *)
Theorem cfg_analyze_preserves_bb_succs:
  !fn bb.
    wf_function fn /\
    MEM bb fn.fn_blocks ==>
    cfg_succs_of (cfg_analyze fn) bb.bb_label = bb_succs bb
Proof
  ACCEPT_TAC cfg_analyze_preserves_bb_succs_proof
QED

(* preds are the inverse edge relation of succs (for block labels). *)
Theorem cfg_analyze_edge_symmetry:
  !fn lbl succ.
    MEM lbl (fn_labels fn) /\
    MEM succ (fn_labels fn) ==>
      (MEM succ (cfg_succs_of (cfg_analyze fn) lbl) <=>
       MEM lbl (cfg_preds_of (cfg_analyze fn) succ))
Proof
  ACCEPT_TAC cfg_analyze_edge_symmetry_proof
QED

(* ==========================================================================
   3) Traversal properties
   ========================================================================== *)

(* DFS postorder contains no duplicates. *)
Theorem cfg_analyze_dfs_post_distinct:
  !fn. ALL_DISTINCT (cfg_dfs_post (cfg_analyze fn))
Proof
  ACCEPT_TAC cfg_analyze_dfs_post_distinct_proof
QED

(* DFS preorder contains no duplicates. *)
Theorem cfg_analyze_dfs_pre_distinct:
  !fn. ALL_DISTINCT (cfg_dfs_pre (cfg_analyze fn))
Proof
  ACCEPT_TAC cfg_analyze_dfs_pre_distinct_proof
QED

(* postorder labels, preorder labels, and reachable labels coincide as sets.
 * together with the previous distinctness theorems, implies that pre and postorders
 * are permutations of each other. *)
Theorem cfg_analyze_reachable_sets:
  !fn.
    wf_function fn ==>
    set (cfg_dfs_post (cfg_analyze fn)) = set (cfg_dfs_pre (cfg_analyze fn)) /\
    set (cfg_dfs_post (cfg_analyze fn)) =
      {lbl | cfg_reachable_of (cfg_analyze fn) lbl}
Proof
  ACCEPT_TAC cfg_analyze_reachable_sets_proof
QED

(* When an entry block exists, the DFS preorder is nonempty and the
 * entry label is its first element. *)
Theorem cfg_analyze_preorder_entry_first:
  !fn bb.
    entry_block fn = SOME bb ==>
    cfg_dfs_pre (cfg_analyze fn) <> [] /\
    HD (cfg_dfs_pre (cfg_analyze fn)) = bb.bb_label
Proof
  ACCEPT_TAC cfg_analyze_preorder_entry_first_proof
QED

(* When an entry block exists, the DFS postorder is nonempty and the
 * entry label is its last element. *)
Theorem cfg_analyze_postorder_entry_last:
  !fn bb.
    entry_block fn = SOME bb ==>
    cfg_dfs_post (cfg_analyze fn) <> [] /\
    LAST (cfg_dfs_post (cfg_analyze fn)) = bb.bb_label
Proof
  ACCEPT_TAC cfg_analyze_postorder_entry_last_proof
QED

(* ==========================================================================
   4) Semantic reachability
   ========================================================================== *)

(* Reachable labels are exactly those on a CFG path from the entry label. *)
Theorem cfg_analyze_semantic_reachability:
  !fn bb lbl.
    wf_function fn /\
    entry_block fn = SOME bb ==>
    (cfg_reachable_of (cfg_analyze fn) lbl <=>
     cfg_path (cfg_analyze fn) bb.bb_label lbl)
Proof
  ACCEPT_TAC cfg_analyze_semantic_reachability_proof
QED

(* ==========================================================================
   5) Traversal ordering
   ========================================================================== *)

(* For an edge a->b where b cannot reach a (i.e. not a back-edge),
 * b appears before a in postorder. Reachable assumption ensures both
 * appear in the postorder list (INDEX_OF returns SOME). *)
Theorem cfg_analyze_postorder_order:
  !fn a b i j.
    cfg_reachable_of (cfg_analyze fn) a /\
    MEM b (cfg_succs_of (cfg_analyze fn) a) /\
    ~cfg_path (cfg_analyze fn) b a /\
    INDEX_OF b (cfg_dfs_post (cfg_analyze fn)) = SOME i /\
    INDEX_OF a (cfg_dfs_post (cfg_analyze fn)) = SOME j ==>
    i < j
Proof
  ACCEPT_TAC cfg_analyze_postorder_order_proof
QED

(* preorder_order DELETED — inherently false for DFS preorder (cross edges).
   See ce_preorder_order_false in cfgCorrectnessProofScript.sml. *)
