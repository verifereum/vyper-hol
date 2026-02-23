(*
 * CFG Analysis Correctness Proofs
 *
 * Actual proofs for theorems stated in cfgAnalysisCorrectnessScript.
 * Currently cheated; fill in as proofs are developed.
 *)

Theory cfgCorrectnessProof
Ancestors
  cfgAnalysis

(* ==========================================================================
   1) Label-domain and shape invariants
   ========================================================================== *)

Theorem cfg_analyze_reachable_in_labels_proof:
  !fn lbl.
    cfg_reachable_of (cfg_analyze fn) lbl ==>
    MEM lbl (cfg_labels fn)
Proof
  cheat
QED

Theorem cfg_analyze_succ_labels_proof:
  !fn lbl succ.
    wf_function fn /\
    MEM succ (cfg_succs_of (cfg_analyze fn) lbl) ==>
    MEM succ (cfg_labels fn)
Proof
  cheat
QED

Theorem cfg_analyze_pred_labels_proof:
  !fn lbl pred.
    wf_function fn /\
    MEM pred (cfg_preds_of (cfg_analyze fn) lbl) ==>
    MEM pred (cfg_labels fn)
Proof
  cheat
QED

Theorem cfg_analyze_preds_domain_proof:
  !fn lbl.
    cfg_preds_of (cfg_analyze fn) lbl <> [] ==>
    MEM lbl (cfg_labels fn)
Proof
  cheat
QED

(* ==========================================================================
   2) Structural correctness
   ========================================================================== *)

Theorem cfg_analyze_preserves_bb_succs_proof:
  !fn bb.
    MEM bb fn.fn_blocks ==>
    cfg_succs_of (cfg_analyze fn) bb.bb_label = bb_succs bb
Proof
  cheat
QED

Theorem cfg_analyze_edge_symmetry_proof:
  !fn lbl succ.
    MEM lbl (cfg_labels fn) /\
    MEM succ (cfg_labels fn) ==>
      (MEM succ (cfg_succs_of (cfg_analyze fn) lbl) <=>
       MEM lbl (cfg_preds_of (cfg_analyze fn) succ))
Proof
  cheat
QED

(* ==========================================================================
   3) Traversal properties
   ========================================================================== *)

Theorem cfg_analyze_dfs_post_distinct_proof:
  !fn. ALL_DISTINCT (cfg_dfs_post (cfg_analyze fn))
Proof
  cheat
QED

Theorem cfg_analyze_dfs_pre_distinct_proof:
  !fn. ALL_DISTINCT (cfg_dfs_pre (cfg_analyze fn))
Proof
  cheat
QED

Theorem cfg_analyze_reachable_sets_proof:
  !fn.
    set (cfg_dfs_post (cfg_analyze fn)) = set (cfg_dfs_pre (cfg_analyze fn)) /\
    set (cfg_dfs_post (cfg_analyze fn)) =
      {lbl | cfg_reachable_of (cfg_analyze fn) lbl}
Proof
  cheat
QED

Theorem cfg_analyze_preorder_entry_first_proof:
  !fn bb.
    entry_block fn = SOME bb ==>
    cfg_dfs_pre (cfg_analyze fn) <> [] /\
    HD (cfg_dfs_pre (cfg_analyze fn)) = bb.bb_label
Proof
  cheat
QED

Theorem cfg_analyze_postorder_entry_last_proof:
  !fn bb.
    entry_block fn = SOME bb ==>
    cfg_dfs_post (cfg_analyze fn) <> [] /\
    LAST (cfg_dfs_post (cfg_analyze fn)) = bb.bb_label
Proof
  cheat
QED

(* ==========================================================================
   4) Semantic reachability
   ========================================================================== *)

Theorem cfg_analyze_semantic_reachability_proof:
  !fn bb lbl.
    entry_block fn = SOME bb ==>
    (cfg_reachable_of (cfg_analyze fn) lbl <=>
     cfg_path (cfg_analyze fn) bb.bb_label lbl)
Proof
  cheat
QED

(* ==========================================================================
   5) Traversal ordering
   ========================================================================== *)

Theorem cfg_analyze_postorder_order_proof:
  !fn a b i j.
    cfg_reachable_of (cfg_analyze fn) a /\
    MEM b (cfg_succs_of (cfg_analyze fn) a) /\
    ~cfg_path (cfg_analyze fn) b a /\
    INDEX_OF b (cfg_dfs_post (cfg_analyze fn)) = SOME i /\
    INDEX_OF a (cfg_dfs_post (cfg_analyze fn)) = SOME j ==>
    i < j
Proof
  cheat
QED

Theorem cfg_analyze_preorder_order_proof:
  !fn a b i j.
    cfg_reachable_of (cfg_analyze fn) a /\
    MEM b (cfg_succs_of (cfg_analyze fn) a) /\
    ~cfg_path (cfg_analyze fn) b a /\
    INDEX_OF a (cfg_dfs_pre (cfg_analyze fn)) = SOME i /\
    INDEX_OF b (cfg_dfs_pre (cfg_analyze fn)) = SOME j ==>
    i < j
Proof
  cheat
QED
