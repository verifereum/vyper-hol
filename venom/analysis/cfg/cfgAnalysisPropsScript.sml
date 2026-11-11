(*
 * CFG Analysis Correctness (Statements Only)
 *
 * Statements in four layers. The label-domain invariants, the exact
 * successor equations, postorder facts and the edge relation restricted to
 * labels live only in cfgCorrectnessProof.
 *
 * 1) Structural correctness
 *    - terminator successors are cfg successors.
 *    - preds are the inverse of the edge relation.
 *
 * 2) Traversal properties
 *    - DFS preorder has no duplicates.
 *    - DFS preorder/postorder enumerate exactly the reachable labels.
 *    - Entry label is first in preorder.
 *
 * 3) Semantic reachability
 *    - Reachability coincides with a path relation over successor edges.
 *
 * 4) Traversal ordering
 *    - Preorder does NOT respect edge direction for non-back-edges (cross
 *      edges violate it); see ce_preorder_order_false below.
 *
 * Proofs live in cfgCorrectnessProofScript.sml; this file re-exports via ACCEPT_TAC.
 *)

Theory cfgAnalysisProps
Ancestors
  cfgCorrectnessProof

(* ==========================================================================
   1) Structural correctness
   ========================================================================== *)

(* Unconditional edge symmetry: no MEM-in-fn_labels precondition needed.
 * If a is not a function label, succs is [] so the LHS is vacuously false;
 * symmetrically for the RHS. *)
Theorem cfg_edge_symmetry_uncond:
  !fn a b. MEM b (cfg_succs_of (cfg_analyze fn) a) <=>
           MEM a (cfg_preds_of (cfg_analyze fn) b)
Proof
  ACCEPT_TAC cfg_edge_symmetry_uncond_proof
QED

(* bb_succs of a member block are contained in cfg_succs_of *)
Theorem bb_succs_in_cfg_succs:
  !fn bb lbl.
    ALL_DISTINCT (fn_labels fn) /\
    MEM bb fn.fn_blocks /\
    MEM lbl (bb_succs bb) ==>
    MEM lbl (cfg_succs_of (cfg_analyze fn) bb.bb_label)
Proof
  ACCEPT_TAC cfgHelpersTheory.bb_succs_in_cfg_succs
QED

(* ==========================================================================
   2) Traversal properties
   ========================================================================== *)

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

(* ==========================================================================
   3) Semantic reachability
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
   4) Traversal ordering
   ========================================================================== *)

(* Preorder does NOT have the analogous ordering property. Cross edges in DFS
 * can cause a successor b to appear before its predecessor a in preorder.
 * Counterexample: ce_fn3 (entry→{s,a}, s→{b}, b→{}, a→{b}).
 * DFS preorder: [entry,s,b,a]. a→b is non-back, but INDEX_OF "a"=3 > INDEX_OF "b"=2. *)
Triviality ce_preorder_order_false =
  cfgCorrectnessProofTheory.ce_preorder_order_false

