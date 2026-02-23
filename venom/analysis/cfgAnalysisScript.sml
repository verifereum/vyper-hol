(*
 * CFG Analysis
 *
 * Computes control-flow graph info for Venom IR functions.
 *)

Theory cfgAnalysis
Ancestors
  list finite_map relation
  venomInst

(* ==========================================================================
   Small helpers
   ========================================================================== *)

(* Cons x onto xs if x is not already a member (list-backed set insert). *)
Definition set_insert_def:
  set_insert x xs = if MEM x xs then xs else x::xs
End

(* Look up a key in a finite map, returning [] if absent. *)
Definition fmap_lookup_list_def:
  fmap_lookup_list m k =
    case FLOOKUP m k of
      NONE => []
    | SOME v => v
End

(* ==========================================================================
   Result type and query API
   ========================================================================== *)

Datatype:
  cfg_analysis = <|
    cfg_succs : (string, string list) fmap;
    cfg_preds : (string, string list) fmap;
    cfg_reachable : (string, bool) fmap;
    cfg_dfs_post : string list;
    cfg_dfs_pre : string list
  |>
End

(* Successor labels of lbl in the CFG ([] if lbl is absent). *)
Definition cfg_succs_of_def:
  cfg_succs_of cfg lbl = fmap_lookup_list cfg.cfg_succs lbl
End

(* Predecessor labels of lbl in the CFG ([] if lbl is absent). *)
Definition cfg_preds_of_def:
  cfg_preds_of cfg lbl = fmap_lookup_list cfg.cfg_preds lbl
End

(* Whether lbl was reached during DFS from the entry block. *)
Definition cfg_reachable_of_def:
  cfg_reachable_of cfg lbl =
    case FLOOKUP cfg.cfg_reachable lbl of
      NONE => F
    | SOME b => b
End



(* No critical edges: every block either has at most one predecessor,
 * or all its predecessors have at most one successor.
 * Not currently used but may be a precondition for SSA/phi-elimination. *)
Definition cfg_is_normalized_def:
  cfg_is_normalized cfg fn <=>
    !bb. MEM bb fn.fn_blocks ==>
      (LENGTH (cfg_preds_of cfg bb.bb_label) <= 1) \/
      (!pred.
         MEM pred (cfg_preds_of cfg bb.bb_label) ==>
         LENGTH (cfg_succs_of cfg pred) <= 1)
End

(* ==========================================================================
   Successor / predecessor map construction
   ========================================================================== *)

(* Initialize a label -> [] map for all block labels. *)
Definition init_succs_def:
  init_succs bbs =
    FOLDL (λm bb. m |+ (bb.bb_label, [])) FEMPTY bbs
End

(* Initialize a label -> [] map for all block labels. *)
Definition init_preds_def:
  init_preds bbs =
    FOLDL (λm bb. m |+ (bb.bb_label, [])) FEMPTY bbs
End

(* Map each block label to its bb_succs. *)
Definition build_succs_def:
  build_succs bbs =
    FOLDL (λm bb. m |+ (bb.bb_label, bb_succs bb)) (init_succs bbs) bbs
End

(* For each block, add it as a predecessor of each of its successors. *)
Definition build_preds_def:
  build_preds bbs succs =
    FOLDL
      (λm bb.
         let succs_lbl = fmap_lookup_list succs bb.bb_label in
         FOLDR
           (λsucc m2.
              let old = fmap_lookup_list m2 succ in
              m2 |+ (succ, set_insert bb.bb_label old))
           m succs_lbl)
      (init_preds bbs) bbs
End

(* ==========================================================================
   DFS preorder and postorder (mutually recursive with list helper)
   ========================================================================== *)

Definition dfs_post_walk_def:
  (dfs_post_walk succs visited lbl =
    if MEM lbl visited then (visited, [])
    else
      let visited' = set_insert lbl visited in
      let succs_lbl = fmap_lookup_list succs lbl in
      let (vis2, orders) = dfs_post_walk_list succs visited' succs_lbl in
      (vis2, orders ++ [lbl])) /\
  (dfs_post_walk_list succs visited [] = (visited, [])) /\
  (dfs_post_walk_list succs visited (s::ss) =
    let (v', ords') = dfs_post_walk succs visited s in
    let (v'', ords'') = dfs_post_walk_list succs v' ss in
    (v'', ords' ++ ords''))
Termination
  cheat
End

Definition dfs_pre_walk_def:
  (dfs_pre_walk succs visited lbl =
    if MEM lbl visited then (visited, [])
    else
      let visited' = set_insert lbl visited in
      let succs_lbl = fmap_lookup_list succs lbl in
      let (vis2, orders) = dfs_pre_walk_list succs visited' succs_lbl in
      (vis2, lbl :: orders)) /\
  (dfs_pre_walk_list succs visited [] = (visited, [])) /\
  (dfs_pre_walk_list succs visited (s::ss) =
    let (v', ords') = dfs_pre_walk succs visited s in
    let (v'', ords'') = dfs_pre_walk_list succs v' ss in
    (v'', ords' ++ ords''))
Termination
  cheat
End

(* Map each label to whether it appears in the visited set. *)
Definition build_reachable_def:
  build_reachable labels visited =
    FOLDL (λm k. m |+ (k, MEM k visited)) FEMPTY labels
End

(* ==========================================================================
   Top-level analysis
   ========================================================================== *)

(* Run the full CFG analysis on a function: build successor/predecessor maps,
 * run DFS from the entry block to compute pre/postorder and reachability. *)
Definition cfg_analyze_def:
  cfg_analyze fn =
    let bbs = fn.fn_blocks in
    let succs = build_succs bbs in
    let preds = build_preds bbs succs in
    let labels = MAP (λbb. bb.bb_label) bbs in
    let entry =
      case entry_block fn of
        NONE => NONE
      | SOME bb => SOME bb.bb_label in
    let (vis_post, post) =
      case entry of
        NONE => ([], [])
      | SOME lbl => dfs_post_walk succs [] lbl in
    let (_, pre) =
      case entry of
        NONE => ([], [])
      | SOME lbl => dfs_pre_walk succs [] lbl in
    let reach = build_reachable labels vis_post in
    <| cfg_succs := succs;
       cfg_preds := preds;
       cfg_reachable := reach;
       cfg_dfs_post := post;
       cfg_dfs_pre := pre |>
End

(* ==========================================================================
   Well-formedness and reachability predicates
   ========================================================================== *)

(* wf_function: IR well-formedness for CFG analysis.
 * - unique block labels
 * - at least one block (fn_has_entry)
 * - every block is non-empty and ends with a terminator (bb_well_formed)
 * - successor labels of every block exist in the function (fn_succs_closed) *)
Definition wf_function_def:
  wf_function fn <=>
    ALL_DISTINCT (fn_labels fn) /\
    fn_has_entry fn /\
    (!bb. MEM bb fn.fn_blocks ==> bb_well_formed bb) /\
    fn_succs_closed fn
End

(* cfg_path: reachability via successor edges (defined as RTC). *)
Definition cfg_path_def:
  cfg_path cfg = RTC (λa b. MEM b (cfg_succs_of cfg a))
End
