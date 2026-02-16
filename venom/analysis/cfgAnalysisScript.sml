(*
 * CFG Analysis
 *
 * Computes control-flow graph info for Venom IR functions.
 *)

Theory cfgAnalysis
Ancestors
  list finite_map
  venomInst

(* ==========================================================================
   Small ordered-set helpers (list-backed)
   ========================================================================== *)

Definition ordset_add_def:
  ordset_add x xs = if MEM x xs then xs else x::xs
End

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

Definition cfg_succs_of_def:
  cfg_succs_of cfg lbl = fmap_lookup_list cfg.cfg_succs lbl
End

Definition cfg_preds_of_def:
  cfg_preds_of cfg lbl = fmap_lookup_list cfg.cfg_preds lbl
End

Definition cfg_reachable_of_def:
  cfg_reachable_of cfg lbl =
    case FLOOKUP cfg.cfg_reachable lbl of
      NONE => F
    | SOME b => b
End

Definition cfg_is_normalized_def:
  cfg_is_normalized cfg fn <=>
    !bb. MEM bb fn.fn_blocks ==>
      (LENGTH (cfg_preds_of cfg bb.bb_label) <= 1) \/
      (!pred.
         MEM pred (cfg_preds_of cfg bb.bb_label) ==>
         LENGTH (cfg_succs_of cfg pred) <= 1)
End

(* ==========================================================================
   Successors / predecessors from blocks
   ========================================================================== *)

Definition bb_succs_def:
  bb_succs bb =
    case bb.bb_instructions of
      [] => []
    | insts => REVERSE (get_successors (LAST insts))
End

Definition init_succs_def:
  init_succs bbs =
    FOLDL (λm bb. m |+ (bb.bb_label, [])) FEMPTY bbs
End

Definition init_preds_def:
  init_preds bbs =
    FOLDL (λm bb. m |+ (bb.bb_label, [])) FEMPTY bbs
End

Definition build_succs_def:
  build_succs bbs =
    FOLDL (λm bb. m |+ (bb.bb_label, bb_succs bb)) (init_succs bbs) bbs
End

Definition build_preds_def:
  build_preds bbs succs =
    FOLDL
      (λm bb.
         let succs_lbl = fmap_lookup_list succs bb.bb_label in
         FOLDR
           (λsucc m2.
              let old = fmap_lookup_list m2 succ in
              m2 |+ (succ, ordset_add bb.bb_label old))
           m succs_lbl)
      (init_preds bbs) bbs
End

(* ==========================================================================
   DFS preorder and postorder with fuel (termination-friendly)
   ========================================================================== *)

Definition dfs_post_walk_def:
  dfs_post_walk fuel succs visited lbl =
    case fuel of
      0 => (visited, [])
    | SUC fuel' =>
        if MEM lbl visited then (visited, [])
        else
          let visited' = ordset_add lbl visited in
          let succs_lbl = fmap_lookup_list succs lbl in
          let (vis2, orders) =
            FOLDL
              (λacc s.
                 let (v, ords) = acc in
                 let (v', ords') = dfs_post_walk fuel' succs v s in
                 (v', ords ++ ords'))
              (visited', []) succs_lbl in
          (vis2, orders ++ [lbl])
End

Definition dfs_pre_walk_def:
  dfs_pre_walk fuel succs visited lbl =
    case fuel of
      0 => (visited, [])
    | SUC fuel' =>
        if MEM lbl visited then (visited, [])
        else
          let visited' = ordset_add lbl visited in
          let succs_lbl = fmap_lookup_list succs lbl in
          let (vis2, orders) =
            FOLDL
              (λacc s.
                 let (v, ords) = acc in
                 let (v', ords') = dfs_pre_walk fuel' succs v s in
                 (v', ords ++ ords'))
              (visited', []) succs_lbl in
          (vis2, lbl :: orders)
End

Definition build_reachable_def:
  build_reachable labels visited =
    FOLDL (λm k. m |+ (k, MEM k visited)) FEMPTY labels
End

(* ==========================================================================
   Top-level analysis
   ========================================================================== *)

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
    let fuel = LENGTH bbs + 1 in
    let (vis_post, post) =
      case entry of
        NONE => ([], [])
      | SOME lbl => dfs_post_walk fuel succs [] lbl in
    let (_, pre) =
      case entry of
        NONE => ([], [])
      | SOME lbl => dfs_pre_walk fuel succs [] lbl in
    let reach = build_reachable labels vis_post in
    <| cfg_succs := succs;
       cfg_preds := preds;
       cfg_reachable := reach;
       cfg_dfs_post := post;
       cfg_dfs_pre := pre |>
End

val _ = export_theory();
