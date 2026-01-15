(*
 * CFG Analysis
 *
 * Port of venom/analysis/cfg.py.
 *)

Theory cfgAnalysis
Ancestors
  list finite_map
  orderedSet
  venomInst

Definition block_successors_def:
  block_successors bb =
    case bb.bb_instructions of
      [] => []
    | insts => get_successors (LAST insts)
End

Definition fmap_lookup_ordset_def:
  fmap_lookup_ordset m k =
    case FLOOKUP m k of NONE => [] | SOME v => v
End

Definition fmap_add_ordset_def:
  fmap_add_ordset m k v =
    let s = fmap_lookup_ordset m k in
    m |+ (k, ordset_add v s)
End

Datatype:
  cfg_analysis = <|
    cfg_in : (string, string list) fmap;
    cfg_out : (string, string list) fmap;
    reachable : (string, bool) fmap;
    dfs_post : string list;
    dfs_pre : string list
  |>
End

Definition init_cfg_maps_def:
  init_cfg_maps labels =
    FOLDL (λm k. m |+ (k, [])) FEMPTY labels
End

Definition build_cfg_maps_def:
  build_cfg_maps bbs =
    let labels = MAP (\bb. bb.bb_label) bbs in
    let cfg_in = init_cfg_maps labels in
    let cfg_out = init_cfg_maps labels in
    FOLDL
      (λ(acc:(string,string list) fmap # (string,string list) fmap) bb.
         let (cin, cout) = acc in
         let succs = REVERSE (block_successors bb) in
         let cout' = FOLDL (λm s. fmap_add_ordset m bb.bb_label s) cout succs in
         let cin' = FOLDL (λm s. fmap_add_ordset m s bb.bb_label) cin succs in
         (cin', cout'))
      (cfg_in, cfg_out) bbs
End

Definition dfs_post_walk_def:
  dfs_post_walk fuel cfg_out visited lbl =
    case fuel of
      0 => (visited, [])
    | SUC fuel' =>
        if MEM lbl visited then (visited, [])
        else
          let visited' = ordset_add lbl visited in
          let succs = fmap_lookup_ordset cfg_out lbl in
          let (vis2, orders) =
            FOLDL
              (λacc s.
                 let (v, ords) = acc in
                 let (v', ords') = dfs_post_walk fuel' cfg_out v s in
                 (v', ords ++ ords'))
              (visited', []) succs in
          (vis2, orders ++ [lbl])
End

Definition dfs_pre_walk_def:
  dfs_pre_walk fuel cfg_out visited lbl =
    case fuel of
      0 => (visited, [])
    | SUC fuel' =>
        if MEM lbl visited then (visited, [])
        else
          let visited' = ordset_add lbl visited in
          let succs = fmap_lookup_ordset cfg_out lbl in
          let (vis2, orders) =
            FOLDL
              (λacc s.
                 let (v, ords) = acc in
                 let (v', ords') = dfs_pre_walk fuel' cfg_out v s in
                 (v', ords ++ ords'))
              (visited', []) succs in
          (vis2, lbl :: orders)
End

Definition build_reachable_def:
  build_reachable labels visited =
    FOLDL (λm k. m |+ (k, MEM k visited)) FEMPTY labels
End

Definition cfg_analyze_def:
  cfg_analyze fn =
    let (cin, cout) = build_cfg_maps fn.fn_blocks in
    let labels = MAP (\bb. bb.bb_label) fn.fn_blocks in
    case fn.fn_blocks of
      [] => <| cfg_in := cin; cfg_out := cout; reachable := FEMPTY;
              dfs_post := []; dfs_pre := [] |>
    | bb::_ =>
        let fuel = LENGTH fn.fn_blocks + 1 in
        let (vis_post, post) = dfs_post_walk fuel cout [] bb.bb_label in
        let (vis_pre, pre) = dfs_pre_walk fuel cout [] bb.bb_label in
        let reach = build_reachable labels vis_post in
        <| cfg_in := cin; cfg_out := cout; reachable := reach;
           dfs_post := post; dfs_pre := pre |>
End

val _ = export_theory();
