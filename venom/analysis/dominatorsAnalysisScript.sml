(*
 * Dominator Tree Analysis
 *
 * Port of venom/analysis/dominators.py.
 *)

Theory dominatorsAnalysis
Ancestors
  list finite_map sorting
  orderedSet
  cfgAnalysis

Datatype:
  dominators_analysis = <|
    dominators : (string, string list) fmap;
    immediate_dominators : (string, string option) fmap;
    dominated : (string, string list) fmap;
    dominator_frontiers : (string, string list) fmap;
    cfg_post_order : (string, num) fmap;
    cfg_post_walk : string list
  |>
End

Definition build_post_order_def:
  build_post_order bbs =
    FOLDL (λ(acc:(string,num) fmap # num) bb.
             let (m, idx) = acc in
             (m |+ (bb, idx), idx + 1))
          (FEMPTY, 0) bbs
End

Definition init_dom_map_def:
  init_dom_map bbs =
    FOLDL (λm bb. m |+ (bb, bbs)) FEMPTY bbs
End

Definition doms_intersection_def:
  doms_intersection doms preds =
    ordset_inter_list (MAP (\p. fmap_lookup_ordset doms p) preds)
End

Definition compute_doms_iter_def:
  compute_doms_iter entry cfg_in bbs doms =
    FOLDL
      (λacc bb.
         let (doms_acc, changed) = acc in
         if bb = entry then (doms_acc, changed)
         else
           let preds = fmap_lookup_ordset cfg_in bb in
           if preds = [] then (doms_acc, changed)
           else
             let new_doms = ordset_add bb (doms_intersection doms_acc preds) in
             if new_doms = fmap_lookup_ordset doms_acc bb then
               (doms_acc, changed)
             else
               (doms_acc |+ (bb, new_doms), T))
      (doms, F) bbs
End

Definition compute_dominators_def:
  compute_dominators entry cfg_in bbs doms fuel =
    case fuel of
      0 => NONE
    | SUC fuel' =>
        let (doms', changed) = compute_doms_iter entry cfg_in bbs doms in
        if changed then compute_dominators entry cfg_in bbs doms' fuel'
        else SOME doms'
End

Definition sort_by_postorder_def:
  sort_by_postorder (order:(string,num) fmap) bbs =
    QSORT (λa b.
      case (FLOOKUP order a, FLOOKUP order b) of
        (SOME ia, SOME ib) => ia < ib
      | (SOME _, NONE) => T
      | (NONE, SOME _) => F
      | _ => F) bbs
End

Definition compute_idoms_def:
  compute_idoms entry doms cfg_post_order bbs =
    let idoms_init = FOLDL (λm bb. m |+ (bb, NONE)) FEMPTY bbs in
    let idoms1 = idoms_init |+ (entry, SOME entry) in
    FOLDL
      (λm bb.
         if bb = entry then m else
         let dom_list = sort_by_postorder cfg_post_order (fmap_lookup_ordset doms bb) in
         if LENGTH dom_list < 2 then m
         else m |+ (bb, SOME (EL 1 dom_list)))
      idoms1 bbs
End

Definition compute_dominated_def:
  compute_dominated idoms bbs =
    let doms = FOLDL (λm bb. m |+ (bb, [])) FEMPTY bbs in
    FOLDL
      (λm bb.
         case FLOOKUP idoms bb of
           NONE => m
         | SOME NONE => m
         | SOME (SOME idom) =>
             let kids = fmap_lookup_ordset m idom in
             m |+ (idom, ordset_add bb kids))
      doms bbs
End

Definition df_add_runner_def:
  df_add_runner df runner target idoms fuel =
    case fuel of
      0 => df
    | SUC fuel' =>
        if runner = target then df
        else
          let s = fmap_lookup_ordset df runner in
          let df' = df |+ (runner, ordset_add target s) in
          case FLOOKUP idoms runner of
            NONE => df'
          | SOME NONE => df'
          | SOME (SOME r') => df_add_runner df' r' target idoms fuel'
End

Definition compute_df_def:
  compute_df cfg_in idoms bbs =
    let df = FOLDL (λm bb. m |+ (bb, [])) FEMPTY bbs in
    FOLDL
      (λm bb.
         let preds = fmap_lookup_ordset cfg_in bb in
         if LENGTH preds <= 1 then m
         else
           FOLDL
             (λm2 pred.
                case FLOOKUP idoms bb of
                  NONE => m2
                | SOME NONE => m2
                | SOME (SOME idom) =>
                    df_add_runner m2 pred idom idoms (LENGTH bbs + 1))
             m preds)
      df bbs
End

Definition dominators_analyze_def:
  dominators_analyze fn cfg =
    let bbs = cfg.dfs_post in
    let (post_order, _) = build_post_order bbs in
    case entry_block fn of
      NONE => NONE
    | SOME entry_bb =>
        let entry = entry_bb.bb_label in
        let doms0 = init_dom_map bbs in
        let doms1 = doms0 |+ (entry, [entry]) in
        let fuel = (LENGTH bbs) * (LENGTH bbs) + 1 in
        case compute_dominators entry cfg.cfg_in bbs doms1 fuel of
          NONE => NONE
        | SOME doms =>
            let idoms = compute_idoms entry doms post_order bbs in
            let dominated = compute_dominated idoms bbs in
            let df = compute_df cfg.cfg_in idoms bbs in
            SOME <| dominators := doms;
                   immediate_dominators := idoms;
                   dominated := dominated;
                   dominator_frontiers := df;
                   cfg_post_order := post_order;
                   cfg_post_walk := bbs |>
End

val _ = export_theory();
