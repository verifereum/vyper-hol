(*
 * Variable Definition Analysis
 *
 * Port of venom/analysis/var_definition.py.
 *)

Theory varDefinitionAnalysis
Ancestors
  list finite_map
  orderedSet
  cfgAnalysis irOps

Datatype:
  var_definition_analysis = <|
    defined_vars : (num, string list) fmap;
    defined_vars_bb : (string, string list) fmap
  |>
End

Definition all_variables_def:
  all_variables fn =
    FOLDL
      (λacc bb.
         FOLDL (λacc2 inst. ordset_union acc2 (inst_get_outputs inst)) acc bb.bb_instructions)
      [] fn.fn_blocks
End

Definition init_defined_vars_bb_def:
  init_defined_vars_bb bbs all_vars =
    FOLDL (λm bb. m |+ (bb.bb_label, all_vars)) FEMPTY bbs
End

Definition handle_bb_def:
  handle_bb cfg bb def_bb def_inst =
    let preds = fmap_lookup_ordset cfg.cfg_in bb.bb_label in
    let input_defined = MAP (\lbl. fmap_lookup_ordset def_bb lbl) preds in
    let bb_defined =
      if input_defined = [] then []
      else ordset_inter_list input_defined in
    let (def_inst', bb_defined') =
      FOLDL
        (λacc inst.
           let (m, live) = acc in
           let m' = m |+ (inst.inst_id, live) in
           let live' = ordset_union live (inst_get_outputs inst) in
           (m', live'))
        (def_inst, bb_defined) bb.bb_instructions in
    let old = fmap_lookup_ordset def_bb bb.bb_label in
    let def_bb' = def_bb |+ (bb.bb_label, bb_defined') in
    (def_bb', def_inst', old <> bb_defined')
End

Definition blocks_from_labels_def:
  blocks_from_labels bbs lbls =
    MAP (\lbl. THE (lookup_block lbl bbs)) lbls
End

Definition var_def_iter_def:
  var_def_iter cfg bbs def_bb def_inst work fuel =
    case fuel of
      0 => (def_bb, def_inst)
    | SUC fuel' =>
        (case ordset_pop work of
           NONE => (def_bb, def_inst)
         | SOME (bb, rest) =>
             let (def_bb', def_inst', changed) = handle_bb cfg bb def_bb def_inst in
             let succs = fmap_lookup_ordset cfg.cfg_out bb.bb_label in
             let work' =
               if changed then ordset_union rest (blocks_from_labels bbs succs)
               else rest in
             var_def_iter cfg bbs def_bb' def_inst' work' fuel')
End

Definition var_definition_analyze_def:
  var_definition_analyze fn cfg =
    let bbs = fn.fn_blocks in
    let all_vars = all_variables fn in
    let def_bb0 = init_defined_vars_bb bbs all_vars in
    let def_inst0 = FEMPTY in
    let fuel = (LENGTH bbs) * (LENGTH bbs) + 1 in
    let (def_bb, def_inst) = var_def_iter cfg bbs def_bb0 def_inst0 bbs fuel in
    <| defined_vars := def_inst; defined_vars_bb := def_bb |>
End

val _ = export_theory();
