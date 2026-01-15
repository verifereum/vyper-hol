(*
 * Liveness Analysis
 *
 * Port of venom/analysis/liveness.py.
 *)

Theory livenessAnalysis
Ancestors
  list finite_map
  orderedSet
  cfgAnalysis irOps

Datatype:
  liveness_analysis = <|
    out_vars : (string, string list) fmap;
    inst_liveness : (num, string list) fmap
  |>
End

Definition liveness_live_vars_at_def:
  liveness_live_vars_at live inst_id =
    case FLOOKUP live.inst_liveness inst_id of NONE => [] | SOME v => v
End

Definition liveness_out_vars_def:
  liveness_out_vars live bb_lbl =
    case FLOOKUP live.out_vars bb_lbl of NONE => [] | SOME v => v
End

Definition init_out_vars_def:
  init_out_vars bbs =
    FOLDL (λm bb. m |+ (bb.bb_label, [])) FEMPTY bbs
End

Definition init_inst_liveness_def:
  init_inst_liveness bbs =
    FOLDL
      (λm bb.
         FOLDL (λm2 inst. m2 |+ (inst.inst_id, [])) m bb.bb_instructions)
      FEMPTY bbs
End

Definition input_vars_from_def:
  input_vars_from inst_liveness source_lbl target_bb =
    case target_bb.bb_instructions of
      [] => []
    | inst0::_ =>
        let live0 = fmap_lookup_ordset inst_liveness inst0.inst_id in
        let live = live0 in
        FOLDL
          (λacc inst.
             if inst.inst_opcode = PHI then
               if MEM (Label source_lbl) inst.inst_operands then
                 FOLDL
                   (λacc2 (lbl,v).
                      if lbl = source_lbl then ordset_add v acc2
                      else ordset_remove v acc2)
                   acc (phi_operands inst.inst_operands)
               else acc
             else acc)
          live target_bb.bb_instructions
End

Definition liveness_input_vars_from_def:
  liveness_input_vars_from live bbs origin_lbl target_lbl =
    case lookup_block target_lbl bbs of
      NONE => []
    | SOME target_bb => input_vars_from live.inst_liveness origin_lbl target_bb
End

Definition calculate_out_vars_def:
  calculate_out_vars cfg inst_liveness bbs bb out_vars =
    let old = fmap_lookup_ordset out_vars bb.bb_label in
    let new =
      FOLDL
        (λacc succ_lbl.
           let target =
             case lookup_block succ_lbl bbs of
               NONE => []
             | SOME target_bb => input_vars_from inst_liveness bb.bb_label target_bb in
           ordset_union acc target)
        [] (fmap_lookup_ordset cfg.cfg_out bb.bb_label) in
    let out_vars' = out_vars |+ (bb.bb_label, new) in
    (out_vars', old <> new)
End

Definition calculate_liveness_def:
  calculate_liveness inst_liveness out_vars bb =
    case bb.bb_instructions of
      [] => (inst_liveness, F)
    | inst0::_ =>
        let orig = fmap_lookup_ordset inst_liveness inst0.inst_id in
        let live0 = fmap_lookup_ordset out_vars bb.bb_label in
        let (inst_live, _) =
          FOLDL
            (λ(acc:(num, string list) fmap # string list) inst.
               let (m, live) = acc in
               let ins = inst_input_vars inst in
               let outs = inst_get_outputs inst in
               let live' =
                 if ins = [] /\ outs = [] then live
                 else ordset_union (ordset_remove_many live outs) ins in
               (m |+ (inst.inst_id, live'), live'))
            (inst_liveness, live0) (REVERSE bb.bb_instructions) in
        let new0 = fmap_lookup_ordset inst_live inst0.inst_id in
        (inst_live, orig <> new0)
End

Definition liveness_iter_def:
  liveness_iter cfg bbs inst_liveness out_vars work fuel =
    case fuel of
      0 => (inst_liveness, out_vars)
    | SUC fuel' =>
        case work of
          [] => (inst_liveness, out_vars)
        | bb::rest =>
            let (out_vars', changed1) =
              calculate_out_vars cfg inst_liveness bbs bb out_vars in
            let (inst_liveness', changed2) =
              calculate_liveness inst_liveness out_vars' bb in
            let changed = (changed1 \/ changed2) in
            let work' =
              if changed then
                rest ++
                (MAP (λlbl. THE (lookup_block lbl bbs))
                  (fmap_lookup_ordset cfg.cfg_in bb.bb_label))
              else rest in
            liveness_iter cfg bbs inst_liveness' out_vars' work' fuel'
End

Definition liveness_analyze_def:
  liveness_analyze fn cfg =
    let bbs = fn.fn_blocks in
    let out0 = init_out_vars bbs in
    let inst0 = init_inst_liveness bbs in
    let fuel = (LENGTH bbs) * (LENGTH bbs) + 1 in
    let work0 = MAP (\lbl. THE (lookup_block lbl bbs)) cfg.dfs_post in
    let (inst_live, out_vars) = liveness_iter cfg bbs inst0 out0 work0 fuel in
    <| out_vars := out_vars; inst_liveness := inst_live |>
End

val _ = export_theory();
