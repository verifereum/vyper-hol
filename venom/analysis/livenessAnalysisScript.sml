(*
 * Liveness Analysis
 *
 * Backward dataflow analysis over Venom IR basic blocks.
 * This is the reusable analysis counterpart to Vyper's LivenessAnalysis.
 *)

Theory livenessAnalysis
Ancestors
  list finite_map
  venomInst dfgAnalysis

(* ==========================================================================
   Small ordered-set helpers (list-backed)
   ========================================================================== *)

Definition ordset_add_def:
  ordset_add x xs = if MEM x xs then xs else x::xs
End

Definition ordset_union_def:
  ordset_union xs ys = FOLDL (λacc x. ordset_add x acc) xs ys
End

Definition ordset_remove_def:
  ordset_remove x xs = FILTER (λy. y <> x) xs
End

Definition ordset_remove_many_def:
  ordset_remove_many xs ys = FOLDL (λacc x. ordset_remove x acc) xs ys
End

Definition fmap_lookup_ordset_def:
  fmap_lookup_ordset m k =
    case FLOOKUP m k of
      NONE => []
    | SOME v => v
End

(* ==========================================================================
   Result type and query API
   ========================================================================== *)

Datatype:
  liveness_analysis = <|
    out_vars : (string, string list) fmap;
    inst_liveness : (num, string list) fmap
  |>
End

Definition liveness_live_vars_at_def:
  liveness_live_vars_at live inst_id =
    fmap_lookup_ordset live.inst_liveness inst_id
End

Definition liveness_out_vars_def:
  liveness_out_vars live bb_lbl =
    fmap_lookup_ordset live.out_vars bb_lbl
End

(* ==========================================================================
   CFG helpers from IR blocks
   ========================================================================== *)

Definition bb_succs_def:
  bb_succs bb =
    case REVERSE bb.bb_instructions of
      [] => []
    | inst::_ => get_successors inst
End

Definition bb_preds_def:
  bb_preds bbs lbl =
    FOLDL
      (λacc bb.
         if MEM lbl (bb_succs bb) then ordset_add bb.bb_label acc else acc)
      [] bbs
End

(* ==========================================================================
   Phi edge-sensitive transfer
   ========================================================================== *)

Definition phi_operands_def:
  phi_operands [] = [] /\
  phi_operands [_] = [] /\
  phi_operands (Label lbl :: Var v :: rest) =
    (lbl, v) :: phi_operands rest /\
  phi_operands (_ :: _ :: rest) = phi_operands rest
End

Definition apply_phi_edge_uses_def:
  apply_phi_edge_uses source_lbl live pairs =
    case pairs of
      [] => live
    | (lbl, v)::rest =>
        let live1 =
          if lbl = source_lbl then ordset_add v live
          else ordset_remove v live
        in
          apply_phi_edge_uses source_lbl live1 rest
End

Definition input_vars_from_def:
  input_vars_from inst_liveness source_lbl target_bb =
    case target_bb.bb_instructions of
      [] => []
    | inst0::_ =>
        let live0 = fmap_lookup_ordset inst_liveness inst0.inst_id in
        FOLDL
          (λacc inst.
             if inst.inst_opcode = PHI then
               apply_phi_edge_uses source_lbl acc (phi_operands inst.inst_operands)
             else acc)
          live0 target_bb.bb_instructions
End

Definition liveness_input_vars_from_def:
  liveness_input_vars_from live bbs origin_lbl target_lbl =
    case lookup_block target_lbl bbs of
      NONE => []
    | SOME target_bb =>
        input_vars_from live.inst_liveness origin_lbl target_bb
End

(* ==========================================================================
   Per-block transfer
   ========================================================================== *)

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

Definition calculate_out_vars_def:
  calculate_out_vars bbs inst_liveness bb out_vars =
    let old = fmap_lookup_ordset out_vars bb.bb_label in
    let new =
      FOLDL
        (λacc succ_lbl.
           case lookup_block succ_lbl bbs of
             NONE => acc
           | SOME target_bb =>
               ordset_union acc
                 (input_vars_from inst_liveness bb.bb_label target_bb))
        [] (bb_succs bb)
    in
      let out_vars' = out_vars |+ (bb.bb_label, new) in
        (out_vars', old <> new)
End

Definition calculate_liveness_def:
  calculate_liveness inst_liveness out_vars bb =
    case bb.bb_instructions of
      [] => (inst_liveness, F)
    | inst0::_ =>
        let old0 = fmap_lookup_ordset inst_liveness inst0.inst_id in
        let live0 = fmap_lookup_ordset out_vars bb.bb_label in
        let (inst_liveness', _) =
          FOLDL
            (λ(acc:(num, string list) fmap # string list) inst.
               let (m, live) = acc in
               let ins = operand_vars inst.inst_operands in
               let outs = inst.inst_outputs in
               let live' = ordset_union (ordset_remove_many live outs) ins in
               (m |+ (inst.inst_id, live'), live'))
            (inst_liveness, live0) (REVERSE bb.bb_instructions)
        in
          let new0 = fmap_lookup_ordset inst_liveness' inst0.inst_id in
            (inst_liveness', old0 <> new0)
End

(* ==========================================================================
   Worklist fixpoint
   ========================================================================== *)

Definition liveness_iter_def:
  liveness_iter bbs inst_liveness out_vars work fuel =
    case fuel of
      0 => (inst_liveness, out_vars)
    | SUC fuel' =>
        case work of
          [] => (inst_liveness, out_vars)
        | lbl::rest =>
            (case lookup_block lbl bbs of
               NONE => liveness_iter bbs inst_liveness out_vars rest fuel'
             | SOME bb =>
                 let (out_vars', changed1) =
                   calculate_out_vars bbs inst_liveness bb out_vars in
                 let (inst_liveness', changed2) =
                   calculate_liveness inst_liveness out_vars' bb in
                 let work' =
                   if changed1 \/ changed2 then
                     ordset_union rest (bb_preds bbs bb.bb_label)
                   else rest
                 in
                   liveness_iter bbs inst_liveness' out_vars' work' fuel')
End

Definition liveness_analyze_def:
  liveness_analyze fn =
    let bbs = fn.fn_blocks in
    let out0 = init_out_vars bbs in
    let inst0 = init_inst_liveness bbs in
    let work0 = MAP (λbb. bb.bb_label) (REVERSE bbs) in
    let fuel =
      (LENGTH bbs) * (LENGTH (fn_insts fn) + 1) + 1 in
    let (inst_live, out_live) =
      liveness_iter bbs inst0 out0 work0 fuel in
      <| out_vars := out_live; inst_liveness := inst_live |>
End

val _ = export_theory();

