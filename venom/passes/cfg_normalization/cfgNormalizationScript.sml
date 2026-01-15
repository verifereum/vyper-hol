(*
 * CFG Normalization Pass
 *
 * Port of venom/passes/cfg_normalization.py.
 *)

Theory cfgNormalization
Ancestors
  list
  irOps
  cfgAnalysis
  compilerState

Definition needs_forwarding_store_def:
  needs_forwarding_store v pred_bb =
    case FIND (λinst. MEM v inst.inst_outputs) pred_bb.bb_instructions of
      NONE => T
    | SOME inst => inst.inst_opcode = PHI
End

Definition phi_replace_operands_def:
  phi_replace_operands old_lbl new_lbl var_reps [] = [] /\
phi_replace_operands old_lbl new_lbl var_reps (Label l :: Var v :: rest) =
    (let l' = if l = old_lbl then new_lbl else l in
     let v' =
       if l = old_lbl then
         case ALOOKUP var_reps v of NONE => v | SOME v2 => v2
       else v in
     Label l' :: Var v' :: phi_replace_operands old_lbl new_lbl var_reps rest) /\
  phi_replace_operands old_lbl new_lbl var_reps (op1::op2::rest) =
    op1 :: op2 :: phi_replace_operands old_lbl new_lbl var_reps rest /\
  phi_replace_operands old_lbl new_lbl var_reps ops = ops
End

Definition update_phi_block_def:
  update_phi_block old_lbl new_lbl var_reps bb =
    bb with bb_instructions :=
      MAP
        (λinst.
           if inst.inst_opcode = PHI then
             inst with inst_operands :=
               phi_replace_operands old_lbl new_lbl var_reps inst.inst_operands
           else inst)
        bb.bb_instructions
End

Definition compute_forwarding_def:
  compute_forwarding fn pred_bb bb st =
    let phis = bb_phi_instructions bb in
    FOLDL
      (λacc inst.
         let (assigns, reps, st_acc) = acc in
         let pairs = phi_operands inst.inst_operands in
         FOLDL
           (λacc2 (lbl,v).
              let (as2, reps2, st2) = acc2 in
              if lbl <> pred_bb.bb_label then acc2
              else if MEM v (MAP FST reps2) then acc2
              else if needs_forwarding_store v pred_bb then
                let (new_v, st3) = fresh_var st2 in
                let (iid, st4) = fresh_inst_id st3 in
                let assign_inst = mk_inst iid ASSIGN [Var v] [new_v] in
                (as2 ++ [assign_inst], reps2 ++ [(v, new_v)], st4)
              else acc2)
           (assigns, reps, st_acc) pairs)
      ([], [], st) phis
End

Definition replace_block_def:
  replace_block lbl new_bb bbs =
    MAP (λbb. if bb.bb_label = lbl then new_bb else bb) bbs
End

Definition cfg_normalize_insert_split_def:
  cfg_normalize_insert_split fn st bb_lbl pred_lbl =
    case (lookup_block bb_lbl fn.fn_blocks, lookup_block pred_lbl fn.fn_blocks) of
      (SOME bb, SOME pred_bb) =>
        if pred_bb.bb_instructions = [] then (fn, st, F) else
          let split_lbl = STRCAT pred_bb.bb_label (STRCAT "_split_" bb.bb_label) in
          let term = LAST pred_bb.bb_instructions in
          let term' = replace_label_operands [(bb.bb_label, split_lbl)] term in
          let fn1 = update_inst_in_function term.inst_id term' fn in
          let (assigns, reps, st1) = compute_forwarding fn1 pred_bb bb st in
          let (jmp_id, st2) = fresh_inst_id st1 in
          let jmp_inst = mk_inst jmp_id JMP [Label bb.bb_label] [] in
          let split_bb =
            <| bb_label := split_lbl; bb_instructions := assigns ++ [jmp_inst] |> in
          let bb' = update_phi_block pred_bb.bb_label split_lbl reps bb in
          let fn2 = fn1 with fn_blocks := replace_block bb.bb_label bb' fn1.fn_blocks in
          let fn3 = fn2 with fn_blocks := fn2.fn_blocks ++ [split_bb] in
          (fn3, st2, T)
    | _ => (fn, st, F)
End

Definition cfg_normalize_process_block_def:
  cfg_normalize_process_block fn st cfg bb_lbl preds =
    case preds of
      [] => (fn, st, F)
    | pred_lbl::rest =>
        let succs = fmap_lookup_ordset cfg.cfg_out pred_lbl in
        if LENGTH succs > 1 then
          cfg_normalize_insert_split fn st bb_lbl pred_lbl
        else
          cfg_normalize_process_block fn st cfg bb_lbl rest
End

Definition cfg_normalize_run_def:
  cfg_normalize_run fn st =
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    FOLDL
      (λacc bb.
         let (fn_acc, st_acc, changes) = acc in
         let preds = fmap_lookup_ordset cfg.cfg_in bb.bb_label in
         if LENGTH preds > 1 then
           let (fn1, st1, ch) =
             cfg_normalize_process_block fn_acc st_acc cfg bb.bb_label preds in
           (fn1, st1, changes + (if ch then 1 else 0))
         else (fn_acc, st_acc, changes))
      (fn, st, 0) bbs
End

Definition cfg_normalize_iter_def:
  cfg_normalize_iter 0 fn st = fn /\
  cfg_normalize_iter (SUC fuel) fn st =
    let (fn1, st1, changes) = cfg_normalize_run fn st in
    if changes = 0 then fn1 else cfg_normalize_iter fuel fn1 st1
End

Definition cfg_normalize_function_def:
  cfg_normalize_function fn =
    let st = init_state_for_function fn in
    let fuel = LENGTH fn.fn_blocks * 2 in
    cfg_normalize_iter fuel fn st
End

Definition cfg_normalize_context_def:
  cfg_normalize_context ctx =
    ctx with ctx_functions := MAP cfg_normalize_function ctx.ctx_functions
End

val _ = export_theory();
