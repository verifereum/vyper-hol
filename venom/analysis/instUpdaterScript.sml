(* 
 * Instruction Updater Utilities
 *
 * Port of venom/passes/machinery/inst_updater.py.
 *)

Theory instUpdater
Ancestors
  list
  orderedSet
  irOps dfgAnalysis compilerState

Datatype:
  inst_updater = <|
    iu_dfg : dfg_analysis;
    iu_fn : ir_function;
    iu_state : compiler_state
  |>
End

(* ===== List helpers ===== *)

Definition list_insert_at_def:
  list_insert_at 0 x xs = x :: xs /\
  list_insert_at (SUC n) x [] = [x] /\
  list_insert_at (SUC n) x (y::ys) = y :: list_insert_at n x ys
End

Definition list_remove_inst_def:
  list_remove_inst iid [] = [] /\
  list_remove_inst iid (inst::rest) =
    if inst.inst_id = iid then rest
    else inst :: list_remove_inst iid rest
End

Definition find_inst_index_aux_def:
  find_inst_index_aux iid [] (idx:num) = NONE /\
  find_inst_index_aux iid (inst::rest) idx =
    if inst.inst_id = iid then SOME idx
    else find_inst_index_aux iid rest (idx + 1)
End

Definition find_inst_index_def:
  find_inst_index iid insts = find_inst_index_aux iid insts 0
End

Definition insert_inst_in_blocks_def:
  insert_inst_in_blocks iid new_inst after [] = [] /\
  insert_inst_in_blocks iid new_inst after (bb::bbs) =
    case find_inst_index iid bb.bb_instructions of
      NONE => bb :: insert_inst_in_blocks iid new_inst after bbs
    | SOME idx =>
        let idx' = if after then idx + 1 else idx in
        let insts' = list_insert_at idx' new_inst bb.bb_instructions in
        (bb with bb_instructions := insts') :: bbs
End

Definition remove_inst_in_blocks_def:
  remove_inst_in_blocks iid [] = [] /\
  remove_inst_in_blocks iid (bb::bbs) =
    if MEM iid (MAP (λinst. inst.inst_id) bb.bb_instructions) then
      let insts' = list_remove_inst iid bb.bb_instructions in
      (bb with bb_instructions := insts') :: bbs
    else bb :: remove_inst_in_blocks iid bbs
End

(* ===== DFG helpers ===== *)

Definition dfg_remove_uses_def:
  dfg_remove_uses dfg inst_id ops =
    FOLDL
      (λacc op. case op of
                   Var v => dfg_remove_use acc v inst_id
                 | _ => acc)
      dfg ops
End

Definition dfg_add_uses_def:
  dfg_add_uses dfg inst_id ops =
    FOLDL
      (λacc op. case op of
                   Var v => dfg_add_use acc v inst_id
                 | _ => acc)
      dfg ops
End

Definition opcode_no_output_def:
  opcode_no_output op <=>
    op IN
    {MSTORE; SSTORE; ISTORE; TSTORE; DLOADBYTES; CALLDATACOPY; MCOPY;
     RETURNDATACOPY; CODECOPY; EXTCODECOPY; RETURN; RET; REVERT;
     ASSERT; ASSERT_UNREACHABLE; SELFDESTRUCT; STOP; INVALID; JMP; DJMP; JNZ; LOG; NOP}
End

(* ===== Update operations ===== *)

Definition inst_updater_update_def:
  inst_updater_update updater inst opcode new_operands new_output =
    let dfg1 = dfg_remove_uses updater.iu_dfg inst.inst_id inst.inst_operands in
    let dfg2 = dfg_add_uses dfg1 inst.inst_id new_operands in
    let old_outs = inst.inst_outputs in
    let (dfg3, outs') =
      if opcode_no_output opcode then
        (FOLDL (λacc v. dfg_remove_producing acc v) dfg2 old_outs, [])
      else
        case new_output of
          NONE => (dfg2, old_outs)
        | SOME v =>
            let dfg2' =
              FOLDL (λacc out. if out = v then acc else dfg_remove_producing acc out)
                    dfg2 old_outs in
            let dfg3' = dfg_set_producing dfg2' v inst.inst_id in
            (dfg3', [v]) in
    let inst' =
      inst with <| inst_opcode := opcode;
                   inst_operands := new_operands;
                   inst_outputs := outs' |> in
    let fn' = updater.iu_fn with fn_blocks :=
      update_inst_in_blocks inst.inst_id inst' updater.iu_fn.fn_blocks in
    updater with <| iu_dfg := dfg3; iu_fn := fn' |>
End

Definition replace_operands_list_def:
  replace_operands_list reps ops =
    MAP (λop. case ALOOKUP reps op of NONE => op | SOME v => v) ops
End

Definition inst_updater_update_operands_def:
  inst_updater_update_operands updater inst reps =
    let ops = replace_operands_list reps inst.inst_operands in
    inst_updater_update updater inst inst.inst_opcode ops NONE
End

Definition inst_updater_move_uses_def:
  inst_updater_move_uses updater old_var new_inst =
    case inst_output new_inst of
      NONE => updater
    | SOME new_var =>
        let uses = dfg_get_uses updater.iu_dfg old_var in
        FOLDL
          (λacc iid.
             case lookup_inst_in_function iid acc.iu_fn of
               NONE => acc
             | SOME use_inst =>
                 inst_updater_update_operands acc use_inst [(Var old_var, Var new_var)])
          updater uses
End

Definition inst_updater_replace_def:
  inst_updater_replace updater inst opcode ops new_output =
    inst_updater_update updater inst opcode ops new_output
End

Definition inst_updater_nop_def:
  inst_updater_nop updater inst =
    inst_updater_update updater inst NOP [] NONE
End

Definition inst_outputs_have_uses_def:
  inst_outputs_have_uses dfg outs =
    EXISTS (λv. dfg_get_uses dfg v <> []) outs
End

Definition inst_updater_nop_multi_aux_def:
  inst_updater_nop_multi_aux 0 updater inst_ids = updater /\
  inst_updater_nop_multi_aux (SUC fuel) updater inst_ids =
    case inst_ids of
      [] => updater
    | iid::rest =>
        case lookup_inst_in_function iid updater.iu_fn of
          NONE => inst_updater_nop_multi_aux fuel updater rest
        | SOME inst =>
            if inst_outputs_have_uses updater.iu_dfg inst.inst_outputs then
              inst_updater_nop_multi_aux fuel updater (rest ++ [iid])
            else
              inst_updater_nop_multi_aux fuel (inst_updater_nop updater inst) rest
End

Definition inst_updater_nop_multi_def:
  inst_updater_nop_multi updater inst_ids =
    let n = LENGTH inst_ids in
    let fuel = (2 + n) * (2 + n) in
    inst_updater_nop_multi_aux fuel updater inst_ids
End

Definition inst_updater_remove_def:
  inst_updater_remove updater inst =
    let updater' = inst_updater_nop updater inst in
    let fn' = updater'.iu_fn with fn_blocks :=
      remove_inst_in_blocks inst.inst_id updater'.iu_fn.fn_blocks in
    updater' with iu_fn := fn'
End

Definition inst_updater_mk_assign_def:
  inst_updater_mk_assign updater inst op new_output =
    inst_updater_update updater inst ASSIGN [op] new_output
End

(* ===== Insert operations ===== *)

Definition inst_updater_insert_def:
  inst_updater_insert updater inst opcode ops after =
    let (iid, st1) = fresh_inst_id updater.iu_state in
    let (out_opt, st2) =
      if opcode_no_output opcode then (NONE, st1)
      else
        let (v, st') = fresh_var st1 in
        (SOME v, st') in
    let outs = case out_opt of NONE => [] | SOME v => [v] in
    let new_inst = mk_inst iid opcode ops outs in
    let fn' = updater.iu_fn with fn_blocks :=
      insert_inst_in_blocks inst.inst_id new_inst after updater.iu_fn.fn_blocks in
    let dfg1 = dfg_add_uses updater.iu_dfg iid ops in
    let dfg2 =
      case out_opt of
        NONE => dfg1
      | SOME v => dfg_set_producing dfg1 v iid in
    let updater' =
      updater with <| iu_dfg := dfg2; iu_fn := fn'; iu_state := st2 |> in
    (updater', out_opt)
End

Definition inst_updater_add_before_def:
  inst_updater_add_before updater inst opcode ops =
    inst_updater_insert updater inst opcode ops F
End

Definition inst_updater_add_after_def:
  inst_updater_add_after updater inst opcode ops =
    inst_updater_insert updater inst opcode ops T
End

val _ = export_theory();
