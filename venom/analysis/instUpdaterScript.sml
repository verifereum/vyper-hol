(*
 * Instruction Updater Utilities
 *
 * Lightweight updater-style mutation helpers for Venom passes.
 *)

Theory instUpdater
Ancestors
  list finite_map
  dfgAnalysis

Datatype:
  inst_updater = <|
    iu_dfg : dfg_analysis;
    iu_fn : ir_function;
    iu_next_id : num
  |>
End

(* ==========================================================================
   List / block helpers
   ========================================================================== *)

Definition list_insert_at_def:
  list_insert_at 0 x xs = x::xs /\
  list_insert_at (SUC n) x [] = [x] /\
  list_insert_at (SUC n) x (y::ys) = y :: list_insert_at n x ys
End

Definition find_inst_index_aux_def:
  find_inst_index_aux iid [] (idx:num) = NONE /\
  find_inst_index_aux iid (inst::rest) (idx:num) =
    if inst.inst_id = iid then SOME idx
    else find_inst_index_aux iid rest (idx + 1)
End

Definition find_inst_index_def:
  find_inst_index iid insts = find_inst_index_aux iid insts (0:num)
End

Definition update_inst_in_blocks_def:
  update_inst_in_blocks iid inst' [] = [] /\
  update_inst_in_blocks iid inst' (bb::bbs) =
    if MEM iid (MAP (λinst. inst.inst_id) bb.bb_instructions) then
      let insts' =
        MAP (λinst. if inst.inst_id = iid then inst' else inst) bb.bb_instructions in
      (bb with bb_instructions := insts') :: bbs
    else
      bb :: update_inst_in_blocks iid inst' bbs
End

Definition insert_before_in_blocks_def:
  insert_before_in_blocks iid new_inst [] = [] /\
  insert_before_in_blocks iid new_inst (bb::bbs) =
    case find_inst_index iid bb.bb_instructions of
      NONE => bb :: insert_before_in_blocks iid new_inst bbs
    | SOME idx =>
        let insts' = list_insert_at idx new_inst bb.bb_instructions in
          (bb with bb_instructions := insts') :: bbs
End

Definition lookup_inst_in_function_aux_def:
  lookup_inst_in_function_aux iid [] = NONE /\
  lookup_inst_in_function_aux iid (inst::rest) =
    if inst.inst_id = iid then SOME inst
    else lookup_inst_in_function_aux iid rest
End

Definition lookup_inst_in_function_def:
  lookup_inst_in_function iid fn =
    lookup_inst_in_function_aux iid (fn_insts fn)
End

(* ==========================================================================
   DFG updates
   ========================================================================== *)

Definition dfg_remove_uses_def:
  dfg_remove_uses dfg inst_id ops =
    FOLDL
      (λacc op.
         case op of
           Var v => dfg_remove_use acc v inst_id
         | _ => acc)
      dfg ops
End

Definition dfg_add_uses_def:
  dfg_add_uses dfg inst ops =
    FOLDL
      (λacc op.
         case op of
           Var v => dfg_add_use acc v inst
         | _ => acc)
      dfg ops
End

Definition opcode_has_output_def:
  opcode_has_output op <=>
    ~(op IN {JMP; JNZ; DJMP; RET; RETURN; REVERT; STOP; SINK;
             MSTORE; SSTORE; TSTORE; ISTORE;
             CALLDATACOPY; MCOPY; RETURNDATACOPY; CODECOPY; EXTCODECOPY;
             ASSERT; ASSERT_UNREACHABLE; SELFDESTRUCT; INVALID; LOG; NOP})
End

(* ==========================================================================
   Updater operations
   ========================================================================== *)

Definition max_inst_id_insts_def:
  max_inst_id_insts [] = 0 /\
  max_inst_id_insts (inst::rest) =
    MAX inst.inst_id (max_inst_id_insts rest)
End

Definition inst_updater_init_def:
  inst_updater_init fn =
    let insts = fn_insts fn in
    <| iu_dfg := dfg_build_insts insts;
       iu_fn := fn;
       iu_next_id := SUC (max_inst_id_insts insts) |>
End

Definition inst_updater_update_def:
  inst_updater_update updater inst opcode new_operands =
    let inst' =
      inst with <| inst_opcode := opcode; inst_operands := new_operands |> in
    let dfg1 = dfg_remove_uses updater.iu_dfg inst.inst_id inst.inst_operands in
    let dfg2 = dfg_add_uses dfg1 inst' new_operands in
    let dfg3 =
      FOLDL (λacc v. dfg_set_def acc v inst') dfg2 inst'.inst_outputs in
    let dfg4 = dfg_set_inst_by_id dfg3 inst' in
    let fn' =
      updater.iu_fn with fn_blocks :=
        update_inst_in_blocks inst.inst_id inst' updater.iu_fn.fn_blocks in
      updater with <| iu_dfg := dfg4; iu_fn := fn' |>
End

Definition replace_operands_list_def:
  replace_operands_list reps ops =
    MAP (λop. case ALOOKUP reps op of NONE => op | SOME op' => op') ops
End

Definition inst_updater_update_operands_def:
  inst_updater_update_operands updater inst reps =
    let ops' = replace_operands_list reps inst.inst_operands in
      inst_updater_update updater inst inst.inst_opcode ops'
End

Definition inst_updater_mk_assign_def:
  inst_updater_mk_assign updater inst op =
    inst_updater_update updater inst ASSIGN [op]
End

Definition updater_fresh_var_def:
  updater_fresh_var (id:num) = STRCAT "iu_tmp_" (toString id)
End

Definition inst_updater_add_before_def:
  inst_updater_add_before updater inst opcode ops =
    let iid = updater.iu_next_id in
    let out_opt =
      if opcode_has_output opcode then SOME (updater_fresh_var iid)
      else NONE in
    let outs = case out_opt of NONE => [] | SOME v => [v] in
    let new_inst = mk_inst iid opcode ops outs in
    let fn' =
      updater.iu_fn with fn_blocks :=
        insert_before_in_blocks inst.inst_id new_inst updater.iu_fn.fn_blocks in
    let dfg1 = dfg_add_uses updater.iu_dfg new_inst ops in
    let dfg2 =
      FOLDL (λacc v. dfg_set_def acc v new_inst) dfg1 outs in
    let dfg3 = dfg_set_inst_by_id dfg2 new_inst in
    let updater' =
      updater with <| iu_dfg := dfg3; iu_fn := fn'; iu_next_id := SUC iid |> in
      (updater', out_opt)
End

val _ = export_theory();
