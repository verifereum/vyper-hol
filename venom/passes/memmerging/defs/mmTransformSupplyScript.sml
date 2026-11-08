(*
 * Memmerging — Supply-threaded Transform
 *
 * TOP-LEVEL:
 *   transform_function_supply — transform_function, taking the inserted
 *                               instructions' ids and output vars from an
 *                               ir_supply
 *)

Theory mmTransformSupply
Ancestors
  mmTransform irSupply

(* Python's InstUpdater.add_before creates a new instruction with a fresh
   variable (fn.get_next_variable()). The *_supply variants below take the
   inserted instruction's id and output from an ir_supply instead of
   deriving both from the rewritten instruction's id; the rewritten
   instruction keeps its own id. Otherwise they match the defs in mmTransform. *)

(* Thread a supply through a per-instruction transform, concatenating. *)
Definition mm_flat_map_supply_def:
  mm_flat_map_supply f s [] = ([], s) /\
  mm_flat_map_supply f s (inst::insts) =
    case f s inst of
      (out, s1) =>
        case mm_flat_map_supply f s1 insts of
          (outs, s2) => (out ++ outs, s2)
End

Definition apply_groups_inst_supply_def:
  apply_groups_inst_supply mode nop_set rep_map s inst =
    if MEM inst.inst_id nop_set then
      ([mk_nop_from inst], s)
    else
      case ALOOKUP rep_map inst.inst_id of
        SOME cg =>
          if cg.cg_length <> 32 then
            ([mk_bulk_copy_inst mode inst cg], s)
          else if mode = DloadMerge then
            ([mk_bulk_copy_inst mode inst cg], s)
          else if inst.inst_opcode = MSTORE then
            ([inst], s)
          else
            (case fresh_inst_id s of
               (load_id, s1) =>
                 case fresh_ir_var s1 of
                   (load_var, s2) =>
                     ([mk_load_inst mode (inst with inst_id := load_id)
                         cg.cg_src load_var;
                       mk_mstore_from_load inst cg.cg_dst load_var], s2))
      | NONE => ([inst], s)
End

Definition transform_block_mode_supply_def:
  transform_block_mode_supply dfg mode s bb =
    let groups = (scan_block dfg mode bb).ss_flushed in
    let nop_set = nop_ids_of_groups dfg mode bb.bb_instructions groups in
    let rep_map = rep_map_of_groups bb.bb_instructions groups in
    case mm_flat_map_supply (apply_groups_inst_supply mode nop_set rep_map)
           s bb.bb_instructions of
      (insts, s') => (bb with bb_instructions := insts, s')
End

Definition apply_memzero_inst_supply_def:
  apply_memzero_inst_supply nop_set rep_map s inst =
    if MEM inst.inst_id nop_set then
      ([mk_nop_from inst], s)
    else
      case ALOOKUP rep_map inst.inst_id of
        SOME cg =>
          if cg.cg_length = 32 then
            ([mk_zero_store_inst inst cg.cg_dst], s)
          else
            (case fresh_inst_id s of
               (cds_id, s1) =>
                 case fresh_ir_var s1 of
                   (cds_var, s2) =>
                     ([<| inst_id := cds_id;
                          inst_opcode := CALLDATASIZE;
                          inst_operands := [];
                          inst_outputs := [cds_var] |>;
                       mk_memzero_calldatacopy inst cg cds_var], s2))
      | NONE => ([inst], s)
End

Definition transform_block_memzero_supply_def:
  transform_block_memzero_supply dfg s bb =
    let groups = (scan_block_memzero dfg bb).mz_flushed in
    let nop_set = nop_ids_of_groups dfg Mem2Mem bb.bb_instructions groups in
    let rep_map = rep_map_of_groups bb.bb_instructions groups in
    case mm_flat_map_supply (apply_memzero_inst_supply nop_set rep_map)
           s bb.bb_instructions of
      (insts, s') => (bb with bb_instructions := insts, s')
End

Definition transform_block_supply_def:
  transform_block_supply dfg s bb =
    case transform_block_memzero_supply dfg s bb of
      (bb2, s1) =>
        case transform_block_mode_supply dfg CalldataMerge s1 bb2 of
          (bb3, s2) =>
            case transform_block_mode_supply dfg DloadMerge s2 bb3 of
              (bb4, s3) => transform_block_mode_supply dfg Mem2Mem s3 bb4
End

Definition transform_function_supply_def:
  transform_function_supply s fn =
    transform_function_with transform_block_supply s fn
End
