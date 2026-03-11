(*
 * Memmerging — Block/Function Transform
 *
 * Applies scan results to transform a basic block.
 * For each copy group:
 *   - Last instruction (by block position) becomes the bulk copy
 *   - Earlier instructions become NOPs (if safe per DFG use analysis)
 * For memzero groups:
 *   - 32-byte → mstore(0, dst)
 *   - Larger → calldatacopy(len, calldatasize, dst)
 * For dload pairs:
 *   - dload+mstore → dloadbytes(32, src, dst), dload → NOP
 *
 * TOP-LEVEL:
 *   transform_block          — apply all sub-passes sequentially
 *   transform_function       — apply to all blocks in a function
 *)

Theory mmTransform
Ancestors
  mmScan passSimulationDefs

(* ===== Instruction builders ===== *)

Definition mk_nop_from_def:
  mk_nop_from inst =
    inst with <| inst_opcode := NOP;
                 inst_operands := [];
                 inst_outputs := [] |>
End

(* Build bulk copy: operand order [dst, src, size] matches our semantics. *)
Definition mk_bulk_copy_inst_def:
  mk_bulk_copy_inst mode inst cg =
    inst with <| inst_opcode := mode_copy_opcode mode;
                 inst_operands :=
                   [Lit (n2w cg.cg_dst);
                    Lit (n2w cg.cg_src);
                    Lit (n2w cg.cg_length)];
                 inst_outputs := [] |>
End

(* Semantic order: MSTORE [addr; val] *)
Definition mk_zero_store_inst_def:
  mk_zero_store_inst inst dst =
    inst with <| inst_opcode := MSTORE;
                 inst_operands := [Lit (n2w dst); Lit 0w];
                 inst_outputs := [] |>
End

Definition mk_dloadbytes_inst_def:
  mk_dloadbytes_inst inst src dst =
    inst with <| inst_opcode := DLOADBYTES;
                 inst_operands := [dst; src; Lit 32w];
                 inst_outputs := [] |>
End

(* ===== Copy group ID extraction ===== *)

(* Sort instruction IDs by their position in the block.
   Python: copy.insts.sort(key=bb.instructions.index) *)
Definition sort_ids_by_block_def:
  sort_ids_by_block block_insts ids =
    let id_order = MAP (\inst. inst.inst_id) block_insts in
    FILTER (\id. MEM id ids) id_order
End

(* Pin ID: load feeding the representative mstore when the rep is kept
   (32-byte, not DloadMerge). Python: pin_inst logic in _flush_copies.
   When the representative is a kept mstore, its value-producing load
   must NOT be nop'd even if all uses are "within group". *)
Definition rep_pin_id_def:
  rep_pin_id dfg mode rep_id cg =
    if cg.cg_length = 32 /\ mode <> DloadMerge then
      case dfg_get_inst_by_id dfg rep_id of
        SOME rep_inst =>
          (* Semantic order: MSTORE [addr; val] — val is operand [1] *)
          (case rep_inst.inst_operands of
            [_; Var v] =>
              (case dfg_get_def dfg v of
                 SOME load_inst => SOME load_inst.inst_id
               | NONE => NONE)
          | _ => NONE)
      | NONE => NONE
    else NONE
End

(* IDs to NOP: all but last (by block position) in each group.
   Loads are only nop'd if safe (all uses within group) AND not pinned.
   Python: copy.insts[:-1] filtering in _flush_copies.
   MUST use sort_ids_by_block to match rep_of_group's ordering. *)
Definition nop_ids_of_group_def:
  nop_ids_of_group dfg mode block_insts cg =
    let sorted = sort_ids_by_block block_insts cg.cg_inst_ids in
    case REVERSE sorted of
      [] => []
    | rep_id :: earlier =>
        let pin = rep_pin_id dfg mode rep_id cg in
        FILTER (\id.
          (* Pinned loads must not be nop'd *)
          pin <> SOME id /\
          (case dfg_get_inst_by_id dfg id of
            SOME inst =>
              if inst.inst_opcode IN {MLOAD; CALLDATALOAD; DLOAD} then
                (* Load: only nop if all uses are within group *)
                case inst.inst_outputs of
                  [out_var] => load_safe_to_nop dfg out_var cg.cg_inst_ids
                | _ => T
              else T  (* Non-load (store): always nop *)
          | NONE => T))
        (REVERSE earlier)
End

Definition nop_ids_of_groups_def:
  nop_ids_of_groups dfg mode block_insts groups =
    FLAT (MAP (nop_ids_of_group dfg mode block_insts) groups)
End

(* Representative ID for each group: the LAST by block position.
   Python: inst = copy.insts[-1] after sorting by bb.instructions.index *)
Definition rep_of_group_def:
  rep_of_group block_insts cg =
    let sorted = sort_ids_by_block block_insts cg.cg_inst_ids in
    case REVERSE sorted of
      [] => NONE
    | last_id :: _ => SOME (last_id, cg)
End

Definition rep_map_of_groups_def:
  rep_map_of_groups block_insts groups =
    MAP THE (FILTER IS_SOME (MAP (rep_of_group block_insts) groups))
End

(* ===== Apply transform to instruction list ===== *)

(* Build an mload instruction reading from an address.
   Used when downsizing a 32-byte copy to mload+mstore (smaller bytecode).
   Python: val = self.updater.add_before(inst, load_opcode, [IRLiteral(copy.src)])
   We reuse the inst_id for the load since the original instruction is replaced. *)
Definition mk_load_inst_def:
  mk_load_inst mode inst src_addr out_var =
    inst with <| inst_opcode := mode_load_opcode mode;
                 inst_operands := [Lit (n2w src_addr)];
                 inst_outputs := [out_var] |>
End

(* Build mstore using the loaded value.
   Semantic order: MSTORE [addr; val]. *)
Definition mk_mstore_from_load_def:
  mk_mstore_from_load inst dst_addr load_var =
    inst with <| inst_opcode := MSTORE;
                 inst_operands := [Lit (n2w dst_addr); Var load_var];
                 inst_outputs := [] |>
End

(* Transform one instruction for a merge mode.
   Returns a LIST to allow inserting mload before mstore when
   downsizing a 32-byte copy (Python: updater.add_before).
   Python: _flush_copies logic applied per-instruction *)
Definition apply_groups_inst_def:
  apply_groups_inst mode nop_set rep_map inst =
    if MEM inst.inst_id nop_set then
      [mk_nop_from inst]
    else
      case ALOOKUP rep_map inst.inst_id of
        SOME cg =>
          if cg.cg_length <> 32 then
            [mk_bulk_copy_inst mode inst cg]
          else if mode = DloadMerge then
            [mk_bulk_copy_inst mode inst cg]
          else if inst.inst_opcode = MSTORE then
            [inst]  (* 32-byte mstore: keep original mload+mstore *)
          else
            (* 32-byte non-mstore (e.g. mcopy): downsize to mload+mstore.
               Python: val = add_before(inst, load_opcode, [src]);
                       update(inst, "mstore", [val, dst])
               Uses a fresh variable name derived from inst_id. *)
            let load_var = STRCAT "__mm_load_" (num_to_dec_string inst.inst_id) in
            [mk_load_inst mode inst cg.cg_src load_var;
             mk_mstore_from_load inst cg.cg_dst load_var]
      | NONE => [inst]
End

(* ===== Block-level transforms ===== *)

Definition transform_block_mode_def:
  transform_block_mode dfg mode bb =
    let scan_result = scan_block dfg mode bb in
    let groups = scan_result.ss_flushed in
    let nop_set = nop_ids_of_groups dfg mode bb.bb_instructions groups in
    let rep_map = rep_map_of_groups bb.bb_instructions groups in
    bb with bb_instructions :=
      FLAT (MAP (apply_groups_inst mode nop_set rep_map) bb.bb_instructions)
End

(* Memzero transform.
   Python: _optimize_memzero *)
(* Fresh variable name for calldatasize output in memzero.
   Uses the inst_id to generate a unique name. *)
Definition fresh_calldatasize_var_def:
  fresh_calldatasize_var (id:num) = STRCAT "__mz_cds_" (num_to_dec_string id)
End

(* Build a calldatasize instruction producing a fresh variable. *)
Definition mk_calldatasize_inst_def:
  mk_calldatasize_inst inst_id =
    <| inst_id := inst_id;
       inst_opcode := CALLDATASIZE;
       inst_operands := [];
       inst_outputs := [fresh_calldatasize_var inst_id] |>
End

(* Build a calldatacopy that uses the calldatasize variable as src offset.
   Operand order: CALLDATACOPY [dst_offset; src_offset; size] *)
Definition mk_memzero_calldatacopy_def:
  mk_memzero_calldatacopy inst cg cds_var =
    inst with <| inst_opcode := CALLDATACOPY;
                 inst_operands :=
                   [Lit (n2w cg.cg_dst);
                    Var cds_var;
                    Lit (n2w cg.cg_length)];
                 inst_outputs := [] |>
End

(* Per-instruction transform for memzero. Returns a LIST to allow
   inserting calldatasize instruction before calldatacopy. *)
Definition apply_memzero_inst_def:
  apply_memzero_inst nop_set rep_map inst =
    if MEM inst.inst_id nop_set then
      [mk_nop_from inst]
    else
      case ALOOKUP rep_map inst.inst_id of
        SOME cg =>
          if cg.cg_length = 32 then
            [mk_zero_store_inst inst cg.cg_dst]
          else
            (* Larger: insert calldatasize instruction, then calldatacopy.
               Python: calldatasize = self.updater.add_before(inst, ...) *)
            let cds_id = inst.inst_id in
            let cds_var = fresh_calldatasize_var cds_id in
            [mk_calldatasize_inst cds_id;
             mk_memzero_calldatacopy inst cg cds_var]
      | NONE => [inst]
End

Definition transform_block_memzero_def:
  transform_block_memzero dfg bb =
    let scan_result = scan_block_memzero dfg bb in
    let groups = scan_result.mz_flushed in
    (* Mem2Mem as dummy mode: memzero groups have no loads, so pin
       logic in nop_ids_of_group never fires regardless of mode. *)
    let nop_set = nop_ids_of_groups dfg Mem2Mem bb.bb_instructions groups in
    let rep_map = rep_map_of_groups bb.bb_instructions groups in
    bb with bb_instructions :=
      FLAT (MAP (apply_memzero_inst nop_set rep_map) bb.bb_instructions)
End

(* Dload peephole transform.
   Python: _merge_mstore_dload *)
Definition transform_block_dload_def:
  transform_block_dload dfg bb =
    let pairs = find_dload_pairs dfg bb.bb_instructions in
    let dload_nops = MAP (\dp. dp.dp_dload_id) pairs in
    let mstore_map = MAP (\dp. (dp.dp_mstore_id, dp)) pairs in
    bb with bb_instructions :=
      MAP (\inst.
        if MEM inst.inst_id dload_nops then
          mk_nop_from inst
        else
          case ALOOKUP mstore_map inst.inst_id of
            SOME dp => mk_dloadbytes_inst inst dp.dp_src dp.dp_dst
          | NONE => inst)
      bb.bb_instructions
End

(* ===== Full transform: all sub-passes composed ===== *)

(* Apply all memmerging sub-passes to a block.
   Python: MemMergePass.run_pass *)
Definition transform_block_def:
  transform_block dfg bb =
    let bb1 = transform_block_dload dfg bb in
    let bb2 = transform_block_memzero dfg bb1 in
    let bb3 = transform_block_mode dfg CalldataMerge bb2 in
    let bb4 = transform_block_mode dfg DloadMerge bb3 in
    transform_block_mode dfg Mem2Mem bb4
End

(* ===== Function-level transform ===== *)

Definition transform_function_def:
  transform_function fn =
    let dfg = dfg_build_function fn in
    function_map_transform (transform_block dfg) fn
End
