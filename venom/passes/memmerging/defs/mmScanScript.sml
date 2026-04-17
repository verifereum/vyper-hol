(*
 * Memmerging — Block Scan (Analysis)
 *
 * Forward scan over a basic block that identifies copy groups.
 * Ports the core logic of _handle_bb and _handle_bb_memzero
 * from memmerging.py.
 *
 * Uses DFG analysis for:
 *   - Linking mstore values to their producing mload (dfg_get_def)
 *   - Checking if a load can be safely nop'd (dfg_get_uses)
 *
 * TOP-LEVEL:
 *   merge_mode             — which sub-pass we're running
 *   scan_state             — forward scan state
 *   scan_inst              — process one instruction
 *   scan_block             — process entire block
 *   scan_block_memzero     — memzero variant
 *   dload_peephole_block   — simple dload+mstore → dloadbytes
 *
 * Helper:
 *   flush_copies           — finalize pending copies into output
 *   invalidate_loads       — remove loads overlapping a write
 *   is_volatile_memory     — barrier-triggering instruction (write-effects check)
 *)

Theory mmScan
Ancestors
  mmCopy dfgDefs venomInst venomEffects finite_map

(* ===== Merge mode ===== *)

Datatype:
  merge_mode =
    Mem2Mem        (* mload → mcopy, allow_dst_overlaps_src = F *)
  | CalldataMerge  (* calldataload → calldatacopy, allow_dst_overlaps_src = T *)
  | DloadMerge     (* dload → dloadbytes, allow_dst_overlaps_src = T *)
End

Definition mode_allows_overlap_def:
  mode_allows_overlap Mem2Mem = F /\
  mode_allows_overlap CalldataMerge = T /\
  mode_allows_overlap DloadMerge = T
End

Definition mode_load_opcode_def:
  mode_load_opcode Mem2Mem = MLOAD /\
  mode_load_opcode CalldataMerge = CALLDATALOAD /\
  mode_load_opcode DloadMerge = DLOAD
End

Definition mode_copy_opcode_def:
  mode_copy_opcode Mem2Mem = MCOPY /\
  mode_copy_opcode CalldataMerge = CALLDATACOPY /\
  mode_copy_opcode DloadMerge = DLOADBYTES
End

(* ===== Volatile memory check ===== *)

(* Python: _volatile_memory (#4914) — checks STORAGE/TRANSIENT/MEMORY write effects *)
Definition is_volatile_memory_def:
  is_volatile_memory inst <=>
    Eff_STORAGE IN write_effects inst.inst_opcode \/
    Eff_TRANSIENT IN write_effects inst.inst_opcode \/
    Eff_MEMORY IN write_effects inst.inst_opcode
End

(* ===== Operand helpers ===== *)

Definition operand_lit_val_def:
  operand_lit_val (Lit w) = SOME (w2n w) /\
  operand_lit_val _ = NONE
End

Definition operand_var_name_def:
  operand_var_name (Var v) = SOME v /\
  operand_var_name _ = NONE
End

(* ===== Scan state ===== *)

Datatype:
  scan_state = <|
    ss_loads : (string, num) fmap;     (* var → src address *)
    ss_copies : copy_group list;       (* pending, sorted by dst *)
    ss_flushed : copy_group list       (* finalized groups *)
  |>
End

Definition empty_scan_state_def:
  empty_scan_state =
    <| ss_loads := FEMPTY;
       ss_copies := [];
       ss_flushed := [] |>
End

(* ===== Flush and invalidation ===== *)

Definition flush_copies_def:
  flush_copies ss to_flush =
    ss with <|
      ss_copies := FILTER (\cg. ~MEM cg to_flush) ss.ss_copies;
      ss_flushed := ss.ss_flushed ++ to_flush
    |>
End

Definition hard_barrier_def:
  hard_barrier ss =
    <| ss_loads := FEMPTY;
       ss_copies := [];
       ss_flushed := ss.ss_flushed ++ ss.ss_copies |>
End

(* Helper: does a load at ptr conflict with interval iv? *)
Definition load_conflicts_def:
  load_conflicts iv ptr = interval_overlaps (mk_interval ptr 32) iv
End

(* Remove loads whose range overlaps with a write interval.
   Uses DRESTRICT to keep only non-conflicting entries. *)
Definition invalidate_loads_def:
  invalidate_loads ss iv =
    ss with ss_loads :=
      DRESTRICT ss.ss_loads
        (FDOM ss.ss_loads DIFF
         { v | ?ptr. FLOOKUP ss.ss_loads v = SOME ptr /\
                     load_conflicts iv ptr })
End

(* ===== Hazard flush helper ===== *)

(* Flush hazardous copies, handling WAW + optional RAW/WAR.
   Returns updated scan state with hazards flushed. *)
Definition flush_hazards_def:
  flush_hazards mode ss new_cg =
    let waw = waw_hazards ss.ss_copies new_cg in
    let ss' = if waw <> [] then flush_copies ss waw else ss in
    if mode_allows_overlap mode then ss'
    else
      let raw = raw_hazards ss'.ss_copies new_cg in
      let ss'' = if raw <> [] then flush_copies ss' raw else ss' in
      let war = war_hazards ss''.ss_copies new_cg in
      if war <> [] then flush_copies ss'' war else ss''
End

(* ===== Per-instruction scan ===== *)

(* Process a load instruction.
   Python: the load_opcode branch in _handle_bb *)
Definition scan_load_def:
  scan_load mode ss inst =
    case inst.inst_operands of
      [src_op] =>
        (case operand_lit_val src_op of
           NONE => hard_barrier ss
         | SOME src_addr =>
             let ss' =
               if ~mode_allows_overlap mode then
                 let conflicts =
                   copies_that_overwrite ss.ss_copies
                     (mk_interval src_addr 32) in
                 if conflicts <> [] then flush_copies ss conflicts else ss
               else ss
             in
             case inst.inst_outputs of
               [out_var] =>
                 ss' with ss_loads := ss'.ss_loads |+ (out_var, src_addr)
             | _ => hard_barrier ss)
    | _ => hard_barrier ss
End

(* Process a store instruction (mstore).
   Our IR uses semantic order: MSTORE [addr; val].
   Python uses reversed EVM order: mstore [val, addr]. *)
Definition scan_store_def:
  scan_store dfg mode ss inst =
    case inst.inst_operands of
      [dst_op; val_op] =>
        (case (operand_var_name val_op, operand_lit_val dst_op) of
           (SOME var, SOME dst_addr) =>
             (case FLOOKUP ss.ss_loads var of
                NONE => hard_barrier ss
              | SOME src_addr =>
                  let ss' =
                    if ~mode_allows_overlap mode
                    then invalidate_loads ss (mk_interval dst_addr 32)
                    else ss
                  in
                  (* Track both the mstore and its producing load.
                     Python: _Copy(dst, src, 32, [inst, load_inst]) *)
                  let load_inst_id =
                    case dfg_get_def dfg var of
                      SOME li => [li.inst_id]
                    | NONE => [] in
                  let new_cg = <| cg_dst := dst_addr; cg_src := src_addr;
                                  cg_length := 32;
                                  cg_inst_ids :=
                                    [inst.inst_id] ++ load_inst_id |> in
                  let ss'' = flush_hazards mode ss' new_cg in
                  ss'' with ss_copies := add_copy ss''.ss_copies new_cg)
         | _ => hard_barrier ss)
    | _ => hard_barrier ss
End

(* Process a bulk copy instruction.
   Python: the copy_opcode branch in _handle_bb *)
Definition scan_bulk_copy_def:
  scan_bulk_copy mode ss inst =
    case inst.inst_operands of
      [dst_op; src_op; size_op] =>
        (case (operand_lit_val dst_op, operand_lit_val src_op,
               operand_lit_val size_op) of
           (SOME dst, SOME src, SOME len) =>
             let new_cg = <| cg_dst := dst; cg_src := src;
                             cg_length := len;
                             cg_inst_ids := [inst.inst_id] |> in
             let ss' =
               if ~mode_allows_overlap mode
               then invalidate_loads ss (mk_interval dst len)
               else ss
             in
             let ss'' = flush_hazards mode ss' new_cg in
             ss'' with ss_copies := add_copy ss''.ss_copies new_cg
         | _ => hard_barrier ss)
    | _ => hard_barrier ss
End

(* Process one instruction during the scan. *)
Definition scan_inst_def:
  scan_inst dfg mode ss inst =
    if inst.inst_opcode = mode_load_opcode mode then
      scan_load mode ss inst
    else if inst.inst_opcode = MSTORE then
      scan_store dfg mode ss inst
    else if inst.inst_opcode = mode_copy_opcode mode then
      scan_bulk_copy mode ss inst
    else if is_volatile_memory inst then
      hard_barrier ss
    else
      ss
End

(* Scan an entire block. Flushes all remaining copies at end. *)
Definition scan_block_def:
  scan_block dfg mode bb =
    let ss = FOLDL (scan_inst dfg mode) empty_scan_state bb.bb_instructions in
    hard_barrier ss
End

(* ===== Memzero scan ===== *)

Datatype:
  memzero_scan_state = <|
    mz_copies : copy_group list;
    mz_flushed : copy_group list
  |>
End

Definition empty_memzero_state_def:
  empty_memzero_state =
    <| mz_copies := []; mz_flushed := [] |>
End

Definition memzero_barrier_def:
  memzero_barrier mz =
    <| mz_copies := [];
       mz_flushed := mz.mz_flushed ++ mz.mz_copies |>
End

(* Is this a store of literal 0 to a literal address?
   Semantic order: MSTORE [addr; val]. *)
Definition is_zero_store_def:
  is_zero_store inst <=>
    inst.inst_opcode = MSTORE /\
    case inst.inst_operands of
      [dst_op; val_op] =>
        operand_lit_val val_op = SOME 0 /\ IS_SOME (operand_lit_val dst_op)
    | _ => F
End

(* Is this a calldatacopy from a calldatasize variable?
   In practice, the DFG tells us whether the src operand was produced
   by a calldatasize instruction. We take the DFG as parameter. *)
Definition is_calldatasize_copy_def:
  is_calldatasize_copy dfg inst <=>
    inst.inst_opcode = CALLDATACOPY /\
    case inst.inst_operands of
      [dst_op; src_op; size_op] =>
        IS_SOME (operand_lit_val dst_op) /\
        IS_SOME (operand_lit_val size_op) /\
        (case operand_var_name src_op of
           SOME v =>
             (case dfg_get_def dfg v of
                SOME src_inst => src_inst.inst_opcode = CALLDATASIZE
              | NONE => F)
         | NONE => F)
    | _ => F
End

Definition scan_inst_memzero_def:
  scan_inst_memzero dfg mz inst =
    if is_zero_store inst then
      (* Semantic order: MSTORE [addr; val] *)
      case inst.inst_operands of
        [dst_op; _] =>
          (case operand_lit_val dst_op of
             SOME dst =>
               let new_cg = copy_memzero dst 32 [inst.inst_id] in
               mz with mz_copies := add_copy mz.mz_copies new_cg
           | NONE => memzero_barrier mz)
      | _ => memzero_barrier mz
    else if is_calldatasize_copy dfg inst then
      case inst.inst_operands of
        [dst_op; _; size_op] =>
          (case (operand_lit_val dst_op, operand_lit_val size_op) of
             (SOME dst, SOME len) =>
               let new_cg = copy_memzero dst len [inst.inst_id] in
               mz with mz_copies := add_copy mz.mz_copies new_cg
           | _ => memzero_barrier mz)
      | _ => memzero_barrier mz
    else if is_volatile_memory inst then
      memzero_barrier mz
    else
      mz
End

Definition scan_block_memzero_def:
  scan_block_memzero dfg bb =
    let mz = FOLDL (scan_inst_memzero dfg) empty_memzero_state
                    bb.bb_instructions in
    memzero_barrier mz
End

(* ===== Dload+mstore peephole ===== *)

(* A dload→mstore pair identified by DFG.
   Python: _merge_mstore_dload uses self.dfg *)
Datatype:
  dload_pair = <|
    dp_dload_id : num;
    dp_mstore_id : num;
    dp_src : operand;
    dp_dst : operand
  |>
End

(* Check if a dload output has a single use that is an mstore.
   Python: uses = self.dfg.get_uses(dload_out); len(uses) == 1 *)
Definition find_dload_mstore_pair_def:
  find_dload_mstore_pair dfg inst =
    if inst.inst_opcode <> DLOAD then NONE
    else case (inst.inst_operands, inst.inst_outputs) of
      ([src_op], [out_var]) =>
        (case dfg_get_uses dfg out_var of
           [use_inst] =>
             if use_inst.inst_opcode = MSTORE then
               (* Semantic order: MSTORE [addr; val] *)
               case use_inst.inst_operands of
                 [dst_op; Var v] =>
                   if v = out_var then
                     SOME <| dp_dload_id := inst.inst_id;
                             dp_mstore_id := use_inst.inst_id;
                             dp_src := src_op;
                             dp_dst := dst_op |>
                   else NONE
               | _ => NONE
             else NONE
         | _ => NONE)
    | _ => NONE
End

(* Find all dload→mstore pairs in a block. *)
Definition find_dload_pairs_def:
  find_dload_pairs dfg insts =
    MAP THE (FILTER IS_SOME (MAP (find_dload_mstore_pair dfg) insts))
End

(* ===== Load nop safety ===== *)

(* Can a load instruction be safely nop'd?
   True when ALL uses of its output are within the given copy group.
   Python: not all(use in copy.insts for use in uses) → skip *)
Definition load_safe_to_nop_def:
  load_safe_to_nop dfg var group_inst_ids =
    EVERY (\use_inst. MEM use_inst.inst_id group_inst_ids)
          (dfg_get_uses dfg var)
End
