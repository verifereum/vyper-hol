(* Header at the actual load cut of a raw CREATE snapshot. *)
Theory createSizeSnapshotLengthMods
Ancestors
  createSizeSnapshotLength createExprSizeExitDefsMods
  createSizeByteLength createSizeImmutableLengthMods createSizeSlotHeader
  createSizeSlotTraversal exprSimCopy exprLowering exprLoweringProps compileEnv context emitHelper
  emitHelperProps loweringHalt loweringPosts loweringStateRelDefs fragExec
  abiBufferAllocationCode bufferAllocationExecution copyExecution slotCopyExecution fragGasOrigin
  ssaOperandFrame stmtReasonMemory instMemFrontier venomState venomInst
  venomExecSemantics vfmTypes words list rich_list arithmetic finite_map relation

Theorem snapshot_slot_length_mods[local]:
  vv_location vv = SOME (slot_loc tr) /\
  vv_holds_mods ce cx (BaseT (BytesT (Dynamic k))) tv vv ee s /\
  read_result cx tv ee = (INL (BytesV bytes),ee) /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) =
    SOME (BaseTV (BytesT (Dynamic k))) /\
  copy_old_operand sa (vv_operand vv) /\
  compile_create_snapshot ce vv ty sa = (snap,sb) /\
  emit_op MLOAD [snap] sb = (len,sc) /\
  compile_alloc_buffer (type_memory_bytes ce ty) sa = (buf,sm) /\
  0 < (type_memory_bytes ce ty + 31) DIV 32 /\
  w2n (n2w (buffer_allocation_base s sa.cs_next_id) : bytes32) +
    32 * ((type_memory_bytes ce ty + 31) DIV 32) < dimword (:256) /\
  fn_has_code sm sb func /\
  lookup_block sb.cs_current_bb func.fn_blocks = SOME exit /\
  phi_prefix_length exit.bb_instructions = 0 /\
  u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts /\
  z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = 0 /\
  run_inst_seq (emitted_insts sa sm) s = OK (u with vs_inst_idx := s.vs_inst_idx) /\
  RTC (\v w. (v.vs_current_bb <> sb.cs_current_bb \/ v.vs_inst_idx <> 0) /\
             ?ms. gas_origin_edge F explicit ctx func v ms (OK w)) u z /\
  run_inst_seq (emitted_insts sb sc) z = OK (t with vs_inst_idx := z.vs_inst_idx) ==>
  eval_operand len t = SOME (n2w (LENGTH bytes))
Proof
  cheat
QED

Theorem create_snapshot_length_word_mods:
  vv_post_mods H ctx func ce cx e es start sa s0 ee tv vv s /\
  post_value_type ce e = BaseT (BytesT (Dynamic k)) /\
  read_result cx tv ee = (INL (BytesV bytes),ee) /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) =
    SOME (BaseTV (BytesT (Dynamic k))) /\
  copy_old_operand sa (vv_operand vv) /\
  compile_create_snapshot ce vv ty sa = (snap,sb) /\
  emit_op MLOAD [snap] sb = (len,sc) /\
  ((vv_location vv = NONE \/ vv_location vv = SOME LocMemory) ==>
    LENGTH bytes + 32 < dimword (:256)) /\
  (vv_location vv = SOME LocCode ==>
    local_ptrs_reserved ce sa /\
    (ce.ce_is_ctor ==> !a. eval_operand (vv_operand vv) s = SOME a ==>
      val_in_memory (BaseTV (BytesT (Dynamic k))) (BytesV bytes) (w2n a) s.vs_memory) /\
    w2n (n2w (buffer_allocation_base s sa.cs_next_id) : bytes32) +
      32 * ((type_memory_bytes ce (vv_type vv) + 31) DIV 32) < dimword (:256)) /\
  ((vv_location vv = NONE \/ vv_location vv = SOME LocMemory \/
    vv_location vv = SOME LocCode) ==>
    run_inst_seq (emitted_insts sa sc) s = OK (t with vs_inst_idx := s.vs_inst_idx)) /\
  ((!tr. vv_location vv = SOME (slot_loc tr) ==>
    ?buf sm u z exit.
      compile_alloc_buffer (type_memory_bytes ce ty) sa = (buf,sm) /\
      32 <= type_memory_bytes ce ty /\
      w2n (n2w (buffer_allocation_base s sa.cs_next_id) : bytes32) +
        32 * ((type_memory_bytes ce ty + 31) DIV 32) < dimword (:256) /\
      fn_has_code sm sb func /\
      lookup_block sb.cs_current_bb func.fn_blocks = SOME exit /\
      phi_prefix_length exit.bb_instructions = 0 /\
      u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts /\
      z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = 0 /\
      run_inst_seq (emitted_insts sa sm) s = OK (u with vs_inst_idx := s.vs_inst_idx) /\
      RTC (\v w. (v.vs_current_bb <> sb.cs_current_bb \/ v.vs_inst_idx <> 0) /\
                 ?ms. gas_origin_edge F explicit ctx func v ms (OK w)) u z /\
      run_inst_seq (emitted_insts sb sc) z = OK (t with vs_inst_idx := z.vs_inst_idx))) ==>
  eval_operand len t = SOME (n2w (LENGTH bytes))
Proof
  cheat
QED
