(* Header at the actual load cut of a raw CREATE snapshot. *)
Theory createSizeSnapshotLengthMods
Ancestors
  createSizeSnapshotLength createExprSizeExitDefsMods
  createSizeByteLength createSizeImmutableLengthMods createSizeSlotHeader
  createSizeSnapshotSlotCutMods createSizeSlotTraversal exprSimCopy exprLowering exprLoweringProps compileEnv context emitHelper
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
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `?a. eval_operand (vv_operand vv) s = SOME a /\
       storage_holds cx tr (BaseT (BytesT (Dynamic k))) tv a ee s` by
    (Cases_on `vv` >> Cases_on `tr` >>
     gvs[bodyFullPostsModsTheory.vv_holds_mods_def,
         vv_holds_def, vv_location_def, vv_operand_def, slot_loc_def]) >>
  drule_all create_slot_source_length_word >> strip_tac >>
  drule_all create_snapshot_slot_compile_cut >> strip_tac >>
  qabbrev_tac `n = (type_memory_bytes ce ty + 31) DIV 32` >>
  qabbrev_tac `load = if tr then TLOAD else SLOAD` >>
  qabbrev_tac `b = (n2w (buffer_allocation_base s sa.cs_next_id) : bytes32)` >>
  `load = SLOAD \/ load = TLOAD` by (Cases_on `tr` >> simp[Abbr `load`]) >>
  `n < 2**256 /\ w2n b + 32*n < 2**256` by fs[dimword_def] >>
  `0 < LENGTH sm.cs_current_insts` by
    (drule compile_alloc_buffer_code >> simp[]) >>
  `sb.cs_current_bb = slot_copy_exit sm` by simp[slot_copy_final_def] >>
  `slot_copy_external sm (vv_operand vv) /\ slot_copy_external sm buf.buf_operand /\
   eval_operand (vv_operand vv) u = SOME a /\ eval_operand buf.buf_operand u = SOME b /\
   slot_copy_word load u a = n2w (LENGTH bytes)` by
    (drule_all create_snapshot_slot_alloc_cut >> simp[Abbr `b`]) >>
  `slot_copy_inv sm load u a b n [] n z /\ eval_operand buf.buf_operand z = SOME b` by
    (qpat_x_assum `sb = _` SUBST_ALL_TAC >>
     qpat_x_assum `_.cs_current_bb = slot_copy_exit sm`
       (fn th => rule_assum_tac (REWRITE_RULE [th])) >>
     irule create_slot_copy_actual_exit >> simp[] >>
     qexistsl_tac [`ctx`, `exit`, `explicit`, `func`, `vv_operand vv`] >> fs[]) >>
  fs[slot_copy_inv_def] >> drule_all create_snapshot_slot_mload_cut >> simp[]
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
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `stmt_state_rel H ctx func ce cx ee s /\ immutable_frame_mods func ce cx ee s /\
   vv_holds_mods ce cx (BaseT (BytesT (Dynamic k))) tv vv ee s` by
    fs[bodyFullPostsModsTheory.vv_post_mods_def] >>
  qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  Cases_on `vv_location vv = NONE \/ vv_location vv = SOME LocMemory`
  >- (`expr_val_rel cx (BaseT (BytesT (Dynamic k))) (BytesV bytes) (vv_operand vv) s` by
        (Cases_on `vv` >>
         gvs[bodyFullPostsModsTheory.vv_holds_mods_def, vv_holds_def,
             vv_location_def, vv_operand_def, expr_val_rel_def, is_word_type_def]) >>
      `run_inst_seq (emitted_insts sa sc) s = OK (t with vs_inst_idx := s.vs_inst_idx)` by
        (first_x_assum irule >> metis_tac[]) >>
      `LENGTH bytes + 32 < dimword (:256)` by (first_x_assum irule >> first_assum ACCEPT_TAC) >>
      drule_all (REWRITE_RULE [GSYM copy_old_operand_def] create_snapshot_memory_length_word) >>
      simp[]) >>
  Cases_on `vv_location vv = SOME LocCode`
  >- (`run_inst_seq (emitted_insts sa sc) s = OK (t with vs_inst_idx := s.vs_inst_idx)` by
        (first_x_assum irule >> simp[]) >>
      qpat_assum `vv_location vv = SOME LocCode ==> _` (drule_then strip_assume_tac) >>
      drule_all create_snapshot_code_length_word_mods >> simp[]) >>
  `?tr. vv_location vv = SOME (slot_loc tr)` by
    (Cases_on `vv` >>
     gvs[vv_location_def, bodyFullPostsModsTheory.vv_holds_mods_def, vv_holds_def] >>
     rename1 `p.ptr_location <> LocCode` >> Cases_on `p.ptr_location` >>
     gvs[slot_loc_def] >> metis_tac[]) >>
  first_x_assum drule >> strip_tac >>
  `0 < (type_memory_bytes ce ty + 31) DIV 32` by
    (irule bitTheory.DIV_GT0 >> decide_tac) >>
  drule_all snapshot_slot_length_mods >> simp[]
QED
