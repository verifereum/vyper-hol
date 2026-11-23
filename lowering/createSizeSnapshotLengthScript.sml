(* Header at the actual load cut of a raw CREATE snapshot. *)
Theory createSizeSnapshotLength
Ancestors
  createSizeByteLength createSizeImmutableLength createSizeSlotHeader
  createSizeSlotTraversal exprSimCopy exprLowering exprLoweringProps compileEnv context emitHelper
  emitHelperProps loweringHalt loweringPosts loweringStateRelDefs fragExec
  abiBufferAllocationCode bufferAllocationExecution copyExecution slotCopyExecution fragGasOrigin
  ssaOperandFrame stmtReasonMemory instMemFrontier venomState venomInst
  venomExecSemantics vfmTypes words list rich_list arithmetic finite_map relation

Theorem snapshot_slot_compile[local]:
  vv_location vv = SOME (slot_loc tr) /\
  compile_alloc_buffer (type_memory_bytes ce ty) sa = (buf,sm) /\
  compile_create_snapshot ce vv ty sa = (snap,sb) ==>
  snap = buf.buf_operand /\
  sb = slot_copy_final sm (vv_operand vv) buf.buf_operand
    ((type_memory_bytes ce ty + 31) DIV 32) (if tr then TLOAD else SLOAD)
Proof
  rpt strip_tac >> Cases_on `tr` >>
  gvs[compile_create_snapshot_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, slot_loc_def, compile_slot_to_memory_shape] >>
  gvs[AllCaseEqs()]
QED

Theorem snapshot_slot_alloc[local]:
  compile_alloc_buffer m sa = (buf,sm) /\
  copy_old_operand sa src /\ eval_operand src s = SOME a /\
  run_inst_seq (emitted_insts sa sm) s = OK (u with vs_inst_idx := s.vs_inst_idx) ==>
  slot_copy_external sm src /\ slot_copy_external sm buf.buf_operand /\
  eval_operand src u = SOME a /\
  eval_operand buf.buf_operand u = SOME (n2w (buffer_allocation_base s sa.cs_next_id)) /\
  slot_copy_word load u a = slot_copy_word load s a
Proof
  strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  drule bufferAllocationExecutionTheory.compile_alloc_buffer_execution >>
  disch_then (qspec_then `s` strip_assume_tac) >> gvs[] >>
  `src <> Var (STRING #"%" (toString sa.cs_next_var))` by
    (fs[copy_old_operand_def, not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  `slot_copy_external sm src` by
    (rw[slot_copy_external_def, slot_copy_var_def] >>
     fs[copy_old_operand_def, not_fresh_at_def] >> strip_tac >>
     first_x_assum drule >> simp[]) >>
  `slot_copy_external sm (Var (STRING #"%" (toString sa.cs_next_var)))` by
    simp[slot_copy_external_def, slot_copy_var_def] >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >>
  fs[venom_state_component_equality, update_var_def, buffer_allocation_fields_def] >>
  Cases_on `load = SLOAD` >>
  fs[slot_copy_word_def, sload_def, tload_def, contract_storage_def, contract_transient_def] >>
  qpat_x_assum `_ |+ _ = u.vs_vars` (assume_tac o SYM) >>
  Cases_on `src` >> fs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem snapshot_slot_mload[local]:
  0 < n /\ slot_copy_prefix load u a (w2n b) n z /\
  eval_operand snap z = SOME b /\ emit_op MLOAD [snap] sb = (len,sc) /\
  run_inst_seq (emitted_insts sb sc) z = OK (t with vs_inst_idx := z.vs_inst_idx) ==>
  eval_operand len t = SOME (slot_copy_word load u a)
Proof
  strip_tac >>
  `mload (w2n b) z = slot_copy_word load u a` by
    (fs[slot_copy_prefix_def] >> first_x_assum (qspec_then `0` mp_tac) >>
     simp[] >> strip_tac >>
     `32 <= LENGTH (DROP (w2n b) z.vs_memory)` by fs[] >>
     simp[mload_def, listTheory.TAKE_APPEND1, WORD_ADD_0]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  gvs[run_inst_seq_def, step_mload_eq] >>
  `eval_operand (Var (STRING #"%" (toString sb.cs_next_var)))
     (t with vs_inst_idx := z.vs_inst_idx) = SOME (slot_copy_word load u a)`
    suffices_by simp[] >>
  qpat_x_assum `update_var _ _ _ = t with vs_inst_idx := _`
    (fn th => rewrite_tac [GSYM th]) >>
  simp[eval_operand_def, lookup_var_update_var]
QED

Theorem snapshot_slot_length[local]:
  vv_location vv = SOME (slot_loc tr) /\
  vv_holds ce cx (BaseT (BytesT (Dynamic k))) tv vv ee s /\
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
     gvs[vv_holds_def, vv_location_def, vv_operand_def, slot_loc_def]) >>
  drule_all create_slot_source_length_word >> strip_tac >>
  drule_all snapshot_slot_compile >> strip_tac >>
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
    (drule_all snapshot_slot_alloc >> simp[Abbr `b`]) >>
  `slot_copy_inv sm load u a b n [] n z /\ eval_operand buf.buf_operand z = SOME b` by
    (qpat_x_assum `sb = _` SUBST_ALL_TAC >>
     qpat_x_assum `_.cs_current_bb = slot_copy_exit sm`
       (fn th => rule_assum_tac (REWRITE_RULE [th])) >>
     irule create_slot_copy_actual_exit >> simp[] >>
     qexistsl_tac [`ctx`, `exit`, `explicit`, `func`, `vv_operand vv`] >> fs[]) >>
  fs[slot_copy_inv_def] >> drule_all snapshot_slot_mload >> simp[]
QED

Theorem create_snapshot_length_word:
  vv_post H ctx func ce cx e es start sa s0 ee tv vv s /\
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
  `stmt_state_rel H ctx func ce cx ee s /\
   vv_holds ce cx (BaseT (BytesT (Dynamic k))) tv vv ee s` by fs[vv_post_def] >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  Cases_on `vv_location vv = NONE \/ vv_location vv = SOME LocMemory`
  >- (`expr_val_rel cx (BaseT (BytesT (Dynamic k))) (BytesV bytes) (vv_operand vv) s` by
       (Cases_on `vv` >>
        gvs[vv_holds_def, vv_location_def, vv_operand_def, expr_val_rel_def, is_word_type_def]) >>
      `run_inst_seq (emitted_insts sa sc) s = OK (t with vs_inst_idx := s.vs_inst_idx)` by
        (first_x_assum irule >> metis_tac[]) >>
      `LENGTH bytes + 32 < dimword (:256)` by (first_x_assum irule >> first_assum ACCEPT_TAC) >>
      drule_all (REWRITE_RULE [GSYM copy_old_operand_def] create_snapshot_memory_length_word) >>
      simp[]) >>
  Cases_on `vv_location vv = SOME LocCode`
  >- (`run_inst_seq (emitted_insts sa sc) s = OK (t with vs_inst_idx := s.vs_inst_idx)` by
        (first_x_assum irule >> simp[]) >>
      qpat_assum `vv_location vv = SOME LocCode ==> _` (drule_then strip_assume_tac) >>
      drule_all create_snapshot_code_length_word >> simp[]) >>
  `?tr. vv_location vv = SOME (slot_loc tr)` by
    (Cases_on `vv` >> gvs[vv_location_def,vv_holds_def] >>
     rename1 `p.ptr_location <> LocCode` >> Cases_on `p.ptr_location` >>
     gvs[slot_loc_def] >> metis_tac[]) >>
  first_x_assum drule >> strip_tac >>
  `0 < (type_memory_bytes ce ty + 31) DIV 32` by
    (irule bitTheory.DIV_GT0 >> decide_tac) >>
  drule_all snapshot_slot_length >> simp[]
QED
