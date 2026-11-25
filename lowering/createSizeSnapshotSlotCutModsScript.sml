(* Slot snapshot cuts shared by the storage and transient-storage cases. *)
Theory createSizeSnapshotSlotCutMods
Ancestors
  createSizeByteLength createSizeSlotHeader createSizeSlotTraversal
  exprSimCopy exprLowering exprLoweringProps compileEnv context emitHelper
  emitHelperProps loweringHalt loweringPosts loweringStateRelDefs fragExec
  abiBufferAllocationCode bufferAllocationExecution copyExecution slotCopyExecution
  fragGasOrigin ssaOperandFrame stmtReasonMemory instMemFrontier venomState
  venomInst venomExecSemantics vfmTypes words list rich_list arithmetic
  finite_map relation

Theorem create_snapshot_slot_compile_cut:
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

Theorem create_snapshot_slot_alloc_cut:
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

Theorem create_snapshot_slot_mload_cut:
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
