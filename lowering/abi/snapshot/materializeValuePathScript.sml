(* TOP-LEVEL: materialization executes a typed allocation and copy while
   preserving external state, disjoint values and older operand names.
   Helpers describe the exact runtime state for both copy strategies. *)
Theory materializeValuePath
Ancestors
  memorySnapshotFrame bytesSnapshotProps bytesSnapshotCode bytesSnapshotExec
  memoryValueSnapshot memoryValueDefs memoryValueTyping valueLoadProps
  abiStateFrame abiAllocationFrame abiAllocatedWindows abiBufferAllocationPath
  abiFieldOperands abiStaticLoopCode abiBytestringCode eventTopicValueProps
  compileEnv context exprLoweringProps fragExec fragBlockPath instIdxIndep
  ssaOperandFrame venomState venomExecSemantics finite_map list words arithmetic

Definition materialized_state_def:
  materialized_state ty id var_base capacity src_addr ss =
    if is_bytestring_type ty then bytes_snapshot_result id var_base capacity src_addr ss
    else memory_snapshot_result id var_base capacity src_addr ss
End

Theorem materialized_state_frames:
  !tenv ty tv v id var_base src_addr ss.
    evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
    memory_value_rel tv v (w2n src_addr) ss.vs_memory /\ type_memory_size tv < dimword(:256) ==>
    abi_state_frame ss (materialized_state ty id var_base (type_memory_size tv) src_addr ss) /\
    array_copy_frame tv 1 (w2n (memory_snapshot_addr id ss)) ss.vs_memory
      (materialized_state ty id var_base (type_memory_size tv) src_addr ss).vs_memory /\
    (materialized_state ty id var_base (type_memory_size tv) src_addr ss).vs_allocas =
      (memory_snapshot_alloc_frame id (type_memory_size tv) ss).vs_allocas /\
    (materialized_state ty id var_base (type_memory_size tv) src_addr ss).vs_alloca_next =
      (memory_snapshot_alloc_frame id (type_memory_size tv) ss).vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >> Cases_on `is_bytestring_type ty`
  >- (drule_all bytes_snapshot_result_copy_frame >> DISCH_TAC >>
      simp[materialized_state_def, bytes_snapshot_result_allocator]) >>
  simp[materialized_state_def, memory_snapshot_result_copy_frame, memory_snapshot_result_allocator]
QED

Theorem materialized_state_fresh:
  !ty id cs cs' capacity src_addr ss.
    fresh_vars_wrt cs ss /\
    cs.cs_next_var + (if is_bytestring_type ty then 5 else 1) <= cs'.cs_next_var ==>
    fresh_vars_wrt cs' (materialized_state ty id cs.cs_next_var capacity src_addr ss)
Proof
  rpt gen_tac >> strip_tac >>
  rw[materialized_state_def, bytes_snapshot_result_def, memory_snapshot_result_def,
    compiler_var_names_EL, LET_THM, fresh_vars_wrt_def, memory_snapshot_allocated_def,
    memory_snapshot_alloc_frame_def, update_var_def, mcopy_vars] >>
  fs[fresh_vars_wrt_def] >> first_x_assum irule >> decide_tac
QED

Theorem compile_materialize_value_vars:
  !cenv ty src cs op cs'.
    ~is_word_type ty /\ compile_materialize_vv cenv ty (StackValue ty src) cs = (op,cs') ==>
    cs'.cs_next_var = cs.cs_next_var + (if is_bytestring_type ty then 5 else 1) /\
    abi_operand_before cs'.cs_next_var op
Proof
  rpt gen_tac >> strip_tac >> Cases_on `is_bytestring_type ty`
  >- (drule_all compile_materialize_bytes_code >> strip_tac >>
      simp[compiler_var_names_EL, abi_operand_before_def, compiler_var_name_def]) >>
  drule_all compile_materialize_aggregate_code >> strip_tac >>
  simp[abi_operand_before_def, compiler_var_name_def]
QED

Theorem materialized_allocation_resources:
  !id capacity before after.
    after.vs_allocas = (memory_snapshot_alloc_frame id capacity before).vs_allocas /\
    after.vs_alloca_next = (memory_snapshot_alloc_frame id capacity before).vs_alloca_next /\
    alloca_inv before /\ abi_alloca_request_ok id capacity before /\
    before.vs_alloca_next + capacity < dimword(:256) ==>
    alloca_inv after /\
    abi_allocated_window after id (w2n (memory_snapshot_addr id before)) capacity /\
    before.vs_alloca_next <= after.vs_alloca_next /\
    after.vs_alloca_next <= before.vs_alloca_next + capacity
Proof
  rpt gen_tac >> strip_tac >> `capacity < dimword(:256)` by decide_tac >>
  mp_tac (Q.SPECL [`id`, `capacity`, `before`] abi_allocation_frame_inv) >>
  impl_tac >- simp[] >> DISCH_TAC >>
  `alloca_inv after` by
    (irule abi_allocation_fields_inv >>
     qexists_tac `memory_snapshot_alloc_frame id capacity before` >> simp[]) >>
  mp_tac (Q.SPECL [`id`, `capacity`, `before`] abi_allocation_frame_next) >> strip_tac >>
  drule_all abi_allocation_frame_record >> strip_tac >>
  rename1 `FLOOKUP (memory_snapshot_alloc_frame id capacity before).vs_allocas id = SOME (offset,recorded_size)` >>
  asm_simp_tac bool_ss [] >>
  asm_simp_tac bool_ss [abi_allocated_window_def] >>
  qexistsl_tac [`offset`, `recorded_size`] >> simp[]
QED

Theorem compile_materialize_value_path:
  !tenv ctx func cenv ty tv v src cs op cs' ss src_addr.
    evaluate_type tenv ty = SOME tv /\ ~is_word_type ty /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    compile_materialize_vv cenv ty (StackValue ty src) cs = (op,cs') /\
    type_memory_size tv < dimword(:256) /\
    lowered_value_rel ty tv v src ss /\ eval_operand src ss = SOME src_addr /\
    EVERY (\name. src <> Var name)
      (compiler_var_names cs.cs_next_var (if is_bytestring_type ty then 5 else 1)) /\
    fn_has_code cs cs' func /\ ss.vs_current_bb = cs.cs_current_bb /\
    ss.vs_inst_idx = LENGTH cs.cs_current_insts ==>
    ?out. fragment_path ctx func ss out /\
      out = (materialized_state ty cs.cs_next_id cs.cs_next_var (type_memory_size tv) src_addr ss
        with vs_inst_idx := LENGTH cs'.cs_current_insts) /\
      out.vs_current_bb = cs'.cs_current_bb /\ out.vs_inst_idx = LENGTH cs'.cs_current_insts /\
      out.vs_halted = ss.vs_halted /\ lowered_value_rel ty tv v op out /\
      eval_operand op out = SOME (memory_snapshot_addr cs.cs_next_id ss) /\
      abi_state_frame ss out /\
      array_copy_frame tv 1 (w2n (memory_snapshot_addr cs.cs_next_id ss)) ss.vs_memory out.vs_memory /\
      out.vs_allocas = (memory_snapshot_alloc_frame cs.cs_next_id (type_memory_size tv) ss).vs_allocas /\
      out.vs_alloca_next = (memory_snapshot_alloc_frame cs.cs_next_id (type_memory_size tv) ss).vs_alloca_next /\
      (!arg_op. EVERY (\name. arg_op <> Var name)
        (compiler_var_names cs.cs_next_var (if is_bytestring_type ty then 5 else 1)) ==>
        eval_operand arg_op out = eval_operand arg_op ss)
Proof
  rpt gen_tac >> strip_tac >>
  `value_has_type tv v /\ memory_value_rel tv v (w2n src_addr) ss.vs_memory` by
    gvs[lowered_value_rel_def] >>
  drule_all_then (qspecl_then [`cs.cs_next_id`, `cs.cs_next_var`] strip_assume_tac)
    materialized_state_frames >>
  Cases_on `is_bytestring_type ty` >> fs[]
  >- (mp_tac (Q.SPECL [`tenv`, `ctx`, `func`, `cenv`, `ty`, `tv`, `v`, `src`,
        `cs`, `op`, `cs'`, `ss`, `src_addr`] compile_materialize_bytes_path) >>
      impl_tac >- simp[] >> strip_tac >>
      gvs[materialized_state_def, abi_state_frame_inst_idx]) >>
  `val_wf tv v` by (drule value_has_type_val_wf >> simp[]) >>
  fs[compiler_var_names_def, GENLIST_1] >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cenv`, `ty`, `tv`, `v`, `src`, `cs`, `op`, `cs'`,
    `ss`, `src_addr`] compile_materialize_aggregate_path) >> impl_tac >- simp[] >> strip_tac >>
  gvs[materialized_state_def, lowered_value_rel_def, abi_state_frame_inst_idx,
    eval_op_inst_idx, memory_snapshot_result_operand_frame]
QED
