Theory tupleAssignImmutableDeployExternalGuard
Ancestors
  tupleAssignImmutableDeployExternalAlloc builtinSimple moduleLoweringProps
  exprLowering compileEnv freshWrites loweringStateRelDefs bodyDeclMemoryCounted
  exprSimConvertBytes loweringPosts exprSimRawCallCalldata
  exprSimMemUnwrap exprSimWordArgs exprSimExtCallCase exprSafeOperand
  emitHelperProps exprLoweringProps loweringSlice fragExecMem instMemFrontier
  memSafeRun venomExecSemantics venomState venomInst fragGasPathMem

Theorem guard_run[local]:
  compile_return_value_decode mn cap sa = (hi,sb) /\
  s.vs_returndata = rd /\ mn <= LENGTH rd /\ LENGTH rd < dimword (:256) /\
  mn < dimword (:256) /\ cap < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand hi t = SOME (n2w (MIN (LENGTH rd) cap)) /\
      t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
      t.vs_alloca_next = s.vs_alloca_next /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      contract_storage t = contract_storage s /\
      contract_transient t = contract_transient s /\
      t.vs_labels = s.vs_labels /\ t.vs_returndata = s.vs_returndata /\
      t.vs_current_bb = s.vs_current_bb /\ t.vs_halted = s.vs_halted /\
      t = s with vs_vars := t.vs_vars
Proof
  simp[compile_return_value_decode_def, builtinSimpleTheory.compile_select_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       comp_bind_def, comp_return_def, comp_ignore_bind_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       eval_operand_def, lookup_var_def, update_var_def,
       ASCIInumbersTheory.toString_11] >>
  simp[exec_read0_def, exec_pure2_def, exec_pure1_def,
       eval_operand_def, lookup_var_def, update_var_def,
       ASCIInumbersTheory.toString_11, bool_to_word_def,
       wordsTheory.w2n_n2w] >>
  simp[finite_mapTheory.FLOOKUP_UPDATE, ASCIInumbersTheory.toString_11,
       wordsTheory.w2n_n2w, bool_to_word_def] >>
  simp[venomStateTheory.contract_storage_def,
       venomStateTheory.contract_transient_def] >> conj_tac
  >- (Cases_on `LENGTH s.vs_returndata < cap` >>
      simp[arithmeticTheory.MIN_DEF, bool_to_word_def] >>
      wordsLib.WORD_DECIDE_TAC) >>
  rpt strip_tac >> fs[not_fresh_at_def] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  fs[ASCIInumbersTheory.toString_11]
QED

Theorem guard_shape[local]:
  compile_return_value_decode mn cap sa = (hi,sb) ==>
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  simp[compile_return_value_decode_def, builtinSimpleTheory.compile_select_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       comp_bind_def, comp_return_def, comp_ignore_bind_def,
       fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, same_blocks_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def] >>
  irule run_inst_seq_mem_ok_every >>
  simp[mk_inst_def, inst_dload_in_section_def] >>
  rpt conj_tac >> rpt gen_tac >> irule below_frontier_no_ranges >>
  simp[mk_inst_def]
QED

Theorem tuple_immutable_external_decode_guard:
  !ctx func ce cx tys es sa s0 start addr_op buf_op cap target
   has_default default_op default_ty default_opt returnData ee initial hi finish mn.
  extcall_returned ctx func ce cx (TupleT tys) es sa s0 start addr_op buf_op cap
    target has_default default_op default_ty default_opt returnData ee initial /\
  compile_return_value_decode mn cap start = (hi,finish) /\
  fn_has_code start finish func /\ fn_inst_ids_distinct func /\
  mn <= LENGTH returnData /\ mn < dimword (:256) /\ cap < dimword (:256) ==>
  ?actual. gas_path_mem ctx func initial 0 (OK actual) /\
    extcall_returned ctx func ce cx (TupleT tys) es sa s0 finish addr_op buf_op cap
      target has_default default_op default_ty default_opt returnData ee actual /\
    eval_operand hi actual = SOME (n2w (MIN (LENGTH returnData) cap)) /\
    actual.vs_memory = initial.vs_memory /\ actual.vs_allocas = initial.vs_allocas /\
    actual.vs_alloca_next = initial.vs_alloca_next /\
    (!op. safe_operand start op ==> eval_operand op actual = eval_operand op initial) /\
    (!x. not_fresh_at start x ==> lookup_var x actual = lookup_var x initial) /\
    contract_storage actual = contract_storage initial /\
    contract_transient actual = contract_transient initial /\
    actual.vs_labels = initial.vs_labels /\
    (alloca_history func initial ==> alloca_history func actual)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `compile_return_value_decode mn cap start = (hi,endst)` >>
  qhdtm_x_assum `extcall_returned`
    (strip_assume_tac o REWRITE_RULE [extcall_returned_def]) >>
  drule_all guard_run >> strip_tac >>
  drule guard_shape >> disch_then (qspec_then `initial` strip_assume_tac) >>
  `!op. safe_operand start op ==> eval_operand op t = eval_operand op initial` by
    (Cases >> simp[safe_operand_def, eval_operand_def]) >>
  `stmt_state_rel ctx func ce cx ee t` by
    (irule convert_readonly_state_frame >> qexistsl_tac [`initial`, `start`] >> simp[]) >>
  `wb_frame ce es ee sa s0 t` by
    (irule wb_frame_readonly_tail >> qexistsl_tac [`start`, `initial`] >> simp[]) >>
  `local_ptrs_reserved ce endst` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `start` >> simp[]) >>
  `safe_operand endst addr_op /\ safe_operand endst buf_op /\
   safe_operand endst default_op` by
    (fs[] >> metis_tac[safe_operand_mono]) >>
  drule_all body_decl_zero_gas_path >> strip_tac >>
  `alloca_history func initial ==>
   alloca_history func (t with vs_inst_idx := LENGTH endst.cs_current_insts)` by
    (strip_tac >> `alloca_inv initial` by fs[stmt_state_rel_def] >>
     drule_all straight_path_mem >> simp[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH endst.cs_current_insts` >>
  simp[stmt_state_rel_inst_idx, lookup_var_def,
       venomStateTheory.contract_storage_def, venomStateTheory.contract_transient_def] >>
  conj_tac
  >- (simp[extcall_returned_def, stmt_state_rel_inst_idx,
           raw_call_wb_frame_inst_idx] >>
      `extcall_default_ready cx (TupleT tys) has_default default_op default_ty
        default_opt (t with vs_inst_idx := LENGTH endst.cs_current_insts)` by
        (`eval_operand default_op t = eval_operand default_op initial` by fs[] >>
          qpat_x_assum `extcall_default_ready _ _ _ _ _ _ initial` mp_tac >>
          qpat_x_assum `eval_operand default_op t = _` mp_tac >>
          qpat_x_assum `t.vs_memory = _` mp_tac >>
          qpat_x_assum `t.vs_alloca_next = _` mp_tac >>
          POP_ASSUM_LIST (K all_tac) >>
          simp[extcall_default_ready_def, expr_val_rel_def] >> metis_tac[]) >>
      fs[same_blocks_def] >> conj_tac
      >- (qexistsl_tac [`live`, `buf_size`] >> simp[]) >>
      qpat_x_assum `extcall_default_ready _ _ _ _ _ _ (t with vs_inst_idx := _)`
        mp_tac >> simp[]) >>
  fs[lookup_var_def, venomStateTheory.contract_storage_def,
     venomStateTheory.contract_transient_def]
QED

Theorem tuple_immutable_external_allocated_guard:
  !ctx func ce cx tys es sa s0 sr addr_op buf_op cap target
   has_default default_op default_ty default_opt returnData ee t r mid hi endst mn.
  extcall_returned ctx func ce cx (TupleT tys) es sa s0 sr addr_op buf_op cap
    target has_default default_op default_ty default_opt returnData ee t /\
  compile_alloc_buffer (type_memory_bytes ce (TupleT tys)) sr = (r,mid) /\
  fn_has_code sr mid func /\ fn_inst_ids_distinct func /\
  alloca_history func t /\
  type_memory_bytes ce (TupleT tys) < dimword (:256) /\
  compile_return_value_decode mn cap mid = (hi,endst) /\
  fn_has_code mid endst func /\ mn <= LENGTH returnData /\ mn < dimword (:256) ==>
  ?u w. gas_path_mem ctx func t 0 (OK u) /\
    extcall_returned ctx func ce cx (TupleT tys) es sa s0 endst addr_op buf_op cap
      target has_default default_op default_ty default_opt returnData ee u /\
    eval_operand hi u = SOME (n2w (MIN (LENGTH returnData) cap)) /\
    eval_operand r.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sr.cs_next_id =
      SOME (w2n w,type_memory_bytes ce (TupleT tys)) /\
    sa.cs_next_id <= sr.cs_next_id /\ sr.cs_next_id < mid.cs_next_id /\
    mid.cs_next_id <= endst.cs_next_id /\
    w2n w + type_memory_bytes ce (TupleT tys) < dimword (:256) /\
    w2n w + type_memory_bytes ce (TupleT tys) <= u.vs_alloca_next /\
    alloca_history func u /\
    (!name b len. local_region ce ee.scopes u name b len ==>
       regions_disjoint (w2n w) (type_memory_bytes ce (TupleT tys)) b len) /\
    (?ro live buf_size. eval_operand buf_op u = SOME ro /\
       sa.cs_next_id <= live /\ live < sr.cs_next_id /\ cap <= buf_size /\
       FLOOKUP u.vs_allocas live = SOME (w2n ro,buf_size) /\
       regions_disjoint (w2n w) (type_memory_bytes ce (TupleT tys))
         (w2n ro) buf_size) /\
    u.vs_memory = t.vs_memory /\
    (!x. not_fresh_at sr x ==> lookup_var x u = lookup_var x t) /\
    (!aid entry. FLOOKUP t.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    t.vs_alloca_next <= u.vs_alloca_next /\
    contract_storage u = contract_storage t /\
    contract_transient u = contract_transient t /\ u.vs_labels = t.vs_labels
Proof
  rpt gen_tac >> strip_tac >>
  drule_all tuple_immutable_external_result_allocated >> strip_tac >>
  rename1 `gas_path_mem ctx func t 0 (OK allocated)` >>
  `cap < dimword (:256)` by
    (qpat_assum `extcall_returned _ _ _ _ _ _ _ _ mid _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [extcall_returned_def]) >> decide_tac) >>
  drule_all tuple_immutable_external_decode_guard >> strip_tac >>
  rename1 `gas_path_mem ctx func allocated 0 (OK final)` >>
  drule abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape >> strip_tac >>
  `safe_operand mid r.buf_operand` by
    (metis_tac[emit_op_safe_operand]) >>
  `local_ptrs_reserved ce mid` by fs[extcall_returned_def] >>
  `!name b len. local_region ce ee.scopes final name b len <=>
                local_region ce ee.scopes allocated name b len` by
    (rpt gen_tac >> irule exprSimCopyTheory.copy_buffer_local_region_frame >>
     qexists_tac `mid` >> simp[]) >>
  `sr.cs_next_var <= mid.cs_next_var` by
    (qpat_x_assum `emit_op ALLOCA _ sr = _` mp_tac >>
     simp[emitHelperTheory.emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
          comp_ignore_bind_def, comp_return_def, emit_def] >>
     strip_tac >> gvs[]) >>
  `mid.cs_next_id <= endst.cs_next_id` by
    (drule guard_shape >> simp[]) >>
  `safe_operand mid buf_op` by fs[extcall_returned_def] >>
  qexistsl_tac [`final`, `w`] >>
  conj_tac
  >- (`0 = 0 + 0` by simp[] >> pop_assum SUBST1_TAC >>
      irule gas_path_mem_then >> metis_tac[]) >>
  simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (qexistsl_tac [`live`, `buf_size`] >> simp[]) >>
  rpt strip_tac >>
  `not_fresh_at mid x` by metis_tac[not_fresh_at_mono] >> simp[]
QED
