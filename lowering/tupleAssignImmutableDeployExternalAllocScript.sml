(* The external return buffer and result allocation share one execution witness. *)
Theory tupleAssignImmutableDeployExternalAlloc
Ancestors
  exprSimExtCallCase exprSimMemUnwrap exprSimAlloc exprSimWordArgs
  exprSimRawCallCalldata exprSafeOperand abiBuiltinAllocation emitHelperProps compileEnv loweringSlice exprLoweringProps
  venomExecSemantics venomState venomInst loweringPosts loweringStateRelDefs
  fragExec context venomMemDefs fragExecMem instMemFrontier memSafeRun

Theorem result_alloc_returndata[local]:
  compile_alloc_buffer sz sa = (buf,sm) /\
  run_inst_seq (emitted_insts sa sm) s = OK t ==>
  t.vs_returndata = s.vs_returndata
Proof
  simp[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
       comp_bind_def, comp_return_def, comp_ignore_bind_def, fresh_id_def,
       fresh_var_def, emit_def] >> strip_tac >>
  gvs[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND, run_inst_seq_def,
      step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def, AllCaseEqs()] >>
  gvs[update_var_def]
QED

Theorem tuple_immutable_external_result_allocated:
  !ctx func ce cx tys es sa s0 sr addr_op buf_op cap target
   has_default default_op default_ty default_opt returnData ee t r mid.
  extcall_returned ctx func ce cx (TupleT tys) es sa s0 sr addr_op buf_op cap
    target has_default default_op default_ty default_opt returnData ee t /\
  compile_alloc_buffer (type_memory_bytes ce (TupleT tys)) sr = (r,mid) /\
  fn_has_code sr mid func /\ fn_inst_ids_distinct func /\
  alloca_history func t /\
  type_memory_bytes ce (TupleT tys) < dimword (:256) ==>
  ?u w. gas_path_mem ctx func t 0 (OK u) /\
    extcall_returned ctx func ce cx (TupleT tys) es sa s0 mid addr_op buf_op cap
      target has_default default_op default_ty default_opt returnData ee u /\
    eval_operand r.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sr.cs_next_id =
      SOME (w2n w,type_memory_bytes ce (TupleT tys)) /\
    sa.cs_next_id <= sr.cs_next_id /\ sr.cs_next_id < mid.cs_next_id /\
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
  qhdtm_x_assum `extcall_returned`
    (strip_assume_tac o REWRITE_RULE [extcall_returned_def]) >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq _ t = OK v` >>
  drule_all result_alloc_returndata >> strip_tac >>
  drule_all hash_alloc_buffer_labels >> strip_tac >>
  drule_all alloc_buffer_storage >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `t.vs_alloca_next <= v.vs_alloca_next` by
    (qpat_x_assum `run_inst_seq _ _ = OK v` mp_tac >>
     simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
          exec_alloca_def, eval_operand_def] >>
     Cases_on `FLOOKUP t.vs_allocas sr.cs_next_id` >>
     simp[update_var_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]) >>
  `alloca_inv t /\ alloca_inv v` by fs[stmt_state_rel_def] >>
  `w2n w + type_memory_bytes ce (TupleT tys) <= v.vs_alloca_next` by
    (qpat_x_assum `alloca_inv v`
       (strip_assume_tac o REWRITE_RULE [alloca_inv_def, alloca_next_valid_def]) >>
     first_x_assum drule >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sr mid) t` by
    (qpat_x_assum `emitted_insts sr mid = _` SUBST1_TAC >>
     rewrite_tac[run_inst_seq_mem_ok_last] >> conj_tac
     >- (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
     simp[inst_dload_in_section_def, mk_inst_def]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode) (emitted_insts sr mid)` by
    simp[mk_inst_def, is_terminator_def] >>
  `!op. safe_operand sr op ==> eval_operand op v = eval_operand op t` by
    (rpt strip_tac >> Cases_on `op` >>
     gvs[safe_operand_def, eval_operand_def]) >>
  `wb_frame ce es ee sa s0 v` by
    (irule wb_frame_readonly_tail >> qexistsl_tac [`sr`, `t`] >> simp[]) >>
  `safe_operand sr addr_op /\ safe_operand sr buf_op /\
   safe_operand sr default_op` by fs[] >>
  `local_ptrs_reserved ce mid` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sr` >> simp[]) >>
  `safe_operand mid addr_op /\ safe_operand mid buf_op /\
   safe_operand mid default_op` by
    (metis_tac[safe_operand_mono, arithmeticTheory.LESS_EQ_ADD]) >>
  drule_all straight_path_mem >> strip_tac >>
  qexistsl_tac [`v with vs_inst_idx := LENGTH mid.cs_current_insts`, `w`] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (simp[extcall_returned_def, stmt_state_rel_inst_idx] >>
      conj_tac
      >- simp[raw_call_wb_frame_inst_idx] >>
      conj_tac >- (qexistsl_tac [`live`, `buf_size`] >> simp[]) >>
      `eval_operand default_op v = eval_operand default_op t` by simp[] >>
      qpat_x_assum `extcall_default_ready _ _ _ _ _ _ t` mp_tac >>
      qpat_x_assum `eval_operand default_op v = _` mp_tac >>
      qpat_x_assum `v.vs_memory = _` mp_tac >>
      qpat_x_assum `t.vs_alloca_next <= v.vs_alloca_next` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      simp[extcall_default_ready_def, expr_val_rel_def] >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >>
      gvs[] >> simp[] >>
      strip_tac >> irule arithmeticTheory.LESS_EQ_TRANS >>
      qexists_tac `t.vs_alloca_next` >> simp[]) >>
  simp[lookup_var_def, venomStateTheory.contract_storage_def,
       venomStateTheory.contract_transient_def] >>
  conj_tac
  >- (qpat_x_assum `!name b len. local_region _ _ v _ _ _ ==> _` mp_tac >>
      simp[local_region_def, lookup_var_def]) >>
  conj_tac
  >- (qexistsl_tac [`live`, `buf_size`] >> simp[] >>
      metis_tac[]) >>
  qpat_x_assum `!x. not_fresh_at sr x ==> _` mp_tac >>
  qpat_x_assum `contract_storage v = _` mp_tac >>
  qpat_x_assum `contract_transient v = _` mp_tac >>
  simp[lookup_var_def, venomStateTheory.contract_storage_def,
       venomStateTheory.contract_transient_def]
QED
