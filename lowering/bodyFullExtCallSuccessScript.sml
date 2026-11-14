Theory bodyFullExtCallSuccess
Ancestors
  bodyFullExtCallFrames exprSimExtCallCase valueEncodingProps
  loweringStateRelDefs venomState allocaHistory ghostPcTransportPtr
  abiStaticLoopBody exprLoweringProps exprSafeOperand compileEnv loweringPosts

Theorem extcall_success_default_bytes:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  eval_operand buf_op t = SOME ro /\
  v.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE cap rd) t).vs_memory ==>
  !dv w tv. default_opt = SOME dv /\ ~is_word_type default_ty /\
    eval_operand default_op t = SOME w /\
    evaluate_type (get_tenv cx) default_ty = SOME tv ==>
    mem_bytes_at (w2n w) (val_footprint tv dv) v.vs_memory =
    mem_bytes_at (w2n w) (val_footprint tv dv) t.vs_memory
Proof
  rpt strip_tac >> fs[extcall_request_ready_def] >>
  irule write_memory_mem_bytes_at_disjoint >>
  fs[regions_disjoint_def, listTheory.LENGTH_TAKE_EQ] >>
  IF_CASES_TAC >> decide_tac
QED

Theorem extcall_success_target_boundary:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  sp.cs_next_var <= sr.cs_next_var /\ sp.cs_next_id <= sr.cs_next_id /\
  new_block cont_lbl s10 = (old_lbl,sr) /\
  (!H. valid_horizon cx st0 H ee'.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee' v) /\
  wb_frame cenv es ee' sa s0 v /\
  extcall_default_ready cx ret_type has_default default_op default_ty default_opt v /\
  ~v.vs_halted /\ v.vs_allocas = t.vs_allocas /\
  v.vs_alloca_next = t.vs_alloca_next /\ eval_operand buf_op t = SOME ro /\
  v.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE cap rd) t).vs_memory /\
  v.vs_returndata = rd /\
  (!op. safe_operand sp op ==> eval_operand op v = eval_operand op t) /\
  alloca_history func v /\ s0.vs_alloca_next <= v.vs_alloca_next /\
  ee'.gas_obs = [] /\ accounts_runtime_well_typed ee'.accounts /\
  MAP FDOM es.scopes = MAP FDOM ee'.scopes /\ LENGTH rd < dimword (:256) /\
  (!H. valid_horizon cx st0 H ee'.storage_trace ==>
       storage_well_formed_on cx ee' (FST H)) ==>
  extcall_returned st0 ctx func cenv cx ret_type es sa s0 sr addr_op buf_op cap
    target has_default default_op default_ty default_opt rd ee'
    (jump_to cont_lbl (next_inst v)) /\
  alloca_history func (jump_to cont_lbl (next_inst v)) /\
  s0.vs_alloca_next <= (jump_to cont_lbl (next_inst v)).vs_alloca_next /\
  (!op. safe_operand sp op ==>
    eval_operand op (jump_to cont_lbl (next_inst v)) = eval_operand op t) /\
  (jump_to cont_lbl (next_inst v)).vs_allocas = t.vs_allocas /\
  (jump_to cont_lbl (next_inst v)).vs_alloca_next = t.vs_alloca_next /\
  (jump_to cont_lbl (next_inst v)).vs_memory =
    (write_memory_with_expansion (w2n ro) (TAKE cap rd) t).vs_memory /\
  (!dv w tv. default_opt = SOME dv /\ ~is_word_type default_ty /\
    eval_operand default_op t = SOME w /\
    evaluate_type (get_tenv cx) default_ty = SOME tv ==>
    mem_bytes_at (w2n w) (val_footprint tv dv)
      (jump_to cont_lbl (next_inst v)).vs_memory =
    mem_bytes_at (w2n w) (val_footprint tv dv) t.vs_memory)
Proof
  strip_tac >>
  reverse conj_tac
  >- (simp[eval_operand_jump_to_eq, next_inst_def] >>
      conj_tac >- gvs[alloca_history_def, jump_to_def] >>
      simp[jump_to_def] >>
      drule (REWRITE_RULE [GSYM AND_IMP_INTRO] extcall_success_default_bytes) >>
      disch_then drule >> disch_then drule >> simp[]) >>
  simp[extcall_returned_def, stmt_state_rel_jump_to, next_inst_def,
       stmt_state_rel_inst_idx] >>
  conj_tac
  >- (gvs[wb_frame_def, locals_kept_def, popped_kept_def, jump_to_def,
          lookup_var_def] >> metis_tac[]) >>
  `extcall_default_ready cx ret_type has_default default_op default_ty
     default_opt (jump_to cont_lbl (v with vs_inst_idx := v.vs_inst_idx + 1))` by
    (gvs[extcall_default_ready_def, expr_val_rel_def, jump_to_def,
         eval_operand_def, lookup_var_def] >> metis_tac[]) >>
  fs[extcall_request_ready_def, new_block_def, jump_to_def] >>
  `local_ptrs_reserved cenv sr` by metis_tac[local_ptrs_reserved_next_var] >>
  `safe_operand sr addr_op /\ safe_operand sr buf_op /\ safe_operand sr default_op`
    by metis_tac[safe_operand_mono] >>
  simp[] >>
  gvs[write_memory_mem_bytes_at_same] >>
  qexistsl_tac [`live`, `buf_size`] >> simp[] >> decide_tac
QED
