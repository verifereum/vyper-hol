Theory abiDecodeMemBytesGuards
Ancestors
  abiDecoderReentry abiDecodeMemRange abiDecoderBytesBound bodyFieldMemoryProps freshWrites
  fragGasMode fragGasPathMem fragExec emitHelperProps emitHelper compileEnv
  venomState venomExecSemantics venomInst words list rich_list exprLoweringProps
  loweringStateRelDefs abiDecoderRange localPtrsProps

Theorem abi_decode_add_path_mem:
  emit_op ADD [a;b] st = (v,st') /\
  eval_operand a s = SOME p /\ eval_operand b s = SOME q /\
  fresh_vars_wrt st s /\ fn_has_code st st' func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    eval_operand v t = SOME (p+q) /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted /\
    t.vs_memory = s.vs_memory /\
      t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ alloca_history func t
Proof
  strip_tac >> drule_all abi_decode_add_sequence >> strip_tac >>
  `straight_fresh (emit_op ADD [a;b])` by
    (irule straight_fresh_emit_op >> simp[fresh_write_op_def]) >>
  `writes_fresh st (emitted_insts st st')` by fs[straight_fresh_def] >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  `t.vs_labels = s.vs_labels` by
    (qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s` by
    (Cases >> fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
      eval_operand_def, lookup_var_def, not_fresh_at_def]) >>
  drule_all attr_add_gas_path >> strip_tac >>
  drule_all attr_add_history >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def, fresh_vars_wrt_def] >>
  `t.vs_current_bb = s.vs_current_bb /\ ~t.vs_halted /\
   t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  drule emit_op_extends >> gvs[same_blocks_def, fresh_vars_wrt_def]
QED

Theorem abi_decode_add_range_path_mem[local]:
  emit_op ADD [a;b] st = (v,mid) /\
  compile_abi_decode_range_check a v hi mid = ((),st') /\
  eval_operand a s = SOME p /\ eval_operand b s = SOME q /\
  eval_operand hi s = SOME h /\ fresh_vars_wrt st s /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (w2n p <= w2n (p+q) /\ w2n (p+q) <= w2n h ==>
    ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand v t = SOME (p+q) /\
      t.vs_current_bb = st'.cs_current_bb /\
      t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted /\
      fresh_vars_wrt st' t /\
      (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op s) /\
      t.vs_memory = s.vs_memory /\
      t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\ t.vs_alloca_next = s.vs_alloca_next /\
      t.vs_allocas = s.vs_allocas /\ alloca_history func t) /\
  (~(w2n p <= w2n (p+q) /\ w2n (p+q) <= w2n h) ==>
    ?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t))
Proof
  strip_tac >>
  drule compile_abi_decode_range_check_fragment_shape >> strip_tac >>
  `fn_has_code st mid func /\ fn_has_code mid st' func` by
    (gvs[fn_has_code_def, emitted_blocks_def, inst_extends_def] >>
     metis_tac[IS_PREFIX_APPEND, APPEND_ASSOC]) >>
  drule_all abi_decode_add_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `eval_operand a t = SOME p /\ eval_operand hi t = SOME h` by metis_tac[] >>
  `alloca_inv t` by (irule localPtrsPropsTheory.alloca_inv_fields >> metis_tac[]) >>
  drule_all abi_decode_range_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  conj_tac >- suspend "accept" >> suspend "reject"
QED
Resume abi_decode_add_range_path_mem[accept]:
  strip_tac >> gvs[] >>
  `st.cs_next_var <= mid.cs_next_var` by
    (drule emitted_insts_emit_op >> simp[]) >>
  `gas_path_mem ctx func s 0 (OK t')` by
    metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES] >>
  qexists_tac `t'` >> simp[] >> metis_tac[abi_decoder_operand_live_mono]
QED
Resume abi_decode_add_range_path_mem[reject]:
  strip_tac >> gvs[] >>
  fs[gas_marked_path_def] >>
  metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES]
QED
Finalise abi_decode_add_range_path_mem

Theorem abi_decode_bytes_head_path_mem:
  abi_decode_bytes_head src hi st = (head,st') /\ hi <> Lit 0w /\
  eval_operand src s = SOME p /\ eval_operand hi s = SOME h /\
  fresh_vars_wrt st s /\ fn_has_code st st' func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (w2n p <= w2n (p+32w) /\ w2n (p+32w) <= w2n h ==>
    ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand head t = SOME (p+32w) /\
      t.vs_current_bb = st'.cs_current_bb /\
      t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted /\
      fresh_vars_wrt st' t /\
      (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op s) /\
      t.vs_memory = s.vs_memory /\
      t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\ t.vs_alloca_next = s.vs_alloca_next /\
      t.vs_allocas = s.vs_allocas /\ alloca_history func t) /\
  (~(w2n p <= w2n (p+32w) /\ w2n (p+32w) <= w2n h) ==>
    ?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t))
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_bytes_head _ _ _ = _` mp_tac >>
  simp[abi_decode_bytes_head_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `eval_operand (Lit 32w) s = SOME 32w` by simp[eval_operand_def] >>
  drule_all abi_decode_add_range_path_mem >>
  disch_then (qspec_then `ctx` mp_tac) >> simp_tac bool_ss [DE_MORGAN_THM] >> metis_tac[]
QED

Theorem abi_decode_bytes_payload_guard_path_mem:
  abi_decode_bytes_payload_guard head len hi st = ((),st') /\ hi <> Lit 0w /\
  eval_operand head s = SOME p /\ eval_operand len s = SOME q /\
  eval_operand hi s = SOME h /\ fresh_vars_wrt st s /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (w2n p <= w2n (p+q) /\ w2n (p+q) <= w2n h ==>
    ?t. gas_path_mem ctx func s 0 (OK t) /\
      t.vs_current_bb = st'.cs_current_bb /\
      t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted /\
      fresh_vars_wrt st' t /\
      (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op s) /\
      t.vs_memory = s.vs_memory /\
      t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\ t.vs_alloca_next = s.vs_alloca_next /\
      t.vs_allocas = s.vs_allocas /\ alloca_history func t) /\
  (~(w2n p <= w2n (p+q) /\ w2n (p+q) <= w2n h) ==>
    ?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t))
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_bytes_payload_guard _ _ _ _ = _` mp_tac >>
  simp[abi_decode_bytes_payload_guard_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule_all abi_decode_add_range_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  conj_tac >- (strip_tac >> gvs[] >> qexists_tac `t` >> simp[]) >> simp[]
QED
