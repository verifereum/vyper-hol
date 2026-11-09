Theory externalReturnSuffixRun
Ancestors
  externalReturnAllocEncoder loweringHalt abiDecoderLoop abiEncoderWindowContract
  abiEncoderRegisteredEffect exprLoweringProps fragExec emitHelper context compileEnv
  venomState venomInst venomExecSemantics venomMemDefs valueEncoding words

Theorem abi_decode_sim_halt[local]:
  abi_decode_sim ctx func s t /\ run_from fuel ctx func t = Halt ss ==>
  ?fuel'. run_from fuel' ctx func s = Halt ss
Proof
  strip_tac >> fs[abi_decode_sim_def] >>
  first_x_assum (qspec_then `fuel` mp_tac) >> simp[]
QED

Theorem return_emit_endpoint_halt[local]:
  emit_inst RETURN [buf;len] [] st = (x,sf) /\ fn_has_code st sf func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand buf s = SOME b /\
  eval_operand len s = SOME (n2w (LENGTH bytes)) /\
  LENGTH bytes < dimword (:256) /\
  mem_bytes_at (w2n b) (LENGTH bytes) s.vs_memory = bytes ==>
  ?ss. run_from 0 ctx func s = Halt ss /\ ss.vs_returndata = bytes /\
    ss.vs_accounts = s.vs_accounts /\ ss.vs_transient = s.vs_transient /\
    ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests /\
    ss.vs_pending_deletions = s.vs_pending_deletions
Proof
  strip_tac >>
  qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
  simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >>
  drule fn_has_code_same_block >> simp[] >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx =
     SOME (mk_inst st.cs_next_id RETURN [buf;len] [])` by simp[] >>
  drule_all (SRULE [] return_buffer_run) >>
  disch_then (qspecl_then [`0`, `ctx`] mp_tac) >> simp[]
QED

Theorem return_output_alloc_encoder_halt:
  compile_alloc_buffer msz st = (buf,mid) /\
  compile_abi_encode_to_buf buf.buf_operand src ei mid = (out,en) /\
  fn_has_code st mid func /\ fn_has_code mid en func /\
  fn_inst_ids_distinct func /\ stmt_state_rel ctx func cenv cx es s /\
  local_ptrs_reserved cenv st /\ msz < dimword (:256) /\
  LENGTH (enc at av) <= msz /\ abi_encoder_admissible ei /\
  abi_encoder_window_input ei at av sb cap s.vs_memory /\
  eval_operand src s = SOME (n2w sb) /\
  (!x. src = Var x ==> not_fresh_at st x) /\
  (0 < cap ==>
    (?aid b len. aid < st.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (b,len) /\
      b <= sb /\ sb + cap <= b + len) \/
    (?name b len. local_region cenv es.scopes s name b len /\
      b <= sb /\ sb + cap <= b + len)) /\
  emit_inst RETURN [buf.buf_operand;out] [] en = (x,sf) /\
  fn_has_code en sf func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?fuel u ss. stmt_state_rel ctx func cenv cx es u /\
    run_from fuel ctx func s = Halt ss /\
    ss.vs_returndata = enc at av /\
    ss.vs_accounts = u.vs_accounts /\ ss.vs_transient = u.vs_transient /\
    ss.vs_logs = u.vs_logs /\ ss.vs_requests = u.vs_requests /\
    ss.vs_pending_deletions = u.vs_pending_deletions
Proof
  strip_tac >> drule_all return_output_alloc_encoder_continuation >>
  strip_tac >>
  drule (SRULE [combinTheory.K_DEF] abi_decode_sim_from_fragment) >>
  disch_then drule >> simp[] >> strip_tac >> gvs[] >>
  fs[abi_encoder_window_result_def] >>
  `?ss. run_from 0 ctx func t = Halt ss /\ ss.vs_returndata = enc at av /\
    ss.vs_accounts = t.vs_accounts /\ ss.vs_transient = t.vs_transient /\
    ss.vs_logs = t.vs_logs /\ ss.vs_requests = t.vs_requests /\
    ss.vs_pending_deletions = t.vs_pending_deletions` by
    (irule return_emit_endpoint_halt >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS]) >>
  `?fuel. run_from fuel ctx func u = Halt ss` by
    (irule abi_decode_sim_halt >> goal_assum (drule_at Any) >> simp[]) >>
  `?fuel. run_from fuel ctx func s = Halt ss` by
    (irule abi_decode_sim_halt >> goal_assum (drule_at Any) >> simp[]) >>
  fs[abi_encoder_registered_effect_def] >>
  qexistsl_tac [`fuel'`, `u`, `ss`] >> simp[]
QED
