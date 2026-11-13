(* Input intervals for raw_call; reuse the dynamic-bytes memory boundary. *)
Theory bodyMemRawCallBounds
Ancestors
  bodyMemBiKeccakBounds exprSimMemDefs exprLoweringProps loweringPosts
  exprSimProps compileEnv words instMemFrontier venomInst venomMemDefs
  builtinSystem context emitHelper emitHelperProps fragExecMem memSafeRun rich_list
  allocaHistoryFragment venomExecSemantics fragExec venomMemProps venomState

Theorem raw_call_input_bounds:
  expr_post ctx func cenv cx e es sa sm s0 es' (BytesV bs) op s /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (BaseTV (BytesT (Dynamic cap))) /\
  expr_store_bound cx (expr_type e) (BytesV bs) op s /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  stmt_state_rel ctx func cenv cx ee t ==>
  ?b. eval_operand op s = SOME (n2w b) /\
    mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
    b + 32 + LENGTH bs < dimword (:256) /\
    LENGTH bs < dimword (:256) /\
    b + 32 <= t.vs_alloca_next /\
    (LENGTH bs = 0 \/ b + 32 + LENGTH bs <= t.vs_alloca_next)
Proof
  strip_tac >> drule_all keccak_dynamic_post_bounds >> strip_tac >>
  `alloca_room ctx func t` by fs[stmt_state_rel_def] >>
  drule alloca_room_next_lt >> strip_tac >>
  qexists_tac `b` >> simp[] >>
  Cases_on `LENGTH bs = 0` >> gvs[] >> decide_tac
QED

Theorem raw_call_input_output_frontier:
  eval_operand off s = SOME ao /\ eval_operand len s = SOME az /\
  eval_operand roff s = SOME ro /\ eval_operand rlen s = SOME rz /\
  (w2n az = 0 \/ w2n ao + w2n az <= s.vs_alloca_next) /\
  (w2n rz = 0 \/ w2n ro + w2n rz <= s.vs_alloca_next) ==>
  inst_mem_below_frontier
    (mk_inst id (if stat then STATICCALL else CALL)
      (if stat then [gas;addr;off;len;roff;rlen]
       else [gas;addr;vl;off;len;roff;rlen]) outs) s
Proof
  Cases_on `stat` >>
  simp[below_frontier_CALL, below_frontier_STATICCALL] >>
  rpt strip_tac >> gvs[]
QED

Theorem raw_call_outbuf_mem_ok:
  compile_raw_call_outbuf cap sa = ((ov,op),sb) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> irule run_inst_seq_mem_ok_every >>
  Cases_on `0 < cap` >>
  qpat_x_assum `compile_raw_call_outbuf _ _ = _` mp_tac >>
  simp[compile_raw_call_outbuf_def, compile_alloc_buffer_def,
    emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[below_frontier_no_ranges, inst_dload_in_section_other, mk_inst_def]
QED

Theorem raw_call_outbuf_frontier:
  compile_raw_call_outbuf cap sa = ((ov,op),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  s.vs_alloca_next <= t.vs_alloca_next
Proof
  Cases_on `0 < cap` >>
  simp[compile_raw_call_outbuf_def, compile_alloc_buffer_def,
    emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
       exec_alloca_def, eval_operand_def] >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >>
  simp[update_var_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `step_inst_base ins allocated = OK t` >>
  `t.vs_alloca_next = allocated.vs_alloca_next` by
    (irule step_inst_base_preserves_alloca_next >>
     qexists_tac `ins` >> simp[Abbr `ins`]) >>
  gvs[Abbr `allocated`]
QED

Theorem raw_call_data_prefix_mem_ok:
  emit_op MLOAD [ptr_op] sa = (len,sl) /\
  emit_op ADD [ptr_op; Lit 32w] sl = (data,sm) /\
  eval_operand ptr_op s = SOME p /\ w2n p + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sm) s
Proof
  strip_tac >>
  qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
  qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  rewrite_tac[APPEND, run_inst_seq_mem_ok_cons] >>
  conj_tac >- simp[below_frontier_MLOAD] >>
  simp[inst_dload_in_section_other, mk_inst_def,
       run_inst_seq_mem_ok_last, below_frontier_no_ranges] >>
  CASE_TAC >> simp[]
QED
