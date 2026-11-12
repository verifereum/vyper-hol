(* Memory safety of caller-buffer store/RET suffixes. *)
Theory internalReturnBufferSafety
Ancestors
  internalReturnUnlockMem internalReturnSequenceMem internalReturnZeroStore
  bodyMemAssignTupleLocalsStores fragExecMem memSafeRun instMemFrontier
  stmtSimReturn stmtLowering emitHelper emitHelperProps exprLoweringProps fragExec instIdxIndep context compileEnv
  venomExecSemantics venomInstProofs venomState venomInst list rich_list arithmetic

Theorem buffer_ret_mem_safe[local]:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id RET [rpc] []) /\
  eval_operand rpc s = SOME pc ==>
  mem_safe_run fuel ctx func s
Proof
  strip_tac >>
  simp[mem_safe_run_def, Once mem_safe_block_def,
       mem_safe_step_non_invoke, mk_inst_def, below_frontier_no_ranges,
       inst_dload_in_section_other, run_from_def, Once exec_block_def,
       step_inst_non_invoke, step_inst_base_opcode_eqs, eval_operands_def]
QED

Theorem buffer_store_ret_mem_safe[local]:
  fn_has_code sa sb func /\
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ code ++
    [mk_inst id RET [rpc] []] /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
  run_inst_seq_mem_ok code s /\ run_inst_seq code s = OK t /\
  t.vs_current_bb = s.vs_current_bb /\ eval_operand rpc t = SOME pc ==>
  mem_safe_run fuel ctx func s
Proof
  strip_tac >>
  qpat_x_assum `sb.cs_current_insts = _`
    (assume_tac o PURE_REWRITE_RULE [GSYM APPEND_ASSOC]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  irule (cj 1 mem_safe_run_inst_seq) >>
  qexistsl_tac [`bb`, `code`, `t`] >> simp[] >>
  conj_tac
  >- (fs[fn_has_code_def, IS_PREFIX_APPEND] >> gvs[] >>
      simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, APPEND_ASSOC]) >>
  irule buffer_ret_mem_safe >>
  qexistsl_tac [`bb`, `id`, `pc`, `rpc`] >>
  simp[eval_op_inst_idx] >>
  `get_instruction bb (LENGTH sa.cs_current_insts + LENGTH code) =
     SOME (mk_inst id RET [rpc] [])` by
    (qpat_x_assum `!i. _` (qspec_then `LENGTH code` mp_tac) >>
     simp[EL_APPEND_EQN]) >> metis_tac[ADD_COMM]
QED

Theorem internal_buffer_store_ret_mem_safe[local]:
  compile_internal_return cenv (SOME src) rpc 0 ty sty ets (SOME dst) sa = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. rpc = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  eval_operand rpc s = SOME pc /\ ~is_word_type ty /\
  evaluate_type tenv ty = SOME tv /\ evaluate_type tenv sty = SOME stv /\
  value_has_type tv v /\ val_wf tv v /\ value_has_type stv v /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  (ty = sty \/ is_bytestring_type ty /\ is_bytestring_type sty) /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\
  (val_store_size stv v = 0 \/
   w2n sw + val_store_size stv v <= s.vs_alloca_next) /\
  w2n dw + type_memory_size tv <= s.vs_alloca_next /\
  fn_has_code sa sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  mem_safe_run fuel ctx func s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_internal_return _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_return_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_store_memory _ _ _ _ _ _ = (u,sm)` >>
  Cases_on `u` >> gnvs[] >>
  Cases_on `val_store_size stv v = 0`
  >- (`compile_store_memory cenv src dst ty sty sa = ((),sa)` by
        (irule compile_compatible_zero_store >> metis_tac[]) >>
      gvs[] >>
      qpat_x_assum `emit_inst RET _ _ _ = _` mp_tac >>
      simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
      strip_tac >> gvs[] >>
      drule fn_has_code_same_block >> simp[] >> strip_tac >>
      irule buffer_ret_mem_safe >>
      qexistsl_tac [`bb`, `sa.cs_next_id`, `pc`, `rpc`] >>
      simp[] >> first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  drule tuple_compatible_store_run_mem >>
  disch_then (qspecl_then [`s`, `tenv`, `tv`, `stv`, `v`, `sw`, `dw`] mp_tac) >>
  (impl_tac >- simp[ADD_COMM]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK t` >>
  `t.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _|> = _` mp_tac >>
     simp[venom_state_component_equality]) >>
  `t.vs_labels = s.vs_labels` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _|> = _` mp_tac >>
     simp[venom_state_component_equality]) >>
  `eval_operand rpc t = SOME pc` by
    (irule EQ_TRANS >> qexists_tac `eval_operand rpc s` >> simp[] >>
     Cases_on `rpc` >> gvs[eval_operand_def] >> metis_tac[]) >>
  qpat_x_assum `emit_inst RET _ _ _ = _` mp_tac >>
  simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  irule buffer_store_ret_mem_safe >>
  qexistsl_tac [`emitted_insts sa sm`, `sm.cs_next_id`, `pc`, `rpc`, `sa`,
    `sm with cs_current_insts := sm.cs_current_insts ++
      [mk_inst sm.cs_next_id RET [rpc] []]`, `t`] >>
  simp[] >> fs[same_blocks_def, fn_has_code_def, emitted_blocks_def]
QED

Theorem buffer_unlock_mem_safe[local]:
  compile_return_unlock cenv sa = ((),su) /\ fn_has_code sa su func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static /\
  mem_safe_run fuel ctx func (return_unlock_state cenv s) ==>
  mem_safe_run fuel ctx func s
Proof
  strip_tac >> drule compile_return_unlock_shape >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qabbrev_tac `info = cenv.ce_nonreentrant` >> PairCases_on `info` >>
  Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
  gvs[return_unlock_insts_def, return_unlock_state_def] >>
  fs[mem_safe_run_def, Once mem_safe_block_def, mk_inst_def,
     mem_safe_step_non_invoke, below_frontier_no_ranges,
     inst_dload_in_section_other, run_from_def, Once exec_block_def,
     step_inst_non_invoke, is_terminator_def,
     SRULE [mk_inst_def] step_persistent_return_unlock,
     SRULE [mk_inst_def] transientLockPropsTheory.step_TSTORE_lit] >>
  gvs[sstore_def, tstore_def, ADD1] >>
  simp[Once mem_safe_block_def, Once exec_block_def, ADD1]
QED

Theorem compile_internal_return_buffer_mem_safe:
  compile_return_unlock cenv sa = ((),su) /\
  compile_internal_return cenv (SOME src) rpc 0 ty sty ets (SOME dst) su = ((),sb) /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  (!x. rpc = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  eval_operand rpc s = SOME pc /\ ~is_word_type ty /\
  evaluate_type tenv ty = SOME tv /\ evaluate_type tenv sty = SOME stv /\
  value_has_type tv v /\ val_wf tv v /\ value_has_type stv v /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  (ty = sty \/ is_bytestring_type ty /\ is_bytestring_type sty) /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\
  (val_store_size stv v = 0 \/
   w2n sw + val_store_size stv v <= s.vs_alloca_next) /\
  w2n dw + type_memory_size tv <= s.vs_alloca_next /\
  fn_has_code sa su func /\ fn_has_code su sb func /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static ==>
  !fuel. mem_safe_run fuel ctx func s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> gen_tac >>
  irule buffer_unlock_mem_safe >> simp[] >>
  qexistsl_tac [`cenv`, `sa`, `su`] >> simp[] >>
  drule compile_return_unlock_shape >> strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at su x` by
    fs[loweringStateRelDefsTheory.not_fresh_at_def] >>
  ` (return_unlock_state cenv s).vs_inst_idx = LENGTH su.cs_current_insts` by
    (qabbrev_tac `info = cenv.ce_nonreentrant` >> PairCases_on `info` >>
     Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
     fs[return_unlock_state_def, return_unlock_insts_def, ADD1]) >>
  irule internal_buffer_store_ret_mem_safe >>
  goal_assum (drule_at (Pat `compile_internal_return _ _ _ _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`dw`, `pc`, `stv`, `sw`, `tenv`, `tv`, `v`] >>
  simp[eval_operand_return_unlock] >> fs[ADD_COMM] >> metis_tac[]
QED
