(* Memory-safe compilation of local names whose type is a word type without a
   word value (address, bytesM): the lowering loads the slot with MLOAD. *)
Theory bodyNameWordTypeMemory
Ancestors
  bodyNameMemoryFacts
  exprSimSource exprSimHypsDefs exprSimDefs exprSimProps bodyMemoryDefs
  exprSimMemoryValues exprSimMemoryStack exprSimMemoryRead fragGasSeqMem
  fragGasPathMem gasNormalPrefix gasSummary gasContext gasCount fragGasMode
  loweringPosts exprSimNameWord exprSimNameValue loweringSlice exprLowering
  exprLoweringProps fragExec fragExecMem allocaHistoryFragment instMemFrontier
  emitHelperProps emitHelper compileEnv context venomInst venomState
  venomExecSemantics venomMemDefs vyperInterpreter vyperState vyperAST
  vyperTypeEnv vyperTypeSystem vyperTypeInvariants valueEncoding valueEncodingProofs valueEncodingProps
  list rich_list finite_map words arithmetic

Theorem body_wordtype_name_region[local]:
  expr_sim_pre ce cx env (Name ann id) es /\ is_word_type ann /\
  stmt_state_rel ctx func ce cx es s ==>
  ?entry p sz w.
    lookup_scopes id es.scopes = SOME entry /\
    evaluate_type (get_tenv cx) ann = SOME entry.type /\
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\
    local_region ce es.scopes s id (w2n w) sz /\ 32 <= sz /\
    mload (w2n w) s = typed_val_to_w256 entry.type entry.value
Proof
  rpt strip_tac >> drule_all body_name_source_region >> strip_tac >>
  drule_all word_tv_memory_size >> strip_tac >>
  drule_all val_in_memory_word_type >>
  simp[mem_word_at_eq_mload] >> strip_tac >>
  qexistsl [`entry`, `p`, `sz`, `w`] >> simp[]
QED

Theorem body_wordtype_name_MLOAD_frontier[local]:
  expr_sim_pre ce cx env (Name ann id) es /\ is_word_type ann /\
  stmt_state_rel ctx func ce cx es s /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) ==>
  inst_mem_below_frontier (mk_inst iid MLOAD [Var p] outs) s
Proof
  rpt strip_tac >> drule_all body_wordtype_name_region >> strip_tac >>
  gvs[] >> irule body_local_ptr_MLOAD_frontier >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[n2w_w2n]
QED

Theorem body_name_wordtype_counted[local]:
  expr_sim_pre ce cx env (Name ann id) es /\ is_word_type ann /\
  lower_value compile_expr ce ty (Name ann id) sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?entry p sz out.
    lookup_scopes id es.scopes = SOME entry /\
    evaluate_type (get_tenv cx) ann = SOME entry.type /\
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\ op = Var out /\
    emit_op MLOAD [Var p] sa = (Var out,sb) /\
    sb.cs_current_bb = sa.cs_current_bb /\
    gas_path_mem ctx func s0 0
      (OK (update_var out (typed_val_to_w256 entry.type entry.value)
        (s0 with vs_inst_idx := LENGTH sb.cs_current_insts))) /\
    alloca_history func (update_var out (typed_val_to_w256 entry.type entry.value)
      (s0 with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >> drule_all body_wordtype_name_region >> strip_tac >>
  drule_all lower_value_name_word >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  `run_inst_seq (emitted_insts sa sb) s0 =
    OK (update_var out (typed_val_to_w256 entry.type entry.value) s0)` by
    (simp[run_inst_seq_def, Abbr `out`] >>
     `eval_operand (Var p) s0 = SOME w` by simp[eval_operand_def] >>
     drule step_MLOAD >> simp[]) >>
  `alloca_inv s0` by gvs[stmt_state_rel_def] >>
  `(?bb rest. lookup_block s0.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s0.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest) /\
    s0.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    (fs[fn_has_code_def, IS_PREFIX_APPEND, same_blocks_def] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, mk_inst_def] >> metis_tac[]) >>
  `alloca_history func ((update_var out
      (typed_val_to_w256 entry.type entry.value) s0)
      with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (`EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
       simp[mk_inst_def, is_terminator_def] >>
     drule_all alloca_history_run_inst_seq >> simp[]) >>
  `gas_path_mem ctx func s0 0
    (OK ((update_var out (typed_val_to_w256 entry.type entry.value) s0)
      with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (drule_at (Pos last) run_inst_seq_gas_path_mem >>
     disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
     simp[IS_PREFIX_APPEND, run_inst_seq_mem_ok_last, GSYM mk_inst_def,
          is_terminator_def] >>
     (impl_tac >- (irule body_wordtype_name_MLOAD_frontier >> metis_tac[])) >>
     simp[]) >>
  qexistsl [`entry`, `p`, `sz`, `out`] >>
  gvs[Abbr `out`, same_blocks_def, update_var_def]
QED

Theorem body_name_wordtype_post[local]:
  emit_op MLOAD [Var p] sa = (Var out,sb) /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s0 /\
  is_word_type ann /\ evaluate_type (get_tenv cx) ann = SOME tv ==>
  expr_post ctx func ce cx (Name ann id) es sa sb s0
    (es with gas_obs := []) v (Var out)
    (update_var out (typed_val_to_w256 tv v)
      (s0 with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `out = STRCAT "%" (toString sa.cs_next_var)` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_id_def, fresh_var_def, emit_def] >>
  `not_local_ptr ce (es with gas_obs := []).scopes out` by
    (gvs[] >> irule local_ptrs_reserved_fresh >> qexists `sa` >> simp[]) >>
  `stmt_state_rel ctx func ce cx (es with gas_obs := [])
    (update_var out (typed_val_to_w256 tv v)
      (s0 with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule stmt_state_rel_update_var >> simp[] >>
     drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`,
                            `LENGTH sb.cs_current_insts`, `[]`] mp_tac) >> simp[]) >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       vyperASTTheory.expr_type_def, eval_operand_def, update_var_def,
       lookup_var_def, FLOOKUP_UPDATE, locals_kept_mem] >>
  rpt strip_tac >>
  `STRING #"%" (toString sa.cs_next_var) <> x` by
    (strip_tac >> gvs[not_fresh_at_def]) >> simp[]
QED

Theorem body_name_wordtype_mem_prefix[local]:
  expr_sim_pre ce cx env (Name ann id) es /\ is_word_type ann /\
  lower_value compile_expr ce ty (Name ann id) sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  stmt_state_rel ctx func ce cx es s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?v t. gas_value_prefix T (ctx,func,ce,cx) (ty,Name ann id)
    (sa,sb,op) (es,s0) [] (v,es,t)
Proof
  strip_tac >> drule_all body_name_wordtype_counted >> strip_tac >> gvs[] >>
  qexistsl [`entry.value`,
    `update_var out (typed_val_to_w256 entry.type entry.value)
      (s0 with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  simp[gas_value_prefix_def] >>
  conj_tac
  >- (simp[gas_marked_exec_def, gas_explicit_def, gas_marked_path_def] >>
      gen_tac >>
      qspecl_then [`cx`, `ann`, `id`, `es with gas_obs := tail`, `entry`]
        mp_tac eval_name_word >> simp[] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  conj_tac >- (irule body_name_wordtype_post >> simp[] >> metis_tac[]) >>
  simp[update_var_def]
QED

Theorem compile_name_wordtype_body_sim_mem:
  !ctx func ce cx env ty ann id es.
    expr_sim_pre ce cx env (Name ann id) es /\
    is_word_type ann /\ ~word_value_type ann ==>
    expr_sim_mem ctx func ce cx ty (Name ann id) es
Proof
  rpt strip_tac >> irule expr_sim_mem_word_values >>
  reverse conj_tac >- simp[vyperASTTheory.expr_type_def] >> rpt strip_tac >>
  drule_all body_name_wordtype_mem_prefix >> strip_tac >>
  qexistsl [`[]`, `v`, `es`, `t`] >> simp[]
QED
