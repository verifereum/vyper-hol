(* Memory-safe compilation of local names. *)
Theory bodyNameWordMemory
Ancestors
  bodyNameMemoryFacts
  exprSimSource exprSimHypsDefs exprSimDefs exprSimProps bodyMemoryDefs
  exprSimMemoryValues exprSimMemoryStack fragGasSeqMem fragGasPathMem
  gasNormalPrefix gasSummary gasContext gasCount fragGasMode loweringPosts
  exprSimNameWord exprSimNameValue loweringSlice exprLowering exprLoweringProps
  fragExec fragExecMem allocaHistoryFragment instMemFrontier
  emitHelperProps emitHelper compileEnv loweringStateRelDefs context venomInst venomState
  venomExecSemantics venomMemDefs vyperInterpreter vyperState vyperAST
  vyperTypeEnv vyperTypeSystem vyperTypeInvariants valueEncoding valueEncodingProofs
  list rich_list finite_map words arithmetic

Theorem body_name_load_history[local]:
  emit_op MLOAD [Var p] sa = (op,sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  rpt strip_tac >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_id_def, fresh_var_def, emit_def,
         emitted_insts_def, fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, mk_inst_def, is_terminator_def]) >>
  drule_all alloca_history_run_inst_seq >> simp[]
QED

Theorem body_name_word_counted:
  expr_sim_pre ce cx env (Name ann id) es /\ word_value_type ann /\
  lower_value compile_expr ce ty (Name ann id) sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?entry p sz out.
    lookup_scopes id es.scopes = SOME entry /\
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
    word_value entry.value /\ op = Var out /\
    emit_op MLOAD [Var p] sa = (Var out,sb) /\
    sb.cs_current_bb = sa.cs_current_bb /\
    gas_path_mem ctx func s0 0
      (OK (update_var out (val_to_w256 entry.value)
        (s0 with vs_inst_idx := LENGTH sb.cs_current_insts))) /\
    alloca_history func (update_var out (val_to_w256 entry.value)
      (s0 with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >> drule_all body_word_name_region >> strip_tac >>
  `is_word_type ann` by metis_tac[word_value_type_word] >>
  drule_all lower_value_name_word >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  drule_all step_name_word >> strip_tac >>
  `run_inst_seq (emitted_insts sa sb) s0 =
    OK (update_var out (val_to_w256 entry.value) s0)` by
    simp[run_inst_seq_def, Abbr `out`] >>
  `alloca_inv s0` by gvs[stmt_state_rel_def] >>
  drule_all body_name_load_history >> strip_tac >>
  `(?bb rest. lookup_block s0.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s0.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest) /\
    s0.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    (fs[fn_has_code_def, IS_PREFIX_APPEND, same_blocks_def] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, mk_inst_def] >> metis_tac[]) >>
  `gas_path_mem ctx func s0 0
    (OK ((update_var out (val_to_w256 entry.value) s0)
      with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (drule_at (Pos last) run_inst_seq_gas_path_mem >>
     disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
     simp[IS_PREFIX_APPEND, run_inst_seq_mem_ok_last, GSYM mk_inst_def,
          is_terminator_def] >>
     (impl_tac >- (irule body_word_name_MLOAD_frontier >> metis_tac[])) >>
     simp[]) >>
  qexistsl [`entry`, `p`, `sz`, `out`] >>
  gvs[Abbr `out`, same_blocks_def, update_var_def]
QED

Theorem body_name_word_mem_prefix[local]:
  expr_sim_pre ce cx env (Name ann id) es /\ word_value_type ann /\
  lower_value compile_expr ce ty (Name ann id) sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  stmt_state_rel ctx func ce cx es s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?v t. gas_value_prefix T (ctx,func,ce,cx) (ty,Name ann id)
    (sa,sb,op) (es,s0) [] (v,es,t)
Proof
  strip_tac >> drule_all body_name_word_counted >> strip_tac >> gvs[] >>
  `is_word_type ann` by metis_tac[word_value_type_word] >>
  qexistsl [`entry.value`,
    `update_var out (val_to_w256 entry.value)
      (s0 with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  simp[gas_value_prefix_def] >>
  conj_tac
  >- (simp[gas_marked_exec_def, gas_explicit_def, gas_marked_path_def] >>
      gen_tac >>
      qspecl_then [`cx`, `ann`, `id`, `es with gas_obs := tail`, `entry`]
        mp_tac eval_name_word >> simp[] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  conj_tac >- (irule name_word_post >> simp[] >> metis_tac[]) >>
  simp[update_var_def]
QED

Theorem compile_name_word_body_sim_mem:
  !ctx func ce cx env ty ann id es.
    expr_sim_pre ce cx env (Name ann id) es /\ word_value_type ann ==>
    expr_sim_mem ctx func ce cx ty (Name ann id) es
Proof
  rpt strip_tac >> irule expr_sim_mem_word_values >> reverse conj_tac
  >- (simp[vyperASTTheory.expr_type_def] >>
      metis_tac[word_value_type_word]) >>
  rpt strip_tac >>
  drule_all body_name_word_mem_prefix >> strip_tac >>
  qexistsl [`[]`, `v`, `es`, `t`] >> simp[]
QED

(* Prior proof, preserved verbatim; not checked against the counted schema.
Proof
  rpt strip_tac >> simp[expr_sim_mem_def] >> rpt strip_tac >>
  `?entry. lookup_scopes id es.scopes = SOME entry /\
           evaluate_type (get_tenv cx) ann = SOME entry.type /\
           value_has_type entry.type entry.value` by
    (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
     drule_all well_typed_Name_lookup >> strip_tac >>
     gvs[env_consistent_def, env_context_consistent_def]) >>
  `?p sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  `word_value entry.value` by metis_tac[word_value_type_typed] >>
  `is_word_type ann` by metis_tac[word_value_type_word] >>
  drule_all lower_value_name_word >> strip_tac >>
  drule_then (qspecl_then [`cx`, `ann`] assume_tac) eval_name_word >> gvs[] >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >> metis_tac[LESS_EQ_REFL]) >>
  `not_local_ptr ce es.scopes out` by
    (qunabbrev_tac `out` >> irule local_ptrs_reserved_fresh >> metis_tac[LESS_EQ_REFL]) >>
  fs[same_blocks_def] >>
  irule frag_exec_mem_run_inst_seq_at_cursor >>
  simp[IS_PREFIX_APPEND3, mk_inst_def, is_terminator_def] >>
  rpt strip_tac >> gvs[]
  >- (simp[GSYM mk_inst_def, run_inst_seq_mem_ok_last] >>
      irule body_word_name_MLOAD_frontier >> metis_tac[]) >>
  drule_all step_name_word >> strip_tac >>
  qexists_tac `update_var out (val_to_w256 entry.value) s0` >>
  simp[GSYM mk_inst_def, run_inst_seq_def] >>
  reverse conj_tac
  >- (`alloca_history func
        (update_var out (val_to_w256 entry.value) s0 with
         vs_inst_idx := LENGTH sb.cs_current_insts)` suffices_by simp[] >>
      irule body_name_load_history >> simp[Once CONJ_ASSOC] >>
      qexistsl [`Var out`, `p`, `s0`, `sa`] >>
      simp[run_inst_seq_def] >> fs[stmt_state_rel_def]) >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       vyperASTTheory.expr_type_def, typed_val_to_w256_word_value,
       locals_kept_mem, stmt_state_rel_inst_idx] >>
  conj_tac
  >- (irule stmt_state_rel_update_var >> simp[]) >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `out = x` >> gvs[] >>
  irule locals_kept_mem >> simp[]
QED
*)

