(* Memory-safe compilation of local names. *)
Theory bodyNameWordMemory
Ancestors
  bodyNameMemoryFacts
  exprSimSource exprSimHypsDefs exprSimDefs exprSimProps bodyMemoryDefs
  exprSimMemoryValues exprSimMemoryStack fragGasSeqMem fragGasPathMem
  gasNormalPrefix gasSummary gasContext gasCount fragGasMode loweringPosts
  exprSimNameWord exprSimNameValue loweringSlice exprLowering exprLoweringProps
  fragExec fragExecMem allocaHistoryFragment instMemFrontier
  emitHelperProps emitHelper compileEnv context venomInst venomState
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

Theorem compile_name_word_body_sim_mem:
  !ctx func ce cx env ty ann id es.
    expr_sim_pre ce cx env (Name ann id) es /\ word_value_type ann ==>
    expr_sim_mem ctx func ce cx ty (Name ann id) es
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

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_NAME_MEMORY_AUDIT OK\n"
     else raise Fail "memory source fact inherited admission"
  end) [compile_name_word_body_sim_mem];
