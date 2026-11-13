Theory bodyFullNameWord
Ancestors
  bodySimFull gasOutcomeFullCompose bodyFullGhostFrame bodyPtrMakeArrayMloadFrame
  bodyNameWordMemory bodyNameWordTypeMemory bodyNameMemoryFacts
  exprSimSource exprSimHypsDefs exprSimNameValue exprSimNameWord
  exprSimProps entryDecodeStaticProps
  exprLoweringProps exprLowering loweringSlice loweringPosts bodyPtrDefs
  fragGasSeqPtr fragGasOriginPtr exprPtrCtorImmStore wordLoadStorePtr
  representationCleanPtr valueEncodingProps vyperStorageTrace
  venomExecSemantics venomInst venomState vyperInterpreter vyperState
  vyperAST vyperTyping finite_map list words emitHelper compileEnv fragExec
  instMemFrontier fragExecMem bodyMemoryDefs memSafeRun

Theorem name_word_ghost_inputs[local]:
  expr_sim_pre ce cx env (Name ann id) es /\ is_word_type ann /\
  stmt_state_rel H ctx func ce cx es s /\
  ghost_inv_at D lo d ce cx es G tn s ==>
  ?entry p sz w.
    lookup_scopes id es.scopes = SOME entry /\
    evaluate_type (get_tenv cx) ann = SOME entry.type /\
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\ ptr_covers G tn p s 32 /\
    mload (w2n w) s = typed_val_to_w256 entry.type entry.value /\
    (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem)
Proof
  strip_tac >> drule_all body_name_source_region >> strip_tac >>
  `type_memory_size entry.type = 32` by metis_tac[word_type_memory_size] >>
  `ptr_covers G tn p s sz /\
   !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory entry.type entry.value (w2n w) mem` by
    (gvs[ghost_inv_at_def] >> metis_tac[]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    mem_word_at (w2n w) mem = typed_val_to_w256 entry.type entry.value` by
    metis_tac[val_in_memory_word_type] >>
  drule robust_mem_word_at_clean >> strip_tac >>
  qexistsl [`entry`, `p`, `sz`, `w`] >>
  simp[] >> conj_tac >- (gvs[ptr_covers_def]) >>
  metis_tac[mem_word_at_eq_mload, mem_agree_outside_def]
QED

Theorem name_word_full_edge[local]:
  expr_sim_pre ce cx env (Name ann id) es /\ is_word_type ann /\
  stmt_state_rel H ctx func ce cx es s /\
  ghost_inv_at D lo d ce cx es G tn s /\ ~ctx_has_dalloca ctx /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  emit_op MLOAD [Var p] sa = (Var out,sb) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (update_var out (mload (w2n (THE (lookup_var p s))) s) s
         with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G (mk_inst sa.cs_next_id MLOAD [Var p] [out])
       (update_var out (mload (w2n (THE (lookup_var p s))) s) s),
     step_taint (mk_inst sa.cs_next_id MLOAD [Var p] [out]) s
       (update_var out (mload (w2n (THE (lookup_var p s))) s) s) tn)
Proof
  strip_tac >> drule_all name_word_ghost_inputs >> strip_tac >> gvs[] >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id MLOAD [Var p] [out]]` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_id_def, fresh_var_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  `inst_mem_below_frontier (mk_inst sa.cs_next_id MLOAD [Var p] [out]) s` by
    (drule_all body_name_source_region >> strip_tac >> gvs[] >>
     irule body_local_ptr_MLOAD_frontier >>
     goal_assum (drule_at Any) >> simp[] >>
     metis_tac[n2w_w2n, word_type_memory_size]) >>
  `allocas_from lo s` by gvs[ghost_inv_at_def] >>
  `ptr_inst_ok D lo 0 ctx func G tn
    (mk_inst sa.cs_next_id MLOAD [Var p] [out]) s` by
    (irule ptr_inst_ok_mload_lo >> simp[]) >>
  drule_at (Pat `ptr_inst_ok _ _ _ _ _ _ _ _ _`)
    straight_line_origin_ptr_edge >>
  simp[mk_inst_def, is_terminator_def, inst_dload_in_section_def,
       step_inst_base_opcode_eqs, exec_read1_def, eval_operand_def] >>
  metis_tac[]
QED

Theorem name_word_full_ghost_frame[local]:
  lower_value compile_expr ce ty (Name ann id) sa = (Var out,sb) /\
  emit_op MLOAD [Var p] sa = (Var out,sb) /\
  ghost_inv_at D lo d ce cx es G tn s /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ghost_inv_at D lo d ce cx (es with gas_obs := [])
    (step_prov PG G (mk_inst sa.cs_next_id MLOAD [Var p] [out]) (update_var out w s))
    (step_taint (mk_inst sa.cs_next_id MLOAD [Var p] [out]) s (update_var out w s) tn)
    (update_var out w s with vs_inst_idx := k) /\
  ghost_kept_at lo ce es sa G tn s
    (step_prov PG G (mk_inst sa.cs_next_id MLOAD [Var p] [out]) (update_var out w s))
    (step_taint (mk_inst sa.cs_next_id MLOAD [Var p] [out]) s (update_var out w s) tn)
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
         fresh_id_def, fresh_var_def, emit_def, loweringStateRelDefsTheory.not_fresh_at_def] >>
     rpt strip_tac >> gvs[]) >>
  conj_tac
  >- (irule ghost_inv_at_exterior_frame >>
      qexistsl_tac [`G`, `es`, `s`, `sa`, `tn`] >>
      simp[mload_ghost_frame, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
      metis_tac[mload_ghost_frame]) >>
  simp[ghost_kept_at_def, mload_ghost_frame] >> metis_tac[mload_ghost_frame]
QED

Theorem name_word_full:
  expr_body_pre cenv cx env (Name ann id) es /\ is_word_type ann ==>
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Name ann id) es
Proof
  rw[expr_sim_full_def] >>
  `expr_sim_pre cenv cx env (Name ann id) es` by
    simp[expr_sim_pre_body, vyperTypeCallGraphTheory.int_calls_expr_def] >>
  irule gas_outcome_full_initial_domain >>
  conj_tac >- simp[storage_trace_frame_bind, evaluate_storage_trace_frame,
                   storage_trace_frame_read_result] >>
  simp[] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace)
     es.storage_trace` by gvs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  first_assum drule >> strip_tac >>
  drule_all body_name_wordtype_counted >> strip_tac >>
  qmatch_asmsub_abbrev_tac `alloca_history func t` >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id MLOAD [Var p] [out]` >>
  qabbrev_tac `u = update_var out (typed_val_to_w256 entry.type entry.value) s0` >>
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`step_prov PG G0 inst u`, `es`, `INL entry.value`, `t`,
               `step_taint inst s0 u tn0`] >>
  conj_tac
  >- (gen_tac >> qspecl_then [`cx`, `ann`, `id`, `es with gas_obs := tail`, `entry`]
       mp_tac eval_name_word >> simp[vyperStateTheory.bind_def]) >>
  simp[] >> rpt strip_tac >>
  first_assum drule >> strip_tac >>
  all_tac >~ [`gas_origin_ptr_path _ _ _ _`]
  >- suspend "name_load_path" >>
  all_tac >~ [`expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`]
  >- (drule_all body_name_wordtype_post >>
      disch_then (qspec_then `entry.value` mp_tac) >>
      simp[Abbr `t`, Abbr `u`, update_var_def]) >>
  all_tac >~ [`expr_store_bound _ _ _ _ _`]
  >- simp[exprSimMemDefsTheory.expr_store_bound_def, vyperASTTheory.expr_type_def] >>
  qpat_x_assum `op = Var out` SUBST_ALL_TAC >>
  drule_all name_word_full_ghost_frame >>
  disch_then (qspecl_then [`typed_val_to_w256 entry.type entry.value`,
                          `LENGTH sb.cs_current_insts`, `PG`] strip_assume_tac) >>
  fs[Abbr `t`, Abbr `u`, Abbr `inst`, update_var_def, vyperASTTheory.expr_type_def] >>
  drule_all name_word_ghost_inputs >> strip_tac >> gvs[] >>
  simp[ptr_val_ok_def] >>
  conj_tac
  >- (qpat_x_assum `mload _ _ = _` (SUBST1_TAC o SYM) >>
      irule (SRULE [update_var_def] (cj 1 mload_ghost_clean)) >>
      simp[eval_operand_def] >> goal_assum (drule_at Any) >> simp[]) >>
  simp[ptrDisciplineTheory.step_prov_def, ptrDisciplineTheory.op_prov_def,
       ptrDisciplineTheory.set_prov_def, ptrDisciplineTheory.out_prov_def, mk_inst_def,
       FLOOKUP_DRESTRICT]
QED

Resume name_word_full[name_load_path]:
  drule_all name_word_ghost_inputs >> strip_tac >> gvs[] >>
  `LENGTH sb.cs_current_insts = SUC s0.vs_inst_idx` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_id_def, fresh_var_def, emit_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule_all name_word_full_edge >>
  simp[Abbr `t`, Abbr `inst`, Abbr `u`, update_var_def] >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`, `PG`] assume_tac) >>
  once_rewrite_tac[GSYM APPEND_NIL] >>
  irule (cj 2 gas_origin_ptr_path_rules) >>
  pure_rewrite_tac[APPEND_NIL] >>
  goal_assum (drule_at Any) >> simp[gas_origin_ptr_path_rules]
QED

Finalise name_word_full
