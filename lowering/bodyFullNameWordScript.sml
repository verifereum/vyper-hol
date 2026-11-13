Theory bodyFullNameWord
Ancestors
  bodySimFull gasOutcomeFullCompose bodyFullGhostFrame
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
