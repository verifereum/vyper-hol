Theory bodyPtrMakeArrayAllocCursor
Ancestors
  bodyPtrMakeArrayAllocBuffer exprSimAlloc exprLoweringProps compileEnv
  venomState venomInst venomExecSemantics ptrDiscipline fragExec
  emitHelperProps finite_map words

Theorem literal_alloc_buffer_cursor_run:
  compile_alloc_buffer sz sa = (buf,sm) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ sz < dimword (:256) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?a w H tm.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK a) /\
    stmt_state_rel ctx func cenv cx es a /\
    eval_operand buf.buf_operand a = SOME w /\
    FLOOKUP a.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    w2n w + sz < dimword (:256) /\ a.vs_memory = s.vs_memory /\
    sa.cs_next_id < sm.cs_next_id /\
    (!x. not_fresh_at sa x ==>
      lookup_var x a = lookup_var x s /\
      op_prov H (Var x) = op_prov G (Var x) /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP a.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n w) sz b len) /\
    (!name b len. local_region cenv es.scopes a name b len ==>
      regions_disjoint (w2n w) sz b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sm p /\ ptr_covers H tm p a sz) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!i. i < w2n w \/ w2n w+sz <= i ==> (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    a.vs_current_bb = s.vs_current_bb /\ a.vs_inst_idx = SUC s.vs_inst_idx /\
    a.vs_halted = s.vs_halted /\ a.vs_labels = s.vs_labels /\
    a.vs_data_section = s.vs_data_section /\ a.vs_immutables = s.vs_immutables /\
    a.vs_fmp = s.vs_fmp /\ a.vs_call_ctx = s.vs_call_ctx /\
    a.vs_accounts = s.vs_accounts /\ a.vs_transient = s.vs_transient
Proof
  strip_tac >> drule_all literal_alloc_buffer_ptr_run >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  drule alloc_buffer_emitted >> strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]) s = OK u` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  drule literal_alloca_static_frame >> strip_tac >>
  drule_all literal_alloca_old_ghost >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  drule_all literal_alloca_exterior_taint >> strip_tac >>
  `!x. not_fresh_at sa x ==> x <> STRING #"%" (toString sa.cs_next_var)` by
    metis_tac[alloc_buffer_root_fresh] >>
  qexistsl_tac [`u with vs_inst_idx := SUC s.vs_inst_idx`, `w`, `G1`, `tn1`] >>
  gvs[stmt_state_rel_inst_idx, eval_operand_def, lookup_var_def,
      local_region_def, op_prov_def] >>
  metis_tac[]
QED
