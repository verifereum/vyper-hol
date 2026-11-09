Theory bodyPtrStructLitAllocationBridge
Ancestors bodyPtrStructLitFreshAlloc bodyPtrStructLitAllocEntry allocationPtr
  exprSimAlloc exprSimProps abiBuiltinAllocation emitHelperProps exprLoweringProps
  context emitHelper compileEnv finite_map words fragExec loweringHalt
  bodyPtrStructLitAlloc ptrDiscipline venomState bodyPtrDefs

Theorem structlit_alloc_buffer_cursor:
  compile_alloc_buffer N sa = (buf,sm) ==>
  sm.cs_current_bb = sa.cs_current_bb /\
  sm.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)]
      [STRING #"%" (toString sa.cs_next_var)]] /\
  buf.buf_operand = Var (STRING #"%" (toString sa.cs_next_var))
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> simp[] >>
  gvs[emit_op_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def]
QED

Theorem structlit_alloc_buffer_instruction:
  compile_alloc_buffer N sa = (buf,sm) /\ fn_has_code sa sm fn ==>
  ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) =
      SOME (mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)]
        [STRING #"%" (toString sa.cs_next_var)])
Proof
  strip_tac >> drule structlit_alloc_buffer_cursor >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qexists `bb` >> simp[] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED

Theorem structlit_alloc_buffer_base_step:
  compile_alloc_buffer N sa = (buf,sm) ==>
  run_inst_seq (emitted_insts sa sm) s =
    step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)]
      [STRING #"%" (toString sa.cs_next_var)]) s
Proof
  strip_tac >> drule structlit_alloc_buffer_cursor >> strip_tac >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND, run_inst_seq_def] >>
  CASE_TAC >> simp[]
QED

Theorem structlit_local_footprint_bound:
  stmt_state_rel ctx fn ce cx es s /\
  lookup_scopes name es.scopes = SOME entry /\
  FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w ==>
  val_wf entry.type entry.value /\
  w2n w + val_footprint entry.type entry.value <= s.vs_alloca_next
Proof
  strip_tac >>
  `local_ptrs_rel fn ce es.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  fs[local_ptrs_rel_def] >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  drule val_footprint_le >> strip_tac >> simp[] >> decide_tac
QED

Theorem structlit_alloc_buffer_ghost:
  stmt_state_rel ctx fn ce cx es s /\ ghost_inv d ce cx es G tn s /\
  local_ptrs_reserved ce sa /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  N < dimword (:256) /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)]
    [STRING #"%" (toString sa.cs_next_var)]) s = OK u ==>
  ghost_inv d ce cx es
    (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)]
      [STRING #"%" (toString sa.cs_next_var)]) u)
    (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)]
      [STRING #"%" (toString sa.cs_next_var)]) s u tn)
    (u with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `~not_fresh_at sa (STRING #"%" (toString sa.cs_next_var))` by
    simp[not_fresh_at_def] >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
  >- (irule structlit_fresh_alloca_ghost_inv >> simp[] >>
      reverse conj_tac >- (qexists `sa` >> simp[]) >>
      rpt gen_tac >> strip_tac >> drule_all structlit_local_footprint_bound >> simp[]) >>
  rename1 `FLOOKUP s.vs_allocas sa.cs_next_id = SOME site` >>
  PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >>
  disch_then (qspec_then `STRING #"%" (toString sa.cs_next_var)` assume_tac) >>
  gvs[] >> irule structlit_reused_alloca_ghost_inv >> simp[] >>
  fs[local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem structlit_alloc_buffer_ptr_entry:
  compile_alloc_buffer N sa = (buf,sm) /\
  stmt_state_rel ctx fn ce cx es s /\ ghost_inv d ce cx es G tn s /\
  fn_has_code sa sm fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sa /\ N < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  ?u t G1 tn1 p w.
    run_inst_seq (emitted_insts sa sm) s = OK u /\
    t = u with vs_inst_idx := SUC s.vs_inst_idx /\
    buf.buf_operand = Var p /\ not_fresh_at sm p /\
    G1 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)] [p]) u /\
    tn1 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)] [p]) s u tn /\
    gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G1 tn1 (OK t) /\
    stmt_state_rel ctx fn ce cx es t /\ ghost_inv d ce cx es G1 tn1 t /\
    ptr_covers G1 tn1 p t N /\ eval_operand buf.buf_operand t = SOME w /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,N) /\
    w2n w + N < dimword (:256) /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts
Proof
  strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  drule structlit_alloc_buffer_base_step >> disch_then (qspec_then `s` assume_tac) >>
  drule structlit_alloc_buffer_cursor >> strip_tac >>
  drule_all structlit_alloc_buffer_instruction >> strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)]
     [STRING #"%" (toString sa.cs_next_var)]) s = OK t` by metis_tac[] >>
  drule_all structlit_alloc_buffer_ghost >> strip_tac >>
  drule_all alloca_step_ptr_covers >> strip_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx = SOME (mk_inst sa.cs_next_id ALLOCA
     [Lit (n2w N)] [STRING #"%" (toString sa.cs_next_var)])` by simp[] >>
  drule_all structlit_alloca_counted_edge >> strip_tac >>
  qspecl_then [`sa.cs_next_id`, `n2w N`,
    `STRING #"%" (toString sa.cs_next_var)`, `s`] strip_assume_tac step_alloca_frame >>
  gvs[] >>
  fs[stmt_state_rel_inst_idx, ptr_covers_def, eval_operand_def, lookup_var_def] >>
  metis_tac[]
QED
