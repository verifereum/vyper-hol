Theory bodyAppendStorageStaging
Ancestors
  localMemoryStorePath placeMemoryStaging exprSimOperands exprSimAlloc loweringHalt abiTupleProps
  context exprLoweringProps compileEnv loweringStateRelDefs venomExecSemantics
  venomState venomInst emitHelper fragExec rich_list instIdxIndep finite_map

Theorem append_storage_aggregate_staging_bounded_path:
  compile_alloc_buffer n sb = (buf,sc) /\
  compile_store_memory cenv raw buf.buf_operand elem elem sc = ((),sd) /\
  n = type_memory_bytes cenv elem /\ 0 < n /\ n < dimword (:256) /\
  ~is_word_type elem /\ ~is_bytestring_type elem /\
  val_wf tv v /\ val_in_memory tv v (w2n sw) s.vs_memory /\
  val_footprint tv v <= n /\ eval_operand raw s = SOME sw /\
  (!x. raw = Var x ==> not_fresh_at sb x) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func cenv cx ee s) /\ local_ptrs_reserved cenv sb /\
  fn_inst_ids_distinct func /\ fn_has_code sb sd func /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?u w. gas_marked_path F ctx func s 0 (OK u) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee u) /\
    eval_operand buf.buf_operand u = SOME w /\
    val_in_memory tv v (w2n w) u.vs_memory /\
    (!x. not_fresh_at sb x ==> lookup_var x u = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                 FLOOKUP u.vs_allocas aid = SOME entry) /\
    ~u.vs_halted /\ u.vs_current_bb = sd.cs_current_bb /\
    u.vs_inst_idx = LENGTH sd.cs_current_insts /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sd p) /\
    w2n w + n < dimword (:256)
Proof
  strip_tac >>
  `cs_extends sb sc` by metis_tac[compile_alloc_buffer_extends] >>
  `compile_copy_memory buf.buf_operand raw n sc = ((),sd)` by
    gvs[compile_store_memory_def] >>
  `cs_extends sc sd` by
    (drule_all compile_copy_memory_extends >> strip_tac >>
     gvs[same_blocks_def] >> irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  qabbrev_tac `p = STRING #"%" (toString sb.cs_next_var)` >>
  qabbrev_tac `pre = sb with cs_next_var := sb.cs_next_var + 1` >>
  `buf.buf_operand = Var p /\
   emit_inst ALLOCA [Lit (n2w n)] [p] pre = ((),sc)` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, emit_inst_def,
          comp_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
          emit_def, comp_ignore_bind_def, Abbr `p`, Abbr `pre`] >>
     strip_tac >> gvs[]) >>
  `~not_fresh_at sb p` by simp[not_fresh_at_def, Abbr `p`] >>
  `raw <> Var p` by metis_tac[] >>
  `not_local_ptr cenv ee.scopes p` by metis_tac[fresh_not_local_ptr] >>
  `emit_void MCOPY [Var p; raw; Lit (n2w n)] sc = ((),sd)` by
    (Cases_on `n` >> gvs[compile_copy_memory_def]) >>
  `fn_has_code pre sc func /\
   MEM (mk_inst pre.cs_next_id ALLOCA [Lit (n2w n)] [p]) (fn_insts func) /\
   s.vs_current_bb = pre.cs_current_bb /\
   s.vs_inst_idx = LENGTH pre.cs_current_insts` by
    gvs[Abbr `pre`, fn_has_code_def, emitted_blocks_def] >>
  qspecl_then [`cx`, `st0`, `ctx`, `func`, `cenv`, `ee`, `pre`, `sc`,
    `sd`, `s`, `p`, `raw`, `n`, `sw`, `tv`, `v`]
    mp_tac alloc_copy_memory_framed_bounded_path >>
  impl_tac >- (asm_rewrite_tac[] >> qexists_tac `H` >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  `not_fresh_at sd p` by
    (qpat_x_assum `emit_inst ALLOCA _ _ _ = _` mp_tac >>
     simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def,
          comp_ignore_bind_def, comp_return_def, Abbr `pre`] >>
     strip_tac >>
     qpat_x_assum `emit_void MCOPY _ _ = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, fresh_id_def, emit_def,
          comp_ignore_bind_def, comp_return_def] >>
     strip_tac >> gvs[not_fresh_at_def, Abbr `p`] >> decide_tac) >>
  qexistsl_tac [`s2`, `w`] >> simp[eval_operand_def] >> metis_tac[]
QED

Theorem append_storage_aggregate_staging_path:
  compile_alloc_buffer n sb = (buf,sc) /\
  compile_store_memory cenv raw buf.buf_operand elem elem sc = ((),sd) /\
  n = type_memory_bytes cenv elem /\ 0 < n /\ n < dimword (:256) /\
  ~is_word_type elem /\ ~is_bytestring_type elem /\
  val_wf tv v /\ val_in_memory tv v (w2n sw) s.vs_memory /\
  val_footprint tv v <= n /\ eval_operand raw s = SOME sw /\
  (!x. raw = Var x ==> not_fresh_at sb x) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func cenv cx ee s) /\ local_ptrs_reserved cenv sb /\
  fn_inst_ids_distinct func /\ fn_has_code sb sd func /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?u w. gas_marked_path F ctx func s 0 (OK u) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee u) /\
    eval_operand buf.buf_operand u = SOME w /\
    val_in_memory tv v (w2n w) u.vs_memory /\
    (!x. not_fresh_at sb x ==> lookup_var x u = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                 FLOOKUP u.vs_allocas aid = SOME entry) /\
    ~u.vs_halted /\ u.vs_current_bb = sd.cs_current_bb /\
    u.vs_inst_idx = LENGTH sd.cs_current_insts /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sd p)
Proof
  strip_tac >>
  drule_all (SRULE [PULL_EXISTS] append_storage_aggregate_staging_bounded_path) >>
  disch_then (qx_choosel_then [`u`, `w`] strip_assume_tac) >>
  qexistsl_tac [`u`, `w`] >> simp[]
QED
