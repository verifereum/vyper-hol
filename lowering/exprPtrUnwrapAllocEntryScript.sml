(* One allocation endpoint shared by source transfer and pointer execution. *)
Theory exprPtrUnwrapAllocEntry
Ancestors
  exprPtrUnwrapAllocation exprPtrUnwrapAllocationFrame exprPtrUnwrapAllocSeparation
  bufferAllocationExecution exprSimAlloc loweringPosts exprLoweringProps
  fragGasSeqPtr fragGasSeqAbort fragExec fragExecMem allocaHistory
  ptrDiscipline ptrSafeRun bodyPtrDefs venomState venomInst finite_map words
  compileEnv loweringStateRelDefs fragGasPathPtr stmtAppendStorageRunPtr exprPtrUnwrapStorageSource

Theorem unwrap_alloc_origin_path:
  compile_alloc_buffer nb sm = (buf,mid) /\ fn_has_code sm mid func /\
  stmt_state_rel H ctx func cenv cx es s /\ nb < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?out u.
    buf.buf_operand = Var out /\
    step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [out]) s = OK u /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
       step_prov PG G (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [out]) u,
       step_taint (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [out]) s u tn)
Proof
  strip_tac >> drule_all unwrap_alloc_generated_step >>
  disch_then (qspec_then `s` strip_assume_tac) >>
  qexistsl [`out`, `update_var out (n2w (buffer_allocation_base s sm.cs_next_id))
    (buffer_allocation_fields s sm.cs_next_id nb)`] >>
  simp[] >>
  qmatch_asmsub_abbrev_tac `step_inst_base inst s = OK u` >>
  drule_all unwrap_alloc_code_prefix >> strip_tac >>
  qpat_x_assum `s.vs_inst_idx = _` (fn th => rewrite_tac[GSYM th]) >>
  qspec_then `[inst]` mp_tac run_inst_seq_gas_origin_ptr_path >>
  simp[Abbr `inst`, mk_inst_def, is_terminator_def, arithmeticTheory.ADD1] >>
  disch_then irule >>
  simp[run_inst_seq_def, GSYM mk_inst_def] >>
  conj_tac
  >- (simp[run_inst_seq_mem_ok_def, unitTransformDefsTheory.inst_mem_below_frontier_def,
      memSafeRunTheory.inst_dload_in_section_def, mk_inst_def,
      contextCodegenRelTheory.source_memory_read_ranges_def,
      codegenRelTheory.source_memory_write_ranges_def]) >>
  conj_tac
  >- gvs[] >>
  simp[inst_seq_ptr_def] >>
  irule unwrap_alloc_ptr_check >>
  simp[] >>
  simp[Abbr `u`, update_var_def,
    bufferAllocationExecutionTheory.buffer_allocation_fields_def] >>
  Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id` >> simp[]
QED

Theorem unwrap_alloc_origin_history:
  compile_alloc_buffer nb sa = (buf,sm) /\ buf.buf_operand = Var root /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  stmt_state_rel H ctx func cenv cx es s /\ alloca_history func s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u ==>
  alloca_history func (u with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> drule_all unwrap_alloc_code_prefix >> strip_tac >>
  drule unwrap_alloc_generated_code >> strip_tac >>
  `out = root` by fs[] >>
  qpat_x_assum `out = root` SUBST_ALL_TAC >>
  qpat_x_assum `isPREFIX _ _` mp_tac >>
  asm_rewrite_tac[] >> disch_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  qpat_x_assum `get_instruction _ _ = _` mp_tac >>
  qpat_assum `s.vs_inst_idx = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_assum `root = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  disch_tac >>
  drule_all allocaHistoryTheory.alloca_history_base_step >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem unwrap_alloc_entry:
  compile_alloc_buffer nb sm = (buf,mid) /\ fn_has_code sm mid func /\
  stmt_state_rel H ctx func cenv cx es s /\ nb < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?out u Gf tnf a.
    buf.buf_operand = Var out /\ buf.buf_size = nb /\
    out = STRING #"%" (toString sm.cs_next_var) /\
    u = update_var out (n2w (buffer_allocation_base s sm.cs_next_id))
      (buffer_allocation_fields s sm.cs_next_id nb) /\
    step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [out]) s = OK u /\
    Gf = step_prov PG G (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [out]) u /\
    tnf = step_taint (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [out]) s u tn /\
    a = u with vs_inst_idx := SUC s.vs_inst_idx /\
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK a) /\
    a.vs_current_bb = mid.cs_current_bb /\
    a.vs_inst_idx = LENGTH mid.cs_current_insts /\
    ptr_covers Gf tnf out a nb /\
    eval_operand buf.buf_operand a = SOME (n2w (buffer_allocation_base s sm.cs_next_id))
Proof
  strip_tac >> drule_all unwrap_alloc_code_prefix >> strip_tac >>
  `allocas_from 0 s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s)` by
    simp[allocas_from_def] >>
  drule_all unwrap_alloc_counted_edge >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  drule unwrap_alloc_generated_code >> strip_tac >> gvs[] >>
  drule_all unwrap_alloc_generated_step >>
  disch_then (qspec_then `s` strip_assume_tac) >> gvs[] >>
  simp[] >> conj_tac
  >- (drule unwrap_alloc_current_block >>
      simp[buffer_allocation_fields_def, update_var_def] >>
      Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id` >> simp[]) >>
  conj_tac
  >- (drule_all unwrap_alloc_output_coverage >> simp[]) >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem unwrap_alloc_old_operand_ghost:
  step_inst_base (mk_inst id ALLOCA [Lit (n2w nb)] [out]) s = OK u /\
  (!p. src = Var p ==> p <> out) ==>
  eval_operand src (u with vs_inst_idx := k) = eval_operand src s /\
  op_taint (step_taint (mk_inst id ALLOCA [Lit (n2w nb)] [out]) s u tn) src =
    op_taint tn src /\
  op_prov (step_prov PG G (mk_inst id ALLOCA [Lit (n2w nb)] [out]) u) src =
    op_prov G src
Proof
  strip_tac >> conj_tac
  >- (irule unwrap_alloc_operand_frame >> metis_tac[]) >>
  Cases_on `src` >> gvs[] >>
  simp[scalar_step_old_taint, op_prov_def, scalar_step_old_prov, op_taint_def]
QED

Theorem unwrap_alloc_storage_source:
  compile_alloc_buffer nb sm = (buf,mid) /\ fn_has_code sm mid func /\
  stmt_state_rel H ctx func cenv cx es s /\ nb < dimword (:256) /\
  buf.buf_operand = Var out /\
  u = update_var out (n2w (buffer_allocation_base s sm.cs_next_id))
      (buffer_allocation_fields s sm.cs_next_id nb) /\
  step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [out]) s = OK u /\
  (!x. p.ptr_operand = Var x ==> x <> out) /\ p.ptr_location = slot_loc tr /\
  ptr_vv_ok cx t tv (LocatedValue t' p) es G tn s ==>
  eval_operand p.ptr_operand (u with vs_inst_idx := k) = eval_operand p.ptr_operand s /\
  ptr_vv_ok cx t tv (LocatedValue t' p) es
    (step_prov PG G (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [out]) u)
    (step_taint (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [out]) s u tn)
    (u with vs_inst_idx := k)
Proof
  strip_tac >>
  `eval_operand p.ptr_operand (u with vs_inst_idx := k) = eval_operand p.ptr_operand s` by
    (irule unwrap_alloc_operand_frame >> metis_tac[]) >>
  simp[] >> irule ptr_vv_ok_storage_frame >>
  (conj_tac >- metis_tac[]) >>
  qexistsl [`G`, `s`, `tn`] >> simp[] >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [out]) (fn_insts func)` by
    (drule_all buffer_alloc_code >> strip_tac >>
     drule unwrap_alloc_generated_code >> strip_tac >> gvs[]) >>
  drule_all unwrap_alloc_taint_frame >>
  disch_then (qspec_then `tn` strip_assume_tac) >>
  drule unwrap_alloc_runtime_frame >>
  disch_then (qspec_then `k` strip_assume_tac) >> simp[] >>
  drule_all unwrap_alloc_old_operand_ghost >> simp[] >> gvs[]
QED

Theorem unwrap_alloc_old_operand_distinct:
  compile_alloc_buffer nb sm = (buf,mid) /\ buf.buf_operand = Var out /\
  (!x. src = Var x ==> not_fresh_at sm x) ==>
  !x. src = Var x ==> x <> out
Proof
  strip_tac >> drule unwrap_alloc_generated_code >> strip_tac >>
  gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED
