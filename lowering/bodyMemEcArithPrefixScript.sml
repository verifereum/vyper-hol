Theory bodyMemEcArithPrefix
Ancestors
  exprSimAlloc loweringHalt fragExecMem instMemFrontier emitHelperProps exprLoweringProps compileEnv fragExec
  bodyLiteralBufferMemory allocaHistoryFragment

Theorem ec_alloc_buffer_mem_ok:
  compile_alloc_buffer sz sa = (buf,sm) ==>
  run_inst_seq_mem_ok (emitted_insts sa sm) s
Proof
  strip_tac >> drule compile_alloc_buffer_insts >> strip_tac >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1,
       run_inst_seq_mem_ok_last] >>
  irule below_frontier_no_ranges >> simp[]
QED

Theorem ec_alloc_buffer_frontier:
  compile_alloc_buffer sz sa = (buf,sm) /\
  run_inst_seq (emitted_insts sa sm) s = OK t ==>
  s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >> drule compile_alloc_buffer_insts >> strip_tac >>
  gvs[emitted_insts_def, rich_listTheory.DROP_APPEND1] >>
  drule literal_alloca_frontier >> simp[]
QED

Theorem ec_alloc_buffer_endpoint:
  compile_alloc_buffer sz sa = (buf,sm) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  sz < dimword (:256) /\ alloca_history func s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sm) s = OK t ==>
  (?w. eval_operand buf.buf_operand t = SOME w /\
       w2n w + sz <= t.vs_alloca_next) /\
  alloca_history func (t with vs_inst_idx := LENGTH sm.cs_current_insts)
Proof
  strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
     [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    metis_tac[buffer_alloc_code] >>
  drule_all literal_alloc_buffer_run >> strip_tac >> gvs[] >>
  conj_tac
  >- (irule alloca_region_below_frontier >>
      conj_tac >- gvs[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def] >>
      qexistsl [`sa.cs_next_id`, `w2n w`, `sz`] >> simp[]) >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  gvs[fn_has_code_def] >>
  gvs[rich_listTheory.IS_PREFIX_APPEND] >>
  `alloca_inv s` by gvs[stmt_state_rel_def] >>
  qpat_assum `run_inst_seq _ s = OK t`
    (mp_then Any mp_tac alloca_history_run_inst_seq) >>
  disch_then (qspecl_then [`func`, `bb`] mp_tac) >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1] >>
  disch_then irule >> simp[venomInstTheory.is_terminator_def]
QED
