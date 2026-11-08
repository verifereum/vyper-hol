Theory bodyPtrPopCaptureAllocation
Ancestors exprSimAlloc exprSimCopy compileEnv

Theorem pop_capture_alloc_buffer_run:
  compile_alloc_buffer sz sa = (buf,sm) /\ fn_has_code sa sm func /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ sz < dimword (:256) /\
  local_region cenv es.scopes s name lo capacity /\
  lo <= capture /\ capture + extent <= lo + capacity ==>
  ?t w. run_inst_seq (emitted_insts sa sm) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\
    eval_operand buf.buf_operand t = SOME w /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    w2n w + sz < dimword (:256) /\ t.vs_memory = s.vs_memory /\
    sa.cs_next_id < sm.cs_next_id /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n w) sz b len) /\
    (!n b len. local_region cenv es.scopes t n b len ==>
      regions_disjoint (w2n w) sz b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sm p) /\
    regions_disjoint (w2n w) sz capture extent
Proof
  strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `local_region cenv es.scopes t name lo capacity` by
    (drule_all copy_buffer_local_region_frame >> metis_tac[]) >>
  `regions_disjoint (w2n w) sz lo capacity` by metis_tac[] >>
  `regions_disjoint (w2n w) sz capture extent` by
    (fs[regions_disjoint_def] >> decide_tac) >>
  qexistsl_tac [`t`, `w`] >> simp[] >> metis_tac[]
QED
