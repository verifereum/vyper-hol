Theory bodyPtrPrecompileBuiltinsRunWitnesses
Ancestors exprSimPrecompiles exprSimLiteralBuffer exprSimWordArgs compileEnv
          bodyPtrPrecompileBuiltinsRunAllocation

Theorem allocated_payload_run_witnesses:
  context$compile_alloc_buffer insz sf = (ib,sa) /\
  context$compile_alloc_buffer outsz sb = (ob,sm) /\
  emitted_insts sf sm = emitted_insts sf sa ++ code ++ emitted_insts sb sm /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sb /\
  insz < dimword (:256) /\ outsz < dimword (:256) /\
  MEM (mk_inst sf.cs_next_id ALLOCA [Lit (n2w insz)]
    [STRING #"%" (toString sf.cs_next_var)]) (fn_insts func) /\
  MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w outsz)]
    [STRING #"%" (toString sb.cs_next_var)]) (fn_insts func) /\
  sa.cs_next_id <= sb.cs_next_id /\
  sf.cs_next_var <= sa.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var /\
  (!s1 wi.
    run_inst_seq (emitted_insts sf sa) s = OK s1 /\
    stmt_state_rel ctx func cenv cx es s1 /\
    eval_operand ib.buf_operand s1 = SOME wi /\
    FLOOKUP s1.vs_allocas sf.cs_next_id = SOME (w2n wi,insz) /\
    w2n wi + insz < dimword (:256) /\ s1.vs_memory = s.vs_memory /\
    wb_frame cenv es sf s s1 /\ s1.vs_labels = s.vs_labels /\
    (!name b len. local_region cenv es.scopes s1 name b len ==>
      regions_disjoint (w2n wi) insz b len) /\
    (!aid b len. aid < sf.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n wi) insz b len) /\
    (!aid b len. aid < sf.cs_next_id /\
      FLOOKUP s1.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n wi) insz b len) /\
    (!x. not_fresh_at sf x ==> lookup_var x s1 = lookup_var x s) ==>
    ?u. run_inst_seq code s1 = OK u /\ stmt_state_rel ctx func cenv cx es u /\
      wb_frame cenv es sf s1 u /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s1) /\
      FLOOKUP u.vs_allocas sf.cs_next_id = SOME (w2n wi,insz) /\
      eval_operand ib.buf_operand u = SOME wi /\
      mem_bytes_at (w2n wi) insz u.vs_memory = bytes) ==>
  ?t pi po s1 u.
    run_inst_seq (emitted_insts sf sm) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sf s t /\
    eval_operand ib.buf_operand t = SOME pi /\
    eval_operand ob.buf_operand t = SOME po /\
    w2n pi + insz < dimword (:256) /\ w2n po + outsz < dimword (:256) /\
    mem_bytes_at (w2n pi) insz t.vs_memory = bytes /\
    FLOOKUP t.vs_allocas sb.cs_next_id = SOME (w2n po,outsz) /\
    sf.cs_next_id <= sb.cs_next_id /\ sb.cs_next_id < sm.cs_next_id /\
    regions_disjoint (w2n po) outsz (w2n pi) insz /\
    (!name b sz. local_region cenv es.scopes t name b sz ==>
      regions_disjoint (w2n po) outsz b sz) /\
    (!old b sz. old < sf.cs_next_id /\ FLOOKUP t.vs_allocas old = SOME (b,sz) ==>
      regions_disjoint (w2n po) outsz b sz) /\
    (!x. not_fresh_at sf x ==> lookup_var x t = lookup_var x s) /\
    (?x. ib.buf_operand = Var x /\ not_fresh_at sm x) /\
    (?x. ob.buf_operand = Var x /\ not_fresh_at sm x) /\
    run_inst_seq (emitted_insts sf sa) s = OK s1 /\
    stmt_state_rel ctx func cenv cx es s1 /\
    eval_operand ib.buf_operand s1 = SOME pi /\
    FLOOKUP s1.vs_allocas sf.cs_next_id = SOME (w2n pi,insz) /\
    s1.vs_memory = s.vs_memory /\ wb_frame cenv es sf s s1 /\
    s1.vs_labels = s.vs_labels /\
    (!name b len. local_region cenv es.scopes s1 name b len ==>
      regions_disjoint (w2n pi) insz b len) /\
    (!aid b len. aid < sf.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n pi) insz b len) /\
    (!aid b len. aid < sf.cs_next_id /\ FLOOKUP s1.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n pi) insz b len) /\
    (!x. not_fresh_at sf x ==> lookup_var x s1 = lookup_var x s) /\
    run_inst_seq code s1 = OK u /\ stmt_state_rel ctx func cenv cx es u /\
    wb_frame cenv es sf s1 u /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s1) /\
    FLOOKUP u.vs_allocas sf.cs_next_id = SOME (w2n pi,insz) /\
    eval_operand ib.buf_operand u = SOME pi /\
    mem_bytes_at (w2n pi) insz u.vs_memory = bytes /\
    run_inst_seq (emitted_insts sb sm) u = OK t
Proof
  strip_tac >>
  qpat_assum `context$compile_alloc_buffer insz sf = _`
    (mp_then Any mp_tac alloc_buffer_frame_run) >>
  disch_then drule >> (impl_tac >- simp[]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sf sa) s = OK s1` >>
  rename1 `eval_operand ib.buf_operand s1 = SOME wi` >>
  `!aid b len. aid < sf.cs_next_id /\
    FLOOKUP s1.vs_allocas aid = SOME (b,len) ==>
    regions_disjoint (w2n wi) insz b len` by
    (rpt strip_tac >> irule state_allocations_disjoint >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  qpat_x_assum `!s1 wi. _` (qspecl_then [`s1`,`wi`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `sf.cs_next_id <= sb.cs_next_id /\ sf.cs_next_var <= sb.cs_next_var` by decide_tac >>
  `!x. not_fresh_at sf x ==> lookup_var x u = lookup_var x s` by
    (rpt strip_tac >>
     `not_fresh_at sa x` by (gvs[not_fresh_at_def] >> decide_tac) >> simp[]) >>
  `wb_frame cenv es sf s u` by
    (irule wb_frame_trans >> simp[] >>
     conj_tac >- (qexistsl [`es`,`sf`,`s1`] >> simp[]) >>
     qexistsl [`ctx`,`cx`,`func`] >> simp[]) >>
  `!x. ib.buf_operand = Var x ==> not_fresh_at sb x` by
    (rpt strip_tac >> gvs[not_fresh_at_def] >> decide_tac) >>
  drule_all alloc_buffer_finish >> strip_tac >>
  `FLOOKUP t.vs_allocas sf.cs_next_id = SOME (w2n wi,insz)` by metis_tac[] >>
  `regions_disjoint (w2n po) outsz (w2n wi) insz` by
    (irule state_allocations_disjoint >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  qexistsl [`t`,`wi`,`po`,`s1`,`u`] >>
  conj_tac
  >- (asm_rewrite_tac[] >>
      qpat_x_assum `run_inst_seq (emitted_insts sf sa) s = OK s1` mp_tac >>
      qpat_x_assum `run_inst_seq code s1 = OK u` mp_tac >>
      qpat_x_assum `run_inst_seq (emitted_insts sb sm) u = OK t` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> metis_tac[exprLoweringPropsTheory.run_inst_seq_append]) >>
  simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
