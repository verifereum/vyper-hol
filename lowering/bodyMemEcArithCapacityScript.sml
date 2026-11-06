Theory bodyMemEcArithCapacity
Ancestors
  bodyMemEcArithCallbacks bodyMemEcArithPrefix exprSimLiteralBuffer
  exprSimPrecompiles exprLoweringProps instMemFrontier venomState exprSimAlloc compileEnv

Theorem ec_allocated_payload_capacity_run:
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
  ?t pi po. run_inst_seq (emitted_insts sf sm) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sf s t /\
    eval_operand ib.buf_operand t = SOME pi /\
    eval_operand ob.buf_operand t = SOME po /\
    w2n pi + insz < dimword (:256) /\ w2n po + outsz < dimword (:256) /\
    w2n pi + insz <= t.vs_alloca_next /\ w2n po + outsz <= t.vs_alloca_next /\
    mem_bytes_at (w2n pi) insz t.vs_memory = bytes /\
    (!x. not_fresh_at sf x ==> lookup_var x t = lookup_var x s) /\
    (?x. ib.buf_operand = Var x /\ not_fresh_at sm x) /\
    (?x. ob.buf_operand = Var x /\ not_fresh_at sm x)
Proof
  strip_tac >>
  qpat_assum `compile_alloc_buffer insz sf = _`
    (mp_then Any mp_tac alloc_buffer_frame_run) >>
  disch_then drule_all >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sf sa) s = OK s1` >>
  `!aid b len. aid < sf.cs_next_id /\
    FLOOKUP s1.vs_allocas aid = SOME (b,len) ==>
    regions_disjoint (w2n w) insz b len` by
    (rpt strip_tac >> irule state_allocations_disjoint >>
     qexistsl [`sf.cs_next_id`,`aid`,`cenv`,`ctx`,`cx`,`es`,`func`,`s1`] >>
     simp[] >> decide_tac) >>
  qpat_assum `!s1 wi. _` (qspecl_then [`s1`,`w`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  drule_all (Q.INST [`s` |-> `u`, `sa` |-> `sb`, `sz` |-> `outsz`]
    (SPEC_ALL literal_alloc_buffer_run)) >> strip_tac >>
  `FLOOKUP t.vs_allocas sf.cs_next_id = SOME (w2n w,insz)` by
    (first_x_assum irule >> first_assum ACCEPT_TAC) >>
  `w2n w + insz <= t.vs_alloca_next /\
   w2n w' + outsz <= t.vs_alloca_next` by
    (conj_tac
     >- (irule alloca_region_below_frontier >> conj_tac
         >- (qpat_assum `stmt_state_rel _ _ _ _ _ t` mp_tac >>
             simp_tac (srw_ss()) [stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def]) >>
         qexistsl [`sf.cs_next_id`,`w2n w`,`insz`] >> simp[]) >>
     irule alloca_region_below_frontier >> conj_tac
     >- (qpat_assum `stmt_state_rel _ _ _ _ _ t` mp_tac >>
         simp_tac (srw_ss()) [stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def]) >>
     qexistsl [`sb.cs_next_id`,`w2n w'`,`outsz`] >> simp[]) >>
  `run_inst_seq (emitted_insts sf sm) s = OK t` by
    (asm_rewrite_tac[] >>
     qpat_x_assum `run_inst_seq (emitted_insts sf sa) s = _` mp_tac >>
     qpat_x_assum `run_inst_seq code s1 = _` mp_tac >>
     qpat_x_assum `run_inst_seq (emitted_insts sb sm) u = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[run_inst_seq_append]) >>
  `eval_operand ib.buf_operand t = SOME w` by
    (gvs[eval_operand_def, not_fresh_at_def] >>
     first_x_assum irule >> decide_tac) >>
  drule_all allocated_payload_run >> strip_tac >>
  gvs[] >> qexistsl [`t`,`w`,`w'`] >> simp[]
QED
