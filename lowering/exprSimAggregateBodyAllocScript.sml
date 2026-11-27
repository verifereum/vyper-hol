(* Separation interface for a generated aggregate buffer and its used prefix. *)
Theory exprSimAggregateBodyAlloc
Ancestors
  exprSimAlloc exprLoweringProps compileEnv loweringStateRelDefs fragExec venomInst
  vyperState valueEncoding placeMemoryProtectedFrame

Theorem aggregate_body_alloc_immutable_prefix_source:
  compile_alloc_buffer sz sa = (buf,sm) /\
  fn_has_code sa sm func /\
  stmt_state_rel H ctx func ce cx es t /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,sz) /\ used <= sz ==>
  ce.ce_is_ctor ==>
  !src name itv iv io.
    (src = ce.ce_module \/ IS_SOME (ALOOKUP ce.ce_modules src)) /\
    FLOOKUP ce.ce_module_vars (src,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables src imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) b used
Proof
  strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  disch_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `regions_disjoint io (type_memory_size itv) b sz` by
    (drule stmt_state_rel_immutable_alloca_disjoint >>
     disch_then (drule_at (Pat `MEM _ (fn_insts func)`)) >>
     simp[mk_inst_def] >> metis_tac[]) >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem aggregate_body_alloc_immutable_prefix:
  compile_alloc_buffer sz sa = (buf,sm) /\
  fn_has_code sa sm func /\
  stmt_state_rel H ctx func ce cx es t /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,sz) /\ used <= sz ==>
  ce.ce_is_ctor ==>
  !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) b used
Proof
  metis_tac[aggregate_body_alloc_immutable_prefix_source]
QED
