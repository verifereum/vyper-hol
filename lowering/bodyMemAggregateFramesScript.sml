(* Frame transport at aggregate buffer boundaries. *)
Theory bodyMemAggregateFrames
Ancestors exprSimAggregates exprSimHypsDefs valueEncoding compileEnv

Theorem aggregate_exterior_frame_transport:
  (!aid p n. FLOOKUP t.vs_allocas aid = SOME (p,n) /\
    aid < sm.cs_next_id /\ (n+p <= b \/ b+sz <= p) /\
    (!name lo sz. local_region ce scopes u name lo sz ==> n+p <= lo \/ lo+sz <= p) ==>
    mem_bytes_at p n r.vs_memory = mem_bytes_at p n mem) ==>
  !p n. (?aid. FLOOKUP t.vs_allocas aid = SOME (p,n) /\ aid < sm.cs_next_id) /\
    regions_disjoint p n b sz /\
    (!name lo k. local_region ce scopes u name lo k ==> p+n <= lo \/ k+lo <= p) ==>
    mem_bytes_at p n r.vs_memory = mem_bytes_at p n mem
Proof
  rpt strip_tac >>
  qpat_x_assum `!aid p n. FLOOKUP _ _ = _ /\ _ ==> _` irule >>
  gvs[regions_disjoint_def, AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  (conj_tac >- (rpt strip_tac >>
    metis_tac[arithmeticTheory.ADD_COMM]) >>
   qexists_tac `aid` >> simp[])
QED

Theorem aggregate_alloca_immutable_prefix_sep:
  stmt_state_rel ctx func ce cx es t /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = venomInst$ALLOCA /\
  FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) /\ used <= sz ==>
  ce.ce_is_ctor ==>
  !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    io + type_memory_size itv <= b \/ b + used <= io
Proof
  rpt strip_tac >>
  drule_all aggregate_alloca_immutable_sep >>
  simp[regions_disjoint_def] >> strip_tac >> decide_tac
QED
