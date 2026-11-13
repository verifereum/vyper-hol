Theory assignEffectfulIndexSnapshotSeparation
Ancestors
  stmtSimDefs exprLoweringProps loweringStateRelDefs venomMemDefs
  venomState venomInst

Theorem snapshot_origin_allocations_disjoint:
  stmt_state_rel ctx func ce cx es s /\ origin.cs_next_id <= aid /\
  FLOOKUP s.vs_allocas aid = SOME (b,N) ==>
  !id off n. id < origin.cs_next_id /\
    FLOOKUP s.vs_allocas id = SOME (off,n) ==>
    regions_disjoint off n b N
Proof
  rpt strip_tac >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  qpat_x_assum `alloca_inv s` mp_tac >>
  simp[alloca_inv_def, allocas_non_overlapping_def, loweringStateRelDefsTheory.regions_disjoint_def] >>
  strip_tac >>
  qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _`
    (qspecl_then [`id`, `aid`] mp_tac) >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem snapshot_constructor_allocations_disjoint:
  stmt_state_rel ctx func ce cx es s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,N) ==>
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) b N)
Proof
  rpt strip_tac >>
  `immutable_alloca_sep func ce cx es s` by fs[stmt_state_rel_def] >>
  fs[immutable_alloca_sep_def] >> metis_tac[]
QED
