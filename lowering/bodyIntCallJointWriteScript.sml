Theory bodyIntCallJointWrite
Ancestors
  list finite_map exprSimAlloc exprSimHash exprLoweringProps compileEnv vyperState
  venomState venomExecSemantics

(* All windows are framed at the same concrete bounded-write endpoint. *)
Theorem joint_alloca_write_frame:
  stmt_state_rel ctx func ce cx es s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  b <= a /\ a + 32 <= b + sz /\
  (!name lb len. local_region ce es.scopes s name lb len ==>
     regions_disjoint b sz lb len) /\
  EVERY (\(off,len). regions_disjoint b sz off len) hs ==>
  stmt_state_rel ctx func ce cx es (mstore a w s) /\
  EVERY (\(off,len).
    mem_bytes_at off len (mstore a w s).vs_memory =
    mem_bytes_at off len s.vs_memory) hs /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
      NONE => FEMPTY | SOME imms => get_source_immutables ce.ce_module imms)
      name = SOME (tv,v) ==>
    mem_bytes_at off (type_memory_size tv) (mstore a w s).vs_memory =
    mem_bytes_at off (type_memory_size tv) s.vs_memory)
Proof
  strip_tac >> conj_tac
  >- (irule literal_mstore_state_rel >> simp[] >>
      qexistsl_tac [`b`, `inst`, `sz`] >>
      gvs[regions_disjoint_def] >> metis_tac[]) >>
  conj_tac
  >- (gvs[EVERY_MEM] >> rpt strip_tac >>
      PairCases_on `e` >> gvs[] >>
      irule mstore_region_frame >>
      qexistsl_tac [`b`, `sz`] >> simp[] >>
      first_x_assum drule >> simp[]) >>
  rpt strip_tac >>
  irule mstore_region_frame >> qexistsl_tac [`b`, `sz`] >>
  simp[] >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
  simp[stmt_state_rel_def, immutable_alloca_sep_def] >>
  rpt strip_tac >>
  first_x_assum drule_all >>
  simp[regions_disjoint_def] >> metis_tac[]
QED
