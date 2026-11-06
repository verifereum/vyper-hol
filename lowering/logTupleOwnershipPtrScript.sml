(* Actual allocation-site ownership, including allocations reused in loops. *)
Theory logTupleOwnershipPtr
Ancestors
  localPtrsProps abiDecoderFrame bodyPtrDefs compileEnv exprLoweringProps
  venomMemDefs venomState venomInst finite_map list arithmetic

Theorem log_alloca_candidate_other_region:
  alloca_inv s /\ id <> site /\
  ((FLOOKUP s.vs_allocas site = NONE /\ p = s.vs_alloca_next) \/
   FLOOKUP s.vs_allocas site = SOME (p,cap)) /\
  FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
  abi_footprint_disjoint b sz [(p,cap)]
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `(_ /\ _) \/ _` (DISJ_CASES_THEN strip_assume_tac)
  >- (fs[alloca_inv_def, alloca_next_valid_def, abi_footprint_disjoint_def] >>
      disj1_tac >> first_x_assum irule >> metis_tac[]) >>
  fs[alloca_inv_def, allocas_non_overlapping_def, abi_footprint_disjoint_def] >>
  first_x_assum (qspecl_then [`id`,`site`,`b`,`sz`,`p`,`cap`] mp_tac) >> simp[]
QED

Theorem log_alloca_candidate_local_region:
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce st /\ ~not_fresh_at st q /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [q] /\
  ((FLOOKUP s.vs_allocas inst.inst_id = NONE /\ p = s.vs_alloca_next) \/
   FLOOKUP s.vs_allocas inst.inst_id = SOME (p,cap)) ==>
  !name lo sz. local_region ce es.scopes s name lo sz ==>
    abi_footprint_disjoint lo sz [(p,cap)]
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `local_ptrs_rel func ce es.scopes s /\ alloca_inv s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `not_local_ptr ce es.scopes q` by
    (fs[not_local_ptr_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  rpt strip_tac >>
  qpat_x_assum `(_ /\ _) \/ _` (DISJ_CASES_THEN strip_assume_tac)
  >- (`regions_disjoint lo sz p cap` by
        (irule local_ptrs_rel_above_frontier >> metis_tac[LESS_EQ_REFL]) >>
      fs[compileEnvTheory.regions_disjoint_def, abi_footprint_disjoint_def]) >>
  `regions_disjoint p cap lo sz` by
    (irule local_ptrs_rel_alloca_disjoint >> metis_tac[]) >>
  fs[compileEnvTheory.regions_disjoint_def, abi_footprint_disjoint_def] >>
  metis_tac[]
QED
