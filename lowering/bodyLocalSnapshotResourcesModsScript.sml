(* Transport resources at the fixed endpoints of a scratch allocation and copy. *)
Theory bodyLocalSnapshotResourcesMods
Ancestors
  bodyFullMemoryFrames bodyFullPostsMods bodyInvSplit bodyPtrDefs compileEnv
  exprLoweringProps exprSimPtrLiteralBuffer finite_map loweringSlice
  loweringStateRelDefs stmtSimDefs typedMemoryCopy venomMemDefs venomState
  bodyFullShadowBodyInv ptrDiscipline

Theorem snapshot_immutable_frame[local]:
  immutable_frame_mods func ce cx mid s /\
  s.vs_alloca_next <= u.vs_alloca_next /\
  (!aid a len. FLOOKUP u.vs_allocas aid = SOME (a,len) ==>
    FLOOKUP s.vs_allocas aid = SOME (a,len) \/ s.vs_alloca_next <= a) /\
  (!name a len. local_region ce mid.scopes u name a len <=>
    local_region ce mid.scopes s name a len) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP u.vs_allocas inst.inst_id = SOME (b,n) /\
  typed_copy_frame b n s.vs_memory u.vs_memory /\
  u.vs_data_section = s.vs_data_section ==>
  immutable_frame_mods func ce cx mid u
Proof
  strip_tac >>
  fs[immutable_frame_mods_def, immutables_rel_mods_def,
     immutable_alloca_sep_mods_def] >>
  `!src tops. ALOOKUP ce.ce_modules src = SOME tops ==>
    immutable_alloca_sep func (ce with ce_module := src) cx mid u` by
    (rpt gen_tac >> disch_tac >> irule immutable_alloca_sep_frame >>
     qexistsl_tac [`s`,`mid`] >> simp[] >>
     rpt gen_tac >> disch_tac >> disj1_tac >>
     qmatch_asmsub_rename_tac `local_region _ _ u name a len` >>
     qexists_tac `name` >>
     qpat_x_assum `!name a len. local_region ce _ u name a len <=> _`
       (qspecl_then [`name`,`a`,`len`] mp_tac) >>
     fs[local_region_def] >> metis_tac[]) >>
  simp[] >> rpt gen_tac >> disch_tac >>
  irule immutables_rel_mem_agree >> qexists_tac `s` >>
  simp[] >>
  fs[typed_copy_frame_def] >> rpt strip_tac >>
  `immutable_alloca_sep func (ce with ce_module := src) cx mid u` by
    metis_tac[] >>
  `loweringStateRelDefs$regions_disjoint off (type_memory_size tv) b n` by
    (qpat_x_assum `immutable_alloca_sep _ _ _ _ u`
       (mp_tac o cj 2 o REWRITE_RULE [immutable_alloca_sep_def]) >>
     simp[] >>
     disch_then (qspecl_then [`name`,`tv`,`v`,`off`] mp_tac) >>
     simp[] >> strip_tac >> first_x_assum drule_all >> simp[]) >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def]
QED

Theorem snapshot_ghost_zero[local]:
  ghost_inv_at_mods D lo d ce cx mid G tn s ==>
  ghost_inv_at D 0 d ce cx mid G tn s
Proof
  rw[ghost_inv_at_mods_def, ghost_inv_at_def, allocas_from_def] >>
  metis_tac[]
QED

Theorem snapshot_ghost_linked[local]:
  ghost_inv_at_mods D lo d ce cx mid G tn s /\
  ghost_inv_at D 0 d ce cx mid Gu tu u /\
  local_ptrs_reserved ce sa /\
  (!x. not_fresh_at sa x ==> FLOOKUP Gu x = FLOOKUP G x /\
    op_taint tu (Var x) = op_taint tn (Var x)) /\
  allocas_from lo u /\ lo <= u.vs_alloca_next /\
  mem_bytes_at 0 lo u.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
  (!i. i < lo ==> (i IN tu.t_mem <=> i IN tn.t_mem)) ==>
  ghost_inv_at_mods D lo d ce cx mid Gu tu u
Proof
  rw[ghost_inv_at_mods_def, ghost_inv_at_def] >>
  metis_tac[local_ptrs_reserved_def]
QED

Theorem local_snapshot_resources_mods:
  stmt_state_rel H0 ctx func ce cx mid s /\
  local_ptrs_reserved ce sa /\
  (!x len. ce.ce_return_buf = SOME (PtrVar (Var x) len) ==> not_fresh_at sa x) /\
  (!x len. ce.ce_return_pc = SOME (PtrVar (Var x) len) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
    FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x)) /\
  s.vs_alloca_next <= u.vs_alloca_next /\ allocas_from lo u /\ lo <= b /\
  lo <= u.vs_alloca_next /\
  (!aid a len. FLOOKUP u.vs_allocas aid = SOME (a,len) ==>
    FLOOKUP s.vs_allocas aid = SOME (a,len) \/ s.vs_alloca_next <= a) /\
  (!name a len. local_region ce mid.scopes u name a len <=>
    local_region ce mid.scopes s name a len) /\
  (!name a len. local_region ce mid.scopes s name a len ==>
    loweringStateRelDefs$regions_disjoint b n a len) /\
  (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,len) ==>
    loweringStateRelDefs$regions_disjoint b n a len) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP u.vs_allocas inst.inst_id = SOME (b,n) /\
  typed_copy_frame b n s.vs_memory u.vs_memory /\
  (!i. ~(b <= i /\ i < b+n) ==> (i IN tu.t_mem <=> i IN tn.t_mem)) /\
  u.vs_data_section = s.vs_data_section /\ u.vs_call_ctx = s.vs_call_ctx /\
  u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
  u.vs_immutables = s.vs_immutables /\
  tu.t_stor = tn.t_stor /\ tu.t_trans = tn.t_trans /\ tu.t_imm = tn.t_imm ==>
  (immutable_frame_mods func ce cx mid s ==> immutable_frame_mods func ce cx mid u) /\
  (!D d. ghost_inv_at_mods D lo d ce cx mid G tn s ==>
    ghost_inv_at_mods D lo d ce cx mid Gu tu u) /\
  (!D d. ghost_inv_at D lo d ce cx mid G tn s ==>
    ghost_inv_at D lo d ce cx mid Gu tu u) /\
  alloca_frame ce mid sa s ce mid u /\
  (!aid off len i.
    FLOOKUP s.vs_allocas aid = SOME (off,len) /\ aid < sa.cs_next_id /\
    (!name a sz. local_region ce mid.scopes s name a sz ==>
      off+len <= a \/ a+sz <= off) /\
    off <= i /\ i < off+len /\ i IN tu.t_mem ==> i IN tn.t_mem) /\
  mem_bytes_at 0 lo u.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
  (!i. i < lo ==> (i IN tu.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >>
  conj_tac >- (disch_tac >> irule snapshot_immutable_frame >>
               qexistsl_tac [`b`,`inst`,`n`,`s`] >> simp[]) >>
  `mem_bytes_at 0 lo u.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    fs[typed_copy_frame_def] >>
  `!i. i < lo ==> (i IN tu.t_mem <=> i IN tn.t_mem)` by
    (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `!name entry p sz w. lookup_scopes name mid.scopes = SOME entry /\
     FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\ lookup_var p s = SOME w ==>
     val_wf entry.type entry.value /\
     (!i. w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
       i NOTIN {i | b <= i /\ i < b+n})` by
    metis_tac[literal_ptr_local_footprint_exterior] >>
  `!i. i NOTIN {i | b <= i /\ i < b+n} ==>
    mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tu.t_mem <=> i IN tn.t_mem)` by
    (gen_tac >> simp[] >> disch_tac >>
     fs[typed_copy_frame_def] >> first_x_assum irule >> decide_tac) >>
  `!D d k. (k = lo \/ k = 0) /\ ghost_inv_at D k d ce cx mid G tn s ==>
     ghost_inv_at D k d ce cx mid Gu tu u` by
    (rpt gen_tac >> strip_tac >>
     `allocas_from k u /\ k <= u.vs_alloca_next` by
       (fs[allocas_from_def] >> metis_tac[]) >>
     `mem_bytes_at 0 k u.vs_memory = mem_bytes_at 0 k s.vs_memory` by
       (gvs[] >> fs[typed_copy_frame_def]) >>
     `!i. i < k /\ i IN tu.t_mem ==> i IN tn.t_mem` by
       (rpt strip_tac >> `~(b <= i /\ i < b+n)` by decide_tac >>
        metis_tac[]) >>
     qpat_x_assum `k = _` SUBST_ALL_TAC >>
     irule body_full_memory_ghost_frame >> simp[] >>
     qexistsl_tac [`G`,`s`,`sa`,`tn`,`{i | b <= i /\ i < b+n}`] >>
     fs[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule snapshot_ghost_zero >> strip_tac >>
      `ghost_inv_at D 0 d ce cx mid Gu tu u` by metis_tac[] >>
      irule snapshot_ghost_linked >> simp[] >>
      qexistsl_tac [`G`,`s`,`sa`,`tn`] >> simp[] >> metis_tac[])
  >- (rw[alloca_frame_def] >>
      qpat_assum `!aid a len. aid < sa.cs_next_id /\ _ ==> _`
        (drule_all_then mp_tac) >>
      fs[loweringStateRelDefsTheory.regions_disjoint_def, typed_copy_frame_def] >>
      metis_tac[]) >>
  rpt strip_tac >>
  qpat_assum `!aid a len. aid < sa.cs_next_id /\ _ ==> _`
    (drule_all_then mp_tac) >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
  disch_tac >>
  `~(b <= i /\ i < b+n)` by decide_tac >> metis_tac[]
QED
