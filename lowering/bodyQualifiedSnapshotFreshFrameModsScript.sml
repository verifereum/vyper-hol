(* Frame transport over the saved RHS's bounded scratch write. *)
Theory bodyQualifiedSnapshotFreshFrameMods
Ancestors
  bodyPtrMakeArrayCopyStateFrame bodyFullPostsMods bodyFullShadowBodyInv
  bodyMemoryDefs assignTuplePtrCopyLen exprSimCopy freshWrites finite_map
  typedMemoryCopy loweringPosts exprSimPtrLiteralBuffer robustCopyTransportPtr
  vyperTypeEnvPreservation vyperStorageFootprint bodyPtrDefs venomMemDefs
  compileEnv exprLoweringProps loweringSlice venomState bodyInvSplit
  loweringStateRelDefs exprSimStorageCopy ptrDiscipline words venomInst
  gasOutcomeFullMods

Theorem snapshot_local_region_module[local]:
  local_region (ce with ce_module := src) scopes s id off len <=>
  local_region ce scopes s id off len
Proof
  simp[local_region_def]
QED

Theorem snapshot_immutable_write[local]:
  immutable_frame_mods func ce cx mid z /\
  (!name off len. local_region ce mid.scopes u name off len <=>
                   local_region ce mid.scopes z name off len) /\
  u.vs_allocas = z.vs_allocas /\ u.vs_alloca_next = z.vs_alloca_next /\
  u.vs_data_section = z.vs_data_section /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP z.vs_allocas inst.inst_id = SOME (b,cap) /\
  typed_copy_frame b cap z.vs_memory u.vs_memory ==>
  immutable_frame_mods func ce cx mid u
Proof
  strip_tac >> fs[immutable_frame_mods_def, immutables_rel_mods_def,
                  immutable_alloca_sep_mods_def] >> reverse conj_tac
  >- (rpt gen_tac >> disch_tac >> irule immutable_alloca_sep_fields >>
      qexistsl_tac [`z`,`mid`] >> simp[] >>
      simp[snapshot_local_region_module] >> metis_tac[]) >>
  rpt gen_tac >> disch_tac >> irule immutables_rel_mem_agree >>
  qexists_tac `z` >> fs[typed_copy_frame_def] >>
  rpt strip_tac >> first_x_assum irule >>
  simp[GSYM loweringStateRelDefsTheory.regions_disjoint_def] >>
  qpat_assum `!src tops. ALOOKUP ce.ce_modules src = SOME tops ==> immutable_alloca_sep _ _ _ _ _`
    (drule_then (mp_tac o cj 2 o REWRITE_RULE [immutable_alloca_sep_def])) >>
  simp[] >> disch_then (qspecl_then [`name`,`tv`,`v`,`off`] mp_tac) >>
  simp[] >> strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem snapshot_entry_write[local]:
  wb_frame ce es mid sa s0 z /\ ghost_kept_at lo ce es sa G0 t0 s0 Gz tz /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x z /\
     FLOOKUP Gu x = FLOOKUP Gz x /\ op_taint tu (Var x) = op_taint tz (Var x)) /\
  u.vs_allocas = z.vs_allocas /\
  (!off len. off+len <= b \/ b+cap <= off ==>
    mem_bytes_at off len u.vs_memory = mem_bytes_at off len z.vs_memory) /\
  (!i. ~(b <= i /\ i < b+cap) ==> (i IN tu.t_mem <=> i IN tz.t_mem)) /\
  (!name off len. local_region ce es.scopes s0 name off len ==>
     off+len <= b \/ b+cap <= off) /\
  (!aid off len. aid < sa.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (off,len) ==>
     off+len <= b \/ b+cap <= off) ==>
  wb_frame ce es mid sa s0 u /\ ghost_kept_at lo ce es sa G0 t0 s0 Gu tu
Proof
  strip_tac >> fs[wb_frame_def,ghost_kept_at_def] >> rpt conj_tac
  >- metis_tac[]
  >- (irule copy_buffer_locals_kept_frame >> qexistsl_tac [`b`,`z`,`cap`] >>
      simp[] >> conj_tac
      >- (rpt strip_tac >>
          qpat_assum `!name off len. local_region ce _ _ _ _ _ ==> _`
            (drule_then assume_tac) >> decide_tac) >>
      rpt strip_tac >> first_x_assum irule >> decide_tac)
  >- (rpt strip_tac >>
      qpat_assum `!aid off len. _ /\ _ ==> _ \/ _` (drule_all_then assume_tac) >>
      `~(b <= i /\ i < b+cap)` by decide_tac >>
      `i IN tz.t_mem` by
        (qpat_assum `!j. _ ==> (j IN tu.t_mem <=> _)` (qspec_then `i` mp_tac) >> simp[]) >>
      qpat_assum `!aid off sz i. _ /\ _ ==> i IN t0.t_mem`
        (drule_all_then ACCEPT_TAC))
  >- (rpt strip_tac >>
      qpat_assum `!name off len. local_region ce _ _ _ _ _ ==> _`
        (drule_then assume_tac) >>
      `~(b <= i /\ i < b+cap)` by decide_tac >>
      qpat_assum `!j. _ ==> (j IN tu.t_mem <=> _)` (qspec_then `i` mp_tac) >>
      simp[] >> metis_tac[])
QED

Theorem snapshot_ghost_write_mods[local]:
  ghost_inv_at_mods D lo d ce cx mid Gz tz z /\
  local_ptrs_reserved ce sk /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sk x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sk x) /\
  (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sk x) /\
  (!x. not_fresh_at sk x ==> lookup_var x u = lookup_var x z /\
     FLOOKUP Gu x = FLOOKUP Gz x /\ op_taint tu (Var x) = op_taint tz (Var x)) /\
  (!name entry p sz w. lookup_scopes name mid.scopes = SOME entry /\
     FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\ lookup_var p z = SOME w ==>
     val_wf entry.type entry.value /\
     (!i. w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
       i NOTIN {j | b <= j /\ j < b+cap})) /\
  (!i. i NOTIN {j | b <= j /\ j < b+cap} ==>
    mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 z.vs_memory /\
    (i IN tu.t_mem <=> i IN tz.t_mem)) /\
  mem_bytes_at 0 lo u.vs_memory = mem_bytes_at 0 lo z.vs_memory /\
  (!i. i < lo ==> (i IN tu.t_mem <=> i IN tz.t_mem)) /\
  u.vs_allocas = z.vs_allocas /\ u.vs_alloca_next = z.vs_alloca_next /\
  u.vs_call_ctx = z.vs_call_ctx /\ u.vs_accounts = z.vs_accounts /\
  u.vs_transient = z.vs_transient /\ u.vs_immutables = z.vs_immutables /\
  tu.t_stor = tz.t_stor /\ tu.t_trans = tz.t_trans /\ tu.t_imm = tz.t_imm ==>
  ghost_inv_at_mods D lo d ce cx mid Gu tu u
Proof
  strip_tac >>
  `!p sz. not_fresh_at sk p /\ ptr_covers Gz tz p z sz ==>
     ptr_covers Gu tu p u sz` by
    (rpt strip_tac >> irule ptr_covers_lookup_frame >>
     qexistsl_tac [`Gz`,`z`,`tz`] >> metis_tac[]) >>
  fs[ghost_inv_at_mods_def, stor_taint_ok_at_def, allocas_from_def] >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sk p` by metis_tac[local_ptrs_reserved_def] >>
      conj_tac >- metis_tac[] >>
      rpt gen_tac >> strip_tac >>
      `lookup_var p z = SOME w` by metis_tac[] >>
      irule robust_val_in_memory_exterior_frame >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`z.vs_memory`,`u.vs_memory`,`tz.t_mem`,`tu.t_mem`,
        `{j | b <= j /\ j < b+cap}`] >> simp[] >>
      qpat_assum `!name entry p sz. _ /\ _ ==> ptr_covers _ _ _ _ _ /\ _`
        (drule_all_then strip_assume_tac) >>
      qpat_assum `!name entry p sz w. _ /\ _ ==> val_wf _ _ /\ _`
        (drule_all_then strip_assume_tac) >>
      simp[] >> metis_tac[])
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
      gvs[return_buf_ptr_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem qualified_snapshot_fresh_store_frame_mods:
  wb_frame ce es mid sa s0 z /\ ghost_kept_at lo ce es sa G0 t0 s0 Gz tz /\
  return_buf_frame d ce sk z /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sk x) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sk x) /\
  (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sk x) /\
  sa.cs_next_var <= sk.cs_next_var /\ sk.cs_next_var <= sr.cs_next_var /\
  sa.cs_next_id <= aid /\ aid < sr.cs_next_id /\
  alloca_inv z /\
  MEM (mk_inst aid ALLOCA [Lit (n2w cap)] [p]) (fn_insts func) /\
  FLOOKUP z.vs_allocas aid = SOME (b,cap) /\
  lo <= b /\ b+cap < dimword (:256) /\ b+cap <= z.vs_alloca_next /\
  not_fresh_at sk p /\ lookup_var p z = SOME (n2w b) /\ ptr_covers Gz tz p z cap /\
  (!name off len. local_region ce mid.scopes z name off len ==>
     loweringStateRelDefs$regions_disjoint b cap off len) /\
  n <= cap /\ typed_copy_state_frame sk b n z u /\
  (!x. not_fresh_at sk x ==>
     FLOOKUP Gu x = FLOOKUP Gz x /\ op_taint tu (Var x) = op_taint tz (Var x)) /\
  (!i. ~(b <= i /\ i < b+n) ==> (i IN tu.t_mem <=> i IN tz.t_mem)) /\
  tu.t_stor = tz.t_stor /\ tu.t_trans = tz.t_trans /\ tu.t_imm = tz.t_imm /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func ce cx mid z /\ immutable_frame_mods func ce cx mid z /\
    storage_well_formed_on cx mid (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx mid Gz tz z) ==>
  wb_frame ce es mid sa s0 u /\ ghost_kept_at lo ce es sa G0 t0 s0 Gu tu /\
  return_buf_frame d ce sr u /\
  FLOOKUP u.vs_allocas aid = SOME (b,cap) /\ aid < sr.cs_next_id /\
  lo <= b /\ b+cap < dimword (:256) /\ b+cap <= u.vs_alloca_next /\
  (!name off len. local_region ce mid.scopes u name off len ==>
     loweringStateRelDefs$regions_disjoint b cap off len) /\
  not_fresh_at sr p /\ lookup_var p u = SOME (n2w b) /\ ptr_covers Gu tu p u cap /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func ce cx mid u /\ immutable_frame_mods func ce cx mid u /\
    storage_well_formed_on cx mid (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx mid Gu tu u)
Proof
  strip_tac >>
  `typed_copy_state_frame sk b cap z u` by
    (irule typed_copy_state_frame_subinterval >> qexistsl_tac [`b`,`n`] >> simp[]) >>
  `!i. ~(b <= i /\ i < b+cap) ==> (i IN tu.t_mem <=> i IN tz.t_mem)` by
    (gen_tac >> strip_tac >> first_x_assum irule >> decide_tac) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sk x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `local_ptrs_reserved ce sk` by metis_tac[local_ptrs_reserved_next_var] >>
  qpat_assum `typed_copy_state_frame sk b cap z u`
    (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def]) >>
  `copy_static u = copy_static z` by
    (qpat_assum `u with <|vs_vars := _; vs_memory := _; vs_prev_bb := _;
                         vs_current_bb := _; vs_inst_idx := _|> = z`
       (mp_tac o AP_TERM ``copy_static``) >> simp[copy_static_def]) >>
  drule_then strip_assume_tac copy_static_fields >>
  `u.vs_immutables = z.vs_immutables` by
    (qpat_assum `copy_static u = copy_static z`
       (mp_tac o AP_TERM ``\s. s.vs_immutables``) >>
     SIMP_TAC (srw_ss()) [copy_static_def]) >>
  `!name off len. local_region ce mid.scopes u name off len <=>
                   local_region ce mid.scopes z name off len` by
    (rpt gen_tac >> irule local_region_lookup_cong >>
     metis_tac[local_ptrs_reserved_def]) >>
  suspend "assembly"
QED

Resume qualified_snapshot_fresh_store_frame_mods[assembly]:
  `wb_frame ce es mid sa s0 u /\ ghost_kept_at lo ce es sa G0 t0 s0 Gu tu` by
    suspend "entry" >>
  `return_buf_frame d ce sr u` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`z`,`sk`] >> simp[] >> metis_tac[]) >>
  `lookup_var p u = SOME (n2w b)` by metis_tac[] >>
  `not_fresh_at sr p` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `ptr_covers Gu tu p u cap` by
    (irule ptr_covers_lookup_frame >> qexistsl_tac [`Gz`,`z`,`tz`] >> metis_tac[]) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!name off len. local_region ce _ z _ _ _ ==> _`
        (drule_then ACCEPT_TAC)) >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _` (drule_then strip_assume_tac) >>
  simp[] >> conj_tac >- suspend "state" >>
  conj_tac >- suspend "immutable" >>
  suspend "ghost"
QED

Resume qualified_snapshot_fresh_store_frame_mods[entry]:
  irule snapshot_entry_write >> qexistsl_tac [`Gz`,`b`,`cap`,`tz`,`z`] >>
  simp[] >> suspend "old_regions"
QED

Resume qualified_snapshot_fresh_store_frame_mods[old_regions]:
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `local_region ce mid.scopes z name off len` by
        (fs[wb_frame_def,locals_kept_def,local_region_def] >>
         `not_fresh_at sa p'` by metis_tac[local_ptrs_reserved_def] >>
         `IS_SOME (lookup_scopes name mid.scopes)` by
           metis_tac[lookup_scopes_same_fdoms_some] >>
         metis_tac[optionTheory.IS_SOME_EXISTS]) >>
      qpat_assum `!name off len. local_region ce _ z _ _ _ ==> _`
        (drule_then mp_tac) >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  reverse conj_tac
  >- (fs[typed_copy_frame_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  rpt strip_tac >>
  `FLOOKUP z.vs_allocas aid' = SOME (off,len)` by fs[wb_frame_def] >>
  `aid' <> aid` by decide_tac >>
  fs[alloca_inv_def,allocas_non_overlapping_def] >>
  qpat_assum `!a1 a2 b1 sz1 b2 sz2. _ /\ _ ==> _`
    (qspecl_then [`aid'`,`aid`,`off`,`len`,`b`,`cap`] mp_tac) >>
  simp[] >> decide_tac
QED

Resume qualified_snapshot_fresh_store_frame_mods[state]:
  irule literal_copy_window_stmt_state_rel >>
  qexistsl_tac [`aid`,`b`,`cap`,`p`,`sk`,`sk`,`z`] >>
  fs[typed_copy_frame_def] >> conj_tac >- first_assum ACCEPT_TAC >>
  first_assum ACCEPT_TAC
QED

Resume qualified_snapshot_fresh_store_frame_mods[immutable]:
  irule snapshot_immutable_write >>
  qexistsl_tac [`b`,`cap`,`mk_inst aid ALLOCA [Lit (n2w cap)] [p]`,`z`] >>
  simp[venomInstTheory.mk_inst_def]
QED

Resume qualified_snapshot_fresh_store_frame_mods[ghost]:
  irule snapshot_ghost_write_mods >>
  qexistsl_tac [`Gz`,`b`,`cap`,`sk`,`tz`,`z`] >> simp[] >> rpt conj_tac
  >- (drule literal_ptr_local_footprint_exterior >>
      disch_then (qspecl_then [`cap`,`b`] assume_tac) >>
      qx_genl_tac [`name`,`entry`,`x`,`sz`,`w`] >> strip_tac >>
      first_x_assum (qspecl_then [`name`,`entry`,`x`,`sz`,`w`] mp_tac) >>
      simp[] >> disch_then irule >> first_assum ACCEPT_TAC)
  >- (fs[typed_copy_frame_def] >> rpt strip_tac >>
      qpat_assum `!a n. _ \/ _ ==> mem_bytes_at a n u.vs_memory = _` irule >> decide_tac) >>
  fs[typed_copy_frame_def] >>
  qpat_assum `!a n. _ \/ _ ==> mem_bytes_at a n u.vs_memory = _` irule >> decide_tac
QED

Finalise qualified_snapshot_fresh_store_frame_mods
