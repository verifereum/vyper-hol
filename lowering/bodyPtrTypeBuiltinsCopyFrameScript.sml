Theory bodyPtrTypeBuiltinsCopyFrame
Ancestors
  bodyPtrTypeBuiltinsCopyCounted bodyPtrTypeBuiltinsEmptyFrame
  bodyPtrTypeBuiltinsEmptyAlloc exprSimAlloc robustCopyTransportPtr
  exprLoweringProps localPtrsProps venomMemProofs pred_set
  venomState venomExecSemantics bodyPtrDefs ptrDiscipline compileEnv exprSimProps arithmetic

Theorem copy_memory_destination_robust:
  compile_copy_memory (Var dst) (Var src) n sa = ((),sb) /\
  n < dimword(:256) /\ lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  val_wf tv v /\ val_footprint tv v <= n /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n a) m) ==>
  ?th. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G th /\
    th.t_var = tn.t_var /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    (!m. mem_agree_outside th.t_mem t.vs_memory m ==> val_in_memory tv v (w2n b) m)
Proof
  strip_tac >> drule_all copy_memory_counted_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  drule_all copy_memory_endpoint_frame >> strip_tac >>
  qexists_tac `th` >> simp[] >> rpt strip_tac >>
  irule robust_val_in_memory_copy_transport >> simp[] >>
  qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `n`, `w2n a`, `tn.t_mem`, `th.t_mem`] >>
  simp[] >> rpt strip_tac >> simp[] >> decide_tac
QED

Theorem copy_memory_exterior_taint:
  th.t_mem = (tn.t_mem DIFF {j | b <= j /\ j < b+n}) UNION
    {b+j | j < n /\ a+j IN tn.t_mem} ==>
  !i. ~(b <= i /\ i < b+n) ==> (i IN th.t_mem <=> i IN tn.t_mem)
Proof
  strip_tac >> simp[] >> rpt strip_tac >> eq_tac >> simp[] >> decide_tac
QED

Theorem copy_memory_runtime_frame:
  (if n = 0 then t = s else t = mcopy b a n s) ==>
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient
Proof
  Cases_on `n = 0` >> simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem copy_memory_ptr_covers_frame:
  (!p. lookup_var p t = lookup_var p s) /\ th.t_var = tn.t_var ==>
  !p k. ptr_covers G th p t k <=> ptr_covers G tn p s k
Proof
  simp[ptr_covers_def, op_taint_def]
QED

Theorem ghost_kept_exterior_frame:
  (!p. op_taint th (Var p) = op_taint tn (Var p)) /\
  (!i. i NOTIN writes ==> (i IN th.t_mem <=> i IN tn.t_mem)) /\
  (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
    aid < sa.cs_next_id /\ off <= i /\ i < off+sz ==> i NOTIN writes) /\
  (!name off sz i. local_region cenv es.scopes s0 name off sz /\
    off <= i /\ i < off+sz ==> i NOTIN writes) /\
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  ghost_kept cenv es sa G0 tn0 s0 G th
Proof
  simp[ghost_kept_def] >> metis_tac[]
QED

Theorem copy_local_footprint_separation:
  stmt_state_rel ctx fn cenv cx es s /\
  (!name off sz. local_region cenv es.scopes s name off sz ==>
    regions_disjoint b capacity off sz) /\ n <= capacity ==>
  !name entry p sz w.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w ==>
    val_wf entry.type entry.value /\
    (w2n w + val_footprint entry.type entry.value <= b \/ b+n <= w2n w)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `local_region cenv es.scopes s name (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `regions_disjoint b capacity (w2n w) sz` by metis_tac[] >>
  `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     qpat_x_assum `!name entry p sz. _ ==> ?w. _` drule_all >>
     strip_tac >> gvs[]) >>
  `val_footprint entry.type entry.value <= type_memory_size entry.type` by
    metis_tac[val_footprint_le] >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem copy_memory_ghost_inv:
  compile_copy_memory (Var dst) (Var src) n sa = ((),sb) /\
  n < dimword(:256) /\ lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  stmt_state_rel ctx fn cenv cx es s /\ n <= capacity /\
  (!name off sz. local_region cenv es.scopes s name off sz ==>
    regions_disjoint (w2n b) capacity off sz) /\
  ghost_inv d cenv cx es G tn s ==>
  ?th. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G th /\
    ghost_inv d cenv cx es G th t /\
    (!p k. ptr_covers G th p t k <=> ptr_covers G tn p s k) /\
    th.t_var = tn.t_var /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    th.t_mem = (tn.t_mem DIFF {j | w2n b <= j /\ j < w2n b+n}) UNION
      {w2n b+j | j < n /\ w2n a+j IN tn.t_mem} /\
    (!i. ~(w2n b <= i /\ i < w2n b+n) ==> (i IN th.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >>
  `!name entry p sz w.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\ lookup_var p s = SOME w ==>
    val_wf entry.type entry.value /\
    (w2n w + val_footprint entry.type entry.value <= w2n b \/ w2n b+n <= w2n w)` by
    metis_tac[copy_local_footprint_separation] >>
  drule_all copy_memory_counted_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  drule_all copy_memory_endpoint_frame >> strip_tac >>
  drule copy_memory_runtime_frame >> strip_tac >>
  drule copy_memory_exterior_taint >> strip_tac >>
  `!p k. ptr_covers G th p t k <=> ptr_covers G tn p s k` by
    (irule copy_memory_ptr_covers_frame >> simp[]) >>
  qexists_tac `th` >> simp[] >>
  irule ghost_inv_exterior_frame >>
  qexistsl_tac [`G`, `K T`, `s`, `tn`, `{i | w2n b <= i /\ i < w2n b+n}`] >>
  simp[op_taint_def] >> conj_tac
  >- (rpt strip_tac >> first_x_assum drule_all >> strip_tac >> simp[] >> decide_tac) >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED


Theorem allocated_copy_separation:
  compile_alloc_buffer capacity sa = (buf,sm) /\
  stmt_state_rel ctx fn cenv cx es s0 /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ capacity < dimword(:256) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w capacity)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  run_inst_seq (emitted_insts sa sm) s0 = OK s /\
  eval_operand buf.buf_operand s = SOME b ==>
  stmt_state_rel ctx fn cenv cx es s /\
  (!name off sz. local_region cenv es.scopes s name off sz ==>
    regions_disjoint (w2n b) capacity off sz) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
    regions_disjoint (w2n b) capacity off sz) /\
  (!name off sz. local_region cenv es.scopes s0 name off sz ==>
    regions_disjoint (w2n b) capacity off sz)
Proof
  strip_tac >> drule_all literal_alloc_buffer_run >> strip_tac >> gvs[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >> first_x_assum irule >>
  fs[local_region_def] >>
  rename1 `FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var lp) sz)` >>
  `not_fresh_at sa lp` by
    (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  metis_tac[]
QED


Theorem allocated_copy_ghost_frame:
  compile_alloc_buffer capacity sa = (buf,sm) /\
  stmt_state_rel ctx fn cenv cx es s0 /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ capacity < dimword(:256) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w capacity)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  run_inst_seq (emitted_insts sa sm) s0 = OK s /\ buf.buf_operand = Var dst /\
  lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
  compile_copy_memory (Var dst) (Var src) n sm = ((),sb) /\
  run_inst_seq (emitted_insts sm sb) s = OK t /\ n <= capacity /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s capacity /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  ?th. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sm sb) s G th /\
    ghost_inv d cenv cx es G th t /\ ghost_kept cenv es sa G0 tn0 s0 G th /\
    (!p k. ptr_covers G th p t k <=> ptr_covers G tn p s k) /\
    ptr_covers G th dst t capacity /\
    th.t_var = tn.t_var /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    th.t_mem = (tn.t_mem DIFF {j | w2n b <= j /\ j < w2n b+n}) UNION
      {w2n b+j | j < n /\ w2n a+j IN tn.t_mem}
Proof
  strip_tac >>
  `eval_operand buf.buf_operand s = SOME b` by simp[eval_operand_def] >>
  drule_all allocated_copy_separation >> strip_tac >>
  `n < dimword(:256) /\ ptr_covers G tn dst s n` by
    (conj_tac >- decide_tac >> fs[ptr_covers_def] >>
     goal_assum (drule_at Any) >> decide_tac) >>
  drule_all copy_memory_ghost_inv >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexists_tac `th` >> simp[] >>
  irule ghost_kept_exterior_frame >>
  qexistsl_tac [`tn`, `{i | w2n b <= i /\ i < w2n b+n}`] >>
  simp[op_taint_def] >> conj_tac
  >- (rpt strip_tac >> first_x_assum drule_all >> fs[regions_disjoint_def] >> decide_tac) >>
  rpt strip_tac >> first_x_assum drule_all >> fs[regions_disjoint_def] >> decide_tac
QED
