(* Exterior-write transport for statement ghosts; writes may contain tainted padding. *)
Theory logFieldGhostPtr
Ancestors logDataFieldRunPtr logTopicFramePtr robustCopyTransportPtr
  bodyPtrDefs stmtFragPtr compileEnv exprSimProps stmtSimDefs stmtSimLogDataFrame
  ptrDiscipline venomState finite_map words pred_set arithmetic

Theorem ghost_kept_exterior_transport:
  ghost_kept ce es sa G0 tn0 s0 G tn /\ sa.cs_next_var <= sm.cs_next_var /\
  (!p. not_fresh_at sm p ==>
    FLOOKUP H p = FLOOKUP G p /\ op_taint tm (Var p) = op_taint tn (Var p)) /\
  (!i. i NOTIN writes ==> (i IN tm.t_mem <=> i IN tn.t_mem)) /\
  (!aid off sz i.
    FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!n b sz'. local_region ce es.scopes s0 n b sz' ==>
      off+sz <= b \/ b+sz' <= off) /\ off <= i /\ i < off+sz ==> i NOTIN writes) /\
  (!n b sz i. local_region ce es.scopes s0 n b sz /\ b <= i /\ i < b+sz /\
    (!k. dynarray_len_at ce n k ==> i < b+k \/ b+k+32 <= i) ==> i NOTIN writes) ==>
  ghost_kept ce es sa G0 tn0 s0 H tm
Proof
  rw[ghost_kept_def] >> metis_tac[not_fresh_at_mono]
QED

Theorem ghost_inv_exterior_transport:
  ghost_inv d ce cx es G tn s /\ local_ptrs_rel func ce es.scopes s /\
  local_ptrs_reserved ce sm /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!n b sz i. local_region ce es.scopes s n b sz /\ b <= i /\ i < b+sz ==>
    i NOTIN writes) /\
  (!i. i NOTIN writes ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tm.t_mem <=> i IN tn.t_mem)) /\
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_call_ctx = s.vs_call_ctx /\ tm.t_stor = tn.t_stor /\
  tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
  (!p. not_fresh_at sm p ==>
    lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
    op_taint tm (Var p) = op_taint tn (Var p)) ==>
  ghost_inv d ce cx es H tm t
Proof
  strip_tac >> simp[ghost_inv_def] >> conj_tac
  >- suspend "locals" >>
  conj_tac
  >- (Cases_on `d` >- simp[return_buf_ptr_def] >>
      PairCases_on `x` >> gvs[ghost_inv_def,return_buf_ptr_def,ptr_covers_def] >>
      metis_tac[]) >>
  gvs[ghost_inv_def,stor_taint_ok_def]
QED
Resume ghost_inv_exterior_transport[locals]:
  rpt gen_tac >> strip_tac >>
  `not_fresh_at sm p` by metis_tac[local_ptrs_reserved_def] >>
  `ptr_covers G tn p s sz /\
   !w mem. lookup_var p s = SOME w /\ mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory entry.type entry.value (w2n w) mem` by metis_tac[ghost_inv_def] >>
  conj_tac >- (gvs[ptr_covers_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `lookup_var p s = SOME w` by metis_tac[] >>
  `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
    (qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
     rewrite_tac[local_ptrs_rel_def] >> strip_tac >> first_x_assum drule_all >> gvs[]) >>
  `local_region ce es.scopes s name (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `val_footprint entry.type entry.value <= sz` by
    metis_tac[val_footprint_le,LESS_EQ_TRANS] >>
  irule robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`,`t.vs_memory`,`tn.t_mem`,`tm.t_mem`,`writes`] >>
  simp[] >> rpt gen_tac >> strip_tac >>
  `i < w2n w + sz` by decide_tac >> metis_tac[]
QED
Finalise ghost_inv_exterior_transport
