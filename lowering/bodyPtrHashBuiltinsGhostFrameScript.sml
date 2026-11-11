(* Exterior memory/taint transport for hash suffix frames. *)
Theory bodyPtrHashBuiltinsGhostFrame
Ancestors bodyPtrDefs robustCopyTransportPtr exprSimProps exprLoweringProps
  compileEnv venomState finite_map pred_set

Theorem hash_ghost_kept_frame:
  !cenv es sa G tn s G' tn'.
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!aid off sz i.
      FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!n b sz'. local_region cenv es.scopes s n b sz' ==>
        off + sz <= b \/ b + sz' <= off) /\
      off <= i /\ i < off + sz /\ i IN tn'.t_mem ==> i IN tn.t_mem) /\
    (!n b sz i. local_region cenv es.scopes s n b sz /\
      b <= i /\ i < b + sz /\
      (!k. dynarray_len_at cenv n k ==> i < b+k \/ b+k+32 <= i) /\
      i IN tn'.t_mem ==> i IN tn.t_mem) ==>
    ghost_kept cenv es sa G tn s G' tn'
Proof
  pure_rewrite_tac[ghost_kept_def] >> metis_tac[]
QED

Theorem hash_local_robust_exterior_frame:
  !ctx fn cenv cx es s tn t tn' writes name entry p sz w.
    stmt_state_rel ctx fn cenv cx es s /\
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\
    (!n b k i. local_region cenv es.scopes s n b k /\
      b <= i /\ i < b+k ==> i NOTIN writes) /\
    (!i. i NOTIN writes ==> mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    (!i. i NOTIN writes ==> (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory entry.type entry.value (w2n w) m) ==>
    !m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
      val_in_memory entry.type entry.value (w2n w) m
Proof
  rpt gen_tac >> strip_tac >>
  `local_ptrs_rel fn cenv es.scopes s` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
    metis_tac[local_ptrs_rel_def] >>
  `local_region cenv es.scopes s name (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `val_footprint entry.type entry.value <= sz` by
    metis_tac[val_footprint_le, arithmeticTheory.LESS_EQ_TRANS] >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `tn.t_mem`, `tn'.t_mem`, `writes`] >>
  simp[] >> rpt strip_tac >>
  `i < w2n w + sz` by decide_tac >> metis_tac[]
QED

Theorem hash_ghost_inv_exterior_frame:
  !d cenv cx es G tn s ctx fn sa t G' tn' writes.
    ghost_inv d cenv cx es G tn s /\
    stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
    (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!n b k i. local_region cenv es.scopes s n b k /\
      b <= i /\ i < b+k ==> i NOTIN writes) /\
    (!i. i NOTIN writes ==> mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    (!i. i NOTIN writes ==> (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    stor_taint_ok cx tn' t ==>
    ghost_inv d cenv cx es G' tn' t
Proof
  rpt gen_tac >> strip_tac >>
  `!p k. not_fresh_at sa p /\ ptr_covers G tn p s k ==>
    ptr_covers G' tn' p t k` by
    (rpt strip_tac >> gvs[ptr_covers_def] >> metis_tac[]) >>
  qpat_x_assum `ghost_inv _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ghost_inv_def] >> strip_tac >>
  conj_tac >- suspend "locals" >>
  conj_tac >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
    PairCases_on `x` >> gvs[return_buf_ptr_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >> simp[]
QED

Resume hash_ghost_inv_exterior_frame[locals]:
  rpt gen_tac >> strip_tac >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  `ptr_covers G tn p s sz /\
   !w mem. lookup_var p s = SOME w /\
     mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory entry.type entry.value (w2n w) mem` by metis_tac[] >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `lookup_var p s = SOME w` by metis_tac[] >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory entry.type entry.value (w2n w) m` by metis_tac[] >>
  drule_all hash_local_robust_exterior_frame >> simp[]
QED

Finalise hash_ghost_inv_exterior_frame

Theorem hash_ghost_inv_inst_idx:
  !d cenv cx es G tn s k.
    ghost_inv d cenv cx es G tn (s with vs_inst_idx := k) <=>
    ghost_inv d cenv cx es G tn s
Proof
  Cases_on `d` >>
  simp[ghost_inv_def, ptr_covers_def, lookup_var_def,
    return_buf_ptr_def, stor_taint_ok_def] >>
  PairCases_on `x` >>
  simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def]
QED

(* Read-only suffixes need no semantic local-value frame premise. *)
Theorem hash_readonly_ghost_inv:
  !d cenv cx es G tn s t G' tn' sa.
    ghost_inv d cenv cx es G tn s /\
    (t with vs_vars := s.vs_vars) = s /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    local_ptrs_reserved cenv sa /\
    (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
    (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p)) ==>
    ghost_inv d cenv cx es G' tn' t
Proof
  rpt gen_tac >> strip_tac >>
  `t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
   t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient` by
    (qpat_x_assum `(t with vs_vars := s.vs_vars) = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `!p k. not_fresh_at sa p /\ ptr_covers G tn p s k ==>
    ptr_covers G' tn' p t k` by
    (rpt strip_tac >> gvs[ptr_covers_def] >> metis_tac[]) >>
  qpat_x_assum `ghost_inv _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ghost_inv_def] >> strip_tac >>
  conj_tac >- (rpt gen_tac >> strip_tac >>
    `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
    conj_tac >- metis_tac[] >> metis_tac[]) >>
  conj_tac >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
    PairCases_on `x` >> gvs[return_buf_ptr_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >> gvs[stor_taint_ok_def]
QED
