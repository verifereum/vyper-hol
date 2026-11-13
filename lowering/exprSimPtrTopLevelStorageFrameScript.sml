(* Pointer and ghost posts for an allocated storage copy. *)
Theory exprSimPtrTopLevelStorageFrame
Ancestors
  bodyPtrDefs exprLowering exprSimProps valueEncoding words finite_map
  exprSimPtrTopLevelStorageDecode exprSimPtrTopLevelStoragePost
  pred_set list venomState vyperAST robustCopyTransportPtr valueEncodingProps
  compileEnv loweringStateRelDefs exprLoweringProps exprSimDefs

Theorem toplevel_storage_copy_pointer_post:
  ~is_word_type ann /\
  evaluate_type (get_tenv cx) ann = SOME tv /\
  lookup_var dst t = SOME w /\ ptr_covers G tn dst t nb /\
  val_store_size tv v <= nb /\ type_memory_bytes cenv ann <= nb /\
  (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
    val_in_memory tv v (w2n w) mem) ==>
  ptr_val_ok cx ann v (Var dst) G tn t /\
  ptr_buf_ok cenv (TopLevelName ann nsid) (Var dst) G t
Proof
  simp[ptr_val_ok_def, ptr_mem_ok_def, ptr_buf_ok_def,
    ptr_covers_def, eval_operand_def, lowered_value_type_def, expr_type_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
    arithmeticTheory.LESS_EQ_MONO_ADD_EQ]
QED

Theorem toplevel_robust_exterior_frame:
  val_wf tv v /\
  (!i. p <= i /\ i < p+val_footprint tv v ==> i NOTIN writes) /\
  (!i. i NOTIN writes ==> mem_bytes_at i 1 mem' = mem_bytes_at i 1 mem) /\
  (!i. i NOTIN writes /\ i IN ms1 ==> i IN ms0) /\
  (!m. mem_agree_outside ms0 mem m ==> val_in_memory tv v p m) ==>
  !m. mem_agree_outside ms1 mem' m ==> val_in_memory tv v p m
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!m. mem_agree_outside (ms0 UNION writes) mem' m ==>
       val_in_memory tv v p m` by
    (rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
     rpt (goal_assum (drule_at Any)) >> simp[] >>
     qexistsl_tac [`mem`, `ms0`, `writes`] >> simp[] >> SET_TAC[]) >>
  rpt strip_tac >> first_x_assum irule >>
  gvs[mem_agree_outside_def] >> metis_tac[IN_UNION]
QED

Theorem toplevel_ghost_inv_memory_frame:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x s' = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  (!name entry p sz w.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w ==>
    val_wf entry.type entry.value /\
    (!i. w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
      i NOTIN writes)) /\
  (!i. i NOTIN writes ==> mem_bytes_at i 1 s'.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
  (!i. i NOTIN writes /\ i IN tn'.t_mem ==> i IN tn.t_mem) /\
  es'.scopes = es.scopes /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  s'.vs_call_ctx = s.vs_call_ctx /\ s'.vs_accounts = s.vs_accounts /\
  s'.vs_transient = s.vs_transient ==>
  ghost_inv d cenv cx es' G' tn' s'
Proof
  strip_tac >>
  `!x sz. not_fresh_at sa x /\ ptr_covers G tn x s sz ==>
    ptr_covers G' tn' x s' sz` by
    (rw[ptr_covers_def] >> metis_tac[]) >>
  fs[ghost_inv_def, stor_taint_ok_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      conj_tac >- metis_tac[] >>
      rpt gen_tac >> strip_tac >>
      `lookup_var p s = SOME w` by metis_tac[] >>
      irule toplevel_robust_exterior_frame >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`s.vs_memory`, `s'.vs_memory`, `tn.t_mem`, `tn'.t_mem`, `writes`] >>
      metis_tac[])
  >- (Cases_on `d` >> fs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME bc)` >> PairCases_on `bc` >>
      fs[return_buf_ptr_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem toplevel_ghost_kept_memory_frame:
  (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  (!i. i NOTIN writes /\ i IN tn'.t_mem ==> i IN tn.t_mem) /\
  (!aid off sz i.
    FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!n b sz'. local_region cenv es.scopes s n b sz' ==>
      off+sz <= b \/ b+sz' <= off) /\ off <= i /\ i < off+sz ==>
    i NOTIN writes) /\
  (!n b sz i. local_region cenv es.scopes s n b sz /\ b <= i /\ i < b+sz ==>
    i NOTIN writes) ==>
  ghost_kept cenv es sa G tn s G' tn'
Proof
  simp[ghost_kept_def] >> metis_tac[]
QED

Theorem toplevel_local_footprint_disjoint:
  stmt_state_rel ctx func cenv cx es s /\
  (!name b sz i. local_region cenv es.scopes s name b sz /\
    b <= i /\ i < b+sz ==> i NOTIN writes) ==>
  !name entry p sz w.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w ==>
    val_wf entry.type entry.value /\
    (!i. w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
      i NOTIN writes)
Proof
  rpt strip_tac >>
  `type_memory_size entry.type <= sz /\ val_wf entry.type entry.value` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> metis_tac[]) >>
  `local_region cenv es.scopes s name (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  drule val_footprint_le >> strip_tac >>
  `i < w2n w + sz` by decide_tac >>
  metis_tac[]
QED
