(* The SHA256 output write shrinks taint outside the fixed prefix. *)
Theory bodyFullHashShaFrame
Ancestors
  bodyPtrHashBuiltinsGhostFrame bodyPtrDefs loweringStateRelDefs
  compileEnv ptrDiscipline venomState finite_map pred_set

Theorem sha_shrinking_ghost_frame_at:
  !D lo d cenv cx es G tn s ctx fn sa t G' tn' writes.
    ghost_inv_at D lo d cenv cx es G tn s /\
    stmt_state_rel H ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
    (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!name b k i. local_region cenv es.scopes s name b k /\
      b <= i /\ i < b+k ==> i NOTIN writes) /\
    (!i. i NOTIN writes ==> mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    tn'.t_mem = tn.t_mem DIFF writes /\ stor_taint_ok_at D tn' t /\
    mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
    ghost_inv_at D lo d cenv cx es G' tn' t /\
    ghost_kept_at lo cenv es sa G tn s G' tn'
Proof
  rpt gen_tac >> strip_tac >>
  `!p k. not_fresh_at sa p /\ ptr_covers G tn p s k ==>
    ptr_covers G' tn' p t k` by
    (rpt strip_tac >> gvs[ptr_covers_def] >> metis_tac[]) >>
  conj_tac >- suspend "invariant" >>
  simp[ghost_kept_at_def] >> metis_tac[]
QED

Resume sha_shrinking_ghost_frame_at[invariant]:
  qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ghost_inv_at_def] >> strip_tac >>
  conj_tac >- suspend "locals" >>
  conj_tac >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
    PairCases_on `x` >> gvs[return_buf_ptr_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (rpt strip_tac >> fs[] >> metis_tac[IN_DIFF]) >>
  conj_tac >- (rpt strip_tac >>
    `not_fresh_at sa x` by metis_tac[local_ptrs_reserved_def] >> metis_tac[]) >>
  gvs[allocas_from_def] >> first_assum ACCEPT_TAC
QED

Resume sha_shrinking_ghost_frame_at[locals]:
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
  `!i. i NOTIN writes ==> (i IN tn'.t_mem <=> i IN tn.t_mem)` by simp[] >>
  drule_all hash_local_robust_exterior_frame >> simp[]
QED

Finalise sha_shrinking_ghost_frame_at
