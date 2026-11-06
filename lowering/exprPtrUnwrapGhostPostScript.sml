Theory exprPtrUnwrapGhostPost
Ancestors
  exprPtrUnwrapRetained bodyPtrDefs compileEnv exprLoweringProps
  ptrDiscipline loweringPosts finite_map exprSimProps

(* Reconstruct the invariant at a shared runtime/ghost endpoint. *)
Theorem unwrap_ghost_inv_transport:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv st /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x k. not_fresh_at st x /\ ptr_covers G tn x s k ==> ptr_covers H tm x t k) /\
  (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
    op_taint tm (Var x) = op_taint tn (Var x)) /\
  (!name entry p sz w.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\ lookup_var p s = SOME w ==>
    !mem. mem_agree_outside tm.t_mem t.vs_memory mem ==>
      val_in_memory entry.type entry.value (w2n w) mem) /\
  stor_taint_ok cx tm t ==>
  ghost_inv d cenv cx es H tm t
Proof
  strip_tac >> fs[ghost_inv_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at st p` by
        (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
      conj_tac >- metis_tac[] >> metis_tac[]) >>
  Cases_on `d` >- simp[return_buf_ptr_def] >>
  rename1 `return_buf_ptr (SOME pair) cenv H tm t` >> PairCases_on `pair` >>
  fs[return_buf_ptr_def] >> metis_tac[]
QED

Theorem unwrap_local_robust_frame:
  local_ptrs_rel func cenv es.scopes s /\ ghost_inv d cenv cx es G tn s /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    start+nb <= b \/ b+sz <= start) /\
  (!a k. a+k <= start \/ start+nb <= a ==>
    mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory) /\
  (!j. j < start \/ start+nb <= j ==> (j IN tm.t_mem <=> j IN tn.t_mem)) ==>
  !name entry p sz w.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\ lookup_var p s = SOME w ==>
    !mem. mem_agree_outside tm.t_mem t.vs_memory mem ==>
      val_in_memory entry.type entry.value (w2n w) mem
Proof
  rpt strip_tac >>
  `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
    (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  `val_footprint entry.type entry.value <= sz` by
    metis_tac[val_footprint_le, arithmeticTheory.LESS_EQ_TRANS] >>
  `local_region cenv es.scopes s name (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `start+nb <= w2n w \/ w2n w+sz <= start` by metis_tac[] >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory entry.type entry.value (w2n w) m` by
    (fs[ghost_inv_def] >> metis_tac[]) >>
  irule copy_retained_robust_value >> metis_tac[]
QED
