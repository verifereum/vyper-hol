(* Region-separated transport at the single joint allocation/copy endpoint.
   Copied dead storage bytes may remain tainted. *)
Theory bodyFullUnwrapSlotPost
Ancestors
  exprPtrUnwrapStoragePost exprPtrUnwrapEndpointFrames exprPtrUnwrapRetained
  bodyPtrDefs loweringPosts compileEnv exprSimProps localPtrsProps
  ptrDiscipline venomState finite_map arithmetic pred_set

Theorem unwrap_slot_copy_ghost_kept_at:
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP H x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!aid off sz i.
    FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!name b len. local_region cenv es.scopes s0 name b len ==>
      off+sz <= b \/ b+len <= off) /\ off <= i /\ i < off+sz /\ i IN tf.t_mem ==>
    i IN tn.t_mem) /\
  (!name b sz i. local_region cenv es.scopes s0 name b sz /\
    b <= i /\ i < b+sz /\
    (!k. dynarray_len_at cenv name k ==> i < b+k \/ b+k+32 <= i) /\
    i IN tf.t_mem ==> i IN tn.t_mem) /\
  (!i. i < lo /\ i IN tf.t_mem ==> i IN tn.t_mem) ==>
  ghost_kept_at lo cenv es sa Gi ti s0 H tf
Proof
  rw[ghost_kept_at_def] >> metis_tac[]
QED

Theorem copy_local_robust_at[local]:
  local_ptrs_rel func cenv es.scopes s /\ ghost_inv_at D lo d cenv cx es G tn s /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    start+nb <= b \/ b+sz <= start) /\
  (!a k. a+k <= start \/ start+nb <= a ==>
    mem_bytes_at a k z.vs_memory = mem_bytes_at a k s.vs_memory) /\
  (!j. j < start \/ start+nb <= j ==> (j IN tf.t_mem <=> j IN tn.t_mem)) ==>
  !name entry p sz w.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\ lookup_var p s = SOME w ==>
    !mem. mem_agree_outside tf.t_mem z.vs_memory mem ==>
      val_in_memory entry.type entry.value (w2n w) mem
Proof
  rpt strip_tac >>
  `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
    (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  `val_footprint entry.type entry.value <= sz` by
    metis_tac[val_footprint_le, LESS_EQ_TRANS] >>
  `local_region cenv es.scopes s name (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `start+nb <= w2n w \/ w2n w+sz <= start` by metis_tac[] >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory entry.type entry.value (w2n w) m` by
    (fs[ghost_inv_at_def] >> metis_tac[]) >>
  irule copy_retained_robust_value >> metis_tac[]
QED

Theorem unwrap_slot_copy_ghost_inv_at:
  ghost_inv_at D lo d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  local_ptrs_rel func cenv es.scopes s /\
  (!name b len. local_region cenv es.scopes s name b len ==>
    start+nb <= b \/ b+len <= start) /\
  (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s /\
    FLOOKUP H x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!a k. a+k <= start \/ start+nb <= a ==>
    mem_bytes_at a k z.vs_memory = mem_bytes_at a k s.vs_memory) /\
  (!j. j < start \/ start+nb <= j ==> (j IN tf.t_mem <=> j IN tn.t_mem)) /\
  lo <= start /\ stor_taint_ok_at D tf z /\ allocas_from lo z /\ lo <= z.vs_alloca_next ==>
  ghost_inv_at D lo d cenv cx es H tf z
Proof
  strip_tac >>
  `!name entry p sz w.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\ lookup_var p s = SOME w ==>
    !mem. mem_agree_outside tf.t_mem z.vs_memory mem ==>
      val_in_memory entry.type entry.value (w2n w) mem` by
    (rpt strip_tac >> irule copy_local_robust_at >>
     goal_assum (drule_at (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
     goal_assum (drule_at (Pat `lookup_scopes _ _ = _`)) >>
     goal_assum (drule_at (Pat `FLOOKUP _ _ = _`)) >>
     goal_assum (drule_at (Pat `mem_agree_outside _ _ _`)) >>
     qexistsl [`nb`, `start`] >> gvs[ADD_COMM] >> metis_tac[]) >>
  `mem_bytes_at 0 lo z.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (first_assum irule >> simp[]) >>
  fs[ghost_inv_at_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
      conj_tac >- (fs[ptr_covers_def] >> metis_tac[]) >> metis_tac[])
  >- (Cases_on `d` >- simp[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME pair) cenv H tf z` >> PairCases_on `pair` >>
      gvs[return_buf_ptr_def, ptr_covers_def] >> metis_tac[])
  >- (rpt strip_tac >> `i < start` by decide_tac >> metis_tac[])
  >> rpt strip_tac >> fs[local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem unwrap_slot_copy_wb_frame:
  (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP z.vs_allocas aid = SOME entry) /\
  (!aid off sz. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!name b len. local_region cenv es.scopes s name b len ==>
      off+sz <= b \/ b+len <= off) ==> off+sz <= start \/ start+nb <= off) /\
  (!name b len. local_region cenv es.scopes s name b len ==>
    b+len <= start \/ start+nb <= b) /\
  (!off len. off+len <= start \/ start+nb <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) ==>
  wb_frame cenv es sa s z
Proof
  strip_tac >> simp[wb_frame_def] >> conj_tac
  >- metis_tac[] >>
  irule locals_kept_regions >> metis_tac[]
QED
