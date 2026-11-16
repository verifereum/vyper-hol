Theory bodyFullStructLitFrames
Ancestors bodyPtrMakeArrayMemoryFrame
  bodyPtrMakeArrayCopyStateFrame
  exprSimStorageCopy venomState
  robustCopyTransportPtr typedMemoryCopy bodyPtrDefs ptrDiscipline compileEnv
  freshWrites loweringStateRelDefs

(* The write window may be a proper suffix of the allocated root.  In
   particular this argument does not exclude constructor mode. *)
Theorem structlit_store_state_prefix_frame:
  stmt_state_rel H ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  typed_copy_state_frame sa (addr+off) n s z /\ off+n <= capacity /\
  (!name b k. local_region ce es.scopes s name b k ==>
     regions_disjoint addr capacity b k) /\
  MEM (mk_inst aid ALLOCA [Lit (n2w capacity)] [root]) (fn_insts func) /\
  FLOOKUP s.vs_allocas aid = SOME (addr,capacity) /\
  literal_prefix_ok cells tn s /\
  EVERY (\(tv,v,p,k). p+k <= addr+off) cells /\
  (!i. ~(addr+off <= i /\ i < addr+off+n) ==>
     (i IN tm.t_mem <=> i IN tn.t_mem)) ==>
  stmt_state_rel H ctx func ce cx es z /\ literal_prefix_ok cells tm z
Proof
  strip_tac >>
  `!a k. a+k <= addr+off \/ addr+off+n <= a ==>
     mem_bytes_at a k z.vs_memory = mem_bytes_at a k s.vs_memory` by
    (gvs[typed_copy_state_frame_def, typed_copy_frame_def] >> metis_tac[]) >>
  conj_tac
  >- (fs[typed_copy_state_frame_def, typed_copy_frame_def] >>
      `copy_static z = copy_static s` by
        gvs[copy_static_def, venom_state_component_equality] >>
      irule literal_copy_window_stmt_state_rel >>
      qexistsl_tac [`aid`, `addr`, `capacity`, `root`, `sa`, `sa`, `s`] >>
      simp[] >> conj_tac >- metis_tac[] >>
      `!p k. p+k <= addr \/ addr+capacity <= p ==>
        p+k <= addr+off \/ addr+(n+off) <= p` by decide_tac >> metis_tac[]) >>
  `!i. ~(addr+off <= i /\ i < addr+off+n) ==>
    i+1 <= addr+off \/ addr+off+n <= i` by decide_tac >>
  irule literal_prefix_store_frame >> qexistsl_tac [`addr+off`, `n`, `s`, `tn`] >>
  metis_tac[]
QED

(* Pointwise semantic frame; no compile-specific or destination-value posts. *)
Theorem structlit_store_ghost_frame:
  typed_copy_state_frame k B N s q /\
  (!p. not_fresh_at k p ==> FLOOKUP Gq p = FLOOKUP G p /\
    op_taint tq (Var p) = op_taint tn (Var p)) /\
  tq.t_imm = tn.t_imm /\ tq.t_stor = tn.t_stor /\ tq.t_trans = tn.t_trans /\
  (!i. ~(B <= i /\ i < B+N) ==> (i IN tq.t_mem <=> i IN tn.t_mem)) /\
  ghost_inv_at D lo d ce cx ee G tn s /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\
  sa.cs_next_var <= k.cs_next_var /\ local_ptrs_reserved ce k /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at k x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at k x) /\
  (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at k x) /\
  lo <= B /\
  (!name entry p sz w. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w ==>
    val_wf entry.type entry.value /\
    (w2n w + val_footprint entry.type entry.value <= B \/ B+N <= w2n w)) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
    off+sz <= B \/ B+N <= off) /\
  (!name b sz. local_region ce es.scopes s0 name b sz ==>
    b+sz <= B \/ B+N <= b) ==>
  ghost_inv_at D lo d ce cx ee Gq tq q /\
  ghost_kept_at lo ce es sa Gi ti s0 Gq tq
Proof
  strip_tac >>
  `q.vs_call_ctx = s.vs_call_ctx /\ q.vs_accounts = s.vs_accounts /\
   q.vs_transient = s.vs_transient /\ q.vs_immutables = s.vs_immutables /\
   q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next` by
    gvs[typed_copy_state_frame_def, venom_state_component_equality] >>
  `!p. not_fresh_at k p ==> lookup_var p q = lookup_var p s` by
    gvs[typed_copy_state_frame_def] >>
  `!i. ~(B <= i /\ i < B+N) ==>
    mem_bytes_at i 1 q.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (gvs[typed_copy_state_frame_def, typed_copy_frame_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `mem_bytes_at 0 lo q.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (gvs[typed_copy_state_frame_def, typed_copy_frame_def] >>
     first_x_assum irule >> decide_tac) >>
  `!p sz. not_fresh_at k p /\ ptr_covers G tn p s sz ==>
    ptr_covers Gq tq p q sz` by
    (rpt strip_tac >> gvs[ptr_covers_def] >> metis_tac[]) >>
  conj_tac >- suspend "inv" >> suspend "kept"
QED

Resume structlit_store_ghost_frame[inv]:
  qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ghost_inv_at_def] >> strip_tac >>
  conj_tac >- suspend "locals" >>
  conj_tac >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
    PairCases_on `x` >> gvs[return_buf_ptr_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- gvs[stor_taint_ok_at_def] >>
  conj_tac >- (rpt strip_tac >> `~(B <= i /\ i < B+N)` by decide_tac >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  gvs[allocas_from_def] >> metis_tac[]
QED

Resume structlit_store_ghost_frame[locals]:
  rpt gen_tac >> strip_tac >>
  `not_fresh_at k p` by metis_tac[local_ptrs_reserved_def] >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `lookup_var p s = SOME w` by metis_tac[] >>
  `val_wf entry.type entry.value /\
   (w2n w + val_footprint entry.type entry.value <= B \/ B+N <= w2n w)` by metis_tac[] >>
  `!i. w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
    ~(B <= i /\ i < B+N)` by (rpt strip_tac >> decide_tac) >>
  irule robust_val_in_memory_exterior_frame >>
  (conj_tac >- metis_tac[]) >>
  qexistsl_tac [`s.vs_memory`, `q.vs_memory`, `tn.t_mem`, `tq.t_mem`, `{i | B <= i /\ i < B+N}`] >>
  simp[] >> metis_tac[]
QED

Resume structlit_store_ghost_frame[kept]:
  `!x. not_fresh_at sa x ==> not_fresh_at k x` by metis_tac[not_fresh_at_mono] >>
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ghost_kept_at_def] >> strip_tac >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (rpt strip_tac >>
    `off+sz <= B \/ B+N <= off` by metis_tac[] >>
    `~(B <= i /\ i < B+N)` by decide_tac >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >>
    `b+sz <= B \/ B+N <= b` by metis_tac[] >>
    `~(B <= i /\ i < B+N)` by decide_tac >> metis_tac[]) >>
  rpt strip_tac >> `~(B <= i /\ i < B+N)` by decide_tac >> metis_tac[]
QED

Finalise structlit_store_ghost_frame
