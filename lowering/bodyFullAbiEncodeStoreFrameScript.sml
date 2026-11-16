(* Compiler-independent caller ghosts across a fresh bounded write. *)
Theory bodyFullAbiEncodeStoreFrame
Ancestors
  bodySimFull bodyPtrDefs typedMemoryCopy robustCopyTransportPtr
  loweringStateRelDefs exprLoweringProps localPtrsProps ptrDiscipline
  venomState finite_map pred_set arithmetic freshWrites

Theorem abi_encode_store_exterior_ghost_frame:
  typed_copy_state_frame k B N s q /\
  (!p. not_fresh_at k p ==> FLOOKUP Gq p = FLOOKUP G p /\
    op_taint tq (Var p) = op_taint tn (Var p)) /\
  tq.t_imm = tn.t_imm /\ tq.t_stor = tn.t_stor /\ tq.t_trans = tn.t_trans /\
  (!i. ~(B <= i /\ i < B+N) ==> (i IN tq.t_mem <=> i IN tn.t_mem)) /\
  ghost_inv_at D lo d cenv cx ee G tn s /\
  ghost_kept_at lo cenv es sa Gi ti s0 G tn /\
  sa.cs_next_var <= k.cs_next_var /\ local_ptrs_reserved cenv k /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at k x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at k x) /\
  (!x. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at k x) /\
  lo <= B /\
  (!name entry p sz w. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w ==>
    val_wf entry.type entry.value /\
    (w2n w + val_footprint entry.type entry.value <= B \/ B+N <= w2n w)) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
    off+sz <= B \/ B+N <= off) /\
  (!name b sz. local_region cenv es.scopes s0 name b sz ==>
    b+sz <= B \/ B+N <= b) ==>
  ghost_inv_at D lo d cenv cx ee Gq tq q /\
  ghost_kept_at lo cenv es sa Gi ti s0 Gq tq
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
  conj_tac >- suspend "inv" >>
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

Resume abi_encode_store_exterior_ghost_frame[inv]:
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

Resume abi_encode_store_exterior_ghost_frame[locals]:
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

Finalise abi_encode_store_exterior_ghost_frame
