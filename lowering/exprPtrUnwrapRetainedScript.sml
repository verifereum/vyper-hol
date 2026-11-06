Theory exprPtrUnwrapRetained
Ancestors
  exprPtrUnwrapPostFrames exprPtrUnwrapFramedLoop exprPtrUnwrapAllocationFrame
  exprPtrUnwrapAllocSeparation exprSimAlloc exprSimProps localPtrsProps
  robustCopyTransportPtr bodyPtrDefs ptrDiscipline exprLoweringProps loweringPosts
  finite_map compileEnv arithmetic bufferAllocationExecution allocationPtr venomInst
  exprPtrUnwrapLoopInvariant exprPtrUnwrapRuntimeFrame

Theorem copy_retained_no_new_taint:
  ((start:num)+nb <= off \/ off+sz <= start) /\ off <= i /\ i < off+sz /\
  (!j. j < start \/ start+nb <= j ==> (j IN tm.t_mem <=> j IN tn.t_mem)) /\
  (!j. j < start \/ start+nb <= j ==> (j IN tf.t_mem <=> j IN tm.t_mem)) ==>
  (i IN tf.t_mem <=> i IN tn.t_mem)
Proof
  strip_tac >> `i < start \/ start+nb <= i` by decide_tac >> metis_tac[]
QED

Theorem copy_retained_robust_value:
  val_wf tv v /\ val_footprint tv v <= sz /\
  (start+nb <= p \/ p+sz <= start) /\
  mem_bytes_at p sz t.vs_memory = mem_bytes_at p sz s.vs_memory /\
  (!j. j < start \/ start+nb <= j ==> (j IN tm.t_mem <=> j IN tn.t_mem)) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v p m) ==>
  !m. mem_agree_outside tm.t_mem t.vs_memory m ==> val_in_memory tv v p m
Proof
  rpt strip_tac >> (irule robust_val_in_memory_copy_transport >>
  conj_tac >- simp[] >>
  qexistsl [`s.vs_memory`, `t.vs_memory`, `sz`, `p`, `tn.t_mem`, `tm.t_mem`] >>
  simp[] >> rpt strip_tac >> first_x_assum irule >> decide_tac)
QED

Theorem unwrap_alloc_local_separation:
  compile_alloc_buffer nb sm = (buf,mid) /\ fn_has_code sm mid func /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\ nb < dimword (:256) /\
  local_region cenv es.scopes s name off len ==>
  buffer_allocation_base s sm.cs_next_id + nb <= off \/
  off+len <= buffer_allocation_base s sm.cs_next_id
Proof
  strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  `local_ptrs_rel func cenv es.scopes s /\ alloca_inv s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id`
  >- (simp[buffer_allocation_base_def] >>
      drule local_ptrs_rel_above_frontier >>
      disch_then (qspecl_then [`name`, `off`, `len`, `s.vs_alloca_next`, `nb`] mp_tac) >>
      simp[regions_disjoint_def] >> decide_tac) >>
  rename1 `FLOOKUP s.vs_allocas sm.cs_next_id = SOME site` >>
  PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString sm.cs_next_var))` by
    (irule local_ptrs_reserved_fresh >> qexists_tac `sm` >> simp[]) >>
  drule_at (Pat `MEM _ _`) local_ptrs_rel_alloca_disjoint >>
  simp[mk_inst_def] >> disch_then drule_all >>
  simp[buffer_allocation_base_def, regions_disjoint_def]
QED

Theorem unwrap_alloc_entry_local_separation:
  compile_alloc_buffer nb sm = (buf,mid) /\ fn_has_code sm mid func /\
  vv_post ctx func cenv cx e es sa sm s0 es' result vv s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sm /\ MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  nb < dimword (:256) /\ local_region cenv es.scopes s0 name off len ==>
  buffer_allocation_base s sm.cs_next_id + nb <= off \/
  off+len <= buffer_allocation_base s sm.cs_next_id
Proof
  strip_tac >>
  `local_region cenv es'.scopes s name off len` by
    (irule local_region_frame_fwd >>
     qexistsl [`s0`, `sa`, `es.scopes`] >> fs[vv_post_def]) >>
  irule unwrap_alloc_local_separation >> metis_tac[vv_post_def]
QED

Theorem unwrap_copy_ghost_kept:
  compile_alloc_buffer nb sm = (buf,mid) /\ fn_has_code sm mid func /\
  vv_post ctx func cenv cx e es sa sm s0 es' result vv s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sm /\ MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  nb < dimword (:256) /\ sa.cs_next_id <= sm.cs_next_id /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP H x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x)) /\
  (!i. i < buffer_allocation_base s sm.cs_next_id \/
       buffer_allocation_base s sm.cs_next_id + nb <= i ==>
       (i IN tm.t_mem <=> i IN tn.t_mem)) /\
  (!i. i < buffer_allocation_base s sm.cs_next_id \/
       buffer_allocation_base s sm.cs_next_id + nb <= i ==>
       (i IN tf.t_mem <=> i IN tm.t_mem)) ==>
  ghost_kept cenv es sa G0 tn0 s0 H tf
Proof
  strip_tac >> irule copy_ghost_kept_transport >>
  qexistsl [`G`, `tn`] >> simp[] >> reverse conj_tac
  >- (rpt strip_tac >>
      drule_all unwrap_alloc_old_entry_separation >> disch_tac >>
      `i IN tf.t_mem <=> i IN tn.t_mem` by
        (irule copy_retained_no_new_taint >> metis_tac[]) >> metis_tac[]) >>
  rpt strip_tac >>
  drule_all unwrap_alloc_entry_local_separation >> disch_tac >>
  `i IN tf.t_mem <=> i IN tn.t_mem` by
    (irule copy_retained_no_new_taint >> metis_tac[]) >> metis_tac[]
QED

Theorem copy_retained_frame_robust:
  slot_copy_runtime_frame cs d i r t /\ r.vs_memory = s.vs_memory /\
  val_wf tv v /\ val_footprint tv v <= sz /\
  (w2n d + 32*i <= p \/ p+sz <= w2n d) /\
  (!j. j < w2n d \/ w2n d+32*i <= j ==> (j IN tf.t_mem <=> j IN tn.t_mem)) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v p m) ==>
  !m. mem_agree_outside tf.t_mem t.vs_memory m ==> val_in_memory tv v p m
Proof
  rpt strip_tac >> (gnvs[slot_copy_runtime_frame_def] >>
  irule copy_retained_robust_value >> simp[] >>
  qexistsl [`32*i`, `s`, `w2n d`, `sz`, `t`, `tf`, `tn`] >> simp[] >> metis_tac[])
QED

Theorem copy_framed_stor_taint:
  stor_taint_ok cx tn0 r /\ slot_copy_runtime_frame cs d i r s /\
  slot_copy_ghost_inv cs load p d root n G0 tn0 i G tn s ==>
  stor_taint_ok cx tn s
Proof
  strip_tac >> fs[slot_copy_runtime_frame_def] >>
  irule copy_stor_taint_frame >>
  qexistsl [`r`, `tn0`] >> fs[slot_copy_ghost_inv_def]
QED
