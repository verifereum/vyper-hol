(* Observational transport of statement-boundary pointer ghosts. *)
Theory ghostObservationPtr
Ancestors bodyPtrDefs robustCopyTransportPtr valueEncodingProps
  valueEncodingProofs

Theorem ghost_kept_observational_frame:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tnf (Var x) = op_taint tn (Var x)) /\
  (!aid off sz i.
    FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
      off+sz <= b \/ b+sz' <= off) /\
    off <= i /\ i < off+sz /\ i IN tnf.t_mem ==> i IN tn.t_mem) /\
  (!n b sz i.
    local_region cenv es.scopes s0 n b sz /\ b <= i /\ i < b+sz /\
    (!k. dynarray_len_at cenv n k ==> i < b+k \/ b+k+32 <= i) /\
    i IN tnf.t_mem ==> i IN tn.t_mem) ==>
  ghost_kept cenv es sa G0 tn0 s0 Gf tnf
Proof
  simp[ghost_kept_def] >> rpt strip_tac >> metis_tac[]
QED

Theorem ghost_kept_exterior_frame:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!x. not_fresh_at sa x ==>
    FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tnf (Var x) = op_taint tn (Var x)) /\
  (!i. i NOTIN R /\ i IN tnf.t_mem ==> i IN tn.t_mem) /\
  (!aid off sz i.
    FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
      off+sz <= b \/ b+sz' <= off) /\
    off <= i /\ i < off+sz ==> i NOTIN R) /\
  (!n b sz i.
    local_region cenv es.scopes s0 n b sz /\ b <= i /\ i < b+sz /\
    (!k. dynarray_len_at cenv n k ==> i < b+k \/ b+k+32 <= i) ==>
    i NOTIN R) ==>
  ghost_kept cenv es sa G0 tn0 s0 Gf tnf
Proof
  strip_tac >> irule ghost_kept_observational_frame >>
  qexistsl_tac [`G`, `tn`] >>
  RULE_ASSUM_TAC (REWRITE_RULE[arithmeticTheory.ADD_ASSOC]) >>
  pure_rewrite_tac[arithmeticTheory.ADD_ASSOC] >> metis_tac[]
QED

Theorem robust_val_in_memory_exterior_no_new_taint:
  !tn tn' mem mem' R tv v p.
    val_wf tv v /\
    (!i. p <= i /\ i < p + val_footprint tv v ==> i NOTIN R) /\
    (!i. i NOTIN R ==> mem_bytes_at i 1 mem' = mem_bytes_at i 1 mem) /\
    (!i. i NOTIN R /\ i IN tn' ==> i IN tn) /\
    (!m. mem_agree_outside tn mem m ==> val_in_memory tv v p m) ==>
    !m. mem_agree_outside tn' mem' m ==> val_in_memory tv v p m
Proof
  rpt gen_tac >> strip_tac >>
  `!m. mem_agree_outside (tn' UNION (tn DIFF R)) mem' m ==>
    val_in_memory tv v p m` by
    (rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
     conj_tac >- simp[] >>
     qexistsl_tac [`mem`, `mem'`, `tn`, `tn' UNION (tn DIFF R)`, `R`] >>
     simp[] >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum irule >>
  fs[mem_agree_outside_def] >> metis_tac[]
QED

Theorem ghost_inv_exterior_frame:
  ghost_inv d cenv cx es G tn s /\
  (!name entry p sz.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    val_wf entry.type entry.value /\
    lookup_var p sf = lookup_var p s /\
    ptr_covers Gf tnf p sf sz /\
    (!w i. lookup_var p s = SOME w /\ w2n w <= i /\
      i < w2n w + val_footprint entry.type entry.value ==> i NOTIN R)) /\
  (!i. i NOTIN R ==>
    mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
  (!i. i NOTIN R /\ i IN tnf.t_mem ==> i IN tn.t_mem) /\
  return_buf_ptr d cenv Gf tnf sf /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    op_taint tnf (Var x) = {}) /\
  stor_taint_ok cx tnf sf ==>
  ghost_inv d cenv cx es Gf tnf sf
Proof
  strip_tac >> simp[ghost_inv_def] >> rpt strip_tac >-
    metis_tac[] >>
  `val_wf entry.type entry.value /\ lookup_var p sf = lookup_var p s /\
   (!w i. lookup_var p s = SOME w /\ w2n w <= i /\
      i < w2n w + val_footprint entry.type entry.value ==> i NOTIN R)` by
    metis_tac[] >>
  irule robust_val_in_memory_exterior_no_new_taint >>
  conj_tac >- simp[] >>
  qexistsl_tac [`R`, `s.vs_memory`, `sf.vs_memory`, `tn.t_mem`, `tnf.t_mem`] >>
  simp[] >> fs[ghost_inv_def] >> metis_tac[]
QED
