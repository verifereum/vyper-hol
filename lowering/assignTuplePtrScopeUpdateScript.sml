(* Robust reconstruction of the ghost invariant after updating one local.
   Padding within the write window may acquire taint. *)
Theory assignTuplePtrScopeUpdate
Ancestors
  bodyPtrDefs robustCopyTransportPtr

Theorem ghost_inv_local_copy_update:
  ghost_inv d cenv cx es G tn s /\
  (!name entry. lookup_scopes name es'.scopes = SOME entry ==>
    (?old. lookup_scopes name es.scopes = SOME old) /\
    (name = id ==> entry.type = tv /\ entry.value = v) /\
    (name <> id ==> lookup_scopes name es.scopes = SOME entry)) /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p t = lookup_var p s /\
    (ptr_covers G tn p s sz ==> ptr_covers G' tn' p t sz)) /\
  (!entry p sz w. lookup_scopes id es'.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p t = SOME w ==> w2n w = dst) /\
  val_wf tv v /\ val_footprint tv v <= n /\
  mem_bytes_at dst n t.vs_memory = mem_bytes_at src n s.vs_memory /\
  (!i. i < n ==> (dst+i IN tn'.t_mem <=> src+i IN tn.t_mem)) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v src m) /\
  (!i. i NOTIN writes ==> mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
  (!i. i NOTIN writes ==> (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
  (!name entry p sz w. name <> id /\
    lookup_scopes name es'.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w ==>
    val_wf entry.type entry.value /\
    (!i. w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==> i NOTIN writes)) /\
  return_buf_ptr d cenv G' tn' t /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  stor_taint_ok cx tn' t
  ==> ghost_inv d cenv cx es' G' tn' t
Proof
  strip_tac >>
  `!m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
       val_in_memory tv v dst m` by
    (rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
     simp[] >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> qexists_tac `n` >> simp[arithmeticTheory.ADD_COMM]) >>
  fs[ghost_inv_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!name entry. lookup_scopes name es'.scopes = SOME entry ==> _`
        drule >> strip_tac >>
      qpat_assum `!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> _`
        drule >> strip_tac >>
      conj_tac >- metis_tac[] >>
      rpt gen_tac >> strip_tac >>
      Cases_on `name = id`
      >- (gvs[] >> metis_tac[]) >>
      `lookup_var p s = SOME w` by metis_tac[] >>
      `val_wf entry.type entry.value /\
       (!i. w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==> i NOTIN writes)`
        by metis_tac[] >>
      irule robust_val_in_memory_exterior_frame >>
      simp[] >> goal_assum (drule_at Any) >>
      qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `tn.t_mem`, `tn'.t_mem`] >>
      simp[] >> metis_tac[]) >>
  metis_tac[]
QED
