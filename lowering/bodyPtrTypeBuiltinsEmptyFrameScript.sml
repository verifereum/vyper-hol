Theory bodyPtrTypeBuiltinsEmptyFrame
Ancestors
  bodyPtrDefs robustCopyTransportPtr compileEnv venomState venomExecSemantics
  finite_map pred_set

Theorem ghost_kept_decreasing_frame:
  !cenv es sa G0 tn0 s0 G tn G' tn'.
    tn'.t_mem SUBSET tn.t_mem /\
    (!p. not_fresh_at sa p ==> FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p)) /\
    ghost_kept cenv es sa G0 tn0 s0 G tn ==>
    ghost_kept cenv es sa G0 tn0 s0 G' tn'
Proof
  simp[ghost_kept_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem ghost_inv_exterior_frame:
  !P writes d cenv cx es G tn s G' tn' s'.
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_accounts = s.vs_accounts /\ s'.vs_transient = s.vs_transient /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!i. i NOTIN writes ==>
      mem_bytes_at i 1 s'.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    (!i. i NOTIN writes ==> (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    (!p. P p ==> lookup_var p s' = lookup_var p s /\
      FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p)) /\
    (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> P p) /\
    (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> P p) /\
    (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> P p) /\
    (!name entry p sz w.
      lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
      lookup_var p s = SOME w ==>
      val_wf entry.type entry.value /\
      (!i. w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
        i NOTIN writes)) /\
    ghost_inv d cenv cx es G tn s ==>
    ghost_inv d cenv cx es G' tn' s'
Proof
  rpt gen_tac >> strip_tac >>
  `!p sz. P p ==> (ptr_covers G' tn' p s' sz <=> ptr_covers G tn p s sz)` by
    (rpt strip_tac >> simp[ptr_covers_def]) >>
  qpat_x_assum `ghost_inv _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ghost_inv_def] >> strip_tac >> rpt conj_tac
  >- suspend "locals"
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
      PairCases_on `x` >> gvs[return_buf_ptr_def] >> metis_tac[]) 
  >- metis_tac[] >>
  gvs[stor_taint_ok_def]
QED
Resume ghost_inv_exterior_frame[locals]:
  rpt gen_tac >> strip_tac >>
  `P p` by metis_tac[] >>
  `ptr_covers G tn p s sz` by metis_tac[] >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `lookup_var p s = SOME w` by metis_tac[] >>
  `val_wf entry.type entry.value /\
    (!i. w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
      i NOTIN writes)` by metis_tac[] >>
  irule robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`s.vs_memory`, `s'.vs_memory`, `tn.t_mem`, `tn'.t_mem`] >>
  simp[] >> metis_tac[]
QED
Finalise ghost_inv_exterior_frame
