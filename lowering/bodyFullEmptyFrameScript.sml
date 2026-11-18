Theory bodyFullEmptyFrame
Ancestors
  bodyPtrDefs robustCopyTransportPtr compileEnv venomState venomExecSemantics
  finite_map pred_set abiDecodeStaticProps bodyFullUnwrapRun ptrDiscipline

(* The decreasing-taint kept frame is already provided by
   bodyFullUnwrapRunTheory.ghost_kept_at_clean_suffix. *)

Theorem empty_ghost_inv_exterior_frame_at:
  !D lo P writes d cenv cx es G tn s G' tn' s'.
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_accounts = s.vs_accounts /\ s'.vs_transient = s.vs_transient /\
    s'.vs_immutables = s.vs_immutables /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!i. i NOTIN writes ==>
      mem_bytes_at i 1 s'.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    (!i. i NOTIN writes ==> (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    (!i. i < lo ==> i NOTIN writes) /\
    (!p. P p ==> lookup_var p s' = lookup_var p s /\
      FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p)) /\
    (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> P p) /\
    (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> P p) /\
    (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> P p) /\
    (!p. lo <> 0 /\ cenv.ce_imm_alloca = SOME (Var p) ==> P p) /\
    (!name entry p sz w.
      lookup_scopes name es.scopes = SOME entry /\
      FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
      lookup_var p s = SOME w ==>
      val_wf entry.type entry.value /\
      (!i. w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
        i NOTIN writes)) /\
    ghost_inv_at D lo d cenv cx es G tn s ==>
    ghost_inv_at D lo d cenv cx es G' tn' s'
Proof
  rpt gen_tac >> strip_tac >>
  `!p sz. P p ==> (ptr_covers G' tn' p s' sz <=> ptr_covers G tn p s sz)` by
    (rpt strip_tac >> simp[ptr_covers_def]) >>
  `mem_bytes_at 0 lo s'.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (irule mem_bytes_at_bytewise >> simp[]) >>
  qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ghost_inv_at_def] >> strip_tac >> rpt conj_tac
  >- suspend "locals"
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
      PairCases_on `x` >> gvs[return_buf_ptr_def] >> metis_tac[])
  >- metis_tac[]
  >- gvs[stor_taint_ok_at_def]
  >- metis_tac[]
  >- metis_tac[]
  >- (gvs[allocas_from_def] >> metis_tac[]) >> simp[]
QED
Resume empty_ghost_inv_exterior_frame_at[locals]:
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
Finalise empty_ghost_inv_exterior_frame_at
