Theory bodyPtrIfExpAllocKept
Ancestors
  bodyPtrIfExpAllocFrame allocationPtr decoderGhostFramePtr bodyPtrDefs
  ptrDiscipline venomState venomInst finite_map compileEnv

Theorem alloca_step_taint_below_frontier:
  !s id n out u tn i.
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
    i < s.vs_alloca_next ==>
    (i IN (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn).t_mem
     <=> i IN tn.t_mem)
Proof
  rpt strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (irule fresh_alloca_taint_below_frontier >> simp[] >> metis_tac[]) >>
  rename1 `SOME site` >> PairCases_on `site` >>
  drule reused_alloca_memory_effects >>
  disch_then (qspecl_then [`n`, `out`, `tn`] strip_assume_tac) >> gvs[]
QED

Theorem alloca_step_ghost_kept_bounded:
  !cenv es sa G0 tn0 s0 G tn s id n out u PG.
    ghost_kept cenv es sa G0 tn0 s0 G tn /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
    (!x. not_fresh_at sa x ==> x <> out) /\
    (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
                  aid < sa.cs_next_id ==> off + sz <= s.vs_alloca_next) /\
    (!name b sz. local_region cenv es.scopes s0 name b sz ==>
                  b + sz <= s.vs_alloca_next) ==>
    ghost_kept cenv es sa G0 tn0 s0
      (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `ghost_kept _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ghost_kept_def] >> strip_tac >>
  rewrite_tac[ghost_kept_def] >> conj_tac
  >- (rpt strip_tac >>
      `x <> out` by metis_tac[] >>
      simp[step_prov_other_output, step_taint_other_output, mk_inst_def] >>
      metis_tac[]) >>
  conj_tac >> rpt strip_tac >>
  `i < s.vs_alloca_next` by metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS] >>
  drule_all alloca_step_taint_below_frontier >> strip_tac >> metis_tac[]
QED
