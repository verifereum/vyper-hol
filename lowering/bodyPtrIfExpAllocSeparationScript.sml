Theory bodyPtrIfExpAllocSeparation
Ancestors bodyPtrIfExpAllocCompiler bodyPtrIfExpAllocGhost allocationPtr
  bufferAllocationExecution localPtrsProps loweringPosts compileEnv
  venomState venomInst finite_map words loweringHalt exprLoweringProps

Theorem ifexp_alloca_old_site_separate:
  stmt_state_rel ctx fn ce cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
  n < dimword(:256) /\ aid <> id /\
  FLOOKUP s.vs_allocas aid = SOME (off,sz) ==>
  off+sz <= buffer_allocation_base s id \/
  buffer_allocation_base s id+n <= off
Proof
  strip_tac >>
  `alloca_inv s` by gvs[stmt_state_rel_def] >>
  `!b k. FLOOKUP s.vs_allocas id = SOME (b,k) ==> k = n` by
    (rpt strip_tac >> drule_all stmt_state_rel_alloca_site_bound >> simp[]) >>
  `id <> aid` by simp[] >>
  drule_all buffer_allocation_disjoint >> metis_tac[]
QED

Theorem ifexp_alloca_local_separate:
  stmt_state_rel ctx fn ce cx es s /\ fn_inst_ids_distinct fn /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
  not_local_ptr ce es.scopes out /\ n < dimword(:256) /\
  local_region ce es.scopes s name p sz ==>
  p+sz <= buffer_allocation_base s id \/ buffer_allocation_base s id+n <= p
Proof
  strip_tac >>
  `alloca_inv s /\ local_ptrs_rel fn ce es.scopes s` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  Cases_on `FLOOKUP s.vs_allocas id`
  >- (simp[buffer_allocation_base_def] >>
      drule_at (Pat `local_region _ _ _ _ _ _`) local_ptrs_rel_above_frontier >>
      disch_then (qspecl_then [`fn`, `s.vs_alloca_next`, `n`] mp_tac) >>
      simp[regions_disjoint_def]) >>
  rename1 `SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  `regions_disjoint site0 n p sz` by
    (irule local_ptrs_rel_alloca_disjoint >>
     goal_assum (drule_at Any) >>
     qexistsl_tac [`mk_inst id ALLOCA [Lit (n2w n)] [out]`, `name`, `out`] >>
     simp[mk_inst_def]) >>
  gvs[buffer_allocation_base_def, regions_disjoint_def]
QED

Theorem ifexp_alloca_original_site_separate:
  vv_post ctx fn ce cx e es sa sb s0 es' tv vv s /\
  MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
  sa.cs_next_id <= sb.cs_next_id /\ n < dimword(:256) /\
  FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
  off+sz <= buffer_allocation_base s sb.cs_next_id \/
  buffer_allocation_base s sb.cs_next_id+n <= off
Proof
  strip_tac >>
  `stmt_state_rel ctx fn ce cx es' s /\
   FLOOKUP s.vs_allocas aid = SOME (off,sz)` by gvs[vv_post_def] >>
  `aid <> sb.cs_next_id` by decide_tac >>
  drule_all ifexp_alloca_old_site_separate >> simp[]
QED

Theorem ifexp_alloca_original_local_separate:
  vv_post ctx fn ce cx e es sa sb s0 es' tv vv s /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  fn_inst_ids_distinct fn /\
  MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
  not_local_ptr ce es'.scopes out /\ n < dimword(:256) /\
  local_region ce es.scopes s0 name p sz ==>
  p+sz <= buffer_allocation_base s sb.cs_next_id \/
  buffer_allocation_base s sb.cs_next_id+n <= p
Proof
  strip_tac >>
  `local_region ce es'.scopes s name p sz` by
    (irule exprSimPropsTheory.local_region_frame_fwd >>
     simp[] >> qexistsl_tac [`s0`, `sa`, `es.scopes`] >> gvs[vv_post_def]) >>
  `stmt_state_rel ctx fn ce cx es' s` by gvs[vv_post_def] >>
  drule_all ifexp_alloca_local_separate >> simp[]
QED

Theorem ifexp_alloca_step_base:
  n < dimword(:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
  lookup_var out u = SOME (n2w (buffer_allocation_base s id))
Proof
  strip_tac >> qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[Once venomExecSemanticsTheory.step_inst_base_opcode_eqs] >>
  simp[mk_inst_def, venomExecSemanticsTheory.exec_alloca_def,
       buffer_allocation_base_def, AllCaseEqs()] >>
  strip_tac >> gvs[venomStateTheory.update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem ifexp_alloca_base_bound:
  stmt_state_rel ctx fn ce cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
  n < dimword(:256) ==>
  buffer_allocation_base s id+n < dimword(:256)
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all stmt_state_rel_alloca_fresh_bound >> simp[buffer_allocation_base_def]) >>
  rename1 `SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> simp[buffer_allocation_base_def]
QED


Theorem ifexp_alloca_step_site:
  stmt_state_rel ctx fn ce cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
  n < dimword(:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
  FLOOKUP u.vs_allocas id = SOME (buffer_allocation_base s id,n)
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
      simp[] >> disch_then (qspec_then `out` assume_tac) >>
      gvs[buffer_allocation_base_def, update_var_def, FLOOKUP_UPDATE]) >>
  qmatch_asmsub_rename_tac `FLOOKUP s.vs_allocas id = SOME site` >>
  PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >>
  gvs[buffer_allocation_base_def, update_var_def]
QED
