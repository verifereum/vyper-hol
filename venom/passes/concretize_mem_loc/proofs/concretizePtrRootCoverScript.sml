Theory concretizePtrRootCover
Ancestors concretizePtrParamSupport concretizePtrSingletonSite
  o1FnScheduleDecompHelpers venomWf ptrDiscipline concretizeAnalysisRoots
  concretizePtrFrameOrigins concretizePtrBPOrigins pointerConfinedDefs
  venomInst list finite_map pred_set words

Theorem ptr_param_root_cover:
  ptr_params_ok P fn PG /\ ssa_form fn /\
  EVERY inst_wf (fn_insts fn) ==>
  !r. r IN ptr_frame_site_roots fn A PG site ==>
    (?bid. FLOOKUP A bid = SOME site /\ r IN ptr_bp_alloc_roots fn bid) \/
    r IN (ptr_roots P fn DIFF alloca_roots fn)
Proof
  strip_tac >> gen_tac >> simp[ptr_frame_site_roots_def] >>
  disch_then (qx_choose_then `i` strip_assume_tac) >>
  `inst_wf i` by fs[EVERY_MEM] >>
  `inst_output i = SOME r` by
    (gvs[inst_wf_def] >> Cases_on `i.inst_outputs` >>
     gvs[inst_output_def] >> Cases_on `t` >> gvs[]) >>
  gvs[]
  >- (disj1_tac >> qexists `i.inst_id` >>
      simp[ptr_bp_alloc_roots_def] >> metis_tac[]) >>
  disj2_tac >> simp[IN_DIFF] >> conj_tac
  >- (simp[ptr_roots_def] >> disj2_tac >>
      qexistsl [`i`, `idx`] >> fs[ptr_params_ok_def] >> metis_tac[]) >>
  simp[alloca_roots_def] >> rpt strip_tac >>
  rename1 `j.inst_opcode = ALLOCA` >>
  `MEM r j.inst_outputs` by
    (Cases_on `j.inst_outputs` >> gvs[inst_output_def] >>
     Cases_on `t` >> gvs[]) >>
  `i <> j` by (strip_tac >> gvs[]) >>
  fs[ssa_form_def] >>
  metis_tac[distinct_flat_map_members_disjoint]
QED

Theorem ptr_frame_current_root_cover:
  frame_reachable vs0 ctx stk PG G tn fn inst s /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) ctx.ctx_functions /\
  EVERY ssa_form ctx.ctx_functions ==>
  !r. r IN ptr_frame_site_roots fn A PG site ==>
    (?bid. FLOOKUP A bid = SOME site /\ r IN ptr_bp_alloc_roots fn bid) \/
    r IN (ptr_roots P fn DIFF alloca_roots fn)
Proof
  rpt strip_tac >> irule ptr_param_root_cover >> simp[] >>
  drule ptr_frame_current_static >>
  disch_then (qspec_then `P` mp_tac) >> simp[] >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem ptr_frame_saved_root_cover:
  frame_reachable vs0 ctx stk PG G tn fn inst s /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) ctx.ctx_functions /\
  EVERY ssa_form ctx.ctx_functions /\ n < LENGTH stk ==>
  !r. r IN ptr_frame_site_roots (EL n stk).cf_fn A (EL n stk).cf_params site ==>
    (?bid. FLOOKUP A bid = SOME site /\
      r IN ptr_bp_alloc_roots (EL n stk).cf_fn bid) \/
    r IN (ptr_roots P (EL n stk).cf_fn DIFF alloca_roots (EL n stk).cf_fn)
Proof
  rpt strip_tac >> irule ptr_param_root_cover >> simp[] >>
  `MEM (EL n stk).cf_fn ctx.ctx_functions /\
   ptr_params_ok P (EL n stk).cf_fn (EL n stk).cf_params` by
    metis_tac[ptr_frame_saved_static] >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem ptr_param_supported_production_singleton_write_site:
  fn_ptr_ok P fn /\ wf_function fn /\ all_reachable fn /\ ssa_form fn /\
  EVERY inst_wf (fn_insts fn) /\ ptr_params_ok P fn PG /\
  ptr_bp_origins fn (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) /\
  MEM inst (fn_insts fn) /\ mem_write_ops inst = SOME ops /\
  ops.iao_ofst = Var v /\
  bp_get_ptrs (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) v =
    [Ptr (Allocation aid) off] /\
  ptr_site_supported
    (pointer_derived_vars fn (ptr_frame_site_roots fn A PG site)) G site /\
  FLOOKUP G v = SOME site ==>
  FLOOKUP A aid = SOME site
Proof
  strip_tac >>
  `!r. r IN ptr_frame_site_roots fn A PG site ==>
    (?bid. FLOOKUP A bid = SOME site /\ r IN ptr_bp_alloc_roots fn bid) \/
    r IN (ptr_roots P fn DIFF alloca_roots fn)` by
    metis_tac[ptr_param_root_cover] >>
  irule ptr_supported_production_singleton_write_site >> metis_tac[]
QED
