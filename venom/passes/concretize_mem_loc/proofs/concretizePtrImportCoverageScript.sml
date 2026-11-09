Theory concretizePtrImportCoverage
Ancestors
  concretizePtrImportOrigins concretizePtrMetadataTransport
  concretizePtrOrdering concretizeAnalysisLivenessTransfer
  concretizeMemLocDefs venomFnScheduleRunner venomInst fcgDefs fcgBridge mem2varProofs list pair

Theorem ptr_unique_mems_keys:
  !xs a. MEM a (MAP FST (unique_mems_used xs)) <=> MEM a (MAP FST xs)
Proof
  ho_match_mp_tac unique_mems_used_ind >>
  simp[unique_mems_used_def] >> rpt strip_tac >>
  Cases_on `a' = a` >> simp[] >>
  fs[MEM_MAP, MEM_FILTER, EXISTS_PROD] >> metis_tac[]
QED

Theorem ptr_unique_mems_coherent:
  !xs a p sz. MEM (a,p,sz) xs /\
    (!q n. MEM (a,q,n) xs ==> q = p /\ n = sz) ==>
    MEM (a,p,sz) (unique_mems_used xs)
Proof
  ho_match_mp_tac unique_mems_used_ind >>
  simp[unique_mems_used_def, MEM_FILTER] >> rpt strip_tac >>
  metis_tac[]
QED

Theorem ptr_import_callee_key:
  MEM i (fn_insts fn) /\ i.inst_opcode = INVOKE /\
  i.inst_operands = Label nm :: ops /\
  MEM (a,p,sz) (callee_mems_used ctx nm) ==>
  MEM a (MAP FST (imported_mems_used ctx fn))
Proof
  strip_tac >> rewrite_tac[imported_mems_used_def, ptr_unique_mems_keys] >>
  simp[MEM_MAP, MEM_FLAT] >>
  qexists_tac `(a,p,sz)` >> simp[] >>
  qexists_tac `callee_mems_used ctx nm` >> simp[] >>
  qexists_tac `i` >> simp[]
QED

Theorem ptr_import_callee_coherent:
  MEM i (fn_insts fn) /\ i.inst_opcode = INVOKE /\
  i.inst_operands = Label nm :: ops /\
  MEM (a,p,sz) (callee_mems_used ctx nm) /\
  (!name q n. MEM name (fn_invoke_targets fn) /\
    MEM (a,q,n) (callee_mems_used ctx name) ==> q = p /\ n = sz) ==>
  MEM (a,p,sz) (imported_mems_used ctx fn)
Proof
  strip_tac >> rewrite_tac[imported_mems_used_def] >>
  irule ptr_unique_mems_coherent >> reverse conj_tac
  >- (simp[MEM_FLAT, MEM_MAP] >>
      qexists_tac `callee_mems_used ctx nm` >> simp[] >>
      qexists_tac `i` >> simp[]) >>
  simp[MEM_FLAT, MEM_MAP] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  `MEM name (fn_invoke_targets fn)` by
    (simp[fn_invoke_targets_def, fcg_scan_function_def, mem_get_invoke_targets] >>
     metis_tac[]) >>
  metis_tac[]
QED

Theorem ptr_o1_walk_invoke_demand:
  o1_walk_view rpolicy 2 C' fn observed /\
  MEM i (fn_insts fn) /\ i.inst_opcode = INVOKE /\
  i.inst_operands = Label nm :: ops /\
  lookup_function nm C'.ctx_functions = SOME g /\
  MEM (a,p,sz) g.fn_mems_used ==>
  ml_callee_gen a
    (\name. incr_ssort alloc_to (MAP FST (callee_mems_used observed.cu_context name))) i
Proof
  strip_tac >>
  `MEM nm (fn_invoke_targets fn)` by
    (simp[fn_invoke_targets_def, fcg_scan_function_def, mem_get_invoke_targets] >>
     metis_tac[]) >>
  drule_all ptr_o1_walk_callee_mems >> strip_tac >>
  `!xs. set (incr_ssort alloc_to xs) = set xs` by
    metis_tac[enumeralTheory.set_OWL_thm, enumeralTheory.OWL] >>
  simp[ml_callee_gen_def, callee_mems_used_def] >>
  metis_tac[MEM_MAP, pairTheory.FST]
QED

Theorem ptr_stage_mems_coherent:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  lookup_function x C'.ctx_functions = SOME f /\
  lookup_function y C'.ctx_functions = SOME g /\
  MEM (a,p,sz) f.fn_mems_used /\ MEM (a,q,n) g.fn_mems_used ==>
  p = q /\ sz = n
Proof
  strip_tac >>
  qpat_assum `lookup_function x _ = _`
    (mp_then Any mp_tac ptr_stage_lookup_mems_canonical) >>
  disch_then drule_all >> strip_tac >>
  qpat_assum `lookup_function y _ = _`
    (mp_then Any mp_tac ptr_stage_lookup_mems_canonical) >>
  disch_then drule_all >> strip_tac >>
  `owner = owner'` by
    (irule ptr_ctx_inst_owner_unique >> conj_tac
     >- (qexistsl [`i`,`i'`] >> gvs[]) >>
     qexists_tac `C` >> simp[]) >>
  gvs[] >>
  qpat_assum `lookup_function owner.fn_name _ = _`
    (mp_then Any mp_tac ptr_stage_lookup_origin) >>
  disch_then drule_all >> strip_tac >>
  `fn.fn_eom = NONE` by
    (qpat_x_assum `EVERY _ _` mp_tac >> simp[EVERY_MEM] >>
     metis_tac[lookup_function_MEM]) >>
  gvs[] >> irule ptr_step_mems_functional >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem ptr_stage_invoke_import_tuple:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  ctx_fn_names observed.cu_context = ctx_fn_names C /\
  o1_walk_view rpolicy 2 C' fn observed /\
  MEM i (fn_insts fn) /\ i.inst_opcode = INVOKE /\
  i.inst_operands = Label nm :: ops /\
  lookup_function nm C'.ctx_functions = SOME g /\
  MEM (a,p,sz) g.fn_mems_used ==>
  MEM (a,p,sz) (imported_mems_used observed.cu_context fn)
Proof
  strip_tac >>
  `MEM nm (fn_invoke_targets fn)` by
    (simp[fn_invoke_targets_def, fcg_scan_function_def, mem_get_invoke_targets] >>
     metis_tac[]) >>
  drule_all ptr_o1_walk_callee_mems >> strip_tac >>
  irule ptr_import_callee_coherent >> reverse conj_tac
  >- (qexistsl_tac [`i`,`nm`,`ops`] >> simp[callee_mems_used_def]) >>
  rpt strip_tac >>
  Cases_on `lookup_function name observed.cu_context.ctx_functions` >>
  fs[callee_mems_used_def] >>
  qpat_assum `lookup_function name _ = SOME _`
    (mp_then Any mp_tac ptr_stage_observed_callee) >>
  disch_then drule_all >> strip_tac >>
  gvs[] >> metis_tac[ptr_stage_mems_coherent]
QED
