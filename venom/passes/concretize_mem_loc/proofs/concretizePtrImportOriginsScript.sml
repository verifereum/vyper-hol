Theory concretizePtrImportOrigins
Ancestors
  concretizePtrMetadataTransport staticLayoutAllocatorProofs
  concretizeMemLocDefs o1ScheduleDecomp o1PassContract venomPassDispatcher
  venomFnScheduleRunner venomWf venomInst fcgDefs fcgBridge list finite_map
  mem2varProofs fmpAnalysisProps

Theorem ptr_unique_mems_subset:
  !xs item. MEM item (unique_mems_used xs) ==> MEM item xs
Proof
  ho_match_mp_tac unique_mems_used_ind >> simp[unique_mems_used_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[MEM_FILTER]
QED
Theorem ptr_unique_mems_functional:
  !xs a p sz q n.
    MEM (a,p,sz) (unique_mems_used xs) /\
    MEM (a,q,n) (unique_mems_used xs) ==> p = q /\ sz = n
Proof
  ho_match_mp_tac unique_mems_used_ind >>
  simp[unique_mems_used_def] >> rpt strip_tac >>
  imp_res_tac ptr_unique_mems_subset >>
  fs[MEM_FILTER] >> metis_tac[]
QED


Theorem ptr_import_mems_origin:
  MEM item (imported_mems_used ctx fn) ==>
  ?name callee. MEM name (fn_invoke_targets fn) /\
    lookup_function name ctx.ctx_functions = SOME callee /\
    MEM item callee.fn_mems_used
Proof
  simp[imported_mems_used_def] >> strip_tac >>
  drule ptr_unique_mems_subset >>
  simp[MEM_FLAT, MEM_MAP] >> rpt strip_tac >>
  gvs[AllCaseEqs(), callee_mems_used_def] >>
  qexistsl [`name`,`fn'`] >> simp[] >>
  simp[fn_invoke_targets_def, fcg_scan_function_def, mem_get_invoke_targets] >>
  metis_tac[]
QED

Theorem ptr_concretize_mems_origin:
  fn.fn_eom = NONE /\
  concretize_function_fuel_in_context fuel ctx reserved fn = SOME fn' /\
  MEM (a,p,sz) fn'.fn_mems_used ==>
  (?i. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
       a = Allocation i.inst_id) \/
  MEM (a,p,sz) (imported_mems_used ctx fn)
Proof
  simp[concretize_function_fuel_in_context_def, fn_has_static_layout_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  gvs[apply_context_concretize_layout_def] >>
  drule ptr_unique_mems_subset >>
  simp[MEM_MAP, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  TRY disj1_tac >> PairCases_on `y` >>
  Cases_on `static_alloca_items fn` >> gvs[] >>
  drule static_alloca_items_MEM >>
  disch_then (qspec_then `(a,sz)` mp_tac) >> simp[] >>
  strip_tac >> qexists `inst` >>
  gvs[exact_static_alloca_def, AllCaseEqs()]
QED

Theorem ptr_related_lookup[local]:
  !xs ys name g.
    LIST_REL R xs ys /\
    (!f g. R f g ==> f.fn_name = g.fn_name) /\
    lookup_function name ys = SOME g ==>
    ?f. lookup_function name xs = SOME f /\ R f g
Proof
  Induct >> Cases_on `ys` >> simp[] >> rpt strip_tac >>
  gvs[lookup_function_def, FIND_thm] >>
  `h.fn_name = h'.fn_name` by metis_tac[] >>
  Cases_on `h'.fn_name = name` >> gvs[] >> metis_tac[]
QED

Theorem ptr_stage_lookup_origin:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) view C C' /\
  lookup_function name C'.ctx_functions = SOME g ==>
  ?fn observed s out.
    lookup_function name C.ctx_functions = SOME fn /\
    fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
    out.fpo_function = g /\
    ctx_fn_names observed.cu_context = ctx_fn_names C /\
    view C' fn observed
Proof
  simp[ctx_pass_stage_def] >> rpt strip_tac >>
  drule ptr_related_lookup >>
  disch_then (qspecl_then [`name`,`g`] mp_tac) >>
  impl_tac >- (simp[] >> rpt strip_tac >> gvs[fn_pass_step_def]) >>
  simp[] >> metis_tac[]
QED

Theorem ptr_related_names[local]:
  !xs ys. LIST_REL R xs ys /\
    (!f g. R f g ==> f.fn_name = g.fn_name) ==>
    MAP (\f. f.fn_name) xs = MAP (\f. f.fn_name) ys
Proof
  Induct >> Cases_on `ys` >> simp[] >> metis_tac[]
QED

Theorem ptr_stage_names:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) view C C' ==>
  ctx_fn_names C = ctx_fn_names C'
Proof
  simp[ctx_pass_stage_def, ctx_fn_names_def] >> rpt strip_tac >>
  drule ptr_related_names >>
  impl_tac >- (rpt strip_tac >> gvs[fn_pass_step_def]) >> simp[]
QED

Theorem ptr_stage_observed_callee:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) view C C' /\
  ctx_fn_names observed.cu_context = ctx_fn_names C /\
  o1_walk_view rpolicy 2 C' fn observed /\
  MEM name (fn_invoke_targets fn) /\
  lookup_function name observed.cu_context.ctx_functions = SOME callee ==>
  ?g'. lookup_function name C'.ctx_functions = SOME g' /\
    g'.fn_mems_used = callee.fn_mems_used
Proof
  rpt strip_tac >>
  `ctx_fn_names C = ctx_fn_names C'` by metis_tac[ptr_stage_names] >>
  `MEM name (ctx_fn_names observed.cu_context)` by
    metis_tac[lookup_function_mem, ctx_fn_names_def] >>
  `?g'. lookup_function name C'.ctx_functions = SOME g'` by
    (Cases_on `lookup_function name C'.ctx_functions` >> simp[] >>
     metis_tac[lookup_function_not_mem, ctx_fn_names_def]) >>
  drule_all ptr_o1_walk_callee_mems >> strip_tac >>
  gvs[] >> goal_assum drule >> simp[]
QED

Theorem ptr_stage_import_lookup:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) view C C' /\
  ctx_fn_names observed.cu_context = ctx_fn_names C /\
  o1_walk_view rpolicy 2 C' fn observed /\
  MEM item (imported_mems_used observed.cu_context fn) ==>
  ?name g'. MEM name (fn_invoke_targets fn) /\
    lookup_function name C'.ctx_functions = SOME g' /\
    MEM item g'.fn_mems_used
Proof
  rpt strip_tac >> drule ptr_import_mems_origin >> strip_tac >>
  drule_all ptr_stage_observed_callee >> strip_tac >>
  metis_tac[]
QED

Theorem ptr_step_mems_origin:
  fn.fn_eom = NONE /\
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
  MEM (a,p,sz) out.fpo_function.fn_mems_used ==>
  (?i. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
       a = Allocation i.inst_id) \/
  MEM (a,p,sz) (imported_mems_used observed.cu_context fn)
Proof
  simp[fn_pass_step_def, execute_configured_fn_pass_concretize,
       AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  irule ptr_concretize_mems_origin >> simp[] >>
  qexistsl [`fn'`,`concretize_memloc_fuel fn`,
            `observed.cu_context.ctx_global_reserved`] >> simp[]
QED

Theorem ptr_stage_mems_canonical:
  !n name g a p sz.
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\
  list_index name names = SOME n /\
  lookup_function name C'.ctx_functions = SOME g /\
  MEM (a,p,sz) g.fn_mems_used ==>
  ?owner i owner_out. MEM owner C.ctx_functions /\ MEM i (fn_insts owner) /\
    i.inst_opcode = ALLOCA /\ a = Allocation i.inst_id /\
    lookup_function owner.fn_name C'.ctx_functions = SOME owner_out /\
    MEM (a,p,sz) owner_out.fn_mems_used /\
    fcg_path C name owner.fn_name /\
    (owner.fn_name = name \/ list_precedes owner.fn_name name names)
Proof
  completeInduct_on `n` >> rpt strip_tac >>
  drule_all ptr_stage_lookup_origin >> strip_tac >>
  `MEM fn C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `fn.fn_name = name` by metis_tac[lookup_function_name] >>
  `fn.fn_eom = NONE` by
    (qpat_x_assum `EVERY _ _` mp_tac >> simp[EVERY_MEM] >>
     disch_then drule >> simp[]) >>
  qpat_x_assum `out.fpo_function = g` (SUBST_ALL_TAC o SYM) >>
  drule_all ptr_step_mems_origin >> strip_tac
  >- (qexistsl [`fn`,`i`,`out.fpo_function`] >>
      simp[fcg_path_def, relationTheory.RTC_REFL]) >>
  drule_all ptr_stage_import_lookup >> strip_tac >>
  rename1 `lookup_function callee C'.ctx_functions = SOME g'` >>
  `list_precedes callee name names` by
    (gvs[callee_first_def] >> metis_tac[]) >>
  gvs[list_precedes_iff] >>
  qpat_x_assum `!m. m < n ==> _` (qspec_then `i` mp_tac) >> simp[] >>
  disch_then drule_all >> strip_tac >>
  `fn_directly_calls C fn.fn_name callee` by
    (simp[fn_directly_calls_scan, GSYM fn_invoke_targets_def] >>
     qexists `fn` >> simp[]) >>
  `fcg_path C fn.fn_name owner.fn_name` by
    (gvs[fcg_path_def] >> metis_tac[relationTheory.RTC_RULES]) >>
  qexistsl [`owner`,`i'`,`owner_out`] >> simp[] >>
  metis_tac[arithmeticTheory.LESS_TRANS]
QED

Theorem ptr_stage_mems_source:
  !n name g a p sz.
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\
  list_index name names = SOME n /\
  lookup_function name C'.ctx_functions = SOME g /\
  MEM (a,p,sz) g.fn_mems_used ==>
  ?owner i. MEM owner C.ctx_functions /\ MEM i (fn_insts owner) /\
    i.inst_opcode = ALLOCA /\ a = Allocation i.inst_id /\
    fcg_path C name owner.fn_name /\
    (owner.fn_name = name \/ list_precedes owner.fn_name name names)
Proof
  metis_tac[ptr_stage_mems_canonical]
QED

Theorem ptr_stage_import_source:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\
  lookup_function fn.fn_name C.ctx_functions = SOME fn /\
  ctx_fn_names observed.cu_context = ctx_fn_names C /\
  o1_walk_view rpolicy 2 C' fn observed /\
  MEM (a,p,sz) (imported_mems_used observed.cu_context fn) ==>
  ?owner i. MEM owner C.ctx_functions /\ MEM i (fn_insts owner) /\
    i.inst_opcode = ALLOCA /\ a = Allocation i.inst_id /\
    fcg_path C fn.fn_name owner.fn_name /\
    list_precedes owner.fn_name fn.fn_name names
Proof
  rpt strip_tac >> drule_all ptr_stage_import_lookup >> strip_tac >>
  `MEM fn C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `list_precedes name fn.fn_name names` by
    (gvs[callee_first_def] >> metis_tac[]) >>
  `fn_directly_calls C fn.fn_name name` by
    (simp[fn_directly_calls_scan, GSYM fn_invoke_targets_def] >>
     qexists `fn` >> simp[]) >>
  gvs[list_precedes_iff] >>
  drule_all ptr_stage_mems_source >> strip_tac >>
  `fcg_path C fn.fn_name owner.fn_name` by
    (gvs[fcg_path_def] >> metis_tac[relationTheory.RTC_RULES]) >>
  qexistsl [`owner`,`i'`] >> gvs[list_precedes_iff] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem ptr_ctx_inst_owner_unique:
  ctx_inst_ids_distinct C /\
  MEM f C.ctx_functions /\ MEM g C.ctx_functions /\
  MEM i (fn_insts f) /\ MEM j (fn_insts g) /\
  i.inst_id = j.inst_id ==> f = g
Proof
  rpt strip_tac >>
  irule (INST_TYPE [``:'b`` |-> ``:num``]
    mem2varProofsTheory.ALL_DISTINCT_FLAT_MAP_unique) >>
  qexistsl [`\fn. MAP (\i. i.inst_id) (fn_insts fn)`,
            `i.inst_id`,`C.ctx_functions`] >>
  simp[MEM_MAP] >> conj_tac
  >- (gvs[ctx_inst_ids_distinct_def, fn_insts_def, removeUnusedSsaProofsTheory.fn_insts_blocks_flat, MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF]) >>
  conj_tac >- metis_tac[] >> metis_tac[]
QED

Theorem ptr_stage_local_not_imported:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  lookup_function fn.fn_name C.ctx_functions = SOME fn /\
  lookup_function fn.fn_name C'.ctx_functions = SOME out.fpo_function /\
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
  ctx_fn_names observed.cu_context = ctx_fn_names C /\
  o1_walk_view rpolicy 2 C' fn observed /\
  MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA ==>
  ~MEM (Allocation i.inst_id)
    (MAP FST (imported_mems_used observed.cu_context fn))
Proof
  rpt strip_tac >> gvs[MEM_MAP] >>
  PairCases_on `y` >> gvs[] >>
  drule_all ptr_stage_import_source >> strip_tac >>
  `MEM fn C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `fn = owner` by
    (gvs[] >> irule ptr_ctx_inst_owner_unique >>
     conj_tac >- (qexistsl [`i`,`i'`] >> simp[]) >>
     qexists `C` >> simp[]) >>
  gvs[list_precedes_iff]
QED

Theorem ptr_step_mems_functional:
  fn.fn_eom = NONE /\
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
  MEM (a,p,sz) out.fpo_function.fn_mems_used /\
  MEM (a,q,n) out.fpo_function.fn_mems_used ==> p = q /\ sz = n
Proof
  simp[fn_pass_step_def, execute_configured_fn_pass_concretize,
       AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  gvs[concretize_function_fuel_in_context_def, fn_has_static_layout_def,
      AllCaseEqs(), apply_context_concretize_layout_def] >>
  metis_tac[ptr_unique_mems_functional]
QED

Theorem ptr_stage_lookup_mems_canonical:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\
  lookup_function name C'.ctx_functions = SOME g /\
  MEM (a,p,sz) g.fn_mems_used ==>
  ?owner i owner_out. MEM owner C.ctx_functions /\ MEM i (fn_insts owner) /\
    i.inst_opcode = ALLOCA /\ a = Allocation i.inst_id /\
    lookup_function owner.fn_name C'.ctx_functions = SOME owner_out /\
    MEM (a,p,sz) owner_out.fn_mems_used /\
    fcg_path C name owner.fn_name /\
    (owner.fn_name = name \/ list_precedes owner.fn_name name names)
Proof
  strip_tac >> drule_all ptr_stage_lookup_origin >> strip_tac >>
  `MEM fn C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `fn.fn_name = name` by metis_tac[lookup_function_name] >>
  `fn.fn_eom = NONE` by
    (qpat_x_assum `EVERY _ _` mp_tac >> simp[EVERY_MEM] >>
     disch_then drule >> simp[]) >>
  qpat_x_assum `out.fpo_function = g` (SUBST_ALL_TAC o SYM) >>
  drule_all ptr_step_mems_origin >> strip_tac
  >- (qexistsl [`fn`,`i`,`out.fpo_function`] >>
      simp[fcg_path_def, relationTheory.RTC_REFL]) >>
  drule_all ptr_stage_import_lookup >> strip_tac >>
  `list_precedes name' name names` by
    (gvs[callee_first_def] >> metis_tac[]) >>
  fs[list_precedes_iff] >>
  drule_all ptr_stage_mems_canonical >> strip_tac >>
  `fn_directly_calls C fn.fn_name name'` by
    (simp[fn_directly_calls_scan, GSYM fn_invoke_targets_def] >>
     qexists `fn` >> simp[]) >>
  `fcg_path C fn.fn_name owner.fn_name` by
    (gvs[fcg_path_def] >> metis_tac[relationTheory.RTC_RULES]) >>
  qexistsl [`owner`,`i'`,`owner_out`] >> simp[] >>
  gvs[list_precedes_iff] >> metis_tac[arithmeticTheory.LESS_TRANS]
QED
