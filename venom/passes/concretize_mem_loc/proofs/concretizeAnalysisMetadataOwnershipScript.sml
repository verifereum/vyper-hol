Theory concretizeAnalysisMetadataOwnership
Ancestors
  concretizeAnalysisMetadata concretizeAnalysisOwnership
  concretizeAnalysisMetadataSchedule staticLayoutAllocatorProofs
  concretizeStageLookup concretizeMemLocDefs list fcgBridge fcgDefs
  venomFnScheduleRunner o1PassContract venomPassDispatcher venomWf venomInst pair

Theorem static_alloca_items_source_owns:
  MEM fn C.ctx_functions /\ static_alloca_items fn = SOME items ==>
  EVERY (\(a,s). source_owns C fn a s) items
Proof
  strip_tac >> simp[EVERY_MEM] >> PairCases >> strip_tac >>
  drule static_alloca_items_MEM >>
  disch_then (qspec_then `(e0,e1)` mp_tac) >> simp[] >> strip_tac >>
  gvs[exact_static_alloca_def, exact_static_alloca_size_def, AllCaseEqs()] >>
  metis_tac[source_owns_literal]
QED

Theorem concretize_context_source_owns:
  MEM fn C.ctx_functions /\ fn.fn_eom = NONE /\
  concretize_function_fuel_in_context fuel observed reserved fn = SOME out /\
  (!inst name args g.
    MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
    inst.inst_operands = Label name :: args /\
    lookup_function name observed.ctx_functions = SOME g ==>
    EVERY (\(a,p,s). source_owns C fn a s) g.fn_mems_used) ==>
  EVERY (\(a,p,s). source_owns C fn a s) out.fn_mems_used
Proof
  strip_tac >>
  `EVERY (\(a,p,s). source_owns C fn a s) (imported_mems_used observed fn)` by
    (irule imported_mems_used_every >> metis_tac[]) >>
  drule_all concretize_context_rebuilds_metadata >> strip_tac >> gvs[] >>
  Cases_on `static_alloca_items fn`
  >- (simp[apply_context_concretize_layout_def] >>
      irule unique_mems_used_every >> simp[]) >>
  irule apply_context_layout_mems_every >>
  goal_assum (drule_at Any) >> simp[] >>
  drule_all static_alloca_items_source_owns >>
  simp[EVERY_MEM] >> metis_tac[]
QED

Theorem invoke_target_instruction:
  MEM name (fn_invoke_targets fn) <=>
  ?inst args. MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
    inst.inst_operands = Label name :: args
Proof
  simp[fn_invoke_targets_def, fcg_scan_function_def,
       fcgBridgeTheory.mem_get_invoke_targets]
QED

Theorem lookup_function_name[local]:
  !fns name fn. lookup_function name fns = SOME fn ==> fn.fn_name = name
Proof
  Induct >> simp[lookup_function_def, FIND_thm] >>
  rpt strip_tac >> Cases_on `h.fn_name = name` >> gvs[lookup_function_def] >> metis_tac[]
QED

Theorem source_invoke_lookup:
  o1_ctx_shape C /\ MEM fn C.ctx_functions /\
  MEM name (fn_invoke_targets fn) ==>
  ?callee. lookup_function name C.ctx_functions = SOME callee /\
    source_call C fn callee
Proof
  simp[o1_ctx_shape_def, EVERY_MEM] >> rpt strip_tac >>
  `fn_invoke_ok (ctx_fn_names C) fn` by metis_tac[o1_fn_shape_def] >>
  `MEM name (ctx_fn_names C)` by
    (gvs[invoke_target_instruction, fn_invoke_ok_def] >>
     first_x_assum drule_all >> simp[]) >>
  Cases_on `lookup_function name C.ctx_functions`
  >- gvs[lookup_function_not_mem, ctx_fn_names_def] >>
  rename1 `lookup_function name C.ctx_functions = SOME callee` >>
  qexists_tac `callee` >> simp[source_call_def] >>
  drule lookup_function_MEM >> strip_tac >>
  metis_tac[lookup_function_name]
QED

Theorem concretize_stage_lookup:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  lookup_function name C.ctx_functions = SOME fn ==>
  ?out observed.
    lookup_function name C'.ctx_functions = SOME out /\
    walk_view rpolicy (DROP 3 o1_fn_passes) C' fn observed /\
    concretize_function_fuel_in_context (concretize_memloc_fuel fn)
      observed.cu_context observed.cu_context.ctx_global_reserved fn = SOME out
Proof
  strip_tac >> drule_all ctx_pass_stage_lookup >> strip_tac >>
  gvs[fn_pass_step_def, o1_walk_view_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem concretize_stage_source_owns_bounded[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions ==>
  !n name fn out.
    (!i. list_index fn.fn_name names = SOME i ==> i < n) /\
    lookup_function name C.ctx_functions = SOME fn /\
    lookup_function name C'.ctx_functions = SOME out ==>
    EVERY (\(a,p,s). source_owns C fn a s) out.fn_mems_used
Proof
  strip_tac >> completeInduct_on `n` >> rpt strip_tac >>
  drule_all concretize_stage_lookup >> strip_tac >> gvs[] >>
  irule concretize_context_source_owns >>
  `MEM fn C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  reverse conj_tac >- gvs[EVERY_MEM] >>
  qexistsl_tac [`concretize_memloc_fuel fn`, `observed.cu_context`,
                `observed.cu_context.ctx_global_reserved`] >> simp[] >>
  rpt strip_tac >>
  `MEM name' (fn_invoke_targets fn)` by metis_tac[invoke_target_instruction] >>
  drule_all source_invoke_lookup >> strip_tac >>
  drule_all source_call_precedes >> simp[list_precedes_iff] >> strip_tac >>
  drule_all concretize_stage_lookup >> strip_tac >>
  `j < n` by metis_tac[] >>
  `EVERY (\(a,p,s). source_owns C callee a s) out'.fn_mems_used` by
    (qpat_x_assum `!m. m < n ==> _` (qspec_then `j` mp_tac) >>
     simp[] >> disch_then irule >>
     conj_tac >- simp[] >> metis_tac[]) >>
  drule_all concretize_walk_view_mems_used >> strip_tac >> gvs[] >>
  gvs[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
  irule source_owns_prepend_call >> metis_tac[]
QED

Theorem concretize_stage_source_owns:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\
  lookup_function name C.ctx_functions = SOME fn /\
  lookup_function name C'.ctx_functions = SOME out ==>
  EVERY (\(a,p,s). source_owns C fn a s) out.fn_mems_used
Proof
  strip_tac >>
  `?n. !i. list_index fn.fn_name names = SOME i ==> i < n` by
    (Cases_on `list_index fn.fn_name names` >> simp[] >>
     rename1 `list_index fn.fn_name names = SOME i` >>
     qexists_tac `SUC i` >> simp[]) >>
  drule_all concretize_stage_source_owns_bounded >> metis_tac[]
QED

Theorem concretize_observed_source_owns:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\
  MEM caller C.ctx_functions /\ o1_walk_view rpolicy 2 C' caller observed /\
  MEM name (fn_invoke_targets caller) /\
  lookup_function name observed.cu_context.ctx_functions = SOME g ==>
  ?callee. lookup_function name C.ctx_functions = SOME callee /\
    source_call C caller callee /\
    EVERY (\(a,p,s). source_owns C callee a s) g.fn_mems_used
Proof
  strip_tac >> drule_all source_invoke_lookup >> strip_tac >>
  drule_all concretize_stage_lookup >> strip_tac >>
  `EVERY (\(a,p,s). source_owns C callee a s) out.fn_mems_used` by
    metis_tac[concretize_stage_source_owns] >>
  gvs[o1_walk_view_def] >>
  drule_all concretize_walk_view_mems_used >> strip_tac >> gvs[] >>
  metis_tac[]
QED
