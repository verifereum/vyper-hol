Theory concretizePtrDallocaNoEom
Ancestors
  concretizeStageShape ptrDiscipline frameAllocationOwnership
  o1PassContract concretizeMemLocDefs venomPassDispatcher stackPlanGen list

(* Even an allocation-free fresh function validates the reservations. *)
Theorem ptr_dalloca_fresh_reserved_wf:
  fn.fn_eom = NONE /\
  concretize_function_fuel_in_context fuel ctx reserved fn = SOME fn' ==>
  reserved_intervals_wf reserved
Proof
  simp[concretize_function_fuel_in_context_def, fn_has_static_layout_def] >>
  simp[compute_function_layout_fuel_in_context_def,
       compute_function_layout_eval_def, complete_alloc_positions_def,
       complete_alloc_positions_with_items_def,
       complete_alloc_positions_with_imports_def,
       checked_preserved_intervals_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem ptr_dalloca_stage_no_eom_empty:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) view C C' /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  max_live_eom C' = NONE ==>
  C'.ctx_functions = []
Proof
  strip_tac >>
  Cases_on `reserved_intervals_wf C.ctx_global_reserved`
  >- metis_tac[concretize_stage_max_live_eom, optionTheory.NOT_SOME_NONE] >>
  gvs[ctx_pass_stage_def] >>
  Cases_on `C.ctx_functions` >> gvs[listTheory.LIST_REL_CONS1] >>
  rename1 `fn::rest` >>
  gvs[fn_pass_step_def, execute_configured_fn_pass_concretize,
      AllCaseEqs()] >>
  drule_all ptr_dalloca_fresh_reserved_wf >> simp[]
QED

Theorem ptr_dalloca_no_eom_taint_within:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  dead_wf D /\ taint_within D C vs /\ EVERY ssa_form C.ctx_functions /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  (!eom. max_live_eom C' = SOME eom ==> eom <= w2n vs.vs_initial_fmp) /\
  max_live_eom C' = NONE ==>
  taint_within D C' vs
Proof
  strip_tac >>
  `C'.ctx_functions = []` by
    (irule ptr_dalloca_stage_no_eom_empty >> metis_tac[]) >>
  simp[taint_within_def, final_taint_def] >>
  metis_tac[frame_reachable_functions_member, listTheory.MEM]
QED
