Theory concretizePtrStageZero
Ancestors concretizePtrProductionZero concretizePtrStagePlacements
  concretizePtrAllocationSize concretizePtrExecutedCoverage concretizePtrProductionSeparation
  concretizePtrSourceOwnership staticLayoutAllocatorProofs
  o1PassContract ptrDiscipline list finite_map venomWf mem2varProofs
  concretizePtrImportCoverage concretizePtrImportOrigins o1ScheduleDecompHelpers
  venomPassDispatcher venomInst concretizePtrActivationBirths
  concretizePtrActivationChronology concretizePtrChronologicalHistory concretizePtrOwnerPath

Theorem ptr_concretize_zero_instruction[local]:
  fn.fn_eom = NONE /\ fn_ptr_ok P fn /\
  concretize_function_fuel_in_context fuel ctx reserved fn = SOME fn' /\
  MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
  get_alloca_size fn (Allocation i.inst_id) = 0 ==>
  MEM (Allocation i.inst_id,0,0) fn'.fn_mems_used
Proof
  strip_tac >> drule_all ptr_concretize_static_items >> strip_tac >>
  drule_all static_alloca_items_ALLOCA_exact >> strip_tac >>
  rename1 `i.inst_operands = [Lit n]` >>
  `w2n n = 0` by metis_tac[ptr_static_alloca_item_size, static_alloca_items_MEM] >>
  `MEM (Allocation i.inst_id,0) items` by metis_tac[static_alloca_items_MEM] >>
  metis_tac[ptr_production_zero_metadata]
QED

Theorem ptr_stage_zero_instruction[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) view C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
  MEM fn C.ctx_functions /\ fn_ptr_ok P fn /\
  MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
  get_alloca_size fn (Allocation i.inst_id) = 0 ==>
  ?g. lookup_function fn.fn_name C'.ctx_functions = SOME g /\
      MEM (Allocation i.inst_id,0,0) g.fn_mems_used
Proof
  strip_tac >>
  `lookup_function fn.fn_name C.ctx_functions = SOME fn` by
    (fs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def] >>
     metis_tac[lookup_function_member_iff]) >>
  `MEM fn.fn_name (ctx_fn_names C')` by
    (drule ptr_stage_names >> disch_then (SUBST1_TAC o SYM) >>
     simp[ctx_fn_names_def, MEM_MAP] >> metis_tac[]) >>
  `?g. lookup_function fn.fn_name C'.ctx_functions = SOME g` by
    (Cases_on `lookup_function fn.fn_name C'.ctx_functions` >>
     fs[ctx_fn_names_def] >> metis_tac[lookup_function_not_mem]) >>
  drule_all ptr_stage_lookup_origin >> strip_tac >> gvs[] >>
  `fn.fn_eom = NONE` by fs[EVERY_MEM] >>
  qpat_x_assum `fn_pass_step _ _ _ _ _ _` mp_tac >>
  simp[fn_pass_step_def, execute_configured_fn_pass_concretize, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[ptr_concretize_zero_instruction]
QED

Theorem ptr_stage_live_zero_position:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  o1_run_state_ok vs /\ ~ctx_has_dalloca C /\ ptr_discipline lo C vs /\
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  ptr_stage_placements C' positions /\ FLOOKUP TG v = SOME (token,aid) /\
  FLOOKUP a.po_prov v = SOME (b,0) ==>
  FLOOKUP positions (Allocation aid) = SOME (0,0)
Proof
  strip_tac >> drule_all ptr_stage_placements_live_owner >> strip_tac >>
  `ptr_ledger_source_activations vs C h a tokens registry` by
    metis_tac[ptr_source_ownership_caches, ptr_source_birth_caches_activations] >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
     a.po_fn a.po_inst a.po_state` by
    metis_tac[ptr_source_activations_sound, ptr_chrono_history_reachable,
      ptr_observation_reachable_def] >>
  drule_all ptr_frame_table_source >> strip_tac >>
  `MEM owner C.ctx_functions /\ ptr_table_source owner (ptr_owner_view d a).cf_state /\
   get_alloca_size owner (Allocation aid) = 0` by
    (Cases_on `d = LENGTH a.po_stack`
     >- (gvs[ptr_owner_view_def] >>
         metis_tac[ptr_frame_current_allocation_size]) >>
     `MEM (ptr_owner_view d a) a.po_stack` by
       (simp[ptr_owner_view_def] >> irule EL_MEM >> decide_tac) >>
     fs[EVERY_MEM] >> metis_tac[ptr_frame_saved_allocation_size]) >>
  `?P. fn_ptr_ok P owner` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `?i. MEM i (fn_insts owner) /\ i.inst_opcode = ALLOCA /\ i.inst_id = aid` by
    metis_tac[ptr_table_source_def] >>
  gvs[] >> drule_all ptr_stage_zero_instruction >> strip_tac >>
  qpat_x_assum `ptr_stage_placements _ _` mp_tac >>
  pure_rewrite_tac[ptr_stage_placements_def] >>
  disch_then (qspecl_then [`Allocation i.inst_id`,`0`,`0`] mp_tac) >>
  simp[] >> metis_tac[lookup_function_MEM]
QED
