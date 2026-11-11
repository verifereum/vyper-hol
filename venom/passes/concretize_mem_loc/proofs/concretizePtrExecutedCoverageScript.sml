Theory concretizePtrExecutedCoverage
Ancestors venomWfProps
  concretizePtrImportCoverage concretizePtrImportOrigins concretizePtrAllocationSize
  o1ScheduleDecompHelpers
  staticLayoutAllocatorProofs staticLayoutCompletionProofs
  concretizeMemLocDefs venomInst venomPassDispatcher venomFnScheduleRunner
  o1PassContract venomWf mem2varProofs ptrDiscipline ptrDisciplineEmptyTaint
  concretizePtrActivationSupport venomState venomExecSemantics venomMemProps
  contextCodegenRel removeUnusedSsaProofs unitTransformDefs
  concretizeAnalysisBoundary finite_map list pair

Theorem ptr_unique_mems_prefix[local]:
  !xs ys item.
    ALL_DISTINCT (MAP FST xs) /\ MEM item xs ==>
    MEM item (unique_mems_used (xs ++ ys))
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >>
  simp[unique_mems_used_def, FILTER_APPEND_DISTRIB, MEM_MAP] >>
  rpt strip_tac >> gvs[] >>
  `FILTER (\(b,_,_). b <> h0) xs = xs` by
    (simp[FILTER_EQ_ID, EVERY_MEM] >>
     rpt strip_tac >> PairCases_on `e` >> gvs[] >> metis_tac[FST]) >>
  gvs[] >> first_x_assum irule >> simp[]
QED

Theorem ptr_layout_own_mems:
  static_alloca_items fn = SOME items /\ MEM (a,sz) items ==>
  MEM (a,THE (FLOOKUP layout.cl_positions a),sz)
    (apply_context_concretize_layout ctx layout fn).fn_mems_used
Proof
  strip_tac >> simp[apply_context_concretize_layout_def] >>
  irule ptr_unique_mems_prefix >> conj_tac
  >- (`(\(x:allocation,y:num). x) = FST` by (simp[FUN_EQ_THM, FORALL_PROD]) >>
      drule static_alloca_items_ALL_DISTINCT >>
      simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]) >>
  simp[MEM_MAP] >> qexists `(a,sz)` >> simp[]
QED

Theorem ptr_concretize_static_items:
  fn.fn_eom = NONE /\
  concretize_function_fuel_in_context fuel ctx reserved fn = SOME fn' ==>
  ?items layout. static_alloca_items fn = SOME items /\
    fn' = apply_context_concretize_layout ctx layout fn
Proof
  simp[concretize_function_fuel_in_context_def, fn_has_static_layout_def] >>
  Cases_on `fn_needs_liveness_allocation fn \/ imported_mems_used ctx fn <> []` >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[]
  >- (qpat_x_assum `compute_function_layout_fuel_in_context _ _ _ _ = _` mp_tac >>
      simp[compute_function_layout_fuel_in_context_def] >>
      Cases_on `static_alloca_items fn` >> simp[] >> rpt strip_tac >>
      metis_tac[]) >>
  qpat_x_assum `compute_function_layout_eval _ _ = _` mp_tac >>
  simp[compute_function_layout_eval_def, complete_alloc_positions_def] >>
  Cases_on `static_alloca_items fn` >> simp[] >> rpt strip_tac >>
  metis_tac[]
QED

Theorem ptr_concretize_alloca_mems:
  fn.fn_eom = NONE /\ fn_inst_ids_distinct fn /\
  concretize_function_fuel_in_context fuel ctx reserved fn = SOME fn' /\
  MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA ==>
  ?p. MEM (Allocation i.inst_id,p,get_alloca_size fn (Allocation i.inst_id))
    fn'.fn_mems_used
Proof
  strip_tac >> drule_all ptr_concretize_static_items >> strip_tac >>
  drule_all static_alloca_items_ALLOCA_exact >> strip_tac >>
  rename1 `i.inst_operands = [Lit n]` >>
  `get_alloca_size fn (Allocation i.inst_id) = w2n n` by
    metis_tac[ptr_alloca_inst_size] >>
  `MEM (Allocation i.inst_id,w2n n) items` by
    metis_tac[static_alloca_items_MEM] >>
  gvs[] >> metis_tac[ptr_layout_own_mems]
QED

Theorem ptr_step_alloca_mems:
  fn.fn_eom = NONE /\ fn_inst_ids_distinct fn /\
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
  MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA ==>
  ?p. MEM (Allocation i.inst_id,p,get_alloca_size fn (Allocation i.inst_id))
    out.fpo_function.fn_mems_used
Proof
  simp[fn_pass_step_def, execute_configured_fn_pass_concretize,
       AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule_all ptr_concretize_alloca_mems >> simp[]
QED

Theorem ptr_stage_alloca_mems:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) view C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
  MEM fn C.ctx_functions /\ MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA ==>
  ?g p. lookup_function fn.fn_name C'.ctx_functions = SOME g /\
    MEM (Allocation i.inst_id,p,get_alloca_size fn (Allocation i.inst_id))
      g.fn_mems_used
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
  `fn.fn_eom = NONE /\ fn_inst_ids_distinct fn` by
    (fs[EVERY_MEM, o1_ctx_shape_def, o1_fn_shape_def, wf_function_def] >>
     metis_tac[]) >>
  drule_all ptr_step_alloca_mems >> metis_tac[]
QED

Definition ptr_table_source_def:
  ptr_table_source fn s <=>
    !aid site. FLOOKUP s.vs_allocas aid = SOME site ==>
      ?i. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\ i.inst_id = aid
End

Theorem ptr_table_source_step[local]:
  ptr_table_source fn s /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode <> DALLOCA /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel ctx inst s = OK s' ==> ptr_table_source fn s'
Proof
  strip_tac >> Cases_on `inst.inst_opcode = ALLOCA`
  >- (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
      simp[step_inst_non_invoke] >> pure_once_rewrite_tac[step_inst_base_def] >>
      pure_asm_rewrite_tac[] >> simp[AllCaseEqs()] >> strip_tac >>
      gvs[exec_alloca_def, AllCaseEqs(), update_var_def] >>
      fs[ptr_table_source_def, FLOOKUP_UPDATE, AllCaseEqs()] >> metis_tac[]) >>
  `~is_alloca_op inst.inst_opcode` by
    (Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def]) >>
  `s'.vs_allocas = s.vs_allocas` by
    metis_tac[step_inst_non_alloca_preserves_allocas] >>
  fs[ptr_table_source_def]
QED

Theorem ptr_frame_table_source:
  !vs ctx stk PG G tn fn inst s.
  frame_reachable vs ctx stk PG G tn fn inst s ==>
  o1_run_state_ok vs /\ o1_ctx_shape ctx /\ ~ctx_has_dalloca ctx ==>
  MEM fn ctx.ctx_functions /\ ptr_table_source fn s /\
  EVERY (\f. MEM f.cf_fn ctx.ctx_functions /\ ptr_table_source f.cf_fn f.cf_state) stk
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- (rpt strip_tac >>
      `s.vs_allocas = vs.vs_allocas` by (drule enters_block_allocas >> simp[]) >>
      fs[ptr_table_source_def, o1_run_state_ok_def, o1_initial_state_ok_def] >>
      metis_tac[lookup_function_MEM])
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      qpat_x_assum `_ ==> _` mp_tac >> simp[] >> strip_tac >>
      `MEM inst (fn_insts fn)` by
        (gvs[active_inst_def, fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
         metis_tac[MEM_EL]) >>
      `inst.inst_opcode <> DALLOCA` by
        (fs[ctx_has_dalloca_def, EVERY_MEM] >> metis_tac[]) >>
      drule_all ptr_table_source_step >> simp[ptr_table_source_def])
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      qpat_x_assum `_ ==> _` mp_tac >> simp[] >> strip_tac >>
      `~is_alloca_op inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
        (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def, is_alloca_op_def]) >>
      `s'.vs_allocas = s.vs_allocas` by
        metis_tac[step_inst_non_alloca_preserves_allocas] >>
      drule enters_block_allocas >> fs[ptr_table_source_def])
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      qpat_x_assum `_ ==> _` mp_tac >> simp[] >> strip_tac >>
      `cs.vs_allocas = FEMPTY` by metis_tac[setup_callee_empty_allocas] >>
      `s''.vs_allocas = FEMPTY` by metis_tac[enters_block_allocas] >>
      simp[ptr_table_source_def] >> metis_tac[lookup_function_MEM]) >>
  rpt gen_tac >> strip_tac >> strip_tac >>
  qpat_x_assum `_ ==> _` mp_tac >> simp[] >> strip_tac >>
  `s'.vs_allocas = f.cf_state.vs_allocas` by metis_tac[ptr_return_allocas] >>
  fs[ptr_table_source_def]
QED

Theorem ptr_frame_current_mems:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\ ~ctx_has_dalloca C /\
  frame_reachable vs C stk PG G tn fn inst s /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
  ?g p. lookup_function fn.fn_name C'.ctx_functions = SOME g /\
    MEM (Allocation aid,p,sz) g.fn_mems_used
Proof
  strip_tac >> drule_all ptr_frame_table_source >> strip_tac >>
  `?i. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\ i.inst_id = aid` by
    metis_tac[ptr_table_source_def] >>
  drule_all ptr_frame_current_allocation_size >> strip_tac >>
  drule_all ptr_stage_alloca_mems >> gvs[]
QED

Theorem ptr_frame_saved_mems:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\ ~ctx_has_dalloca C /\
  frame_reachable vs C stk PG G tn fn inst s /\
  MEM f stk /\ FLOOKUP f.cf_state.vs_allocas aid = SOME (b,sz) ==>
  ?g p. lookup_function f.cf_fn.fn_name C'.ctx_functions = SOME g /\
    MEM (Allocation aid,p,sz) g.fn_mems_used
Proof
  strip_tac >> drule_all ptr_frame_table_source >> strip_tac >>
  `MEM f.cf_fn C.ctx_functions /\ ptr_table_source f.cf_fn f.cf_state` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `?i. MEM i (fn_insts f.cf_fn) /\ i.inst_opcode = ALLOCA /\ i.inst_id = aid` by
    metis_tac[ptr_table_source_def] >>
  drule_all ptr_frame_saved_allocation_size >> strip_tac >>
  drule_all ptr_stage_alloca_mems >> gvs[]
QED

Theorem ptr_frame_owning_callee_demand:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\ ~ctx_has_dalloca C /\
  frame_reachable vs C stk PG G tn fn inst s /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
  o1_walk_view rpolicy 2 C' caller observed /\
  MEM call (fn_insts caller) /\ call.inst_opcode = INVOKE /\
  call.inst_operands = Label fn.fn_name :: ops ==>
  ml_callee_gen (Allocation aid)
    (\name. incr_ssort alloc_to (MAP FST (callee_mems_used observed.cu_context name))) call
Proof
  strip_tac >> drule_all ptr_frame_current_mems >> strip_tac >>
  drule_all ptr_o1_walk_invoke_demand >> simp[]
QED
