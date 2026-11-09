Theory concretizePtrStackImports
Ancestors venomWfProps
  concretizePtrExecutedCoverage concretizePtrCallAncestry
  concretizePtrImportCoverage concretizePtrImportOrigins
  ptrDiscipline venomExecSemantics venomInst o1PassContract
  removeUnusedSsaProofs contextCodegenRel fmpAnalysisProps o1ScheduleDecompHelpers venomWf
  concretizeMemLocDefs staticLayoutAllocatorProofs list rich_list finite_map

Definition ptr_stack_edges_def:
  (ptr_stack_edges child [] <=> T) /\
  (ptr_stack_edges child (f::stk) <=>
    MEM f.cf_inst (fn_insts f.cf_fn) /\
    f.cf_inst.inst_opcode = INVOKE /\
    (?ops. f.cf_inst.inst_operands = Label child.fn_name :: ops) /\
    ptr_stack_edges f.cf_fn stk)
End

Theorem ptr_frame_stack_edges:
  !vs ctx stk PG G tn fn inst s.
  frame_reachable vs ctx stk PG G tn fn inst s ==>
  ptr_stack_edges fn stk
Proof
  ho_match_mp_tac frame_reachable_ind >>
  simp[ptr_stack_edges_def] >> rpt strip_tac >>
  gvs[decode_invoke_def, AllCaseEqs()] >>
  gvs[active_inst_def, fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
  metis_tac[MEM_EL, lookup_function_name]
QED

Theorem ptr_layout_import_mems[local]:
  static_alloca_items fn = SOME items /\
  ~MEM a (MAP FST items) /\
  MEM (a,p,sz) (imported_mems_used ctx fn) ==>
  MEM (a,p,sz) (apply_context_concretize_layout ctx layout fn).fn_mems_used
Proof
  strip_tac >> simp[concretizeMemLocDefsTheory.apply_context_concretize_layout_def] >>
  irule ptr_unique_mems_coherent >> reverse conj_tac >- simp[] >>
  rpt gen_tac >> simp[MEM_MAP, pairTheory.EXISTS_PROD] >>
  strip_tac
  >- (gvs[] >> fs[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
  gvs[concretizeMemLocDefsTheory.imported_mems_used_def] >>
  metis_tac[ptr_unique_mems_functional]
QED

Theorem ptr_step_static_items[local]:
  fn.fn_eom = NONE /\
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out ==>
  ?items layout. static_alloca_items fn = SOME items /\
    out.fpo_function = apply_context_concretize_layout observed.cu_context layout fn
Proof
  simp[o1PassContractTheory.fn_pass_step_def,
       venomPassDispatcherTheory.execute_configured_fn_pass_concretize,
       AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule_all ptr_concretize_static_items >> simp[]
QED

Theorem ptr_stage_import_retained:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  lookup_function fn.fn_name C.ctx_functions = SOME fn /\
  lookup_function fn.fn_name C'.ctx_functions = SOME out.fpo_function /\
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
  ctx_fn_names observed.cu_context = ctx_fn_names C /\
  o1_walk_view rpolicy 2 C' fn observed /\
  MEM (a,p,sz) (imported_mems_used observed.cu_context fn) ==>
  MEM (a,p,sz) out.fpo_function.fn_mems_used
Proof
  strip_tac >>
  `fn.fn_eom = NONE` by
    (fs[EVERY_MEM] >> metis_tac[lookup_function_MEM]) >>
  drule_all ptr_step_static_items >> strip_tac >>
  `~MEM a (MAP FST items)` by
    (strip_tac >> fs[MEM_MAP, pairTheory.EXISTS_PROD] >>
     `?i. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
          exact_static_alloca i = SOME (a,p_2)` by
       metis_tac[staticLayoutAllocatorProofsTheory.static_alloca_items_MEM] >>
     `a = Allocation i.inst_id` by
       fs[concretizeMemLocDefsTheory.exact_static_alloca_def, AllCaseEqs()] >>
     `~MEM (Allocation i.inst_id)
       (MAP FST (imported_mems_used observed.cu_context fn))` by
       (irule ptr_stage_local_not_imported >>
        rpt (goal_assum (drule_at Any)) >> simp[]) >>
     fs[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
  gvs[] >> irule ptr_layout_import_mems >>
  simp[] >> qexists `items` >> simp[]
QED

Theorem ptr_stage_call_mems:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  MEM caller C.ctx_functions /\ MEM call (fn_insts caller) /\
  call.inst_opcode = INVOKE /\ call.inst_operands = Label nm :: ops /\
  lookup_function nm C'.ctx_functions = SOME g /\ MEM (a,p,sz) g.fn_mems_used ==>
  ?caller_out. lookup_function caller.fn_name C'.ctx_functions = SOME caller_out /\
    MEM (a,p,sz) caller_out.fn_mems_used
Proof
  strip_tac >>
  `lookup_function caller.fn_name C.ctx_functions = SOME caller` by
    (fs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def] >>
     metis_tac[lookup_function_member_iff]) >>
  `MEM caller.fn_name (ctx_fn_names C')` by
    (drule ptr_stage_names >> disch_then (SUBST1_TAC o SYM) >>
     simp[ctx_fn_names_def, MEM_MAP] >> metis_tac[]) >>
  `?caller_out. lookup_function caller.fn_name C'.ctx_functions = SOME caller_out` by
    (Cases_on `lookup_function caller.fn_name C'.ctx_functions` >>
     fs[ctx_fn_names_def] >> metis_tac[lookup_function_not_mem]) >>
  qpat_assum `lookup_function caller.fn_name C'.ctx_functions = _`
    (mp_then Any mp_tac ptr_stage_lookup_origin) >>
  disch_then drule >> strip_tac >> gvs[] >>
  `MEM (a,p,sz) (imported_mems_used observed.cu_context caller)` by
    (drule_all ptr_stage_invoke_import_tuple >> simp[]) >>
  `MEM (a,p,sz) out.fpo_function.fn_mems_used` by
    (irule ptr_stage_import_retained >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  metis_tac[]
QED

Theorem ptr_stack_tuple_transport[local]:
  !stk child k n owner own_out.
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  ptr_stack_edges child stk /\ MEM child C.ctx_functions /\
  EVERY (\f. MEM f.cf_fn C.ctx_functions) stk /\
  n < LENGTH stk /\ k <= n /\
  EL k (child :: MAP (\f. f.cf_fn) stk) = owner /\
  lookup_function owner.fn_name C'.ctx_functions = SOME own_out /\
  MEM (a,p,sz) own_out.fn_mems_used ==>
  ?nm ops g. (EL n stk).cf_inst.inst_opcode = INVOKE /\
    (EL n stk).cf_inst.inst_operands = Label nm :: ops /\
    lookup_function nm C'.ctx_functions = SOME g /\
    MEM (a,p,sz) g.fn_mems_used
Proof
  Induct_on `stk` >- simp[] >>
  rpt gen_tac >> Cases_on `n` >> simp[ptr_stack_edges_def] >> strip_tac
  >- (gvs[] >> metis_tac[]) >>
  Cases_on `k`
  >- (gvs[] >>
      `?caller_out. lookup_function h.cf_fn.fn_name C'.ctx_functions = SOME caller_out /\
        MEM (a,p,sz) caller_out.fn_mems_used` by
        (drule_all ptr_stage_call_mems >> simp[]) >>
      first_x_assum irule >> rpt (goal_assum (drule_at Any)) >> simp[] >>
      qexists `0` >> simp[]) >>
  gvs[] >> first_x_assum irule >> rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem ptr_frame_descendant_mems:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  frame_reachable vs C stk PG G tn fn inst s /\
  n < LENGTH stk /\ k <= n /\
  EL k ((fn,s) :: MAP (\f. (f.cf_fn,f.cf_state)) stk) = (owner,os) /\
  FLOOKUP os.vs_allocas aid = SOME (b,sz) ==>
  ?p own_out nm ops g.
    lookup_function owner.fn_name C'.ctx_functions = SOME own_out /\
    MEM (Allocation aid,p,sz) own_out.fn_mems_used /\
    (EL n stk).cf_inst.inst_opcode = INVOKE /\
    (EL n stk).cf_inst.inst_operands = Label nm :: ops /\
    lookup_function nm C'.ctx_functions = SOME g /\
    MEM (Allocation aid,p,sz) g.fn_mems_used
Proof
  strip_tac >>
  `?own_out p. lookup_function owner.fn_name C'.ctx_functions = SOME own_out /\
    MEM (Allocation aid,p,sz) own_out.fn_mems_used` by
    (Cases_on `k`
     >- (gvs[] >> drule_all ptr_frame_current_mems >> simp[]) >>
     gvs[] >>
     `n' < LENGTH stk` by decide_tac >>
     `MEM (EL n' stk) stk` by simp[EL_MEM] >>
     gvs[EL_MAP] >> drule_all ptr_frame_saved_mems >> simp[]) >>
  `EL k (fn :: MAP (\f. f.cf_fn) stk) = owner` by
    (Cases_on `k` >> gvs[EL_MAP] >>
     `n' < LENGTH stk` by decide_tac >> gvs[EL_MAP]) >>
  drule_all ptr_frame_table_source >> strip_tac >>
  `EVERY (\f. MEM f.cf_fn C.ctx_functions) stk` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  drule ptr_frame_stack_edges >> strip_tac >>
  drule_all ptr_stack_tuple_transport >> metis_tac[]
QED

Theorem ptr_stack_edge_inst[local]:
  !stk child n. ptr_stack_edges child stk /\ n < LENGTH stk ==>
    MEM (EL n stk).cf_inst (fn_insts (EL n stk).cf_fn)
Proof
  Induct >> simp[ptr_stack_edges_def] >> rpt gen_tac >>
  Cases_on `n` >> simp[] >> metis_tac[]
QED

Theorem ptr_frame_descendant_demand:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  frame_reachable vs C stk PG G tn fn inst s /\
  n < LENGTH stk /\ k <= n /\
  EL k ((fn,s) :: MAP (\f. (f.cf_fn,f.cf_state)) stk) = (owner,os) /\
  FLOOKUP os.vs_allocas aid = SOME (b,sz) /\
  o1_walk_view rpolicy 2 C' (EL n stk).cf_fn observed ==>
  ml_callee_gen (Allocation aid)
    (\name. incr_ssort alloc_to (MAP FST (callee_mems_used observed.cu_context name)))
    (EL n stk).cf_inst
Proof
  strip_tac >> drule_all ptr_frame_descendant_mems >> strip_tac >>
  `MEM (EL n stk).cf_inst (fn_insts (EL n stk).cf_fn)` by
    metis_tac[ptr_frame_stack_edges, ptr_stack_edge_inst] >>
  drule_all ptr_o1_walk_invoke_demand >> simp[]
QED

Theorem ptr_frame_descendant_import:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  frame_reachable vs C stk PG G tn fn inst s /\
  n < LENGTH stk /\ k <= n /\
  EL k ((fn,s) :: MAP (\f. (f.cf_fn,f.cf_state)) stk) = (owner,os) /\
  FLOOKUP os.vs_allocas aid = SOME (b,sz) /\
  o1_walk_view rpolicy 2 C' (EL n stk).cf_fn observed /\
  ctx_fn_names observed.cu_context = ctx_fn_names C ==>
  ?p. MEM (Allocation aid,p,sz)
    (imported_mems_used observed.cu_context (EL n stk).cf_fn)
Proof
  strip_tac >> drule_all ptr_frame_descendant_mems >> strip_tac >>
  `MEM (EL n stk).cf_inst (fn_insts (EL n stk).cf_fn)` by
    metis_tac[ptr_frame_stack_edges, ptr_stack_edge_inst] >>
  drule_all ptr_stage_invoke_import_tuple >> metis_tac[]
QED
