Theory requestCutConcretizeCursor
Ancestors
  lowerDloadDefs unitTransformDefs
  concretizePtrDallocaStageCoverage concretizePtrOperationalOpcodes
  concretizePtrChronologicalHistory concretizePtrPairedPrefix
  concretizePtrRequestHistory concretizePtrTaintContent concretizePtrSharedFields
  concretizePtrOpaqueRetpc
  concretizeStepShape concretizeLayoutLocalReturn
  lowerDloadPtrRawReachable lowerDloadPtrForward o1ContractSimplifyCfgSrcFrame
  o1PassContract ptrDiscipline venomWf venomInst
  venomState list arithmetic

Theorem request_cut_concretize_cursor:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C CT /\
  o1_ctx_shape C /\ o1_ctx_shape CT /\
  o1_initial_state_ok clip0 /\ clip0.vs_fmp = clip0.vs_initial_fmp /\
  code_layout_valid clip0 /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C clip0 /\
  fixed_region_reserved lo C /\ ptr_discipline lo C clip0 /\
  EVERY ssa_form C.ctx_functions /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  (ctx_has_dalloca C ==> !eom. max_live_eom CT = SOME eom ==>
    eom <= w2n clip0.vs_initial_fmp) /\
  max_live_eom CT = SOME eom /\
  frame_reachable clip0 CT stk PG G un gn i t /\
  MEM i.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] ==>
  ?R lp positions h a ht done tokens registry births PT TG saved entries H calls ws.
    ptr_stage_placements CT positions /\
    ptr_paired_prefix R lp positions lo clip0 C CT
      h a ht (ptr_observe stk PG G un gn i t)
      done tokens registry births PT TG saved entries H calls ws /\
    EVERY (\n. ~in_revert_forward (EL n h).po_fn (EL n h).po_state) done /\
    frame_reachable clip0 C a.po_stack a.po_params a.po_prov a.po_taint
      a.po_fn i a.po_state /\
    a.po_inst = i /\ active_inst a.po_fn i a.po_state /\
    ~in_revert_forward a.po_fn a.po_state /\
    ptr_mixed_vars births positions TG a.po_taint a.po_fn gn a.po_state t /\
    ptr_history_content a.po_taint a.po_state t /\
    a.po_state.vs_outcomes = t.vs_outcomes /\
    LENGTH a.po_state.vs_requests = LENGTH t.vs_requests
Proof
  strip_tac >>
  mp_tac (Q.INST [`vs` |-> `clip0`, `C'` |-> `CT`]
    ptr_dalloca_stage_frame_coverage_safe_static) >>
  (impl_tac >- (rpt conj_tac >> metis_tac[])) >>
  disch_then (qx_choosel_then [`R`,`lp`,`positions`] strip_assume_tac) >>
  first_x_assum (drule_then strip_assume_tac)
  >- (
    `~MEM i.inst_opcode [ASSIGN;NOP]` by fs[MEM] >>
    `i = a.po_inst` by
      (qpat_assum `i = concretize_inst_with_positions _ _` (fn th =>
         once_rewrite_tac[th] >> irule concretize_positions_other_opcode >>
         rewrite_tac[GSYM th] >> first_assum ACCEPT_TAC)) >>
    `frame_reachable clip0 C a.po_stack a.po_params a.po_prov a.po_taint
         a.po_fn i a.po_state` by fs[ptr_observation_reachable_def] >>
    `active_inst a.po_fn i a.po_state` by
      metis_tac[scfg_frame_reachable_active] >>
    `MEM a.po_fn C.ctx_functions` by metis_tac[ptr_frame_context_membership] >>
    `wf_function a.po_fn` by metis_tac[o1_ctx_shape_function_wf] >>
    `~in_revert_forward a.po_fn a.po_state` by
      (irule active_inst_not_revert_forward >> conj_tac
       >- fs[wf_function_def] >>
       qexists_tac `i` >> fs[MEM]) >>
    drule ptr_paired_prefix_endpoint >> simp[ptr_paired_sample_def, ptr_observe_def] >>
    strip_tac >>
    `a.po_state.vs_outcomes = t.vs_outcomes` by
      fs[ptr_history_content_def, ptr_taint_content_def, ptr_taint_control_def,
         ptr_core_shared_def, ptr_shared_fields_def] >>
    `LENGTH a.po_state.vs_requests = LENGTH t.vs_requests` by
      metis_tac[ptr_history_content_request_lengths] >>
    qexistsl_tac [`R`,`lp`,`positions`,`h`,`a`,`ht`,`done`,`tokens`,
      `registry`,`births`,`PT`,`TG`,`saved`,`entries`,`H`,`calls`,`ws`] >>
    metis_tac[ptr_observe_def]) >>
  `MEM gn CT.ctx_functions` by metis_tac[ptr_frame_context_membership] >>
  `wf_function gn` by metis_tac[o1_ctx_shape_function_wf] >>
  `active_inst gn i t` by metis_tac[scfg_frame_reachable_active] >>
  `?bt. lookup_block t.vs_current_bb gn.fn_blocks = SOME bt /\
     get_instruction bt t.vs_inst_idx = SOME i` by
    metis_tac[active_inst_block_lookup, wf_function_def] >>
  `bt = bb` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `bt = bb` SUBST_ALL_TAC >>
  rename1 `revert_forward_pair bb l r` >>
  `l <= t.vs_inst_idx` by decide_tac >>
  drule_all revert_forward_pair_interval_opcode >> fs[MEM]
QED
