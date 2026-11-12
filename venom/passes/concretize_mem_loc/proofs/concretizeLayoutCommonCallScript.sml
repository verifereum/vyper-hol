Theory concretizeLayoutCommonCall
Ancestors concretizeLayoutInterference concretizeLayoutNumeric
  concretizeLayoutMetadataSchedule concretizeLayoutDemand
  concretizeAnalysisImportSizes concretizeAnalysisRuntimeItems
  concretizeAnalysisOwnership o1ScheduleDecompHelpers
  concretizeAnalysisImportedDemand concretizeAnalysisMetadataOwnership
  concretizePtrOrdering concretizeStageLookup o1PassContract
  frameJointTrace frameJointTransition frameOriginHistory frameOriginReachable
  frameHistoryCfg frameExecutionHistory frameActivationCache ptrDiscipline
  ctxLookupAgreeHelpers
  staticLayoutAllocatorProofs concretizeMemLocDefs venomInst venomWf list pair finite_map arithmetic

Theorem concretize_context_local_import_separation:
  static_alloca_items fn = SOME items /\ fn_inst_ids_distinct fn /\
  fn.fn_forced_alloc_positions = FEMPTY /\
  concretize_function_fuel_in_context fuel ctx reserved fn = SOME out /\
  (!inst p s. MEM inst (fn_insts fn) /\ is_alloca_op inst.inst_opcode ==>
    ~MEM (Allocation inst.inst_id,p,s) (imported_mems_used ctx fn)) /\
  MEM (a,s) items /\ MEM (b,q,t) (imported_mems_used ctx fn) /\
  FLOOKUP (context_mem_livesets fuel ctx fn
    (bp_analyze_fuel fuel (cfg_analyze fn) fn) (cfg_analyze fn)) a = SOME l /\
  FLOOKUP (context_mem_livesets fuel ctx fn
    (bp_analyze_fuel fuel (cfg_analyze fn) fn) (cfg_analyze fn)) b = SOME k /\
  sinter inst_addr_to l k <> [] ==>
  ?p. FIND (\(b,q,t). b = a) out.fn_mems_used = SOME (a,p,s) /\
      (p+s <= q \/ q+t <= p)
Proof
  strip_tac >>
  `fn_has_alloca fn` by
    (drule static_alloca_items_MEM >>
     disch_then (qspec_then `(a,s)` mp_tac) >> simp[] >> strip_tac >>
     simp[fn_has_alloca_def, EXISTS_MEM] >> qexists_tac `inst` >>
     simp[is_alloca_op_def]) >>
  `imported_mems_used ctx fn <> []` by metis_tac[MEM] >>
  qpat_x_assum `concretize_function_fuel_in_context _ _ _ _ = _` mp_tac >>
  simp[concretize_function_fuel_in_context_def] >>
  Cases_on `fn_has_static_layout fn` >> simp[] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  drule_all context_layout_local_import_disjoint >> strip_tac >>
  drule_all context_layout_local_lookup_find >> metis_tac[]
QED

Theorem concretize_common_call_activation_disjoint:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY ssa_form C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  ptr_discipline lo C vs0 /\ EVERY all_reachable C.ctx_functions /\ ~ctx_has_dalloca C /\
  joint_trace vs0 C q0 es qs q /\ c < n /\ n <= j /\ j <= LENGTH es /\
  EL c (q0::qs) = JointConfig stk0 PG0 G0 tn0 caller invoke s0 oms0 om0 hs0 h0 /\
  joint_transition C (EL c (q0::qs)) NONE (EL (SUC c) (q0::qs)) /\
  (!k. c < k /\ k <= n ==> LENGTH stk0 < activation_depth (EL k (q0::qs))) /\
  activation_cache (EL n (q0::qs)) dB ownerB aidB (bB,szB) /\ LENGTH stk0 < dB /\
  bB <= byteB /\ byteB < bB + szB /\
  EL j (q0::qs) = JointConfig stkJ PGJ GJ tnJ reader instJ sJ omsJ omJ hsJ hJ /\
  byteA IN joint_reads (EL j (q0::qs)) /\ lo <= byteA /\
  byteA NOTIN joint_mem_taint (EL j (q0::qs)) /\ ~in_revert_forward reader sJ /\
  (!k. n <= k /\ k < j ==> byteA NOTIN joint_writes (EL k (q0::qs)) (EL k es)) /\
  activation_cache (EL j (q0::qs)) (LENGTH stk0) caller aidA (bA,szA) /\
  bA <= byteA /\ byteA < bA + szA /\
  canonical_metadata C C' (Allocation aidA) pA szA /\
  canonical_metadata C C' (Allocation aidB) pB szB ==>
  pA + szA <= pB \/ pB + szB <= pA
Proof
  strip_tac >>
  `n <= LENGTH es /\ 0 < j` by decide_tac >>
  `joint_config_reachable vs0 C (EL j (q0::qs))` by
    (drule joint_trace_edge_at >> disch_then (qspec_then `j-1` mp_tac) >>
     `SUC (j-1) = j /\ j-1 < LENGTH es` by decide_tac >>
     pure_asm_rewrite_tac[] >> metis_tac[]) >>
  `?itemsA. static_alloca_items caller = SOME itemsA /\
     MEM (Allocation aidA,szA) itemsA` by
    (irule activation_cache_source_static_item >>
     goal_assum (drule_at (Pat `activation_cache _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `joint_config_reachable _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  `MEM caller C.ctx_functions` by
    (`joint_config_reachable vs0 C (EL c (q0::qs))` by
       metis_tac[joint_trace_edge_at, LESS_LESS_EQ_TRANS] >>
     qpat_x_assum `joint_config_reachable _ _ (EL c _)` mp_tac >>
     simp[joint_config_reachable_def] >> strip_tac >>
     drule joint_origin_history_erasure >> strip_tac >>
     drule origin_frame_erasure >> strip_tac >>
     drule frame_reachable_has_history >> strip_tac >>
     `EVERY wf_function C.ctx_functions` by
       (gvs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[o1_fn_shape_def]) >>
     drule_all frame_history_cfg_invariant >> simp[]) >>
  `lookup_function caller.fn_name C.ctx_functions = SOME caller` by
    (irule (iffRL lookup_function_member_iff) >>
     gvs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def]) >>
  drule_all ctx_pass_stage_lookup >> strip_tac >>
  drule_all concretize_common_call_activation_livesets >> strip_tac >>
  `joint_config_reachable vs0 C (EL n (q0::qs))` by
    (drule joint_trace_edge_at >> disch_then (qspec_then `n-1` mp_tac) >>
     `SUC (n-1) = n /\ n-1 < LENGTH es` by decide_tac >>
     pure_asm_rewrite_tac[] >> metis_tac[]) >>
  `?itemsB. static_alloca_items ownerB = SOME itemsB /\
     MEM (Allocation aidB,szB) itemsB` by
    (irule activation_cache_source_static_item >>
     goal_assum (drule_at (Pat `activation_cache _ _ ownerB _ _`)) >>
     goal_assum (drule_at (Pat `joint_config_reachable _ _ (EL n _)`)) >>
     simp[] >> metis_tac[]) >>
  drule_all joint_open_call_activation_summary >> strip_tac >>
  `MEM invoke (fn_insts caller)` by
    (qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
     simp[joint_transition_call_iff] >>
     disch_then (assume_tac o CONJUNCT1) >>
     drule_at (Pat `active_inst _ _ _`) EVERY_active_inst >>
     disch_then (qspec_then `\i. MEM i (fn_insts caller)` mp_tac) >>
     simp[EVERY_MEM]) >>
  `root.fn_name = name` by metis_tac[lookup_function_selected_name] >>
  `MEM (Allocation aidB,p,szB) (imported_mems_used observed.cu_context caller)` by
    (irule concretize_observed_exact_import >> conj_tac
     >- (qexistsl_tac [`ops`,`g`,`invoke`,`name`] >> simp[] >> metis_tac[]) >>
     goal_assum (drule_at (Pat `ctx_pass_stage _ _ _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  `!inst p s. MEM inst (fn_insts caller) /\ is_alloca_op inst.inst_opcode ==>
      ~MEM (Allocation inst.inst_id,p,s) (imported_mems_used observed.cu_context caller)` by
    (rpt strip_tac >> drule_all concretize_imports_exclude_local >>
     simp[EXISTS_MEM, EXISTS_PROD] >> metis_tac[]) >>
  `sinter inst_addr_to addrsA addrsB <> []` by
    (`MEM (s0.vs_current_bb,s0.vs_inst_idx) (sinter inst_addr_to addrsA addrsB)` by
       (irule (iffRL ptr_context_livesets_sinter_membership) >>
        goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
     metis_tac[MEM]) >>
  `caller.fn_forced_alloc_positions = FEMPTY` by
    (gvs[ptr_discipline_def, EVERY_MEM] >> metis_tac[fn_ptr_ok_def]) >>
  `fn_inst_ids_distinct caller` by metis_tac[source_member_ids_distinct] >>
  `concretize_function_fuel_in_context (concretize_memloc_fuel caller)
    observed.cu_context observed.cu_context.ctx_global_reserved caller = SOME fn'` by
    (qpat_x_assum `fn_pass_step _ _ _ _ _ _` mp_tac >>
     simp[fn_pass_step_def, AllCaseEqs()] >> strip_tac >> gvs[]) >>
  drule_all concretize_context_local_import_separation >> strip_tac >>
  `canonical_metadata C C' (Allocation aidA) p' szA` by
    (simp[canonical_metadata_def] >>
     qexistsl_tac [`caller`,`itemsA`,`fn'`] >> simp[]) >>
  `canonical_metadata C C' (Allocation aidB) p szB` by
    (drule_all concretize_import_canonical_metadata >>
     simp[EVERY_MEM, FORALL_PROD] >> metis_tac[]) >>
  metis_tac[canonical_metadata_unique]
QED

Theorem concretize_common_call_disjoint:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY ssa_form C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  ptr_discipline lo C vs0 /\ EVERY all_reachable C.ctx_functions /\ ~ctx_has_dalloca C /\
  joint_trace vs0 C q0 es qs q /\ c < n /\ n <= j /\ j <= LENGTH es /\
  EL c (q0::qs) = JointConfig stk0 PG0 G0 tn0 caller invoke s0 oms0 om0 hs0 h0 /\
  joint_transition C (EL c (q0::qs)) NONE (EL (SUC c) (q0::qs)) /\
  (!k. c < k /\ k <= n ==> LENGTH stk0 < activation_depth (EL k (q0::qs))) /\
  EL n (q0::qs) = JointConfig stkN PGN GN tnN current instN sN omsN omN hsN hN /\
  FLOOKUP sN.vs_allocas aidB = SOME (bB,szB) /\ bB <= byteB /\ byteB < bB + szB /\
  EL j (q0::qs) = JointConfig stkJ PGJ GJ tnJ reader instJ sJ omsJ omJ hsJ hJ /\
  byteA IN joint_reads (EL j (q0::qs)) /\ lo <= byteA /\
  byteA NOTIN joint_mem_taint (EL j (q0::qs)) /\ ~in_revert_forward reader sJ /\
  (!k. n <= k /\ k < j ==> byteA NOTIN joint_writes (EL k (q0::qs)) (EL k es)) /\
  activation_cache (EL j (q0::qs)) (LENGTH stk0) caller aidA (bA,szA) /\
  bA <= byteA /\ byteA < bA + szA /\
  canonical_metadata C C' (Allocation aidA) pA szA /\
  canonical_metadata C C' (Allocation aidB) pB szB ==>
  pA + szA <= pB \/ pB + szB <= pA
Proof
  strip_tac >>
  `activation_cache (EL n (q0::qs)) (LENGTH stkN) current aidB (bB,szB)` by
    simp[activation_cache_current] >>
  `LENGTH stk0 < LENGTH stkN` by
    (qpat_x_assum `!k. c < k /\ k <= n ==> _` (qspec_then `n` mp_tac) >>
     simp[activation_depth_def]) >>
  drule_all concretize_common_call_activation_disjoint >> simp[]
QED
