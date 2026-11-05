Theory concretizeLayoutLocalDemand
Ancestors concretizeLayoutCommonCall concretizeLayoutInterference
  concretizeLayoutNumeric concretizeMemLocDefs staticLayoutAllocatorProofs
  concretizeAnalysisWriteLiveset concretizeAnalysisOwnerDemand
  concretizeAnalysisImportSizes concretizePtrOrdering
  concretizeAnalysisRuntimeItems concretizeAnalysisTemporalDemand concretizeAnalysisOwnership
  concretizeLayoutMetadataSchedule concretizeStageLookup o1ScheduleDecompHelpers
  frameDemandTaint frameJointTrace frameJointTransition frameActivationCache
  frameOriginHistory frameOriginReachable frameExecutionHistory frameHistoryCfg
  frameHistoryInstructions frameHistoryDefinitions
  ptrDiscipline o1PassContract ctxLookupAgreeHelpers contextCodegenRel unitTransformDefs
  venomInst venomWf list pair finite_map option arithmetic

Theorem distinct_allocas_multiple:
  !xs i j. MEM i xs /\ MEM j xs /\ i <> j /\
    is_alloca_op i.inst_opcode /\ is_alloca_op j.inst_opcode ==>
    insts_have_multiple_allocas xs
Proof
  Induct >> simp[insts_have_multiple_allocas_def] >> rpt strip_tac >>
  Cases_on `is_alloca_op h.inst_opcode` >>
  simp[insts_have_multiple_allocas_def, EXISTS_MEM] >> metis_tac[]
QED

Theorem distinct_static_items_need_liveness:
  static_alloca_items fn = SOME items /\ MEM (a,s) items /\
  MEM (b,t) items /\ a <> b ==> fn_needs_liveness_allocation fn
Proof
  strip_tac >>
  `?i. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
    exact_static_alloca i = SOME (a,s)` by metis_tac[static_alloca_items_MEM] >>
  `?j. MEM j (fn_insts fn) /\ j.inst_opcode = ALLOCA /\
    exact_static_alloca j = SOME (b,t)` by metis_tac[static_alloca_items_MEM] >>
  `i <> j` by metis_tac[PAIR_EQ, SOME_11] >>
  simp[fn_needs_liveness_allocation_def] >>
  irule distinct_allocas_multiple >>
  qexistsl_tac [`i`,`j`] >> simp[is_alloca_op_def]
QED

Theorem concretize_context_local_local_separation:
  static_alloca_items fn = SOME items /\ fn_inst_ids_distinct fn /\
  fn.fn_forced_alloc_positions = FEMPTY /\
  concretize_function_fuel_in_context fuel ctx reserved fn = SOME out /\
  (!inst p s. MEM inst (fn_insts fn) /\ is_alloca_op inst.inst_opcode ==>
    ~MEM (Allocation inst.inst_id,p,s) (imported_mems_used ctx fn)) /\
  MEM (a,s) items /\ MEM (b,t) items /\ a <> b /\
  FLOOKUP (context_mem_livesets fuel ctx fn
    (bp_analyze_fuel fuel (cfg_analyze fn) fn) (cfg_analyze fn)) a = SOME l /\
  FLOOKUP (context_mem_livesets fuel ctx fn
    (bp_analyze_fuel fuel (cfg_analyze fn) fn) (cfg_analyze fn)) b = SOME k /\
  sinter inst_addr_to l k <> [] ==>
  ?p q. FIND (\(b,q,t). b = a) out.fn_mems_used = SOME (a,p,s) /\
        FIND (\(a,p,s). a = b) out.fn_mems_used = SOME (b,q,t) /\
        (p+s <= q \/ q+t <= p)
Proof
  strip_tac >>
  `fn_needs_liveness_allocation fn` by metis_tac[distinct_static_items_need_liveness] >>
  `fn_has_alloca fn` by
    (drule static_alloca_items_MEM >>
     disch_then (qspec_then `(a,s)` mp_tac) >> simp[] >> strip_tac >>
     simp[fn_has_alloca_def, EXISTS_MEM] >> qexists_tac `inst` >>
     simp[is_alloca_op_def]) >>
  qpat_x_assum `concretize_function_fuel_in_context _ _ _ _ = _` mp_tac >>
  simp[concretize_function_fuel_in_context_def] >>
  Cases_on `fn_has_static_layout fn` >> simp[] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  drule_all context_layout_local_local_disjoint >> strip_tac >>
  metis_tac[context_layout_local_lookup_find]
QED

Theorem concretize_same_activation_write_demand_disjoint:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY ssa_form C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  ptr_discipline lo C vs0 /\ EVERY all_reachable C.ctx_functions /\ ~ctx_has_dalloca C /\
  joint_trace vs0 C q0 es qs q /\ n < LENGTH es /\ n <= j /\ j <= LENGTH es /\
  EL n (q0::qs) = JointConfig stkN PGN GN tnN writer instN sN omsN omN hsN hN /\
  ~in_revert_forward writer sN /\
  byteB IN joint_writes (EL n (q0::qs)) (EL n es) /\ lo <= byteB /\
  EL j (q0::qs) = JointConfig stkJ PGJ GJ tnJ reader instJ sJ omsJ omJ hsJ hJ /\
  byteA IN joint_reads (EL j (q0::qs)) /\ lo <= byteA /\
  byteA NOTIN joint_mem_taint (EL j (q0::qs)) /\ ~in_revert_forward reader sJ /\
  (!k. n <= k /\ k < j ==> byteA NOTIN joint_writes (EL k (q0::qs)) (EL k es)) /\
  activation_cache (EL j (q0::qs)) d owner aidA (bA,szA) /\
  activation_cache (EL n (q0::qs)) d owner aidB (bB,szB) /\
  bA <= byteA /\ byteA < bA+szA /\ bB <= byteB /\ byteB < bB+szB /\ aidA <> aidB /\
  canonical_metadata C C' (Allocation aidA) pA szA /\
  canonical_metadata C C' (Allocation aidB) pB szB ==>
  pA+szA <= pB \/ pB+szB <= pA
Proof
  strip_tac >>
  `vs0.vs_allocas = FEMPTY` by gvs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  `activation_cache (EL n (q0::qs)) d owner aidA (bA,szA)` by
    (irule (cj 2 joint_untainted_demand_cache) >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `activation_cache (EL j _) _ _ _ _`)) >>
     qexists_tac `byteA` >> simp[] >> qexists_tac `n` >> simp[]) >>
  `joint_config_reachable vs0 C (EL n (q0::qs)) /\
   joint_transition C (EL n (q0::qs)) (EL n es) (EL (SUC n) (q0::qs))` by
    metis_tac[joint_trace_edge_at] >>
  `EVERY wf_function C.ctx_functions` by
    (gvs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[o1_fn_shape_def]) >>
  `MEM owner C.ctx_functions /\ ?loc. activation_location (EL n (q0::qs)) d owner loc` by
    suspend "location" >>
  `lookup_function owner.fn_name C.ctx_functions = SOME owner` by
    (irule (iffRL lookup_function_member_iff) >>
     gvs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def]) >>
  drule_all ctx_pass_stage_lookup >> strip_tac >>
  suspend "livesets"
QED

Resume concretize_same_activation_write_demand_disjoint[location]:
  qpat_x_assum `joint_config_reachable _ _ _` mp_tac >>
  simp[joint_config_reachable_def] >> strip_tac >>
  drule joint_origin_history_erasure >> strip_tac >>
  drule origin_frame_erasure >> strip_tac >>
  drule frame_reachable_has_history >> strip_tac >>
  drule_all frame_history_instruction_prefix_invariant >> strip_tac >>
  `active_inst writer instN sN` by metis_tac[frame_history_active] >>
  qpat_x_assum `activation_cache _ _ _ aidB _` mp_tac >>
  simp[activation_cache_def] >> strip_tac >> gvs[]
  >- (simp[activation_location_def] >> metis_tac[]) >>
  gvs[LIST_REL_EL_EQN] >>
  `LENGTH stkN - SUC d < LENGTH stkN` by decide_tac >>
  `MEM (EL (LENGTH stkN - SUC d) stkN).cf_fn C.ctx_functions /\
   active_inst (EL (LENGTH stkN - SUC d) stkN).cf_fn
     (EL (LENGTH stkN - SUC d) stkN).cf_inst
     (EL (LENGTH stkN - SUC d) stkN).cf_state` by metis_tac[] >>
  simp[activation_location_def] >> metis_tac[]
QED

Resume concretize_same_activation_write_demand_disjoint[livesets]:
  `?addrsB. FLOOKUP (context_mem_livesets (concretize_memloc_fuel owner)
      observed.cu_context owner
      (bp_analyze_fuel (concretize_memloc_fuel owner) (cfg_analyze owner) owner)
      (cfg_analyze owner)) (Allocation aidB) = SOME addrsB /\ MEM loc addrsB` by
    (qpat_assum `EL n (_::_) = _`
       (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
     drule_all concretize_write_owner_liveset >> simp[]) >>
  `?addrsA. FLOOKUP (context_mem_livesets (concretize_memloc_fuel owner)
      observed.cu_context owner
      (bp_analyze_fuel (concretize_memloc_fuel owner) (cfg_analyze owner) owner)
      (cfg_analyze owner)) (Allocation aidA) = SOME addrsA /\ MEM loc addrsA` by
    (irule concretize_untainted_owner_read_liveset >> conj_tac >- simp[] >>
     goal_assum (drule_at (Pat `ctx_pass_stage _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `_ IN joint_reads _`)) >>
     goal_assum (drule_at (Pat `activation_location _ _ _ _`)) >>
     goal_assum (drule_at (Pat `activation_cache (EL j _) _ _ aidA _`)) >>
     goal_assum (drule_at (Pat `EL j (_::_) = _`)) >>
     goal_assum (drule_at (Pat `o1_walk_view _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `ptr_discipline _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  `?itemsA. static_alloca_items owner = SOME itemsA /\
     MEM (Allocation aidA,szA) itemsA` by
    (irule activation_cache_source_static_item >>
     goal_assum (drule_at (Pat `joint_config_reachable _ _ _`)) >>
     goal_assum (drule_at (Pat `activation_cache _ _ _ _ _`)) >>
     simp[]) >>
  `MEM (Allocation aidB,szB) itemsA` by
    (`?itemsB. static_alloca_items owner = SOME itemsB /\
        MEM (Allocation aidB,szB) itemsB` by
       (irule activation_cache_source_static_item >>
        goal_assum (drule_at (Pat `joint_config_reachable _ _ _`)) >>
        goal_assum (drule_at (Pat `activation_cache _ _ _ _ _`)) >>
        simp[]) >> gvs[]) >>
  suspend "numeric"
QED

Resume concretize_same_activation_write_demand_disjoint[numeric]:
  `!inst p s. MEM inst (fn_insts owner) /\ is_alloca_op inst.inst_opcode ==>
      ~MEM (Allocation inst.inst_id,p,s) (imported_mems_used observed.cu_context owner)` by
    (rpt strip_tac >> drule_all concretize_imports_exclude_local >>
     simp[EXISTS_MEM, EXISTS_PROD] >> metis_tac[]) >>
  `sinter inst_addr_to addrsA addrsB <> []` by
    (`MEM loc (sinter inst_addr_to addrsA addrsB)` by
       (irule (iffRL ptr_context_livesets_sinter_membership) >>
        goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
     metis_tac[MEM]) >>
  `owner.fn_forced_alloc_positions = FEMPTY` by
    (gvs[ptr_discipline_def, EVERY_MEM] >> metis_tac[fn_ptr_ok_def]) >>
  `fn_inst_ids_distinct owner` by metis_tac[source_member_ids_distinct] >>
  `concretize_function_fuel_in_context (concretize_memloc_fuel owner)
    observed.cu_context observed.cu_context.ctx_global_reserved owner = SOME fn'` by
    (qpat_x_assum `fn_pass_step _ _ _ _ _ _` mp_tac >>
     simp[fn_pass_step_def, AllCaseEqs()] >> strip_tac >> gvs[]) >>
  `Allocation aidA <> Allocation aidB` by simp[] >>
  drule_all concretize_context_local_local_separation >> strip_tac >>
  `canonical_metadata C C' (Allocation aidA) p szA /\
   canonical_metadata C C' (Allocation aidB) q' szB` by
    (simp[canonical_metadata_def] >> conj_tac >>
     qexistsl_tac [`owner`,`itemsA`,`fn'`] >> simp[]) >>
  metis_tac[canonical_metadata_unique]
QED

Finalise concretize_same_activation_write_demand_disjoint
