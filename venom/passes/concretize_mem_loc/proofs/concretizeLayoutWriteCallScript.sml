Theory concretizeLayoutWriteCall
Ancestors concretizeLayoutCommonCall concretizeAnalysisWriteLiveset
  o1ScheduleDecompHelpers concretizeAnalysisOwnership concretizeAnalysisTemporalDemand
  concretizeAnalysisImportedDemand concretizeAnalysisImportSizes
  concretizeAnalysisRuntimeItems concretizeAnalysisMetadataOwnership
  concretizeLayoutMetadataSchedule concretizePtrOrdering concretizeStageLookup
  frameJointTrace frameJointTransition frameOpenCall frameActivationCache
  frameOriginHistory frameOriginReachable frameHistoryCfg frameExecutionHistory
  ptrDiscipline o1PassContract ctxLookupAgreeHelpers concretizeMemLocDefs
  venomInst venomWf list pair finite_map arithmetic

Theorem concretize_common_call_write_activation_disjoint:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY ssa_form C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  ptr_discipline lo C vs0 /\ EVERY all_reachable C.ctx_functions /\ ~ctx_has_dalloca C /\
  joint_trace vs0 C q0 es qs q /\ c < n /\ n < LENGTH es /\
  EL c (q0::qs) = JointConfig stk0 PG0 G0 tn0 caller invoke s0 oms0 om0 hs0 h0 /\
  joint_transition C (EL c (q0::qs)) NONE (EL (SUC c) (q0::qs)) /\
  (!k. c < k /\ k <= n ==> LENGTH stk0 < activation_depth (EL k (q0::qs))) /\
  EL n (q0::qs) = JointConfig stkN PGN GN tnN writer instN sN omsN omN hsN hN /\
  ~in_revert_forward writer sN /\
  byteB IN joint_writes (EL n (q0::qs)) (EL n es) /\ lo <= byteB /\
  activation_cache (EL n (q0::qs)) (LENGTH stk0) caller aidB (bB,szB) /\
  bB <= byteB /\ byteB < bB+szB /\
  activation_cache (EL n (q0::qs)) dA ownerA aidA (bA,szA) /\ LENGTH stk0 < dA /\
  bA <= byteA /\ byteA < bA+szA /\
  canonical_metadata C C' (Allocation aidA) pA szA /\
  canonical_metadata C C' (Allocation aidB) pB szB ==>
  pA+szA <= pB \/ pB+szB <= pA
Proof
  strip_tac >>
  `n <= LENGTH es` by decide_tac >>
  `joint_config_reachable vs0 C (EL n (q0::qs)) /\
   joint_transition C (EL n (q0::qs)) (EL n es) (EL (SUC n) (q0::qs))` by
    metis_tac[joint_trace_edge_at] >>
  `?itemsB. static_alloca_items caller = SOME itemsB /\
     MEM (Allocation aidB,szB) itemsB` by
    (irule activation_cache_source_static_item >>
     goal_assum (drule_at (Pat `activation_cache _ _ caller _ _`)) >>
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
  suspend "livesets"
QED

Resume concretize_common_call_write_activation_disjoint[livesets]:
  `(EL (LENGTH stkN - SUC (LENGTH stk0)) stkN).cf_fn = caller /\
   (EL (LENGTH stkN - SUC (LENGTH stk0)) stkN).cf_inst = invoke /\
   (EL (LENGTH stkN - SUC (LENGTH stk0)) stkN).cf_state = s0 /\
   invoke.inst_opcode = INVOKE` by
    (irule joint_open_call_saved_at >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `joint_transition _ _ NONE _`)) >>
     goal_assum (drule_at (Pat `EL n (_::_) = _`)) >>
     simp[] >> metis_tac[]) >>
  `LENGTH stk0 < LENGTH stkN` by
    (qpat_x_assum `!k. c < k /\ k <= n ==> _` (qspec_then `n` mp_tac) >>
     simp[activation_depth_def]) >>
  `active_inst caller invoke s0` by
    (qpat_x_assum `joint_transition _ _ NONE _` mp_tac >>
     simp[joint_transition_call_iff] >> metis_tac[]) >>
  `activation_location (EL n (q0::qs)) (LENGTH stk0) caller
     (s0.vs_current_bb,s0.vs_inst_idx)` by simp[activation_location_def] >>
  `?addrsB. FLOOKUP (context_mem_livesets (concretize_memloc_fuel caller)
      observed.cu_context caller
      (bp_analyze_fuel (concretize_memloc_fuel caller) (cfg_analyze caller) caller)
      (cfg_analyze caller)) (Allocation aidB) = SOME addrsB /\
      MEM (s0.vs_current_bb,s0.vs_inst_idx) addrsB` by
    (qpat_assum `EL n (_::_) = _`
       (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
     drule_all concretize_write_owner_liveset >> simp[]) >>
  `?addrsA. FLOOKUP (context_mem_livesets (concretize_memloc_fuel caller)
      observed.cu_context caller
      (bp_analyze_fuel (concretize_memloc_fuel caller) (cfg_analyze caller) caller)
      (cfg_analyze caller)) (Allocation aidA) = SOME addrsA /\
      MEM (s0.vs_current_bb,s0.vs_inst_idx) addrsA` by
    (irule concretize_open_call_activation_liveset_context >>
     goal_assum (drule_at (Pat `ctx_pass_stage _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `joint_transition _ _ NONE _`)) >>
     goal_assum (drule_at (Pat `activation_cache _ _ ownerA _ _`)) >>
     goal_assum (drule_at (Pat `o1_walk_view _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `EL c (_::_) = _`)) >>
     qexists_tac `byteA` >> simp[] >> metis_tac[]) >>
  `?itemsA. static_alloca_items ownerA = SOME itemsA /\
     MEM (Allocation aidA,szA) itemsA` by
    (irule activation_cache_source_static_item >>
     goal_assum (drule_at (Pat `activation_cache _ _ ownerA _ _`)) >>
     goal_assum (drule_at (Pat `joint_config_reachable _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  drule_all joint_open_call_activation_summary >> strip_tac >>
  suspend "numeric"
QED

Resume concretize_common_call_write_activation_disjoint[numeric]:
  qpat_x_assum `joint_trace _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `!k. c < k /\ k <= n ==> _` kall_tac >>
  qpat_x_assum `joint_config_reachable _ _ _` kall_tac >>
  rpt (qpat_x_assum `joint_transition _ _ _ _` kall_tac) >>
  rpt (qpat_x_assum `activation_cache _ _ _ _ _` kall_tac) >>
  qpat_x_assum `activation_location _ _ _ _` kall_tac >>
  `MEM invoke (fn_insts caller)` by
    (drule_at (Pat `active_inst _ _ _`) EVERY_active_inst >>
     disch_then (qspec_then `\i. MEM i (fn_insts caller)` mp_tac) >>
     simp[EVERY_MEM]) >>
  `root.fn_name = name` by metis_tac[lookup_function_selected_name] >>
  `MEM (Allocation aidA,p,szA) (imported_mems_used observed.cu_context caller)` by
    (irule concretize_observed_exact_import >> conj_tac
     >- (qexistsl_tac [`ops`,`g`,`invoke`,`name`] >> simp[] >> metis_tac[]) >>
     goal_assum (drule_at (Pat `ctx_pass_stage _ _ _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  `!inst p s. MEM inst (fn_insts caller) /\ is_alloca_op inst.inst_opcode ==>
      ~MEM (Allocation inst.inst_id,p,s) (imported_mems_used observed.cu_context caller)` by
    (rpt strip_tac >> drule_all concretize_imports_exclude_local >>
     simp[EXISTS_MEM, EXISTS_PROD] >> metis_tac[]) >>
  `sinter inst_addr_to addrsB addrsA <> []` by
    (`MEM (s0.vs_current_bb,s0.vs_inst_idx) (sinter inst_addr_to addrsB addrsA)` by
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
  `canonical_metadata C C' (Allocation aidB) p' szB` by
    (simp[canonical_metadata_def] >>
     qexistsl_tac [`caller`,`itemsB`,`fn'`] >> simp[]) >>
  `canonical_metadata C C' (Allocation aidA) p szA` by
    (drule_all concretize_import_canonical_metadata >>
     simp[EVERY_MEM, FORALL_PROD] >> metis_tac[]) >>
  metis_tac[canonical_metadata_unique]
QED

Finalise concretize_common_call_write_activation_disjoint
