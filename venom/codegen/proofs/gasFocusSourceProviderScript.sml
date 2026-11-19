Theory gasFocusSourceProvider
Ancestors lowerDloadSafetyKernel[qualified,ignore_grammar]
  gasFocusSourceStages
  dftFinitePacket dftGasFromListTraceDefs
  o1ContractCfgNormJointCursors frameJointTrace frameJointTransition
  fnFramePrefixDriver fnFrameSymbolicPrefix codegenEntryRel
  o1PipelineCorrect o1SafeUpto o1PassContract o1PassLift unitMemInv
  venomPipelineRunner venomPassSchedule irSupply fcgDefs
  dftGasOracleDefs gasEvents contextRawReachable memSafeRun
  venomExecSemantics venomWf venomInst venomState unitShapeDefs
  codegenSymRel asmDataEnv asmFrameRel asmOptimizer asmSem asmSymSem symbolResolve
  contextCodegenRel lowerDloadDefs staticAbortDefs frameOutcome callTrace
  o1RequestContract unitTransformDefs ptrDiscipline passSimulationDefs
  vfmExecution codegen asmIR
  finite_map list rich_list words arithmetic
  o1CodeEndSourceCutTransport o1ComposeSupport o1PipelineCompose simplifyCfgDefs
  makeSsaDefs o1ContractSimplifyCfg
  o1CodeEndCfgRounds o1CodeEndCfgCollapse simplifyCfgStaticInterface simplifyCfgShapeCore simplifyCfgProof simplifyCfgSimTools gasFocusFmpCutEntryStatic gasFocusFmpStagePin o1LowerDloadSourceEntry
  fmpStageCoverInv fmpStageCoverMem fmpStageRel fmpLowerDefs fmpStepLayout
  fmpStepStructural fmpAnalysisProps fmpStageFmpStepsEntryLayout
  ctxLookupAgreeHelpers gasFocusFmpCutResidual concretizeLayoutCutSafe
  gasFocusLowerDloadCodecopyPoint lowerDloadSafetyRelation lowerDloadSafetyAmbient o1LowerDloadPtrDiscipline lowerDloadPtrSupport
  o1ContractSimplifyCfgSrcFrame simplifyCfgAvailability ptrStaticDiscipline
  allocaFrontierBound fmpStageControl fmpStageCallArity fmpStageCoverBackParam
  fmpStageCoverBackKeptOps fmpCoverInvokeIndex lowerDloadPtrRawReachable
  gasFocusFmpCutSites gasFocusFmpCutSegments gasFocusFmpCutRestorePrefix
  fmpStageFmpStepsRestoreControl fmpStepReclaim analysisSimDefs
  gasFocusFmpCutForwardLayout gasFocusFmpRetpcPoint
  lowerDloadNormalDispatch o1LowerDloadJointRetpc gasFocusFmpCutSourceJump
  gasFocusFmpCutJumpEntry gasFocusFmpJumpPoint fmpStageRunnerFacts
  gasFocusFmpCutSourceCall gasFocusFmpCutInvokePush gasFocusFmpCutInvokeOutputs
  gasFocusFmpCutSourceReturn gasFocusFmpCutInvokePop
  concretizePtrCoverageStaticMemReachability frameAllocationOwnership
  lowerDloadSafetyKeyedEnvironmentReadEffects lowerDloadSafetyAccountReadEffects
  lowerDloadSafetyStorageReadEffects lowerDloadSafetyHashLog
  lowerDloadSafetyImmutableWriteEffects lowerDloadSafetyWriteAssembly
  lowerDloadSafetyTaintWidth lowerDloadSafetyAllocBounds
  lowerDloadFrontier lowerDloadSafetyUpdates lowerDloadSafetyValues
  pointerConfinedDefs venomEffects gasCount lowerDloadOracleCallAssembly
  fmpStepPredicateTransport fmpStepRewrite fmpStepRestrictionClosure fmpStepBridge
  concretizeAllocationFree o1MakeSsaStructuralShape o1ContractMakeSsaReplay
  simplifyCfgInvariant o1ContractSue singleUseExpansionSupplySim callLayoutDefs
  fmpStageCoverMemAssemble fmpStageOpBase fmpStepRewriteOrigin o1LabelFlowMiddle
  o1CodeEndLowerLifetime o1CodeEndConcretizeLifetime fmpStepOpaque fmpLowerProps
  fmpStageControlWalk fmpLowerIndexedProps frameViewFacts o1LowerDloadRelocationKernel
  fmpStepSupply fmpStepRetpcShape venomFnInstsProofs venomFnScheduleRunner venomFnScheduleRunnerProps
  gasFocusConcretizeCutCoverage gasFocusConcretizeCutActualWrite gasFocusSourceC2Prefix gasFocusLowerDloadCut o1ContractLowerDloadStage lowerDloadMakeSsaInput lowerDloadSupplyProofs contextPlanLayoutProps codegenEntrySim gasFocusConcretizeEndpointCut
  concretizePtrPairedPrefix concretizePtrStructuralTranscript concretizePtrStructuralTrace
  gasFocusConcretizeHistoricalCut o1CodeEndConcretizeRead o1LabelFlowMiddleConcretize o1LabelFlowMiddleFmp concretizePtrChronologicalHistory concretizePtrEventEmbedding concretizePtrActualByteFrame
  concretizePtrPrefixLedger concretizePtrBytes concretizePtrSourceOwnership
  concretizePtrActivationBirths concretizePtrStagePlacements concretizePtrValueTransport
  concretizePtrParamSupport concretizePtrRequestHistory concretizePtrOperationalOpcodes concretizePtrChronologicalDemand lowerDloadReachability lowerDloadRevertSuffix concretizeMemLocDefs concretizePtrOwnerPath lowerDloadDynHeadroom
  lowerDloadDescriptorObservation venomExecProofs pred_set staticLayoutDefs memLocDefs passSharedDefs concretizeStepStructure concretizePtrPairedFields unitLabelMapIdentity stepWriteFootprintBase

(* Recover the byte at its paired write, then frame both later intervals. *)
Theorem focus_layout_owned_recovery[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ EVERY all_reachable C.ctx_functions /\
  EVERY ssa_form C.ctx_functions /\
  o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\
  code_layout_valid vs /\ EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  alloca_frontier_upto n C vs /\ fixed_region_reserved lo C /\
  ptr_discipline_upto lo n C vs /\ gas_cut n vs at.po_state /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  ~in_revert_forward endpoint.po_fn endpoint.po_state /\
  endpoint.po_inst.inst_opcode <> ASSIGN /\
  d <= LENGTH endpoint.po_stack /\ EL (LENGTH endpoint.po_stack - d) tokens = token /\
  FLOOKUP TG v = SOME (token,aid) /\ MEM (Var v) endpoint.po_inst.inst_operands /\
  (inst_read_op endpoint.po_inst = SOME (Var v) \/ endpoint.po_inst.inst_opcode = INVOKE) /\
  FLOOKUP (ptr_owner_view d endpoint).cf_state.vs_allocas aid = SOME (b,sz) /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
  b <= x /\ x < b + sz /\ lo <= x /\ x < dyn_floor C vs /\
  x NOTIN endpoint.po_taint.t_mem ==>
  read_byte x endpoint.po_state.vs_memory = read_byte (pa + (x-b)) at.po_state.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_structural_trace_target >> strip_tac >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  `LENGTH ht = SUC (LENGTH done)` by fs[ptr_event_embedding_def] >>
  `EL (LENGTH h-1) h = endpoint /\ EL (LENGTH ht-1) ht = at /\
   LENGTH h-1 < LENGTH h` by
    (imp_res_tac ptr_chrono_history_end >>
     `0 < LENGTH h` by (Cases_on `h` >> fs[]) >>
     `LENGTH ht - 1 = LENGTH done` by simp[] >>
     qpat_x_assum `LAST h = endpoint` mp_tac >>
     qpat_x_assum `LAST ht = at` mp_tac >>
     simp[LAST_EL, PRE_SUB1]) >>
  `EL (LENGTH h-1) H = (tokens,registry,births,PT,TG,saved,entries)` by
    (drule ptr_structural_transcript_endpoint >> strip_tac >>
     `H <> []` by (Cases_on `H` >> fs[]) >>
     qpat_x_assum `LAST H = _` mp_tac >> simp[LAST_EL, PRE_SUB1]) >>
  Q.SUBGOAL_THEN `LENGTH done = 0 \/ EL (LENGTH done-1) done < LENGTH h-1` assume_tac
  >- (Cases_on `LENGTH done = 0` >- metis_tac[] >>
      `LENGTH done-1 < LENGTH done` by decide_tac >>
      qpat_assum `ptr_event_embedding _ _ _` mp_tac >>
      pure_rewrite_tac[ptr_event_embedding_def] >>
      disch_then (mp_tac o cj 3) >>
      disch_then (qspecl_then [`LENGTH done-1`,`LENGTH done`] mp_tac) >>
      simp[EL_APPEND_EQN]) >>
  mp_tac (Q.INST [`i` |-> `LENGTH h-1`, `qi` |-> `LENGTH done`,
     `tsi` |-> `tokens`, `ri` |-> `registry`, `bi` |-> `births`,
     `PTi` |-> `PT`, `TGi` |-> `TG`, `si` |-> `saved`, `ei` |-> `entries`]
    (SPEC_ALL focus_cut_owned_writer_path)) >>
  (impl_tac >- (simp[EL_APPEND_EQN] >> metis_tac[])) >> strip_tac >>
  `SUC q < LENGTH ht` by decide_tac >>
  `read_byte x (EL (LENGTH h-1) h).po_state.vs_memory =
   read_byte x (EL (SUC w) h).po_state.vs_memory` by
    (irule ptr_chrono_history_actual_interval_byte_frame >> simp[] >>
     qexistsl [`endpoint`,`C`,`vs`] >> simp[]) >>
  `read_byte (pa + (x-b)) (EL (LENGTH ht-1) ht).po_state.vs_memory =
   read_byte (pa + (x-b)) (EL (SUC q) ht).po_state.vs_memory` by
    (irule ptr_chrono_history_actual_interval_byte_frame >> simp[] >>
     qexistsl [`at`,`C'`,`vs`] >> simp[]) >>
  `read_byte x (EL (SUC w) h).po_state.vs_memory =
   read_byte (pa + (x-b)) (EL (SUC q) ht).po_state.vs_memory` by
    (qpat_assum `ptr_ledger_write_pair _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ptr_ledger_write_pair_def, ptr_bytes_agree_def] >>
     strip_tac >>
     qpat_x_assum `!i. _ ==> read_byte i _ = _` (qspec_then `x` mp_tac) >> simp[]) >>
  metis_tac[]
QED

(* A provenance tag identifies a live activation; its slice gives the
   original allocation base and the relocation for the selected byte. *)
Theorem focus_layout_owned_read[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ EVERY all_reachable C.ctx_functions /\
  EVERY ssa_form C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  o1_ptr_safe_upto D lo n C vs /\ alloca_frontier_upto n C vs /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  max_live_eom C' = SOME eom /\ ptr_stage_placements C' positions /\
  (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  gas_cut n vs at.po_state /\ ~in_revert_forward a.po_fn a.po_state /\
  mem_read_ops a.po_inst = SOME ops /\
  eval_operand ops.iao_ofst a.po_state = SOME x /\
  eval_operand ops.iao_ofst at.po_state = SOME y /\
  MEM (w2n x,len) (source_memory_read_ranges a.po_inst a.po_state) /\
  ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {}
    (SOME x) (SOME y) /\
  (?v token aid b sz pa. ops.iao_ofst = Var v /\ FLOOKUP TG v = SOME (token,aid) /\
    FLOOKUP births (token,aid) = SOME (b,sz) /\
    FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
    b <= w2n x /\ w2n x+len <= b+sz /\ w2n y = pa + (w2n x-b)) ==>
  !j. j < len /\ w2n x+j NOTIN a.po_taint.t_mem ==>
    read_byte (w2n x+j) a.po_state.vs_memory =
    read_byte (w2n y+j) at.po_state.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?v token aid b sz pa. _` strip_assume_tac >>
  rpt gen_tac >> strip_tac >>
  `ptr_discipline_upto lo n C vs /\ fixed_region_reserved lo C /\
    EVERY (\f. f.fn_eom = NONE) C.ctx_functions` by fs[o1_ptr_safe_upto_def] >>
  drule_all ptr_paired_endpoint_cut_safety >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  drule ptr_structural_trace_depth >> strip_tac >>
  `a.po_inst.inst_opcode <> ASSIGN` by gvs[mem_read_ops_def, AllCaseEqs()] >>
  `ptr_observation_reachable vs C a` by simp[ptr_observation_reachable_def] >>
  `vs.vs_allocas = FEMPTY` by fs[o1_initial_state_ok_def] >>
  drule_all ptr_source_ownership_live_prov >> pure_rewrite_tac[MEM_EL] >>
  disch_then (qx_choose_then `k` strip_assume_tac) >>
  drule ptr_source_ownership_caches >> strip_tac >>
  drule ptr_source_birth_caches_slices >> strip_tac >>
  qabbrev_tac `d = LENGTH a.po_stack - k` >>
  `d <= LENGTH a.po_stack /\ LENGTH a.po_stack - d = k` by
    (simp[Abbr `d`] >> decide_tac) >>
  `EL (LENGTH a.po_stack - d) tokens = token` by simp[] >>
  `FLOOKUP (ptr_owner_view d a).cf_state.vs_allocas aid = SOME (b,sz)` by
    (qpat_assum `ptr_birth_slices _ _ _` mp_tac >>
     pure_rewrite_tac[ptr_birth_slices_def] >>
     disch_then (qspecl_then [`d`,`aid`] mp_tac) >> fs[]) >>
  `allocas_from lo (ptr_owner_view d a).cf_state` by
    (irule ptr_cut_owner_allocas_from >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `b + sz <= dyn_floor C vs` by
    (irule ptr_cut_owner_below_floor >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `lo <= b` by
    (qpat_assum `allocas_from lo (ptr_owner_view d a).cf_state`
      (mp_tac o REWRITE_RULE [allocas_from_def]) >> disch_then drule >> simp[]) >>
  `inst_read_op a.po_inst = SOME (Var v)` by simp[inst_read_op_def] >>
  `MEM (Var v) a.po_inst.inst_operands` by
    metis_tac[lowerDloadDescriptorObservationTheory.ld_descriptor_offset_operand] >>
  `b <= w2n x+j /\ w2n x+j < b+sz /\ lo <= w2n x+j /\ w2n x+j < dyn_floor C vs` by decide_tac >>
  `w2n y+j = pa + (w2n x+j-b)` by decide_tac >>
  qpat_assum `w2n y+j = _` SUBST1_TAC >>
  drule focus_layout_owned_recovery >> disch_then irule >> simp[] >>
  rpt conj_tac >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

(* LowerDload preserves the static portion of pointer safety. Its bounded
   simulation supplies the dynamic portion at the same shifted root. *)
Theorem focus_lower_dload_ptr_cut_inputs[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  dead_wf D /\ o1_ctx_shape C /\ o1_initial_state_ok V /\
  V.vs_fmp = V.vs_initial_fmp /\ code_layout_valid V /\
  callee_first names C.ctx_functions /\ o1_safe_upto D lo n C V /\
  C'.ctx_entry = SOME nm /\ lookup_function nm C'.ctx_functions = SOME fn2 /\
  fn_entry_label fn2 = SOME lbl ==>
  o1_ptr_safe_upto D lo n C' V /\ alloca_frontier_upto n C' V /\
  mem_inv (\ctx fn inst s. gas_cut n V s ==> dload_headroom_ok ctx fn inst s) C' V /\
  (!fn inst s. raw_reachable V C' fn inst s /\ gas_cut n V s ==>
    raw_mem_ok C' fn inst s /\ dload_offset_ok C' fn inst s) /\
  callee_first names C'.ctx_functions
Proof
  strip_tac >> drule_all lower_dload_stage_focus_safety >> strip_tac >>
  `o1_ptr_safe_upto D lo n C V` by fs[o1_safe_upto_def] >>
  `C'.ctx_global_reserved = C.ctx_global_reserved` by fs[ctx_pass_stage_def] >>
  `fmp_free_ctx C'` by metis_tac[o1_ptr_safe_upto_def, lower_dload_stage_fmp_free] >>
  `EVERY (\fn. fn.fn_eom = NONE) C'.ctx_functions` by
    (fs[EVERY_EL, o1_ptr_safe_upto_def, ctx_pass_stage_def, LIST_REL_EL_EQN] >>
     rpt strip_tac >> rename1 `j < LENGTH C'.ctx_functions` >>
     `j < LENGTH C.ctx_functions` by simp[] >>
     qpat_x_assum `!i. i < LENGTH C.ctx_functions ==> ?observed s out. _`
       (qspec_then `j` mp_tac) >>
     impl_tac >- simp[] >> strip_tac >>
     drule lower_dload_step_supply >> strip_tac >>
     drule lower_dload_function_supply_metadata >> rw[]) >>
  conj_tac
  >- (fs[o1_ptr_safe_upto_def, fixed_region_reserved_def]) >>
  simp[mem_inv_raw_reachable] >> metis_tac[lower_dload_stage_callee_first]
QED

Theorem focus_layout_cut_inputs:
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp /\
  code_layout_valid vs0 /\
  unit.cu_context.ctx_entry = SOME nm /\
  lookup_function nm unit.cu_context.ctx_functions = SOME entryfn /\
  fn_entry_label entryfn = SOME lbl /\
  w2n vs0.vs_initial_fmp <= w2n fmp /\ w2n fmp < 2 ** 254 /\
  unit_alloca_budget unit.cu_context +
    32 * ctx_dload_count unit.cu_context <= w2n fmp /\
  dead_wf D /\
  V = vs0 with <|vs_gas_readings := L; vs_fmp := fmp; vs_initial_fmp := fmp|> /\
  o1_safe_upto D lo n unit.cu_context V /\
  n <= LENGTH (gas_events_blocks f unit.cu_context entryfn
    (V with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) /\
  run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit
    (init_ir_supply unit) = SOME (pre,t) /\
  pre.cu_context.ctx_entry = SOME nm /\
  run_callee_first rpolicy o1_fn_passes
    (fcg_postorder (fcg_analyze pre.cu_context) nm)
    (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)) t =
    SOME (out.po_unit,t') /\
  stage 0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
  stage 9 = out.po_unit.cu_context /\
  (!k. k < 9 ==> ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
    (stage k) (stage (SUC k))) /\
  (!k. k <= 9 ==> o1_ctx_shape (stage k) /\
    EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  generate_context_plan out.po_unit.cu_context = SOME cpl /\
  codegen_asm_entry_rel cpl prog vs0 ast ==>
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) (o1_walk_view rpolicy 2)
    (stage 2) (stage 3) /\
  o1_ctx_shape (stage 2) /\ o1_initial_state_ok V /\
  V.vs_fmp = V.vs_initial_fmp /\ code_layout_valid V /\
  o1_ptr_safe_upto D lo n (stage 2) V /\ alloca_frontier_upto n (stage 2) V /\
  mem_inv (\ctx fn inst s. gas_cut n V s ==> dload_headroom_ok ctx fn inst s)
    (stage 2) V /\
  (!fn inst s. raw_reachable V (stage 2) fn inst s /\ gas_cut n V s ==>
    raw_mem_ok (stage 2) fn inst s /\ dload_offset_ok (stage 2) fn inst s) /\
  EVERY ssa_form (stage 2).ctx_functions /\ EVERY all_reachable (stage 2).ctx_functions /\
  EVERY fn_defs_reach_uses (stage 2).ctx_functions /\ ctx_inst_ids_distinct (stage 2) /\
  callee_first (fcg_postorder (fcg_analyze pre.cu_context) nm) (stage 2).ctx_functions /\
  max_live_eom (stage 3) = SOME cpl.cp_max_static_eom /\
  cpl.cp_max_static_eom <= w2n V.vs_initial_fmp
Proof
  strip_tac >>
  `o1_initial_state_ok V /\ V.vs_fmp = V.vs_initial_fmp /\ code_layout_valid V` by
    (qpat_assum `V = _` SUBST1_TAC >>
     conj_tac >- fs[o1_initial_state_ok_def] >> simp[] >>
     qpat_assum `code_layout_valid vs0` mp_tac >>
     pure_rewrite_tac [code_layout_valid_def] >> simp[]) >>
  `n <= LENGTH (gas_events_blocks f unit.cu_context entryfn
    (vs0 with <|vs_gas_readings := L; vs_fmp := fmp; vs_initial_fmp := fmp;
      vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>))` by
    (qpat_x_assum `n <= LENGTH (gas_events_blocks f _ _ _)` mp_tac >> simp[]) >>
  `o1_safe_upto D lo n unit.cu_context
      (vs0 with <|vs_gas_readings := L; vs_fmp := fmp; vs_initial_fmp := fmp|>)` by
    (qpat_assum `V = _` (SUBST1_TAC o SYM) >> simp[]) >>
  drule_all focus_source_c2_prefix >> strip_tac >>
  `ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) (o1_walk_view rpolicy 1)
     (stage 1) (stage 2) /\
   ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) (o1_walk_view rpolicy 2)
     (stage 2) (stage 3)` by
    (qpat_assum `!k. k < 9 ==> _` (fn th => mp_tac (Q.SPEC `1` th) >> mp_tac (Q.SPEC `2` th)) >>
     simp[NoAsms, o1_fn_passes_def, arithmeticTheory.ADD1]) >>
  `o1_ctx_shape (stage 1) /\ o1_ctx_shape (stage 2) /\
   EVERY make_ssa_input_ok (stage 2).ctx_functions` by
    (qpat_assum `!k. k <= 9 ==> _` (fn th => mp_tac (Q.SPEC `1` th) >> mp_tac (Q.SPEC `2` th)) >>
     simp[NoAsms, o1_fn_row_def, EVERY_MEM]) >>
  `o1_safe_upto D lo n (stage 1) V` by simp[] >>
  drule_all focus_lower_dload_ptr_cut_inputs >> strip_tac >>
  `max_live_eom (stage 9) = max_live_eom (stage 3)` by
    (qsuff_tac `!k. k < LENGTH o1_fn_passes ==>
       ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k) (stage k) (stage (SUC k))`
     >- (disch_then (mp_tac o MATCH_MP o1_walk_stages_max_live_eom) >>
          disch_then (qspec_then `6` mp_tac) >> simp[o1_fn_passes_def]) >>
     fs[o1_fn_passes_def]) >>
  `max_live_eom out.po_unit.cu_context = SOME cpl.cp_max_static_eom` by
    metis_tac[generate_context_plan_spill_gap] >>
  `n2w cpl.cp_initial_fmp = vs0.vs_initial_fmp` by fs[codegen_asm_entry_rel_def] >>
  `cpl.cp_max_static_eom <= w2n vs0.vs_initial_fmp` by
    metis_tac[generate_context_plan_eom_room] >>
  fs[EVERY_MEM, o1_ctx_shape_def, make_ssa_input_ok_def] >> metis_tac[]
QED

(* Entry and source-point facts for the bounded FMP frame induction. *)
Theorem focus_fmp_src_active[local]:
  wf_function fn /\ first_block_no_phi fn /\ fn_entry_label fn = SOME lbl ==>
  ?inst. active_inst fn inst
    (root with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
Proof
  Cases_on `fn.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def] >>
  strip_tac >> rename1 `fn.fn_blocks = bb::bbs` >>
  `bb.bb_instructions <> []` by metis_tac[wf_function_def, bb_well_formed_def, MEM] >>
  Cases_on `bb.bb_instructions` >>
  gvs[active_inst_def, get_instruction_def, lookup_block_def, FIND_thm] >>
  qexists `bb` >> simp[]
QED

Theorem focus_fmp_target_entry[local]:
  ctx_pass_stage rp (CFP_Simple VP_FmpLowering) (o1_walk_view rp 3) C3 C4 /\
  C3.ctx_entry = SOME name /\ lookup_function name C3.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\ wf_function fn /\ entry_fn_no_params fn /\
  first_block_no_phi fn /\ fn.fn_fmp_signature = NONE /\ pre_fmp_ops fn /\
  o1_initial_state_ok v /\ v.vs_fmp = v.vs_initial_fmp /\ code_layout_valid v /\
  w2n v.vs_initial_fmp <= w2n fmp ==>
  ?fn' bb p u inst s t.
    lookup_function name C4.ctx_functions = SOME fn' /\
    fn_entry_label fn' = SOME lbl /\ first_block_no_phi fn' /\
    lookup_block lbl fn'.fn_blocks = SOME bb /\
    s = (v with <|vs_fmp := fmp; vs_initial_fmp := fmp;
                  vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) /\
    t = (v with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) /\
    frame_reachable (v with <|vs_fmp := fmp; vs_initial_fmp := fmp|>)
      C3 [] [] FEMPTY entry_taint fn inst s /\ active_inst fn inst s /\ ~s.vs_halted /\
    fmp_stage_rel D C4 FEMPTY (w2n v.vs_initial_fmp) (w2n fmp) eom F
      [] [] FEMPTY entry_taint fn s (w2n v.vs_initial_fmp) u [] /\
    u.vs_current_bb = lbl /\ u.vs_inst_idx = p /\
    u.vs_gas_readings = v.vs_gas_readings /\
    (!k. fmp_target_run k C4 name t p u) /\
    (!i. i < p ==> i < LENGTH bb.bb_instructions /\
                   fmp_inserted_op (EL i bb.bb_instructions).inst_opcode)
Proof
  strip_tac >> drule_all focus_fmp_selected_root_pin >> strip_tac >>
  `?ctx1 sp sp'. fmp_lower_function ctx1 sp fn = SOME (fn',sp')` by
    (fs[fmp_stage_lowered_def] >>
     rename1 `fmp_lower_function_with_info info0 ctx0 supply fn = SOME (fn',supply')` >>
     qexistsl [`ctx0`, `supply`, `supply'`] >> simp[fmp_lower_function_def]) >>
  `first_block_no_phi fn'` by metis_tac[fmp_lower_function_first_block_no_phi] >>
  `?bb. lookup_block lbl fn'.fn_blocks = SOME bb` by
    metis_tac[fmp_entry_target_block] >>
  qabbrev_tac `root = v with <|vs_fmp := fmp; vs_initial_fmp := fmp|>` >>
  qabbrev_tac `s = root with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>` >>
  `enters_block fn s s` by
    (simp[Abbr `s`] >> metis_tac[dload_no_phi_entry]) >>
  `?inst. active_inst fn inst s` by
    (simp[Abbr `s`] >> metis_tac[focus_fmp_src_active]) >>
  `frame_reachable root C3 [] [] FEMPTY entry_taint fn inst s` by
    (irule frame_reachable_entry >> metis_tac[Abbr `s`]) >>
  mp_tac (Q.INST [`u` |-> `root`, `s` |-> `s`, `v` |-> `v`,
                   `rpolicy` |-> `rp`, `D` |-> `D`, `eom` |-> `eom`]
                 focus_fmp_cut_entry_static) >>
  impl_tac >- (simp[Abbr `root`] >> metis_tac[Abbr `s`]) >>
  disch_then (qx_choose_then `f4` (qx_choose_then `p` (qx_choose_then `u4` strip_assume_tac))) >>
  qexistsl [`f4`, `bb`, `p`, `u4`, `inst`, `s`,
            `v with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>`] >>
  gvs[Abbr `root`, Abbr `s`, o1_initial_state_ok_def, fmp_inserted_op_def,
      update_var_def, mk_inst_def]
QED

(* These quotations are the three recurrent formulas of the induction;
   they introduce no new predicates. *)
val focus_fmp_matched = ``
  ?stk PG G tn fn inst s sm lo u ts restored bb.
    frame_reachable root3 C3 stk PG G tn fn inst s /\
    active_inst fn inst s /\ ~s.vs_halted /\ gas_cut n root3 s /\
    (restored ==> MEM inst.inst_opcode [DALLOCA; INVOKE] \/
                  is_terminator inst.inst_opcode) /\
    fmp_stage_rel D C4 sm (w2n root4.vs_initial_fmp) (w2n (fmp:256 word)) eom restored
      stk PG G tn fn s lo u ts /\
    lookup_function fn.fn_name C4.ctx_functions = SOME fn' /\
    fmp_cov_stack C4 stk ts stk' /\
    LIST_REL (\f g. g.cf_inst.inst_outputs = f.cf_inst.inst_outputs) stk stk' /\
    t.vs_current_bb = u.vs_current_bb /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb /\
    t.vs_inst_idx <= u.vs_inst_idx /\
    s.vs_gas_readings = u.vs_gas_readings /\ u.vs_gas_readings = t.vs_gas_readings /\
    (!k. fmp_target_run k C4 fn.fn_name t (u.vs_inst_idx - t.vs_inst_idx) u) /\
    (!i. t.vs_inst_idx <= i /\ i < u.vs_inst_idx ==>
         i < LENGTH bb.bb_instructions /\
         fmp_inserted_op (EL i bb.bb_instructions).inst_opcode)``;

val focus_fmp_tail = ``
  ?bb p j. ALL_DISTINCT (fn_labels fn') /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb /\
    revert_forward_pair bb p j /\ p < t.vs_inst_idx /\ t.vs_inst_idx <= j``;

val focus_fmp_fields = ``
  !stk PG G tn fn inst s.
    frame_reachable root3 C3 stk PG G tn fn inst s /\ gas_cut n root3 s ==>
    access_ok eom G fn inst s /\ taint_ok fn tn inst s /\
    allocas_from eom s /\ (ctx_has_dalloca C3 ==> allocas_below_fmp s) /\
    (?P. fn_static_ptr_ok P fn /\ ptr_use_static_ok P (fn_pv P fn) inst /\
         FDOM G SUBSET fn_pv P fn)``;

Theorem focus_fmp_matched_entry[local]:
  ctx_pass_stage rp (CFP_Simple VP_FmpLowering) (o1_walk_view rp 3) C3 C4 /\
  C3.ctx_entry = SOME name /\ lookup_function name C3.ctx_functions = SOME src /\
  fn_entry_label src = SOME src_lbl /\ o1_ctx_shape C3 /\ fmp_free_ctx C3 /\
  o1_initial_state_ok root4 /\ root4.vs_fmp = root4.vs_initial_fmp /\
  code_layout_valid root4 /\ w2n root4.vs_initial_fmp <= w2n fmp /\
  root3 = root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|> /\
  C4.ctx_entry = SOME name' /\ lookup_function name' C4.ctx_functions = SOME fn' /\
  fn_entry_label fn' = SOME lbl /\
  enters_block fn' (root4 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) t /\
  gas_cut n root4 t ==>
  ^(subst [``stk':call_frame list`` |-> ``[]:call_frame list``] focus_fmp_matched)
Proof
  strip_tac >>
  `name' = name` by fs[ctx_pass_stage_def] >>
  `MEM src C3.ctx_functions /\ src.fn_name = name` by
    metis_tac[lookup_function_MEM, lookup_function_selected_name] >>
  `wf_function src /\ first_block_no_phi src /\ entry_fn_no_params src /\
   src.fn_fmp_signature = NONE /\ pre_fmp_ops src` by
    (fs[o1_ctx_shape_def, fmp_free_ctx_def, EVERY_MEM] >> metis_tac[o1_fn_shape_def]) >>
  drule_all focus_fmp_target_entry >>
  disch_then (qspecl_then [`eom`, `D`] strip_assume_tac) >> gvs[] >>
  qpat_x_assum `enters_block _ _ _` mp_tac >> simp[dload_no_phi_entry] >>
  disch_then SUBST_ALL_TAC >>
  qexistsl [`[]`, `FEMPTY`, `entry_taint`, `src`, `inst`,
    `root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp; vs_prev_bb := NONE;
                  vs_current_bb := u.vs_current_bb; vs_inst_idx := 0|>`,
    `FEMPTY`, `w2n root4.vs_initial_fmp`, `u`, `[]`, `F`] >>
  gvs[fmp_cov_stack_def, gas_cut_def]
QED

Theorem focus_fmp_source_points[local]:
  o1_ctx_shape C3 /\ EVERY (o1_fn_row 3) C3.ctx_functions /\
  fmp_free_ctx C3 /\ root3.vs_vars = FEMPTY /\ ~root3.vs_halted /\
  frame_reachable root3 C3 stk PG G tn fn inst s /\ active_inst fn inst s /\
  ^focus_fmp_fields /\ gas_cut n root3 s ==>
  lookup_function fn.fn_name C3.ctx_functions = SOME fn /\
  o1_fn_shape C3 fn /\ o1_fn_row 3 fn /\ fn_inst_wf fn /\ wf_function fn /\
  make_ssa_input_ok fn /\ pre_fmp_ops fn /\ fn.fn_fmp_signature = NONE /\
  (!v. inst.inst_opcode <> PHI /\ MEM (Var v) inst.inst_operands ==>
       IS_SOME (lookup_var v s)) /\
  access_ok eom G fn inst s /\ taint_ok fn tn inst s /\
  allocas_from eom s /\ (ctx_has_dalloca C3 ==> allocas_below_fmp s) /\
  (?P. fn_static_ptr_ok P fn /\ ptr_use_static_ok P (fn_pv P fn) inst /\
       FDOM G SUBSET fn_pv P fn)
Proof
  strip_tac >>
  `!nm f. lookup_function nm C3.ctx_functions = SOME f ==> wf_function f` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >>
     metis_tac[lookup_function_MEM]) >>
  drule_all scfg_frame_reachable_entry_root >> strip_tac >>
  `lookup_function fn.fn_name C3.ctx_functions = SOME fn` by
    (drule_all scfg_frame_reachable_rooted >>
     disch_then (strip_assume_tac o MATCH_MP scfg_rooted_elim) >>
     metis_tac[lookup_function_selected_name]) >>
  `MEM fn C3.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `o1_fn_shape C3 fn /\ o1_fn_row 3 fn /\ fn.fn_fmp_signature = NONE` by
    (fs[o1_ctx_shape_def, fmp_free_ctx_def, EVERY_MEM] >> metis_tac[]) >>
  `wf_function fn /\ fn_inst_wf fn /\ make_ssa_input_ok fn /\ pre_fmp_ops fn` by
    fs[o1_fn_shape_def, o1_fn_row_def] >>
  `!v. inst.inst_opcode <> PHI /\ MEM (Var v) inst.inst_operands ==>
       IS_SOME (lookup_var v s)` by
    (fs[make_ssa_input_ok_def] >> metis_tac[scfg_frame_operand_defined]) >>
  qpat_assum `!stk PG G tn fn inst s. frame_reachable _ _ _ _ _ _ _ _ _ /\ _ ==> _`
    drule_all >> simp[]
QED

Theorem focus_fmp_source_call_arity[local]:
  ctx_pass_stage rp (CFP_Simple VP_FmpLowering) (o1_walk_view rp 3) C3 C4 /\
  o1_ctx_shape C3 /\ fmp_free_ctx C3 ==>
  !stk PG G tn caller ivk st nm args callee.
    frame_reachable vs C3 stk PG G tn caller ivk st /\
    active_inst caller ivk st /\ ivk.inst_opcode = INVOKE /\
    ivk.inst_operands = Label nm::args /\
    lookup_function nm C3.ctx_functions = SOME callee ==>
    LENGTH (fn_user_param_insts callee) <= LENGTH args
Proof
  rpt strip_tac >>
  `MEM caller C3.ctx_functions` by metis_tac[frame_reachable_raw_certificate] >>
  `caller.fn_fmp_signature = NONE` by fs[fmp_free_ctx_def, EVERY_MEM] >>
  `lookup_function caller.fn_name C3.ctx_functions = SOME caller` by
    (irule fmpLowerPropsTheory.fmp_lookup_function_self >>
     fs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def]) >>
  `MEM ivk (fn_insts caller)` by metis_tac[active_inst_mem_fn_insts] >>
  `decode_invoke ivk = SOME (nm,args)` by simp[decode_invoke_def] >>
  drule_all fmp_stage_invoke_arity_static >> simp[]
QED

Theorem focus_fmp_aligned_layout[local]:
  wf_function fn /\ ALL_DISTINCT (fn_labels fn') /\
  active_inst fn inst s /\ active_inst fn' ti t /\
  fmp_stage_rel D C4 sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C4.ctx_functions = SOME fn' ==>
  ?infos ctx runner bs bt.
    fmp_stage_lowered infos ctx runner fn fn' /\
    t.vs_current_bb = s.vs_current_bb /\ w2n t.vs_initial_fmp = fmp0 /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bs /\
    s.vs_inst_idx < LENGTH bs.bb_instructions /\
    inst = EL s.vs_inst_idx bs.bb_instructions /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bt /\
    get_instruction bt t.vs_inst_idx = SOME ti /\
    t.vs_inst_idx = fmp_stage_tidx (fmp_stage_plan infos ctx fn)
      (fmp_stage_root infos ctx fn) s.vs_current_bb bs.bb_instructions s.vs_inst_idx +
      (if restored /\ (s.vs_current_bb,s.vs_inst_idx) IN FDOM (fmp_stage_plan infos ctx fn)
       then 1 else 0)
Proof
  strip_tac >> drule_all fmp_cov_frame_pos >> strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by fs[wf_function_def] >>
  `?bs. lookup_block s.vs_current_bb fn.fn_blocks = SOME bs /\
        get_instruction bs s.vs_inst_idx = SOME inst` by
    metis_tac[active_inst_block_lookup] >>
  `?bt. lookup_block t.vs_current_bb fn'.fn_blocks = SOME bt /\
        get_instruction bt t.vs_inst_idx = SOME ti` by
    metis_tac[active_inst_block_lookup] >>
  first_x_assum drule >> strip_tac >>
  qexistsl [`infos`, `ctx`, `runner`, `bs`, `bt`] >> fs[get_instruction_def]
QED

Theorem focus_opt_lower_inst_no_dload[local]:
  lower_dload_inst_supply s i = (xs,t) /\ inst_wf i ==>
  EVERY (\j. j.inst_opcode <> DLOAD /\ j.inst_opcode <> DLOADBYTES) xs
Proof
  strip_tac >> Cases_on `i.inst_opcode = DLOAD`
  >- (fs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
      gvs[lower_dload_inst_supply_def, AllCaseEqs()]) >>
  Cases_on `i.inst_opcode = DLOADBYTES`
  >- (fs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
      gvs[lower_dload_inst_supply_def, AllCaseEqs()]) >>
  gvs[lower_dload_inst_supply_def]
QED

(* Neither source DLOAD opcode survives expansion in a well-formed stage. *)
Theorem focus_opt_lower_no_dload[local]:
  ctx_pass_stage rp (CFP_Simple VP_LowerDload) view C C' /\
  o1_ctx_shape C /\ MEM g C'.ctx_functions /\ MEM j (fn_insts g) ==>
  j.inst_opcode <> DLOAD /\ j.inst_opcode <> DLOADBYTES
Proof
  strip_tac >>
  `?f s t. MEM f C.ctx_functions /\ lower_dload_function_supply s f = (g,t)` by
    (qpat_x_assum `MEM j (fn_insts g)` kall_tac >>
     fs[ctx_pass_stage_def, LIST_REL_EL_EQN] >>
     qpat_x_assum `MEM g C'.ctx_functions` mp_tac >> simp[MEM_EL] >>
     strip_tac >> first_x_assum (qspec_then `n` mp_tac) >>
     impl_tac >- fs[] >> strip_tac >>
     gvs[fn_pass_step_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all o1ContractLowerDloadTheory.lower_dload_function_supply_member >>
  strip_tac >>
  `inst_wf i` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, fn_inst_wf_def,
        fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  drule_all focus_opt_lower_inst_no_dload >> simp[EVERY_MEM] >>
  disch_then drule >> simp[]
QED

(* Induct on the observed C4 history, keeping the independent C3
   reachability and the gas-reading alignment in the motive. *)
Theorem focus_opt_fmp_cut_cover:
  ctx_pass_stage rp (CFP_Simple VP_FmpLowering) (o1_walk_view rp 3) C3 C4 /\
  o1_pre 3 C3 C4 /\ o1_ctx_shape C3 /\ o1_ctx_shape C4 /\
  EVERY (o1_fn_row 3) C3.ctx_functions /\ EVERY ssa_form C3.ctx_functions /\
  C3.ctx_entry = SOME name /\ lookup_function name C3.ctx_functions = SOME src /\
  fn_entry_label src = SOME src_lbl /\
  o1_initial_state_ok root4 /\ root4.vs_fmp = root4.vs_initial_fmp /\
  code_layout_valid root4 /\ w2n root4.vs_initial_fmp <= w2n fmp /\
  root3 = root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|> /\
  dead_wf D /\ fmp_free_ctx C3 /\ taint_within_upto D n C3 root3 /\
  (!g i v. raw_reachable root3 C3 g i v /\ gas_cut n root3 v ==> dalloca_no_wrap i v) /\
  ^focus_fmp_fields /\
  eom <= w2n root4.vs_initial_fmp /\ fmp_variant_room (SOME fmp) C4 root4 /\
  callee_first names C3.ctx_functions ==>
  !stk' PG' G' tn' fn' ti t.
    frame_reachable root4 C4 stk' PG' G' tn' fn' ti t /\ gas_cut n root4 t ==>
    ^focus_fmp_matched \/ ^focus_fmp_tail
Proof
  strip_tac >>
  `!vs ctx stk' PG' G' tn' fn' ti t.
     frame_reachable vs ctx stk' PG' G' tn' fn' ti t ==>
     vs = root4 /\ ctx = C4 /\ gas_cut n root4 t ==> ^focus_fmp_matched \/ ^focus_fmp_tail`
    suffices_by
      (disch_then (qspecl_then [`root4`, `C4`] mp_tac) >>
       rewrite_tac[] >> disch_then (fn th => rpt gen_tac >> strip_tac >>
         drule th >> simp[]) >> simp[]) >>
  ho_match_mp_tac frame_reachable_strongind >> rpt conj_tac >>
  rpt strip_tac >> gvs[]
  >- (disj1_tac >>
      irule (SRULE [] (Q.INST
        [`root3` |-> `root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>`]
        focus_fmp_matched_entry)) >> metis_tac[])
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume focus_opt_fmp_cut_cover[block]:
  `MEM ti.inst_opcode [JMP; JNZ; DJMP]` by
    metis_tac[fnBlockBodyHelpersTheory.step_ok_terminator_jump, MEM] >>
  `ti.inst_opcode <> INVOKE` by (fs[MEM] >> simp[]) >>
  `gas_cut n root4 t` by
    (irule gas_cut_readings_mono >> first_assum (irule_at Any) >>
     drule enters_block_readings >> strip_tac >> simp[] >>
     irule step_inst_noninvoke_readings_le >> metis_tac[]) >>
  qpat_x_assum `gas_cut n root4 t ==> _` drule >>
  reverse (disch_then (DISJ_CASES_THEN strip_assume_tac))
  >- (drule_all (Q.INST [`eom` |-> `eom`, `C4` |-> `C4`] focus_fmp_cut_tail_observation) >>
      strip_tac >> gvs[MEM]) >>
  `ALL_DISTINCT (fn_labels fn')` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, wf_function_def] >>
     metis_tac[lookup_function_MEM]) >>
  `get_instruction bb t.vs_inst_idx = SOME ti` by
    (qpat_assum `active_inst fn' ti t` (mp_then Any drule_all active_inst_block_lookup) >>
     strip_tac >> metis_tac[optionTheory.SOME_11]) >>
  `u = t` by
    (Cases_on `t.vs_inst_idx < u.vs_inst_idx`
     >- (qpat_assum `!i. _ <= i /\ _ ==> _` (qspec_then `t.vs_inst_idx` mp_tac) >>
         gvs[get_instruction_def, fmp_inserted_op_def, MEM]) >>
     `u.vs_inst_idx - t.vs_inst_idx = 0` by decide_tac >>
     metis_tac[fmp_target_run_zero]) >>
  qpat_x_assum `u = t` SUBST_ALL_TAC >>
  `(root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>).vs_vars = FEMPTY /\
   ~(root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>).vs_halted` by
    fs[o1_initial_state_ok_def] >>
  drule_all focus_fmp_source_points >> strip_tac >>
  `ssa_form fn` by metis_tac[lookup_function_MEM, EVERY_MEM] >>
  qabbrev_tac `root3 = root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>` >>
  `w2n root3.vs_fmp = w2n fmp` by simp[Abbr `root3`] >>
  `?m l. fmp_stage_rel D C4 m (w2n root4.vs_initial_fmp) (w2n fmp) eom T
           stk PG G tn fn s l t ts` by
    (`ti.inst_opcode <> ASSIGN` by (fs[MEM] >> simp[]) >>
     qpat_x_assum `MEM ti.inst_opcode _` kall_tac >>
     Cases_on `restored` >- metis_tac[] >> gvs[] >>
     drule_all (SRULE [] (Q.INST [`raw0` |-> `w2n vs.vs_fmp`] focus_fmp_cut_restore_prefix)) >>
     disch_then (qx_choosel_then
       [`rest_fn`, `rest_src`, `rest_bb`, `rest_infos`, `rest_ctx`,
        `rest_runner`, `rest_len`, `rest_post`, `rest_cut`] strip_assume_tac) >>
     Cases_on `FLOOKUP (fmp_stage_plan rest_infos rest_ctx fn) (s.vs_current_bb,s.vs_inst_idx)`
     >- (gvs[] >> metis_tac[]) >>
     gvs[get_instruction_def, mk_inst_def]) >>
  qpat_x_assum `fmp_stage_rel _ _ _ _ _ _ restored _ _ _ _ _ _ _ _ _` kall_tac >>
  drule_all focus_fmp_aligned_layout >> strip_tac >>
  `pre_fmp_opcode inst.inst_opcode` by
    (qpat_assum `pre_fmp_ops fn` (mp_tac o REWRITE_RULE [pre_fmp_ops_def, EVERY_MEM]) >>
     metis_tac[active_inst_mem_fn_insts]) >>
  `inst = ti` by
    (Cases_on `MEM inst.inst_opcode [DALLOCA; RETPC_PARAM]`
     >- (qabbrev_tac `plan = fmp_stage_plan infos ctx fn` >>
         qabbrev_tac `rt = fmp_stage_root infos ctx fn` >>
         qabbrev_tac `idx = s.vs_inst_idx` >>
         qabbrev_tac `lab = s.vs_current_bb` >>
         `fmp_stage_tidx plan rt lab bs.bb_instructions idx +
            (if (lab,idx) IN FDOM plan then 1 else 0) <
          fmp_stage_tidx plan rt lab bs.bb_instructions (SUC idx)` by
           (simp[fmp_stage_tidx_def, GENLIST, SUM_SNOC] >>
            Cases_on `rt` >> simp[]
            >- (IF_CASES_TAC >> simp[]) >>
            rename1 `SOME r = fmp_stage_root _ _ _` >> PairCases_on `r` >> simp[] >>
            rpt (IF_CASES_TAC >> simp[]) >> decide_tac) >>
         mp_tac (Q.INST [`P` |-> `fmp_inserted_op`, `infos` |-> `infos`,
                         `ctx` |-> `ctx`, `runner` |-> `runner`, `fn` |-> `fn`,
                         `fn'` |-> `fn'`, `lbl` |-> `lab`, `bb` |-> `bs`,
                         `idx` |-> `idx`, `i` |-> `t.vs_inst_idx`]
             fmpStageCoverMemAssembleTheory.fmp_cover_inserted_from_root_structural) >>
         (impl_tac >- (simp[fmp_inserted_op_def, Abbr `rt`, Abbr `plan`] >>
                       rw[] >> gvs[MEM])) >>
         strip_tac >> gvs[get_instruction_def, fmp_inserted_op_def, MEM]) >>
     Cases_on `inst.inst_opcode = INVOKE`
     >- (`(EL s.vs_inst_idx bs.bb_instructions).inst_opcode = INVOKE` by metis_tac[] >>
         drule_all (Q.INST [`infos` |-> `infos`, `ctx` |-> `ctx`,
                           `idx` |-> `s.vs_inst_idx`] fmp_stage_invoke_inst) >>
         strip_tac >> gvs[get_instruction_def]) >>
     `~MEM inst.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM]` by fs[MEM] >>
     drule_all (Q.INST [`infos` |-> `infos`, `ctx` |-> `ctx`,
                       `idx` |-> `s.vs_inst_idx`] fmp_stage_kept_inst) >>
     strip_tac >> gvs[get_instruction_def]) >>
  qpat_x_assum `inst = ti` SUBST_ALL_TAC >>
  `inst_wf ti /\ inst_shape_ok ti /\ opaque_use_ok fn /\ first_block_no_preds fn /\
   (C3.ctx_entry = SOME fn.fn_name ==> entry_fn_no_params fn)` by
    (`MEM ti (fn_insts fn)` by metis_tac[active_inst_mem_fn_insts] >>
     conj_tac >- metis_tac[fn_inst_wf_def, fn_insts_def,
                            unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
     fs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def, EVERY_MEM]) >>
  `s.vs_labels = t.vs_labels` by
    (qpat_assum `fmp_stage_rel _ _ m _ _ _ T _ _ _ _ _ _ _ t _` mp_tac >>
     simp[NoAsms, fmp_stage_rel_def, fmp_frame_rel_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `~MEM ti.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; PHI; PARAM] /\
   ti.inst_opcode <> PHI` by (fs[MEM] >> simp[]) >>
  `!v. MEM (Var v) ti.inst_operands ==> IS_SOME (lookup_var v s)` by simp[] >>
  `terminates (step_inst fuel C4 ti t)` by simp[passSimulationDefsTheory.terminates_def] >>
  `terminates (step_inst fuel C3 ti s)` by
    (drule_all fmp_stage_back_kept_nonparam_point >> simp[NoAsms]) >>
  `step_inst fuel C3 ti s = step_inst fuel C3 ti s` by simp[] >>
  drule_all focus_fmp_jump_point >>
  disch_then (CONJUNCTS_THEN2 (K ALL_TAC) (qx_choose_then `dst` strip_assume_tac)) >>
  `s' = jump_to dst t` by metis_tac[exec_result_11] >>
  qpat_x_assum `s' = jump_to dst t` SUBST_ALL_TAC >>
  `fn_labels fn' = fn_labels fn` by metis_tac[fmp_stage_lowered_shape] >>
  `MEM dst (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (`?b. lookup_block dst fn'.fn_blocks = SOME b` by fs[enters_block_def, jump_to_def] >>
     drule stackPlanGenTheory.lookup_block_mem_fn_labels >>
     fs[fn_labels_def]) >>
  drule_all focus_fmp_cut_source_jump_entry >>
  disch_then (qx_choosel_then [`s1`, `si1`] strip_assume_tac) >>
  drule_all focus_fmp_cut_jump_entry >>
  disch_then (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (qx_choose_then `t1` strip_assume_tac))) >>
  `t1 = t'` by (fs[enters_block_def] >> gvs[]) >>
  qpat_x_assum `t1 = t'` SUBST_ALL_TAC >>
  `frame_reachable root3 C3 stk PG (entry_prov fn (jump_to dst s) G)
      (entry_taint_vars fn (jump_to dst s) tn) fn si1 s1` by
    (irule (cj 3 frame_reachable_rules) >>
     goal_assum (drule_at Any) >>
     `~(jump_to dst s).vs_halted` by simp[jump_to_def] >>
     simp[] >> qexistsl [`fuel`, `ti`, `s`] >> simp[]) >>
  `s1.vs_gas_readings = s.vs_gas_readings /\ ~s1.vs_halted` by
    (qpat_assum `enters_block fn _ s1` (mp_then Any assume_tac enters_block_readings) >>
     qpat_assum `enters_block fn _ s1`
       (mp_then Any assume_tac o1LowerDloadRunnerBoundaryTheory.ld_enters_block_halted) >>
     fs[jump_to_def]) >>
  qpat_assum `active_inst fn' ti' t'` (mp_then Any drule_all active_inst_block_lookup) >>
  disch_then (qx_choose_then `bb1` strip_assume_tac) >>
  `s1.vs_gas_readings = t'.vs_gas_readings` by
    (qpat_assum `enters_block fn' _ t'` (mp_then Any assume_tac enters_block_readings) >>
     fs[jump_to_def]) >>
  disj1_tac >>
  qexistsl [`stk`, `PG`, `entry_prov fn (jump_to dst s) G`,
    `entry_taint_vars fn (jump_to dst s) tn`, `fn`, `si1`, `s1`, `m`, `l`, `t'`, `ts`, `F`, `bb1`] >>
  simp[] >> conj_tac
  >- (irule gas_cut_readings_mono >>
      qpat_assum `gas_cut n root3 s` (irule_at Any) >>
      gvs[]) >>
  fs[fmp_target_run_def, run_insts_def, get_instruction_def] >> gvs[]
QED

Resume focus_opt_fmp_cut_cover[next]:
  `gas_cut n root4 t` by
    (irule gas_cut_readings_mono >> qexists `s'` >>
     conj_tac >- metis_tac[step_inst_noninvoke_readings_le] >>
     fs[gas_cut_def]) >>
  qpat_x_assum `gas_cut n root4 t ==> _` drule >>
  reverse (disch_then strip_assume_tac)
  >- (disj2_tac >> drule_all focus_fmp_cut_tail_observation >>
      disch_then (qspecl_then [`eom`, `C4`] strip_assume_tac) >>
      first_x_assum drule_all >> simp[] >> strip_tac >>
      qexistsl [`p`, `j`] >> simp[] >> decide_tac) >>
  `ALL_DISTINCT (fn_labels fn')` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, wf_function_def] >>
     metis_tac[lookup_function_MEM]) >>
  Cases_on `t.vs_inst_idx < u.vs_inst_idx`
  >- (disj1_tac >> drule_all focus_fmp_cut_inserted_residual >> strip_tac >>
      first_x_assum drule >> simp[] >> strip_tac >>
      qexistsl [`stk`, `PG`, `G`, `tn`, `fn`, `inst`, `s`, `sm`, `lo`, `u`, `ts`,
                `restored`, `bb`] >> gvs[] >>
      rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `u = t` by
    (`u.vs_inst_idx - t.vs_inst_idx = 0` by decide_tac >>
     metis_tac[fmp_target_run_zero]) >>
  qpat_x_assum `u = t` SUBST_ALL_TAC >>
  `(root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>).vs_vars = FEMPTY /\
   ~(root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>).vs_halted` by
    fs[o1_initial_state_ok_def] >>
  drule_all focus_fmp_source_points >> strip_tac >>
  drule_all focus_fmp_aligned_layout >> strip_tac >>
  `opaque_use_ok fn /\ all_reachable fn` by
    fs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def, make_ssa_input_ok_def] >>
  `ssa_form fn` by metis_tac[lookup_function_MEM, EVERY_MEM] >>
  qabbrev_tac `root3 = root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>` >>
  `w2n root3.vs_fmp = w2n fmp` by simp[Abbr `root3`] >>
  `inst.inst_opcode = DALLOCA ==> ?post. step_inst fuel C3 inst s = OK post` by
    (strip_tac >>
     `MEM inst (fn_insts fn)` by metis_tac[active_inst_mem_fn_insts] >>
     `MEM bs fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
     `MEM inst bs.bb_instructions` by
       (simp[MEM_EL] >> qexists `s.vs_inst_idx` >> simp[]) >>
     `inst_wf inst` by
       (qpat_assum `fn_inst_wf fn` (mp_tac o REWRITE_RULE [fn_inst_wf_def]) >>
        disch_then (qspecl_then [`bs`, `inst`] mp_tac) >> simp[]) >>
     `inst_shape_ok inst` by
       fs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def, EVERY_MEM] >>
     qpat_x_assum `inst_wf inst` mp_tac >>
     simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> strip_tac >>
     rename1 `_.inst_operands = [szop]` >>
     `?sz. eval_operand szop s = SOME sz` by
       (Cases_on `szop` >> gvs[eval_operand_def, unitShapeDefsTheory.inst_shape_ok_def,
          unitShapeDefsTheory.label_positions_ok_def, stackPlanTypesTheory.is_label_operand_def] >>
        metis_tac[optionTheory.IS_SOME_EXISTS]) >>
     metis_tac[lowerDloadPtrDallocaTheory.dalloca_step_success]) >>
  Cases_on `inst.inst_opcode = DALLOCA /\
    ?m l. fmp_stage_rel D C4 m (w2n root4.vs_initial_fmp) (w2n fmp) eom T stk PG G tn fn s l t ts`
  >- (qpat_x_assum `inst.inst_opcode = DALLOCA /\ _` strip_assume_tac >>
      rename1 `fmp_stage_rel D C4 m _ _ eom T stk PG G tn fn s l t ts` >>
      qpat_x_assum `inst.inst_opcode = DALLOCA ==> _` drule >>
      disch_then (qx_choose_then `post` assume_tac) >>
      `terminates (OK post)` by simp[passSimulationDefsTheory.terminates_def] >>
      `w2n fmp = w2n root3.vs_fmp` by simp[NoAsms, Abbr `root3`] >>
      qpat_assum `fmp_stage_rel D C4 m _ _ eom T stk PG G tn fn s l t ts`
        (mp_then Any drule_all focus_fmp_cut_dalloca_segment) >>
      disch_then (qx_choosel_then [`s1`, `t1`, `m1`, `sz`, `seg_fn`, `seg_bb`, `code`, `tail`,
        `op`, `out`, `runner'`, `plus31`, `mask`, `aligned`, `ai`, `ni`, `mi`, `bi`]
        (strip_assume_tac o SRULE [LET_THM])) >>
      `s1 = post /\ seg_fn = fn' /\ seg_bb = bb` by metis_tac[optionTheory.SOME_11] >>
      qpat_x_assum `s1 = post` SUBST_ALL_TAC >>
      qpat_x_assum `seg_bb = bb` SUBST_ALL_TAC >>
      `t1.vs_inst_idx = t.vs_inst_idx + 4` by
        (qpat_assum `!k. fmp_target_run k C4 _ t 4 t1`
           (qspec_then `fuel` mp_tac) >> simp[NoAsms, fmp_target_run_def] >>
         strip_tac >> simp[]) >>
      `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\ ~is_terminator inst.inst_opcode` by
        simp[is_terminator_def] >>
      `post.vs_current_bb = s.vs_current_bb /\
       post.vs_gas_readings = s.vs_gas_readings /\ ~post.vs_halted` by
        (`step_inst_base inst s = OK post` by
           (qpat_assum `step_inst fuel C3 inst s = OK post` mp_tac >>
            qpat_assum `inst.inst_opcode <> INVOKE`
              (fn th => simp[NoAsms, step_inst_non_invoke, th])) >>
         drule venomExecPropsTheory.step_inst_OK_preserves_halted >>
         drule_all venomInstPropsTheory.step_preserves_control_flow >>
         drule_all oracleExecPropsTheory.step_inst_noninvoke_gas_readings >> simp[]) >>
      `t1.vs_current_bb = t.vs_current_bb /\ post.vs_gas_readings = t1.vs_gas_readings` by
        (qpat_assum `fmp_stage_rel _ _ m1 _ _ _ F _ _ _ _ _ _ _ t1 _` mp_tac >>
         simp[NoAsms, fmp_stage_rel_def, fmp_frame_rel_def,
              o1LowerDloadSharedTheory.ld_shared_agree_def] >>
         strip_tac >> metis_tac[]) >>
      `!i. t.vs_inst_idx <= i /\ i < t1.vs_inst_idx ==>
           i < LENGTH bb.bb_instructions /\
           fmp_inserted_op (EL i bb.bb_instructions).inst_opcode` by
        (qx_gen_tac `i` >> strip_tac >>
         `i - t.vs_inst_idx < 4 /\ i - t.vs_inst_idx + t.vs_inst_idx = i` by decide_tac >>
         `DROP t.vs_inst_idx bb.bb_instructions =
            mk_inst ai ADD [op; Lit 31w] [plus31]::mk_inst ni NOT [Lit 31w] [mask]::
            mk_inst mi AND [Var plus31; Var mask] [aligned]::
            mk_inst bi BUMP [Var runner'; Var aligned] [out; runner']::tail` by simp[] >>
         `i < LENGTH bb.bb_instructions` by
           (pop_assum (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
            simp[NoAsms, LENGTH_DROP] >> decide_tac) >>
         `EL i bb.bb_instructions = EL (i - t.vs_inst_idx) (DROP t.vs_inst_idx bb.bb_instructions)` by
           (qpat_assum `i - t.vs_inst_idx + t.vs_inst_idx = i` (fn idx =>
              qpat_assum `i < LENGTH bb.bb_instructions` (fn bound =>
                simp[NoAsms, EL_DROP, idx, bound]))) >>
         qpat_x_assum `EL i bb.bb_instructions = _` SUBST1_TAC >>
         `i - t.vs_inst_idx = 0 \/ i - t.vs_inst_idx = 1 \/
          i - t.vs_inst_idx = 2 \/ i - t.vs_inst_idx = 3` by decide_tac >>
         simp[fmp_inserted_op_def, mk_inst_def]) >>
      `t1.vs_inst_idx - t.vs_inst_idx = 4 /\ t.vs_inst_idx < t1.vs_inst_idx` by decide_tac >>
      `t.vs_current_bb = t1.vs_current_bb /\
       (!k. fmp_target_run k C4 fn.fn_name t (t1.vs_inst_idx - t.vs_inst_idx) t1)` by
        (conj_tac >- metis_tac[] >>
         qpat_assum `t1.vs_inst_idx - t.vs_inst_idx = 4` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
      drule_all (Q.INST [`u` |-> `t1`] focus_fmp_cut_inserted_residual) >>
      strip_tac >> first_x_assum drule >>
      disch_then (strip_assume_tac o SRULE [LET_THM]) >>
      drule_all o1LowerDloadReadinessTheory.ld_nonterminator_successor >>
      disch_then (qx_choose_then `next` assume_tac) >>
      `gas_cut n root3 (post with vs_inst_idx := SUC s.vs_inst_idx)` by
        (qpat_assum `gas_cut n root3 s` mp_tac >>
         qpat_assum `post.vs_gas_readings = s.vs_gas_readings`
           (fn th => simp[NoAsms, gas_cut_def, th])) >>
      `lookup_block s'.vs_current_bb fn'.fn_blocks = SOME bb /\
       t1.vs_gas_readings = s'.vs_gas_readings` by metis_tac[] >>
      disj1_tac >>
      qexistsl [`stk`, `PG`, `step_prov PG G inst post`, `step_taint inst s post tn`,
        `fn`, `next`, `post with vs_inst_idx := SUC s.vs_inst_idx`, `m1`,
        `l + venomLayout$ceil32 (w2n sz)`, `t1`, `ts`, `F`, `bb`] >>
      conj_tac >- (irule frame_reachable_next >> metis_tac[]) >>
      rpt conj_tac >> simp[NoAsms] >> first_assum ACCEPT_TAC) >>
  reverse (Cases_on `restored`)
  >- (gvs[] >>
      drule_all (SRULE [] (Q.INST [`raw0` |-> `w2n vs.vs_fmp`]
                             focus_fmp_cut_restore_prefix)) >>
      disch_then (qx_choosel_then
        [`rest_fn`, `rest_src`, `rest_bb`, `rest_infos`, `rest_ctx`,
         `rest_runner`, `rest_len`, `rest_post`, `rest_cut`] strip_assume_tac) >>
      (* Dispatch on the layout returned by this run certificate. *)
      reverse (Cases_on `FLOOKUP (fmp_stage_plan rest_infos rest_ctx fn)
                                    (s.vs_current_bb,s.vs_inst_idx)`) >>
      PRED_ASSUM (can optionSyntax.dest_option_case) mp_tac >> simp[] >> strip_tac
      >- (`rest_src = bs /\ rest_fn = fn' /\ rest_bb = bb` by
            metis_tac[optionTheory.SOME_11] >>
          `(s.vs_current_bb,s.vs_inst_idx) IN FDOM
             (fmp_stage_plan rest_infos rest_ctx fn)` by fs[FLOOKUP_DEF] >>
          `fmp_is_reclaim_point rest_infos (EL s.vs_inst_idx bs.bb_instructions)` by
            metis_tac[fmp_stage_plan_point] >>
          (SUBGOAL_THEN
             ``MEM (EL s.vs_inst_idx bs.bb_instructions).inst_opcode [DALLOCA; INVOKE] \/
               is_terminator (EL s.vs_inst_idx bs.bb_instructions).inst_opcode`` assume_tac >-
           (drule fmp_reclaim_point_opcodes >> simp[] >> strip_tac >> simp[is_terminator_def])) >>
          `rest_post = s' with vs_inst_idx := SUC t.vs_inst_idx` by
            (qpat_assum `!k. fmp_target_run k _ _ t _ rest_post`
              (qspec_then `fuel` mp_tac) >>
             gvs[fmp_target_run_def, TAKE1_DROP, run_insts_def, get_instruction_def,
                 arithmeticTheory.ADD1]) >>
          `s'.vs_current_bb = t.vs_current_bb /\ s'.vs_gas_readings = t.vs_gas_readings` by
            (qpat_assum `rest_post = update_var _ _ _ with vs_inst_idx := _`
               (mp_tac o AP_TERM ``\v:venom_state. (v.vs_current_bb,v.vs_gas_readings)``) >>
             qpat_assum `rest_post = s' with vs_inst_idx := _`
               (mp_tac o AP_TERM ``\v:venom_state. (v.vs_current_bb,v.vs_gas_readings)``) >>
             simp[NoAsms, update_var_def]) >>
          `!k. fmp_target_run k C4 fn.fn_name rest_post 0 rest_post` by
            (irule fmp_restore_target_run_zero >> metis_tac[]) >>
          disj1_tac >>
          qpat_assum `t.vs_inst_idx = fmp_stage_tidx _ _ _ _ _`
            (fn th => once_rewrite_tac [GSYM th]) >>
          qexistsl [`stk`, `PG`, `G`, `tn`, `fn`, `EL s.vs_inst_idx bs.bb_instructions`,
            `s`, `DRESTRICT sm {key | key IN FDOM sm /\ FST (sm ' key) < rest_cut}`,
            `rest_cut`, `rest_post`, `ts`, `T`, `bb`] >>
          gvs[arithmeticTheory.ADD1]) >>
      `rest_src = bs /\ rest_fn = fn' /\ rest_bb = bb` by
        metis_tac[optionTheory.SOME_11] >>
      `~((s.vs_current_bb,s.vs_inst_idx) IN FDOM
            (fmp_stage_plan rest_infos rest_ctx fn))` by fs[FLOOKUP_DEF] >>
      `((EL s.vs_inst_idx bs.bb_instructions).inst_opcode <> INVOKE /\
        ~is_terminator (EL s.vs_inst_idx bs.bb_instructions).inst_opcode)` by
        (conj_tac
         >- (strip_tac >>
             drule_all (Q.INST [`infos` |-> `rest_infos`, `ctx` |-> `rest_ctx`,
                               `idx` |-> `s.vs_inst_idx`] fmp_stage_invoke_inst) >>
             gvs[get_instruction_def]) >>
         strip_tac >>
         `pre_fmp_opcode (EL s.vs_inst_idx bs.bb_instructions).inst_opcode` by
           (drule active_inst_mem_fn_insts >> disch_tac >>
            qpat_assum `pre_fmp_ops fn` (mp_tac o REWRITE_RULE [pre_fmp_ops_def, EVERY_MEM]) >>
            simp[]) >>
         `~MEM (EL s.vs_inst_idx bs.bb_instructions).inst_opcode
                [DALLOCA; INVOKE; RETPC_PARAM]` by
           (simp[] >> rpt conj_tac >> strip_tac >> fs[is_terminator_def]) >>
         `?bt. lookup_block s.vs_current_bb fn'.fn_blocks = SOME bt /\
                get_instruction bt t.vs_inst_idx = SOME (EL s.vs_inst_idx bs.bb_instructions)` by
           (mp_tac (Q.INST
              [`infos` |-> `rest_infos`, `ctx` |-> `rest_ctx`, `runner` |-> `rest_runner`,
               `lbl` |-> `s.vs_current_bb`, `idx` |-> `s.vs_inst_idx`, `bb` |-> `bs`,
               `inst` |-> `EL s.vs_inst_idx bs.bb_instructions`] fmp_stage_kept_inst) >>
            simp[get_instruction_def] >> metis_tac[]) >>
         `ti = EL s.vs_inst_idx bs.bb_instructions` by
           metis_tac[optionTheory.SOME_11] >> fs[]) >>
      Cases_on `(EL s.vs_inst_idx bs.bb_instructions).inst_opcode = DALLOCA`
      >- (qpat_x_assum `rest_post = t` SUBST_ALL_TAC >>
          qpat_x_assum `rest_cut = lo` SUBST_ALL_TAC >>
          gvs[]) >>
      rename1 `active_inst fn (EL s.vs_inst_idx bs.bb_instructions) s` >>
      qabbrev_tac `si = EL s.vs_inst_idx bs.bb_instructions` >>
      reverse (Cases_on `si.inst_opcode = RETPC_PARAM`)
      >- (`pre_fmp_opcode si.inst_opcode` by
            (drule active_inst_mem_fn_insts >> disch_tac >>
             qpat_assum `pre_fmp_ops fn`
               (mp_tac o REWRITE_RULE [pre_fmp_ops_def, EVERY_MEM]) >> simp[]) >>
          `~MEM si.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM]` by simp[] >>
          `si = EL s.vs_inst_idx bs.bb_instructions` by simp[Abbr `si`] >>
          drule_all (Q.INST [`infos` |-> `rest_infos`, `ctx` |-> `rest_ctx`,
                             `idx` |-> `s.vs_inst_idx`] fmp_stage_kept_inst) >>
          disch_then (qx_choose_then `kept_bb` strip_assume_tac) >>
          `kept_bb = bb` by metis_tac[optionTheory.SOME_11] >>
          qpat_x_assum `kept_bb = bb` SUBST_ALL_TAC >>
          `get_instruction bb t.vs_inst_idx = SOME si` by
            ((qpat_assum `~(_ IN FDOM (fmp_stage_plan rest_infos rest_ctx fn))` (fn absent =>
             qpat_assum `t.vs_inst_idx = fmp_stage_tidx (fmp_stage_plan rest_infos rest_ctx fn) _ _ _ _`
              (fn idx =>
               qpat_x_assum `_ < LENGTH bb.bb_instructions` (mp_tac o SRULE [NoAsms, absent, GSYM idx]) >>
               qpat_x_assum `EL _ bb.bb_instructions = si` (mp_tac o SRULE [NoAsms, absent, GSYM idx]) >>
               simp[NoAsms, get_instruction_def]))) >> (metis_tac[NoAsms, get_instruction_def])) >>
          `ti = si` by metis_tac[optionTheory.SOME_11] >>
          qpat_x_assum `ti = si` SUBST_ALL_TAC >>
          `s'.vs_current_bb = t.vs_current_bb` by
            metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
          Cases_on `in_revert_forward fn s`
          >- (`?j. revert_forward_pair bs s.vs_inst_idx j` by
                (`get_instruction bs s.vs_inst_idx = SOME si` by
                   simp[get_instruction_def, Abbr `si`] >>
                 qpat_assum `in_revert_forward fn s` (mp_tac o REWRITE_RULE [in_revert_forward_def]) >>
                 disch_then (qx_choose_then `fwd_bb` strip_assume_tac) >>
                 `fwd_bb = bs` by metis_tac[optionTheory.SOME_11] >>
                 qpat_x_assum `fwd_bb = bs` SUBST_ALL_TAC >>
                 qpat_x_assum `revert_forward_at bs _`
                   (qx_choose_then `j` strip_assume_tac o REWRITE_RULE [revert_forward_at_def])
                 >- (qexists `j` >> first_assum ACCEPT_TAC) >>
                 qpat_x_assum `revert_forward_pair bs j _` mp_tac >>
                 simp[NoAsms, revert_forward_pair_def] >> strip_tac >>
                 `inst2 = si` by metis_tac[optionTheory.SOME_11] >> fs[is_terminator_def]) >>
              drule_all (SRULE [LET_THM] (Q.INST [`infos` |-> `infos`, `ctx` |-> `ctx`,
                                `p` |-> `s.vs_inst_idx`] focus_fmp_cut_forward_layout)) >>
              disch_then (qx_choose_then `target_fwd` strip_assume_tac) >>
              `s.vs_inst_idx < j` by metis_tac[revert_forward_pair_def] >>
              `lookup_block s'.vs_current_bb fn'.fn_blocks = SOME target_fwd` by metis_tac[] >>
              `revert_forward_pair target_fwd t.vs_inst_idx (t.vs_inst_idx + (j - s.vs_inst_idx))` by
                metis_tac[] >>
              disj2_tac >>
              qpat_assum `t.vs_inst_idx = fmp_stage_tidx (fmp_stage_plan infos ctx fn) _ _ _ _`
                (SUBST1_TAC o SYM) >>
              qexistsl [`target_fwd`, `t.vs_inst_idx`, `t.vs_inst_idx + (j - s.vs_inst_idx)`] >>
              conj_tac >- first_assum ACCEPT_TAC >>
              conj_tac >- first_assum ACCEPT_TAC >> decide_tac) >>
          `si.inst_opcode <> PHI` by
            (strip_tac >>
             qpat_assum `si.inst_opcode = PHI` (fn opc =>
               qpat_assum `step_inst fuel C4 si t = OK s'`
                 (mp_tac o SRULE [NoAsms, opc, step_inst_non_invoke,
                                  step_inst_base_opcode_eqs])) >> simp[]) >>
          `MEM si (fn_insts fn)` by metis_tac[active_inst_mem_fn_insts] >>
          `inst_wf si /\ inst_shape_ok si` by
            (conj_tac >- metis_tac[fn_inst_wf_def, fn_insts_def,
                                   unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
             qpat_assum `o1_fn_shape C3 fn`
               (mp_tac o REWRITE_RULE [o1_fn_shape_def,
                                       unitShapeDefsTheory.fn_shape_ok_def, EVERY_MEM]) >>
             strip_tac >>
             qpat_assum `!i. MEM i (fn_insts fn) ==> inst_shape_ok i` irule >>
             first_assum ACCEPT_TAC) >>
          `s.vs_labels = t.vs_labels` by
            (qpat_assum `fmp_stage_rel _ _ sm _ _ _ F _ _ _ _ _ _ _ t _` mp_tac >>
             simp[NoAsms, fmp_stage_rel_def, fmp_frame_rel_def] >>
             strip_tac >> first_assum ACCEPT_TAC) >>
          `terminates (step_inst fuel C4 si t)` by simp[passSimulationDefsTheory.terminates_def] >>
          `terminates (step_inst fuel C3 si s)` by
            (Cases_on `si.inst_opcode = PARAM`
             >- (mp_tac (Q.INST [`vs` |-> `root3`] focus_fmp_source_call_arity) >>
                 (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
                 disch_then assume_tac >>
                 drule_all fmp_stage_back_param_point >> simp[NoAsms]) >>
             `~MEM si.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; PHI; PARAM]` by simp[] >>
             `!v. MEM (Var v) si.inst_operands ==> IS_SOME (lookup_var v s)` by
               (rpt strip_tac >> qpat_assum `!v. _ /\ _ ==> IS_SOME (lookup_var v s)` irule >>
                conj_tac >> first_assum ACCEPT_TAC) >>
             drule_all fmp_stage_back_kept_nonparam_point >> simp[NoAsms]) >>
          drule_all (SRULE [] (Q.INST [`raw0` |-> `w2n vs.vs_fmp`] focus_fmp_frame_sites_upto)) >>
          strip_tac >>
          `~MEM si.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; PHI]` by simp[] >>
          `step_inst fuel C3 si s = step_inst fuel C3 si s` by simp[] >>
          drule_all (SRULE [] (Q.INST [`raw0` |-> `w2n vs.vs_fmp`] focus_fmp_cut_ordinary_segment)) >>
          disch_then (qx_choose_then `target_fn` (qx_choose_then `source_bb`
            (qx_choose_then `target_bb` (qx_choose_then `tail`
              (qx_choose_then `r` strip_assume_tac))))) >>
          `r = OK s'` by
            (qpat_assum `!k. step_inst k C4 si t = r` (qspec_then `fuel` mp_tac) >>
             simp[]) >>
          qpat_x_assum `r = OK s'` SUBST_ALL_TAC >>
          qpat_x_assum `(case step_inst fuel C3 si s of OK _ => _ | Halt _ => _ |
                         Abort _ _ => _ | IntRet _ _ => _ | Error _ => _)` mp_tac >>
          Cases_on `step_inst fuel C3 si s` >>
          simp[NoAsms, dead_result_rel_def] >>
          disch_then strip_assume_tac >>
          rename1 `step_inst fuel C3 si s = OK post` >>
          `post.vs_current_bb = s.vs_current_bb /\ ~post.vs_halted` by
            (drule_all venomInstPropsTheory.step_preserves_control_flow >> strip_tac >>
             `step_inst_base si s = OK post` by
               (qpat_assum `si.inst_opcode <> INVOKE` (fn opc =>
                qpat_assum `step_inst fuel C3 si s = OK post` mp_tac >>
                simp[NoAsms, step_inst_non_invoke, opc])) >>
             drule venomExecPropsTheory.step_inst_OK_preserves_halted >> simp[]) >>
          drule_all o1LowerDloadReadinessTheory.ld_nonterminator_successor >>
          disch_then (qx_choose_then `next` assume_tac) >>
          `post.vs_gas_readings = s'.vs_gas_readings` by
            (qpat_assum `fmp_stage_rel _ _ sm _ _ _ F _ _ _ _ _
                         (post with vs_inst_idx := _) lo (s' with vs_inst_idx := _) ts` mp_tac >>
             simp[NoAsms, fmp_stage_rel_def, o1LowerDloadSharedTheory.ld_shared_agree_def]) >>
          `root3.vs_gas_readings = root4.vs_gas_readings` by simp[NoAsms, Abbr `root3`] >>
          `gas_cut n root3 (post with vs_inst_idx := SUC s.vs_inst_idx)` by
            (qpat_assum `gas_cut n root4 (s' with vs_inst_idx := _)` mp_tac >>
             qpat_assum `post.vs_gas_readings = _` (fn readings =>
             qpat_assum `root3.vs_gas_readings = _` (fn roots =>
               simp[NoAsms, gas_cut_def, readings, roots]))) >>
          `lookup_block s'.vs_current_bb fn'.fn_blocks = SOME bb` by metis_tac[] >>
          `!k. fmp_target_run k C4 fn.fn_name
                     (s' with vs_inst_idx := SUC t.vs_inst_idx) 0
                     (s' with vs_inst_idx := SUC t.vs_inst_idx)` by
            (`SUC t.vs_inst_idx < LENGTH bb.bb_instructions` by
               (qpat_assum `active_inst fn' ti' (s' with vs_inst_idx := _)` mp_tac >>
                qpat_assum `t.vs_inst_idx = fmp_stage_tidx (fmp_stage_plan infos ctx fn) _ _ _ _`
                  (fn idx => once_rewrite_tac [GSYM idx]) >>
                disch_tac >> drule_all active_inst_block_lookup >> strip_tac >>
                `bb' = bb` by
                  (qpat_assum `lookup_block (s' with vs_inst_idx := _).vs_current_bb fn'.fn_blocks = SOME bb'` mp_tac >>
                   qpat_assum `lookup_block s'.vs_current_bb fn'.fn_blocks = SOME bb`
                     (fn fetch => simp[NoAsms, fetch])) >>
                qpat_assum `get_instruction bb' _ = SOME ti'` mp_tac >>
                qpat_assum `bb' = bb` (fn eq => simp[NoAsms, eq, get_instruction_def]) >>
                rw[]) >>
             irule fmp_restore_target_run_zero >>
             simp[NoAsms] >> qexistsl [`bb`, `fn'`] >>
             conj_tac
             >- (qpat_assum `SUC t.vs_inst_idx < LENGTH bb.bb_instructions` mp_tac >> decide_tac) >>
             conj_tac >> first_assum ACCEPT_TAC) >>
          disj1_tac >>
          qpat_assum `t.vs_inst_idx = fmp_stage_tidx (fmp_stage_plan infos ctx fn) _ _ _ _`
            (SUBST1_TAC o SYM) >>
          qexistsl [`stk`, `PG`, `step_prov PG G si post`, `step_taint si s post tn`, `fn`,
                    `next`, `post with vs_inst_idx := SUC s.vs_inst_idx`, `sm`, `lo`,
                    `s' with vs_inst_idx := SUC t.vs_inst_idx`, `ts`, `F`, `bb`] >>
          conj_tac >- (irule frame_reachable_next >> metis_tac[]) >>
          rpt conj_tac >> simp[NoAsms] >> first_assum ACCEPT_TAC) >>
      `!k. ?post. step_inst k C3 si s = OK post` by
        (`inst_wf si` by
           (qpat_assum `active_inst fn si s` (mp_tac o MATCH_MP active_inst_mem_fn_insts) >>
            REWRITE_TAC[fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
            disch_then (qx_choose_then `b0` strip_assume_tac) >>
            qpat_assum `fn_inst_wf fn`
              (qspecl_then [`b0`, `si`] irule o REWRITE_RULE [fn_inst_wf_def]) >>
            qexists `b0` >> conj_tac >> first_assum ACCEPT_TAC) >>
         `MEM si.inst_opcode [PARAM; RETPC_PARAM; FMP_PARAM]` by simp[] >>
         drule_all ld_normal_parameter_shape >> strip_tac >>
         simp[ld_retpc_success_iff]) >>
      pop_assum (qspec_then `fuel` (qx_choose_then `post` assume_tac)) >>
      drule_all focus_fmp_retpc_point >>
      disch_then (qx_choosel_then [`len`, `t1`, `ret_fn`, `ret_bb`]
        (map_every assume_tac o CONJUNCTS)) >>
      `ret_fn = fn' /\ ret_bb = bb` by metis_tac[optionTheory.SOME_11] >>
      qpat_x_assum `ret_fn = fn'` SUBST_ALL_TAC >>
      qpat_x_assum `ret_bb = bb` SUBST_ALL_TAC >>
      `t1.vs_inst_idx = t.vs_inst_idx + len /\
       t.vs_inst_idx + len <= LENGTH bb.bb_instructions` by
        (qpat_assum `!k. fmp_target_run k C4 _ t len t1`
           (qspec_then `fuel` mp_tac) >> simp[NoAsms, fmp_target_run_def] >>
         disch_then (qx_choosel_then [`run_fn`, `run_bb`, `run_post`] strip_assume_tac) >>
         `run_fn = fn' /\ run_bb = bb` by metis_tac[optionTheory.SOME_11] >>
         qpat_x_assum `run_bb = bb` SUBST_ALL_TAC >>
         conj_tac
         >- (qpat_assum `t1 = run_post with vs_inst_idx := _` (fn th => simp[NoAsms, th, ADD_COMM])) >>
         qpat_assum `_ <= LENGTH bb.bb_instructions`
           (fn th => simp[NoAsms, ADD_COMM, th])) >>
      `EVERY (\i. fmp_inserted_op i.inst_opcode)
         (TAKE len (DROP t.vs_inst_idx bb.bb_instructions))` by
        (qpat_x_assum `len = 1 \/ len = 2` strip_assume_tac >>
         qpat_assum `if len = 1 then _ else _` mp_tac >>
         qpat_assum `len = _` (fn th => simp[NoAsms, th, Excl "TAKE1_DROP"]) >>
         strip_tac >> simp[fmp_inserted_op_def, mk_inst_def, set_param_index_def]) >>
      `!i. t.vs_inst_idx <= i /\ i < t1.vs_inst_idx ==>
           i < LENGTH bb.bb_instructions /\
           fmp_inserted_op (EL i bb.bb_instructions).inst_opcode` by
        (qx_gen_tac `i` >> strip_tac >>
         `i < LENGTH bb.bb_instructions /\ i - t.vs_inst_idx < len /\
          i - t.vs_inst_idx + t.vs_inst_idx = i` by decide_tac >>
         conj_tac >- first_assum ACCEPT_TAC >>
         qpat_assum `EVERY _ (TAKE len _)`
           (qspec_then `i - t.vs_inst_idx` mp_tac o REWRITE_RULE [EVERY_EL]) >>
         `len <= LENGTH (DROP t.vs_inst_idx bb.bb_instructions)` by
           (simp[NoAsms, LENGTH_DROP] >> decide_tac) >>
         qpat_assum `len <= LENGTH (DROP _ _)` (fn lim =>
           qpat_assum `i - t.vs_inst_idx < len` (fn off =>
           qpat_assum `i - t.vs_inst_idx + t.vs_inst_idx = i` (fn idx =>
           qpat_assum `i < LENGTH bb.bb_instructions` (fn hi =>
             simp[NoAsms, lim, off, idx, hi, LENGTH_TAKE, EL_TAKE, EL_DROP]))))) >>
      `post.vs_current_bb = s.vs_current_bb /\
       post.vs_gas_readings = s.vs_gas_readings /\ ~post.vs_halted` by
        (`step_inst_base si s = OK post` by
           (qpat_assum `step_inst fuel C3 si s = OK post` mp_tac >>
            qpat_assum `si.inst_opcode <> INVOKE`
              (fn th => simp[NoAsms, step_inst_non_invoke, th])) >>
         `si.inst_opcode <> GAS` by simp[] >>
         drule venomExecPropsTheory.step_inst_OK_preserves_halted >>
         drule_all venomInstPropsTheory.step_preserves_control_flow >>
         drule_all oracleExecPropsTheory.step_inst_noninvoke_gas_readings >>
         simp[NoAsms] >> metis_tac[]) >>
      `t1.vs_current_bb = t.vs_current_bb /\ post.vs_gas_readings = t1.vs_gas_readings` by
        (qpat_assum `fmp_stage_rel _ _ sm _ _ _ F _ _ _ _ _
                     (post with vs_inst_idx := _) lo t1 ts` mp_tac >>
         simp[NoAsms, fmp_stage_rel_def, fmp_frame_rel_def,
              o1LowerDloadSharedTheory.ld_shared_agree_def] >>
         strip_tac >> metis_tac[]) >>
      `t1.vs_inst_idx - t.vs_inst_idx = len /\ t.vs_inst_idx < t1.vs_inst_idx` by
        (qpat_assum `len = 1 \/ len = 2` strip_assume_tac >> decide_tac) >>
      `t.vs_current_bb = t1.vs_current_bb /\
       (!k. fmp_target_run k C4 fn.fn_name t (t1.vs_inst_idx - t.vs_inst_idx) t1)` by
        (conj_tac >- metis_tac[] >>
         qpat_assum `t1.vs_inst_idx - t.vs_inst_idx = len` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
      drule_all (Q.INST [`u` |-> `t1`] focus_fmp_cut_inserted_residual) >>
      strip_tac >> first_x_assum drule >>
      disch_then (strip_assume_tac o SRULE [LET_THM]) >>
      drule_all o1LowerDloadReadinessTheory.ld_nonterminator_successor >>
      disch_then (qx_choose_then `next` assume_tac) >>
      `gas_cut n root3 (post with vs_inst_idx := SUC s.vs_inst_idx)` by
        (qpat_assum `gas_cut n root3 s` mp_tac >>
         qpat_assum `post.vs_gas_readings = s.vs_gas_readings`
           (fn th => simp[NoAsms, gas_cut_def, th])) >>
      `lookup_block s'.vs_current_bb fn'.fn_blocks = SOME bb /\
       t1.vs_gas_readings = s'.vs_gas_readings` by metis_tac[] >>
      disj1_tac >>
      qpat_assum `t.vs_inst_idx = fmp_stage_tidx (fmp_stage_plan infos ctx fn) _ _ _ _`
        (SUBST1_TAC o SYM) >>
      qexistsl [`stk`, `PG`, `step_prov PG G si post`, `step_taint si s post tn`,
                `fn`, `next`, `post with vs_inst_idx := SUC s.vs_inst_idx`,
                `sm`, `lo`, `t1`, `ts`, `F`, `bb`] >>
      conj_tac >- (irule frame_reachable_next >> metis_tac[]) >>
      rpt conj_tac >> simp[NoAsms] >> first_assum ACCEPT_TAC) >>
  reverse (Cases_on `inst.inst_opcode = DALLOCA`)
  >- (Cases_on `inst.inst_opcode = INVOKE`
      >- (`(EL s.vs_inst_idx bs.bb_instructions).inst_opcode = INVOKE` by metis_tac[] >>
          drule_all (Q.INST [`infos` |-> `infos`, `ctx` |-> `ctx`,
                            `idx` |-> `s.vs_inst_idx`] fmp_stage_invoke_inst) >>
          gvs[get_instruction_def]) >>
      `is_terminator inst.inst_opcode` by fs[] >>
      `pre_fmp_opcode inst.inst_opcode` by
        (drule active_inst_mem_fn_insts >> disch_tac >>
         qpat_assum `pre_fmp_ops fn` (mp_tac o REWRITE_RULE [pre_fmp_ops_def, EVERY_MEM]) >>
         metis_tac[]) >>
      `~MEM inst.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM]` by
        (simp[NoAsms] >> rpt strip_tac >> fs[is_terminator_def]) >>
      drule_all (Q.INST [`infos` |-> `infos`, `ctx` |-> `ctx`,
                        `idx` |-> `s.vs_inst_idx`] fmp_stage_kept_inst) >>
      gvs[get_instruction_def] >> disch_then SUBST_ALL_TAC >> fs[]) >>
  qpat_x_assum `~(inst.inst_opcode = DALLOCA /\ _)` mp_tac >>
  simp[] >> disch_then (qspecl_then [`sm`, `lo`] mp_tac) >> simp[]
QED

Resume focus_opt_fmp_cut_cover[call]:
  `gas_cut n root4 t` by
    (irule gas_cut_readings_mono >>
     qpat_assum `gas_cut n root4 t'` (irule_at Any) >>
     drule enters_block_readings >>
     drule o1LowerDloadSharedTheory.ld_setup_callee_gas_readings >> simp[]) >>
  qpat_x_assum `gas_cut n root4 t ==> _` drule >>
  reverse (disch_then (DISJ_CASES_THEN strip_assume_tac))
  >- (drule_all (Q.INST [`eom` |-> `eom`, `C4` |-> `C4`] focus_fmp_cut_tail_observation) >>
      strip_tac >> gvs[MEM]) >>
  `ALL_DISTINCT (fn_labels fn')` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, wf_function_def] >>
     metis_tac[lookup_function_MEM]) >>
  `get_instruction bb t.vs_inst_idx = SOME ti` by
    (qpat_assum `active_inst fn' ti t` (mp_then Any drule_all active_inst_block_lookup) >>
     strip_tac >> metis_tac[optionTheory.SOME_11]) >>
  `u = t` by
    (Cases_on `t.vs_inst_idx < u.vs_inst_idx`
     >- (qpat_assum `!i. _ <= i /\ _ ==> _` (qspec_then `t.vs_inst_idx` mp_tac) >>
         gvs[get_instruction_def, fmp_inserted_op_def]) >>
     `u.vs_inst_idx - t.vs_inst_idx = 0` by decide_tac >>
     metis_tac[fmp_target_run_zero]) >>
  qpat_x_assum `u = t` SUBST_ALL_TAC >>
  `(root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>).vs_vars = FEMPTY /\
   ~(root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>).vs_halted` by
    fs[o1_initial_state_ok_def] >>
  drule_all focus_fmp_source_points >> strip_tac >>
  `ssa_form fn` by metis_tac[lookup_function_MEM, EVERY_MEM] >>
  qabbrev_tac `root3 = root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>` >>
  `w2n root3.vs_fmp = w2n fmp` by simp[Abbr `root3`] >>
  `?m l. fmp_stage_rel D C4 m (w2n root4.vs_initial_fmp) (w2n fmp) eom T
           stk PG G tn fn s l t ts` by
    (Cases_on `restored` >- metis_tac[] >> gvs[] >>
     drule_all (SRULE [] (Q.INST [`raw0` |-> `w2n vs.vs_fmp`] focus_fmp_cut_restore_prefix)) >>
     disch_then (qx_choosel_then
       [`rest_fn`, `rest_src`, `rest_bb`, `rest_infos`, `rest_ctx`,
        `rest_runner`, `rest_len`, `rest_post`, `rest_cut`] strip_assume_tac) >>
     Cases_on `FLOOKUP (fmp_stage_plan rest_infos rest_ctx fn) (s.vs_current_bb,s.vs_inst_idx)`
     >- (gvs[] >> metis_tac[]) >>
     gvs[get_instruction_def, mk_inst_def]) >>
  qpat_x_assum `fmp_stage_rel _ _ _ _ _ _ restored _ _ _ _ _ _ _ _ _` kall_tac >>
  drule_all focus_fmp_aligned_layout >> strip_tac >>
  `pre_fmp_opcode inst.inst_opcode` by
    (qpat_assum `pre_fmp_ops fn` (mp_tac o REWRITE_RULE [pre_fmp_ops_def, EVERY_MEM]) >>
     metis_tac[active_inst_mem_fn_insts]) >>
  `inst.inst_opcode = INVOKE` by
    (CCONTR_TAC >>
     Cases_on `MEM inst.inst_opcode [DALLOCA; RETPC_PARAM]`
     >- (qabbrev_tac `plan = fmp_stage_plan infos ctx fn` >>
         qabbrev_tac `rt = fmp_stage_root infos ctx fn` >>
         qabbrev_tac `idx = s.vs_inst_idx` >>
         qabbrev_tac `lab = s.vs_current_bb` >>
         `fmp_stage_tidx plan rt lab bs.bb_instructions idx +
            (if (lab,idx) IN FDOM plan then 1 else 0) <
          fmp_stage_tidx plan rt lab bs.bb_instructions (SUC idx)` by
           (simp[fmp_stage_tidx_def, GENLIST, SUM_SNOC] >>
            Cases_on `rt` >> simp[]
            >- (IF_CASES_TAC >> simp[]) >>
            rename1 `SOME r = fmp_stage_root _ _ _` >> PairCases_on `r` >> simp[] >>
            rpt (IF_CASES_TAC >> simp[]) >> decide_tac) >>
         mp_tac (Q.INST [`P` |-> `fmp_inserted_op`, `infos` |-> `infos`,
                         `ctx` |-> `ctx`, `runner` |-> `runner`, `fn` |-> `fn`,
                         `fn'` |-> `fn'`, `lbl` |-> `lab`, `bb` |-> `bs`,
                         `idx` |-> `idx`, `i` |-> `t.vs_inst_idx`]
             fmpStageCoverMemAssembleTheory.fmp_cover_inserted_from_root_structural) >>
         (impl_tac >- (simp[fmp_inserted_op_def, Abbr `rt`, Abbr `plan`] >>
                       rw[] >> gvs[MEM])) >>
         strip_tac >> gvs[get_instruction_def, fmp_inserted_op_def]) >>
     `~MEM inst.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM]` by fs[MEM] >>
     drule_all (Q.INST [`infos` |-> `infos`, `ctx` |-> `ctx`,
                       `idx` |-> `s.vs_inst_idx`] fmp_stage_kept_inst) >>
     strip_tac >> gvs[get_instruction_def]) >>
  drule_all focus_fmp_cut_source_call_entry >>
  disch_then (qx_choosel_then [`snm`, `sops`, `callee`, `sargs`, `scs`, `si1`]
    strip_assume_tac) >>
  `C3.ctx_entry <> SOME snm` by (drule_all fmp_invoke_not_entry >> simp[]) >>
  `callee.fn_fmp_signature = NONE` by
    (fs[fmp_free_ctx_def, EVERY_MEM] >> metis_tac[lookup_function_MEM]) >>
  drule_all focus_fmp_cut_invoke_push >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`tf`, `sb`, `tb`, `tj`, `ti0`, `tc0`, `tr0`, `tf1`,
      `si0`, `sc0`, `sr0`, `extra`, `rr`, `args1`, `cs1`, `t1`] strip_assume_tac)) >>
  `tf = fn'` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `tf = fn'` SUBST_ALL_TAC >>
  `tj = ti` by metis_tac[fmpStageBlockSimCodeTheory.active_inst_unique] >>
  qpat_x_assum `tj = ti` SUBST_ALL_TAC >>
  `snm = nm /\ sops ++ extra = ops /\ tf1 = fn'' /\ cs1 = cs /\ t1 = t'` by
    (gvs[enters_block_def] >> metis_tac[]) >>
  qpat_x_assum `t1 = t'` SUBST_ALL_TAC >>
  `callee.fn_name = snm` by metis_tac[lookup_function_selected_name] >>
  `fn_inst_ids_distinct fn` by
    (pure_rewrite_tac [algebraicOptSupplyProofsTheory.ao_fn_inst_ids_distinct_alt] >>
     irule ctx_inst_ids_distinct_fn >>
     qexists `C3` >> fs[o1_ctx_shape_def] >> metis_tac[lookup_function_MEM]) >>
  `MEM inst (fn_insts fn) /\ MEM ti (fn_insts fn')` by
    metis_tac[active_inst_mem_fn_insts] >>
  `ti.inst_outputs = inst.inst_outputs` by
    (qpat_assum `ti.inst_id = inst.inst_id` (mp_then Any drule_all focus_fmp_cut_invoke_outputs) >>
     simp[]) >>
  qabbrev_tac `f = <|cf_fn := fn; cf_inst := inst; cf_state := s;
                     cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|>` >>
  `frame_reachable root3 C3 (f::stk) (MAP (op_prov G) sops) FEMPTY
        (tn with t_var := FEMPTY) callee si1 scs` by
    (simp[Abbr `f`] >> irule frame_reachable_call >> metis_tac[]) >>
  `~scs.vs_halted /\ scs.vs_gas_readings = s.vs_gas_readings /\
   t'.vs_gas_readings = t.vs_gas_readings` by
    metis_tac[ld_setup_callee_not_halted, o1LowerDloadSharedTheory.ld_setup_callee_gas_readings,
              enters_block_readings] >>
  `gas_cut n root3 scs` by
    (irule gas_cut_readings_mono >> qpat_assum `gas_cut n root3 s` (irule_at Any) >> gvs[]) >>
  `ALL_DISTINCT (fn_labels fn'')` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, wf_function_def] >>
     metis_tac[lookup_function_MEM]) >>
  qpat_assum `active_inst fn'' ti' t'` (mp_then Any drule_all active_inst_block_lookup) >>
  disch_then (qx_choose_then `bb1` strip_assume_tac) >>
  disj1_tac >>
  qexistsl [`f::stk`, `MAP (op_prov G) sops`, `FEMPTY`, `tn with t_var := FEMPTY`,
    `callee`, `si1`, `scs`, `m`, `l`, `t'`, `(t,l)::ts`, `F`, `bb1`] >>
  simp[Abbr `f`, fmp_cov_stack_def] >>
  gvs[fmp_target_run_def, run_insts_def, get_instruction_def]
QED

Resume focus_opt_fmp_cut_cover[ret]:
  `MEM ti.inst_opcode [RET; RETFMP; DRET]` by metis_tac[step_inst_intret_opcodes] >>
  `gas_cut n root4 t` by
    (irule gas_cut_readings_mono >>
     qpat_assum `gas_cut n root4 (_ with vs_inst_idx := _)` (irule_at Any) >>
     simp[] >> metis_tac[return_readings_le]) >>
  qpat_x_assum `gas_cut n root4 t ==> _` drule >>
  reverse (disch_then (DISJ_CASES_THEN strip_assume_tac))
  >- (drule_all (Q.INST [`eom` |-> `eom`, `C4` |-> `C4`] focus_fmp_cut_tail_observation) >>
      strip_tac >> gvs[MEM]) >>
  `ALL_DISTINCT (fn_labels fn')` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, wf_function_def] >>
     metis_tac[lookup_function_MEM]) >>
  `get_instruction bb t.vs_inst_idx = SOME ti` by
    (qpat_assum `active_inst fn' ti t` (mp_then Any drule_all active_inst_block_lookup) >>
     strip_tac >> metis_tac[optionTheory.SOME_11]) >>
  `u = t` by
    (Cases_on `t.vs_inst_idx < u.vs_inst_idx`
     >- (qpat_assum `!i. _ <= i /\ _ ==> _` (qspec_then `t.vs_inst_idx` mp_tac) >>
         gvs[get_instruction_def, fmp_inserted_op_def, MEM]) >>
     `u.vs_inst_idx - t.vs_inst_idx = 0` by decide_tac >>
     metis_tac[fmp_target_run_zero]) >>
  qpat_x_assum `u = t` SUBST_ALL_TAC >>
  `(root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>).vs_vars = FEMPTY /\
   ~(root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>).vs_halted` by
    fs[o1_initial_state_ok_def] >>
  drule_all focus_fmp_source_points >> strip_tac >>
  `ssa_form fn` by metis_tac[lookup_function_MEM, EVERY_MEM] >>
  qabbrev_tac `root3 = root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>` >>
  `w2n root3.vs_fmp = w2n fmp` by simp[Abbr `root3`] >>
  `?m l. fmp_stage_rel D C4 m (w2n root4.vs_initial_fmp) (w2n fmp) eom T
           stk PG G tn fn s l t ts` by
    (Cases_on `restored` >- metis_tac[] >> gvs[] >>
     drule_all (SRULE [] (Q.INST [`raw0` |-> `w2n vs.vs_fmp`] focus_fmp_cut_restore_prefix)) >>
     disch_then (qx_choosel_then
       [`rest_fn`, `rest_src`, `rest_bb`, `rest_infos`, `rest_ctx`,
        `rest_runner`, `rest_len`, `rest_post`, `rest_cut`] strip_assume_tac) >>
     Cases_on `FLOOKUP (fmp_stage_plan rest_infos rest_ctx fn) (s.vs_current_bb,s.vs_inst_idx)`
     >- (qexistsl [`DRESTRICT sm {key | key IN FDOM sm /\ FST (sm ' key) < rest_cut}`,
                   `rest_cut`] >> gvs[]) >>
     gvs[get_instruction_def, mk_inst_def, MEM] >>
     metis_tac[get_instruction_def, mk_inst_def, MEM,
               SRULE [] (Q.INST [`raw0` |-> `w2n vs.vs_fmp`] focus_fmp_cut_restore_prefix)]) >>
  qpat_x_assum `fmp_stage_rel _ _ _ _ _ _ restored _ _ _ _ _ _ _ _ _` kall_tac >>
  drule_all focus_fmp_aligned_layout >> strip_tac >>
  `pre_fmp_opcode inst.inst_opcode` by
    (qpat_assum `pre_fmp_ops fn` (mp_tac o REWRITE_RULE [pre_fmp_ops_def, EVERY_MEM]) >>
     metis_tac[active_inst_mem_fn_insts]) >>
  `inst = ti` by
    (Cases_on `MEM inst.inst_opcode [DALLOCA; RETPC_PARAM]`
     >- (mp_tac (Q.INST [`P` |-> `fmp_inserted_op`, `infos` |-> `infos`,
                         `ctx` |-> `ctx`, `runner` |-> `runner`, `fn` |-> `fn`,
                         `fn'` |-> `fn'`, `lbl` |-> `s.vs_current_bb`, `bb` |-> `bs`,
                         `idx` |-> `s.vs_inst_idx`, `i` |-> `t.vs_inst_idx`]
             fmpStageCoverMemAssembleTheory.fmp_cover_inserted_from_root_structural) >>
         (impl_tac >- (simp[fmp_inserted_op_def, fmp_cov_tidx_lt] >>
                       rw[] >> gvs[MEM] >>
                       metis_tac[SRULE [] fmp_cov_tidx_lt])) >>
         strip_tac >> gvs[get_instruction_def, fmp_inserted_op_def, MEM]) >>
     Cases_on `inst.inst_opcode = INVOKE`
     >- (qpat_x_assum `inst = EL _ _` SUBST_ALL_TAC >>
         drule_all fmp_stage_invoke_inst >> strip_tac >>
         gvs[get_instruction_def, MEM]) >>
     `~MEM inst.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM]` by fs[MEM] >>
     drule_all (Q.INST [`infos` |-> `infos`, `ctx` |-> `ctx`,
                       `idx` |-> `s.vs_inst_idx`] fmp_stage_kept_inst) >>
     strip_tac >> gvs[get_instruction_def]) >>
  `inst.inst_opcode = RET` by fs[pre_fmp_opcode_def, MEM] >>
  qpat_x_assum `inst = ti` SUBST_ALL_TAC >>
  qpat_x_assum `stk = f'::xs` SUBST_ALL_TAC >>
  Cases_on `ts` >- fs[fmp_cov_stack_def] >>
  rename1 `fmp_cov_stack C4 (f'::xs) (p::ps) (f::stk')` >>
  PairCases_on `p` >>
  qpat_x_assum `fmp_cov_stack C4 (f'::xs) _ _`
    (strip_assume_tac o REWRITE_RULE [fmp_cov_stack_def]) >>
  qpat_x_assum `ti = EL _ _` kall_tac >>
  `s.vs_labels = t.vs_labels` by
    (qpat_assum `fmp_stage_rel _ _ m _ _ _ T _ _ _ _ _ _ _ t _` mp_tac >>
     simp[NoAsms, fmp_stage_rel_def, fmp_frame_rel_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `!v. MEM (Var v) ti.inst_operands ==> IS_SOME (lookup_var v s)` by fs[] >>
  `opaque_use_ok fn` by fs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def] >>
  drule_all focus_fmp_cut_source_return >>
  disch_then (qspec_then `fuel`
    (qx_choosel_then [`sr`, `se`, `sb`, `si`] strip_assume_tac)) >>
  `fmp_stage_rel D C4 m (w2n root4.vs_initial_fmp) (w2n root3.vs_fmp) eom T
     (f'::xs) PG G tn fn s l t ((p0,p1)::ps)` by simp[] >>
  drule_at (Pat `step_inst _ _ _ _ = IntRet _ _`) focus_fmp_cut_invoke_pop >>
  disch_then (drule_at (Pat `fmp_stage_rel _ _ _ _ _ _ T _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `frame_reachable _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `taint_ok _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_use_static_ok _ _ _`)) >>
  disch_then (drule_at (Pat `bind_outputs _ _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `active_inst _ _ (_ with vs_inst_idx := _)`)) >>
  disch_then (qspecl_then [`rp`, `n`, `fn'`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> simp[] >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`jr`, `j`, `t1`] strip_assume_tac))) >>
  qpat_x_assum `!k. step_inst k C4 ti t = _` (qspec_then `fuel` assume_tac) >>
  `ALL_DISTINCT (fn_labels f.cf_fn)` by
    (gs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, wf_function_def] >>
     metis_tac[lookup_function_MEM]) >>
  `j = f.cf_inst` by metis_tac[active_inst_block_lookup, optionTheory.SOME_11] >>
  gvs[] >>
  qabbrev_tac `b3 = sb with vs_inst_idx := SUC f'.cf_state.vs_inst_idx` >>
  qabbrev_tac `b4 = s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx` >>
  `frame_reachable root3 C3 xs f'.cf_params
       (DRESTRICT f'.cf_prov (COMPL (set f'.cf_inst.inst_outputs)))
       (tn with t_var := DRESTRICT f'.cf_tvar (COMPL (set f'.cf_inst.inst_outputs)))
       f'.cf_fn si b3` by
    (simp[Abbr `b3`] >> irule frame_reachable_ret >> metis_tac[]) >>
  `!nm g. lookup_function nm C3.ctx_functions = SOME g ==> wf_function g` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >>
     metis_tac[lookup_function_MEM]) >>
  `~b3.vs_halted` by
    (qpat_assum `frame_reachable root3 C3 xs _ _ _ _ _ b3`
        (mp_then Any drule_all scfg_frame_reachable_entry_root) >> strip_tac >>
     drule o1PassLiftTheory.supply_frame_reach_not_halted >> fs[o1PassLiftTheory.fn_entry_state_def]) >>
  `b3.vs_gas_readings = b4.vs_gas_readings` by
    (qpat_assum `fmp_stage_rel _ _ _ _ _ _ F xs _ _ _ _ b3 _ b4 _` mp_tac >>
     simp[NoAsms, fmp_stage_rel_def, o1LowerDloadSharedTheory.ld_shared_agree_def]) >>
  `gas_cut n root3 b3` by
    (`root3.vs_gas_readings = root4.vs_gas_readings` by simp[Abbr `root3`] >>
     fs[gas_cut_def, Abbr `b4`]) >>
  qpat_assum `active_inst f.cf_fn ti' b4` (mp_then Any drule_all active_inst_block_lookup) >>
  disch_then (qx_choose_then `bb1` strip_assume_tac) >>
  disj1_tac >>
  qexistsl [`xs`, `f'.cf_params`, `DRESTRICT f'.cf_prov (COMPL (set f'.cf_inst.inst_outputs))`,
    `tn with t_var := DRESTRICT f'.cf_tvar (COMPL (set f'.cf_inst.inst_outputs))`,
    `f'.cf_fn`, `si`, `b3`, `DRESTRICT m {key | FST key < w2n f'.cf_state.vs_fmp}`,
    `p1`, `b4`, `ps`, `F`, `bb1`] >>
  gvs[Abbr `b4`, fmp_target_run_def, run_insts_def, get_instruction_def]
QED

Finalise focus_opt_fmp_cut_cover[local]

(* The two sources of non-kept code are the root layout and the indexed
   block walk. Neither can introduce a new code-end chain: the only
   extra ASSIGNs are restores from DALLOCA outputs. *)
Theorem focus_fmp_code_end_layout_origin[local]:
  fmp_stage_lowered infos ctx runner f g /\ MEM j (fn_insts g) ==>
  MEM j (fn_insts_blocks f.fn_blocks) \/
  ?sp s1 info users oldpc suffix root newpc s2 plan blocks s3.
    ir_supply_covers_fn sp f /\ fresh_ir_var sp = (runner,s1) /\
    split_fmp_entry f = SOME (FmpEntryLayout users oldpc suffix) /\
    fmp_make_root_layout ctx f info runner s1 =
      SOME (FmpRootLayout (LENGTH users) root newpc s2) /\
    analyze_fmp_reclaims infos ctx f = SOME plan /\
    fmp_lower_blocks infos ctx runner s2 (fmp_plan_to_alist f plan) f.fn_blocks =
      SOME (FmpBlocksResult blocks [] s3) /\
    (MEM j (fn_insts_blocks blocks) \/
     MEM j (OPTION_TO_LIST root) \/ MEM j (OPTION_TO_LIST newpc))
Proof
  simp[fmp_stage_lowered_def, fmp_lower_function_with_info_def, AllCaseEqs()] >>
  strip_tac >> gvs[fn_insts_def] >>
  drule fmp_checked_seal_some >> strip_tac >> gvs[fmp_seal_def, fn_insts_def] >>
  Cases_on `root_layout` >> gvs[] >>
  `?users oldpc suffix. split_fmp_entry f = SOME (FmpEntryLayout users oldpc suffix)` by
    (qpat_assum `fmp_make_root_layout _ _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[fmp_make_root_layout_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all fmp_make_root_layout_prefix >> strip_tac >> gvs[] >>
  drule_all fmp_lower_blocks_checked_entry_prefix >> strip_tac >>
  `entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail` by
    (Cases_on `oldpc` >> fs[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
  qpat_x_assum `blocks = entry::rest` SUBST_ALL_TAC >>
  rename1 `fresh_ir_var sp = (runner,s1)` >>
  rename1 `fmp_make_root_layout ctx f info runner s1 =
      SOME (FmpRootLayout (LENGTH users) root newpc s2)` >>
  rename1 `fmp_lower_blocks infos ctx runner s2 (fmp_plan_to_alist f plan)
      f.fn_blocks = SOME (FmpBlocksResult (entry::rest) [] s3)` >>
  drule_all (SRULE [fn_insts_def] fmp_install_root_instruction_origin) >>
  disch_then assume_tac >>
  disj2_tac >>
  metis_tac[]
QED

Theorem focus_fmp_code_end_inst_origin[local]:
  fmp_stage_lowered infos ctx runner f g /\ pre_fmp_ops f /\ ssa_form f /\
  MEM j (fn_insts g) /\
  ((j.inst_opcode = ADD /\ ?op. j.inst_operands = [op; Label "code_end"]) \/
   (j.inst_opcode = ASSIGN /\ ?y. j.inst_operands = [Var y] /\ code_end_var f y)) ==>
  MEM j (fn_insts f)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all focus_fmp_code_end_layout_origin >>
  disch_then (DISJ_CASES_THEN2 assume_tac
    (qx_choosel_then [`sp`, `s1`, `info`, `users`, `oldpc`, `suffix`,
       `root`, `newpc`, `s2`, `plan`, `blocks`, `s3`]
       (map_every assume_tac o CONJUNCTS)))
  >- simp[fn_insts_def] >>
  drule_all fmp_make_root_layout_opaque_shape >> strip_tac >>
  `MEM j (fn_insts_blocks blocks)` by
    (qpat_x_assum `MEM j (fn_insts_blocks blocks) \/ _` strip_assume_tac >>
     qpat_x_assum `j.inst_opcode = ADD /\ _ \/ _` strip_assume_tac >>
     qpat_x_assum `!i. MEM i (OPTION_TO_LIST root) ==> _`
       (qspec_then `j` mp_tac) >>
     qpat_x_assum `!i. MEM i (OPTION_TO_LIST newpc) ==> i.inst_opcode = RETPC_PARAM`
       (qspec_then `j` mp_tac) >> simp[]) >>
  fs[fn_insts_def] >>
  qpat_x_assum `MEM j (fn_insts_blocks blocks)` mp_tac >>
  pure_rewrite_tac[fn_insts_blocks_MEM] >> strip_tac >>
  drule_all fmp_lower_blocks_origin >> strip_tac >>
  TRY (rename1 `fmp_lower_inst _ _ _ _ src_inst = SOME _` >>
       `pre_fmp_opcode src_inst.inst_opcode` by
         (fs[pre_fmp_ops_def, fn_insts_def, fn_insts_blocks_MEM, EVERY_MEM] >>
          metis_tac[]) >>
       gvs[fmp_lower_inst_def, AllCaseEqs(), mk_inst_def, pre_fmp_opcode_def] >>
       metis_tac[] >> NO_TAC) >>
  gvs[mk_inst_def] >>
  rename1 `MEM (restore_point,restore_base) (fmp_plan_to_alist f plan)` >>
  `FLOOKUP plan restore_point = SOME restore_base` by
    metis_tac[fmpLowerPropsTheory.MEM_fmp_plan_to_alist] >>
  drule_all analyze_fmp_reclaims_output >> strip_tac >>
  drule_all code_end_var_def_inst >> simp[]
QED

Theorem focus_fmp_code_end_var_backward[local]:
  !g x. code_end_var g x ==> !infos ctx runner f.
    fmp_stage_lowered infos ctx runner f g /\ pre_fmp_ops f /\ ssa_form f ==>
    code_end_var f x
Proof
  Induct_on `code_end_var` >> rpt strip_tac
  >- (`MEM inst (fn_insts f)` by
        (irule focus_fmp_code_end_inst_origin >> metis_tac[]) >>
      metis_tac[code_end_var_rules]) >>
  rename1 `inst.inst_operands = [Var y]` >>
  `code_end_var f y` by metis_tac[] >>
  `MEM inst (fn_insts f)` by
    (irule focus_fmp_code_end_inst_origin >> metis_tac[]) >>
  metis_tac[code_end_var_rules]
QED

Theorem focus_fmp_codecopy_scalar[local]:
  o1_fn_shape C fn /\ make_ssa_input_ok fn /\ active_inst fn inst s /\
  taint_ok fn tn inst s /\ ptr_use_static_ok P (fn_pv P fn) inst /\
  FDOM G SUBSET fn_pv P fn /\
  fmp_stage_rel D C' sm fmp0 raw0 eom restored stk PG G tn fn s lo t ts /\
  inst.inst_opcode = CODECOPY /\ inst.inst_operands = [dst; Var x; sz] /\
  IS_SOME (lookup_var x s) ==>
  eval_operand (Var x) s = eval_operand (Var x) t
Proof
  strip_tac >>
  `x NOTIN fn_pv P fn` by
    (strip_tac >> qpat_x_assum `ptr_use_static_ok _ _ _` mp_tac >>
     pure_rewrite_tac[ptr_use_static_ok_def] >>
     disch_then (CONJUNCTS_THEN2 kall_tac (qspec_then `x` mp_tac)) >>
     simp[is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def] >>
     Cases_on `dst = Var x` >> gvs[AllCaseEqs()]) >>
  `op_prov G (Var x) = NONE` by
    (gvs[op_prov_def, SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]) >>
  `op_taint tn (Var x) = {}` by
    (gvs[taint_ok_def] >> metis_tac[MEM]) >>
  `~retpc_var fn x` by
    (irule ordinary_operand_not_retpc >> conj_tac
     >- fs[o1_fn_shape_def, fn_shape_ok_def] >>
     qexists_tac `inst` >> simp[] >> metis_tac[active_inst_mem_fn_insts]) >>
  `wf_function fn /\ inst.inst_opcode <> PHI /\ MEM (Var x) inst.inst_operands /\
    (!v. Var x = Var v ==> ~retpc_var fn v)` by fs[o1_fn_shape_def] >>
  `?w. eval_operand (Var x) s = SOME w` by
    (Cases_on `lookup_var x s` >> gvs[eval_operand_def]) >>
  drule_all fmp_stage_operand_point >>
  simp[fmp_value_rel_def] >> strip_tac >>
  metis_tac[ld_value_agree_clean]
QED

(* A CODECOPY is not a restore, a rewritten INVOKE, or an FMP primitive. *)
Theorem focus_fmp_codecopy_inst[local]:
  fmp_stage_lowered infos ctx runner fn fn' /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ idx < LENGTH bb.bb_instructions /\
  pre_fmp_ops fn /\ inst = EL idx bb.bb_instructions /\
  lookup_block lbl fn'.fn_blocks = SOME bt /\ get_instruction bt i = SOME ti /\
  ti.inst_opcode = CODECOPY /\
  i = fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
                      lbl bb.bb_instructions idx +
      (if restored /\ (lbl,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0) ==>
  ti = inst
Proof
  strip_tac >>
  qabbrev_tac `q = fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
                                  lbl bb.bb_instructions idx` >>
  qabbrev_tac `k = q + (if (lbl,idx) IN FDOM (fmp_stage_plan infos ctx fn) then 1 else 0)` >>
  `q <= i /\ i <= k` by (Cases_on `restored` >> gvs[Abbr `k`]) >>
  `i < fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
                      lbl bb.bb_instructions (SUC idx)` by
    (qspecl_then [`fmp_stage_plan infos ctx fn`, `fmp_stage_root infos ctx fn`,
       `lbl`, `bb.bb_instructions`, `idx`] mp_tac
       (Q.GENL [`plan`, `root`, `lbl`, `insts`, `idx`] fmp_cov_tidx_lt) >>
     strip_tac >> Cases_on `restored` >> gvs[Abbr `k`, Abbr `q`]) >>
  Cases_on `i <> k \/ MEM inst.inst_opcode [DALLOCA; RETPC_PARAM]`
  >- (`?bt'. lookup_block lbl fn'.fn_blocks = SOME bt' /\ i < LENGTH bt'.bb_instructions /\
              fmp_inserted_op (EL i bt'.bb_instructions).inst_opcode` by
        (irule fmp_cover_inserted_from_root_structural >>
         simp[fmp_inserted_op_def] >>
         qexistsl [`bb`, `ctx`, `fn`, `idx`, `infos`, `runner`] >>
         Cases_on `idx = 0` >> gvs[Abbr `k`, Abbr `q`] >> metis_tac[]) >>
      gvs[get_instruction_def, fmp_inserted_op_def]) >>
  `pre_fmp_opcode inst.inst_opcode` by
    (fs[pre_fmp_ops_def, EVERY_MEM, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[EL_MEM, lookup_block_member_label]) >>
  `i = k` by fs[] >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (`(EL idx bb.bb_instructions).inst_opcode = INVOKE` by metis_tac[] >>
      drule_all fmp_stage_invoke_inst >> gvs[get_instruction_def, Abbr `k`, Abbr `q`]) >>
  `~MEM inst.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM]` by fs[] >>
  drule_all fmp_stage_kept_inst >> gvs[get_instruction_def, Abbr `k`, Abbr `q`]
QED

Theorem focus_opt_fmp_bound_from_cover[local]:
  o1_ctx_shape C3 /\ o1_ctx_shape C4 /\
  EVERY (o1_fn_row 3) C3.ctx_functions /\ EVERY ssa_form C3.ctx_functions /\
  o1_initial_state_ok root4 /\ fmp_free_ctx C3 /\
  root3 = root4 with <|vs_fmp := fmp; vs_initial_fmp := fmp|> /\
  ^focus_fmp_fields /\
  (!stk' PG' G' tn' fn' ti t.
     frame_reachable root4 C4 stk' PG' G' tn' fn' ti t /\ gas_cut n root4 t ==>
     ^focus_fmp_matched \/ ^focus_fmp_tail) /\
  code_end_offset_ok (\ctx fn i s. raw_reachable root3 ctx fn i s /\ gas_cut n root3 s) C3 ==>
  code_end_offset_ok (\ctx fn i s. raw_reachable root4 ctx fn i s /\ gas_cut n root4 s) C4
Proof
  strip_tac >> simp[code_end_offset_ok_def] >>
  map_every qx_gen_tac [`fn'`, `ti`, `t`, `dst`, `x`, `sz`, `w`, `bword`] >> strip_tac >>
  drule ptr_raw_reachable_frame >> strip_tac >>
  `active_inst fn' ti t` by metis_tac[scfg_frame_reachable_active] >>
  qpat_x_assum `!stk' PG' G' tn' fn' ti t. frame_reachable root4 _ _ _ _ _ _ _ _ /\ _ ==> _`
    drule_all >> strip_tac
  >- (`MEM fn' C4.ctx_functions` by
        metis_tac[frameAllocationOwnershipTheory.frame_reachable_functions_member] >>
      `ALL_DISTINCT (fn_labels fn')` by
        fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, wf_function_def] >>
      `get_instruction bb t.vs_inst_idx = SOME ti` by
        metis_tac[active_inst_block_lookup, optionTheory.SOME_11] >>
      Cases_on `t.vs_inst_idx < u.vs_inst_idx`
      >- (qpat_assum `!i. _ <= i /\ _ ==> _` (qspec_then `t.vs_inst_idx` mp_tac) >>
          (impl_tac >- decide_tac) >> strip_tac >>
          gvs[get_instruction_def, fmp_inserted_op_def]) >>
      `u = t` by
        (qpat_assum `!k. fmp_target_run k _ _ _ _ _` (qspec_then `0` mp_tac) >>
         `u.vs_inst_idx - t.vs_inst_idx = 0` by decide_tac >>
         simp[] >> metis_tac[fmp_target_run_zero]) >>
      qpat_x_assum `u = t` SUBST_ALL_TAC >>
      `root3.vs_vars = FEMPTY /\ ~root3.vs_halted` by fs[o1_initial_state_ok_def] >>
      drule_all focus_fmp_source_points >> strip_tac >>
      drule_all focus_fmp_aligned_layout >> strip_tac >>
      `ti = inst` by (irule focus_fmp_codecopy_inst >> metis_tac[]) >>
      `ssa_form fn` by metis_tac[EVERY_MEM, lookup_function_MEM] >>
      `code_end_var fn x` by
        (drule focus_fmp_code_end_var_backward >> metis_tac[]) >>
      `IS_SOME (lookup_var x s)` by fs[] >>
      `eval_operand (Var x) s = eval_operand (Var x) t` by
        (irule focus_fmp_codecopy_scalar >> metis_tac[]) >>
      `s.vs_labels = t.vs_labels` by fs[fmp_stage_rel_def, fmp_frame_rel_def] >>
      `raw_reachable root3 C3 fn inst s` by metis_tac[ld_frame_reachable_raw] >>
      fs[code_end_offset_ok_def] >> metis_tac[]) >>
  `get_instruction bb t.vs_inst_idx = SOME ti` by
    metis_tac[active_inst_block_lookup, optionTheory.SOME_11] >>
  drule_all ld_revert_pair_suffix_opcode >> simp[]
QED

Theorem focus_opt_c1_section[local]:
  o1PipelineCorrect$o1_pipeline rp unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\
  run_pipeline_stages rp o1_pipeline_spec.ps_pre_walk_stages unit
    (init_ir_supply unit) = SOME (pre,t) /\
  pre.cu_context.ctx_entry = SOME nm /\
  ctx_pass_stage rp (CFP_Simple VP_MakeSSA) view
    (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context C1 /\
  EVERY make_ssa_input_ok
    (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context.ctx_functions /\
  unit.cu_context.ctx_entry = SOME nm /\
  lookup_function nm unit.cu_context.ctx_functions = SOME entryfn /\
  fn_entry_label entryfn = SOME lbl /\
  o1_initial_state_ok V /\
  (!fn i s. raw_reachable V unit.cu_context fn i s /\ gas_cut n V s ==>
             inst_dload_in_section i s) /\
  (!fn i. MEM fn unit.cu_context.ctx_functions /\ MEM i (fn_insts fn) ==>
           ~MEM (Label "code_end") i.inst_operands) ==>
  mem_inv (\ctx fn i s. (gas_cut n V s ==> inst_dload_in_section i s) /\
    s.vs_code = V.vs_code /\ s.vs_data_section = V.vs_data_section) C1 V /\
  (!fn i. MEM fn C1.ctx_functions /\ MEM i (fn_insts fn) ==>
           ~MEM (Label "code_end") i.inst_operands)
Proof
  strip_tac >> fs[o1PipelineCorrectTheory.o1_pipeline_def] >>
  drule o1_driver_runs >> strip_tac >>
  `o1_ctx_shape unit.cu_context` by metis_tac[o1_source_unit_ok_ctx_shape] >>
  `EVERY (\fn. EVERY (\i. i.inst_opcode <> PHI) (fn_insts fn))
    unit.cu_context.ctx_functions` by
    (fs[o1_source_unit_ok_def, EVERY_MEM, raw_opcode_ok_def] >> metis_tac[]) >>
  `EVERY simplify_cfg_fn_ok unit.cu_context.ctx_functions` by
    (fs[EVERY_MEM, unit_defs_reach_uses_def, o1_ctx_shape_def] >>
     rpt strip_tac >> irule simplify_cfg_fn_ok_no_phi >>
     simp[EVERY_MEM] >> metis_tac[o1_fn_shape_def]) >>
  `mem_inv (\ctx fn i s. (gas_cut n V s ==> inst_dload_in_section i s) /\
    s.vs_code = V.vs_code /\ s.vs_data_section = V.vs_data_section)
    unit.cu_context V` by
    (simp[mem_inv_raw_reachable] >> metis_tac[raw_reachable_code_data]) >>
  gvs[o1_initial_state_ok_def] >>
  irule code_end_source_prefix_transport_upto >>
  metis_tac[init_ir_supply_inst_ok]
QED

(* A synchronized LowerDload expansion has the same unread gas list at
   the selected COPY. Thus bounded source taint and section safety suffice. *)
Theorem focus_opt_lower_row_bound[local]:
  ld_sync lo P C V stk PG G tn fn si s t0 A (f::fs) fuel /\ o1_ctx_shape C /\
  ir_supply_covers_fn f.lf_supply fn /\ fn' = ld_image f /\
  (!g i. MEM g C.ctx_functions /\ MEM i (fn_insts g) ==>
    ~MEM (Label "code_end") i.inst_operands) /\
  mem_inv (\ctx g i u. (gas_cut n V u ==> inst_dload_in_section i u) /\
    u.vs_code = V.vs_code /\ u.vs_data_section = V.vs_data_section) C V /\
  o1_safe_upto D lo n C V /\ LENGTH V.vs_data_section < dimword (:256) DIV 2 /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\ ld_prefix C' fn' X p h t0 t /\
  s.vs_gas_readings = t.vs_gas_readings /\ gas_cut n V t /\
  (EL h X).inst_opcode = CODECOPY /\ (EL h X).inst_operands = [dst; Var x; sz] /\
  code_end_var fn' x /\ eval_operand (Var x) t = SOME w /\
  FLOOKUP t.vs_labels "code_end" = SOME bword ==>
  w2n (w - bword) < dimword (:256) DIV 2
Proof
  strip_tac >>
  drule_then strip_assume_tac ld_sync_source >>
  `gas_cut n V s` by fs[gas_cut_def] >>
  `taint_ok fn tn si s` by
    (qpat_x_assum `o1_safe_upto _ _ _ _ _` mp_tac >>
     simp[o1_safe_upto_def, o1_ptr_safe_upto_def, ptr_discipline_upto_def] >>
     metis_tac[]) >>
  `MEM fn C.ctx_functions` by metis_tac[frameAllocationOwnershipTheory.frame_reachable_functions_member] >>
  `inst_dload_in_section si s /\ s.vs_data_section = V.vs_data_section` by
    (drule_all ld_sync_source_mem_inv >> simp[] >> metis_tac[]) >>
  irule focus_lower_dload_codecopy_point >> simp[] >> metis_tac[]
QED

(* Shared term quotations for the bounded raw-row induction. The transition
   interfaces keep lo, P, C, C', vs, Sigma and names fixed. *)
val focus_opt_ld_stable = ``\lo P Sigma names fs f0 A0 A frames.
  frames <> [] /\ TL frames = fs /\
  (HD frames).lf_serial = f0.lf_serial /\ ld_global lo A frames /\
  EVERY (\f. f.lf_supply = Sigma f.lf_fn.fn_name) frames /\
  EVERY (\f. !j a. j < LENGTH f.lf_Q /\ EL j f.lf_Q = SOME a ==>
    j IN P f.lf_fn.fn_name) frames /\
  (!j k. j < k /\ k < LENGTH frames ==>
    list_precedes (EL j frames).lf_fn.fn_name
                  (EL k frames).lf_fn.fn_name names) /\
  (!g. MEM g fs ==> FRANGE g.lf_H SUBSET ld_slots A fs /\
    (!a. MEM (SOME a) g.lf_Q ==> a IN ld_slots A fs)) /\
  (!a. a IN FDOM A0 /\ a IN ld_slots A0 fs ==>
    FLOOKUP A a = FLOOKUP A0 a)``;

val focus_opt_ld_row = ``\lo P C C' vs Sigma names gn ti t
                         stk PG G tn fn inst s t0 A f fs N X p h.
  ld_sync lo P C vs stk PG G tn fn inst s t0 A (f::fs) N /\
  ^focus_opt_ld_stable lo P Sigma names fs f A A (f::fs) /\
  gn = ld_image f /\ ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\
  t0.vs_inst_idx = p /\ ld_prefix C' gn X p h t0 t /\ h < LENGTH X /\
  ti = EL h X /\ s.vs_gas_readings = t0.vs_gas_readings /\
  t0.vs_gas_readings = t.vs_gas_readings /\
  EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
    LENGTH s.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) (f::fs)``;

val focus_opt_ld_R = ``\lo P C C' vs Sigma names gn ti t.
  ?stk PG G tn fn inst s t0 A f fs N X p h.
    ^focus_opt_ld_row lo P C C' vs Sigma names gn ti t
      stk PG G tn fn inst s t0 A f fs N X p h``;

val focus_opt_ld_forward = ``\(C':venom_context) gn ti t.
  ?bb i j. lookup_block t.vs_current_bb gn.fn_blocks = SOME bb /\
    revert_forward_pair bb i j /\ i <= t.vs_inst_idx /\
    t.vs_inst_idx <= j /\ get_instruction bb t.vs_inst_idx = SOME ti /\
    t.vs_alloca_next < dimword (:256) /\
    w2n t.vs_initial_fmp <= w2n t.vs_fmp /\
    (ctx_has_dalloca C' ==> t.vs_alloca_next <= w2n t.vs_initial_fmp)``;

val focus_opt_ld_W = ``\C' gn ti t. ^focus_opt_ld_forward C' gn ti t /\
  ALL_DISTINCT (MAP (\b. b.bb_label) gn.fn_blocks)``;

val focus_opt_ld_effect = ``\lo P C vs A f tn PG G inst s t u fuel ss H'.
  step_inst fuel C inst s = OK ss /\
  ld_vars P A (f with <|lf_src := ss; lf_tgt := u; lf_H := H';
    lf_tv := (step_taint inst s ss tn).t_var|>) /\
  ld_memory lo A (step_taint inst s ss tn) ss u /\
  ld_nonghost (step_taint inst s ss tn) ss u /\
  ld_ghost_ok (dyn_floor C vs) A H' (step_prov PG G inst ss) /\
  ld_dyn_agree (dyn_floor C vs) (step_taint inst s ss tn).t_mem ss.vs_memory u.vs_memory /\
  (!a. a IN FRANGE H' ==> a IN FDOM A) /\
  ss.vs_allocas = s.vs_allocas /\ u.vs_allocas = t.vs_allocas /\
  ss.vs_alloca_next = s.vs_alloca_next /\ u.vs_alloca_next = t.vs_alloca_next /\
  ss.vs_current_bb = s.vs_current_bb /\ u.vs_current_bb = t.vs_current_bb``;

val focus_opt_ld_advance = ``\lo P C C' vs Sigma names
                             stk PG G tn fn s A f fs N X p Ar g gn q ss j.
  ^focus_opt_ld_stable lo P Sigma names fs f A A (f::fs) /\
  g.lf_serial = f.lf_serial /\ g.lf_fn = f.lf_fn /\
  g.lf_supply = f.lf_supply /\ g.lf_Q = f.lf_Q /\
  (!a. a IN FDOM A ==> FLOOKUP Ar a = FLOOKUP A a) /\ ld_global lo Ar (g::fs) /\
  gn = ld_image f /\ gn = FST (lower_dload_function_supply f.lf_supply fn) /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\
  q.vs_current_bb = s.vs_current_bb /\ q.vs_inst_idx = p + LENGTH X /\
  ss.vs_current_bb = s.vs_current_bb /\ active_inst gn j q /\
  g.lf_src = (ss with vs_inst_idx := SUC s.vs_inst_idx) /\ g.lf_tgt = q /\
  ss.vs_gas_readings = q.vs_gas_readings /\
  LENGTH ss.vs_gas_readings <= LENGTH s.vs_gas_readings /\
  EVERY (\k. k.lf_src.vs_gas_readings = k.lf_tgt.vs_gas_readings /\
    LENGTH s.vs_gas_readings <= LENGTH k.lf_src.vs_gas_readings) fs /\
  (!ni. active_inst fn ni g.lf_src ==>
    ld_sync lo P C vs stk PG G tn fn ni g.lf_src g.lf_tgt Ar (g::fs) N) ==>
  ^focus_opt_ld_R lo P C C' vs Sigma names gn j q``;

val focus_opt_ld_advance_all = ``\lo P C C' vs Sigma names.
  !stk PG G tn fn s A f fs N X p Ar g gn q ss j.
    ^focus_opt_ld_advance lo P C C' vs Sigma names
      stk PG G tn fn s A f fs N X p Ar g gn q ss j``;

Theorem focus_opt_ld_head_row[local]:
  ld_sync lo P C vs stk PG G tn fn next s1 q A1 (g::fs) N /\
  ^focus_opt_ld_stable lo P Sigma names fs g A1 A1 (g::fs) /\
  gn = ld_image g /\ ld_envelope g.lf_supply fn s1 s1.vs_inst_idx Y q.vs_inst_idx /\
  0 < LENGTH Y /\ j = EL 0 Y /\ s1.vs_gas_readings = q.vs_gas_readings /\
  EVERY (\k. k.lf_src.vs_gas_readings = k.lf_tgt.vs_gas_readings /\
    LENGTH s1.vs_gas_readings <= LENGTH k.lf_src.vs_gas_readings) (g::fs) ==>
  ^focus_opt_ld_R lo P C C' vs Sigma names gn j q
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `active_inst gn (EL 0 Y) q` by
    (drule ld_sync_active >> simp[HD] >> strip_tac >>
     drule ld_sync_control >> strip_tac >>
     drule_at (Pat `ld_envelope _ _ _ _ _ _`)
       lowerDloadReturnInteriorTheory.ld_envelope_target_at >>
     disch_then (qspecl_then [`q`,`0`] mp_tac) >> simp[ld_image_def]) >>
  qexistsl [`stk`,`PG`,`G`,`tn`,`fn`,`next`,`s1`,`q`,`A1`,`g`,`fs`,`N`,
    `Y`,`q.vs_inst_idx`,`0`] >>
  simp[lowerDloadSafetyKernelTheory.ld_prefix_zero] >> metis_tac[]
QED

(* ALLOCA changes the allocation map only on a cache miss. *)
Theorem focus_opt_ld_alloca_cached[local]:
  ^focus_opt_ld_advance_all lo P C C' vs Sigma names /\
  ^focus_opt_ld_stable lo P Sigma names fs f A A (f::fs) /\
  ld_sync lo P C vs stk PG G tn fn inst s t A (f::fs) N /\
  o1_ctx_shape C /\ gn = ld_image f /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [out] /\
  MEM out (fn_ir_vars fn) /\ out IN fn_pv P fn /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (alloc_base,alloc_size) /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] t.vs_inst_idx /\
  step_inst fuel C' inst t = OK u /\
  active_inst gn j (u with vs_inst_idx := SUC t.vs_inst_idx) /\
  EVERY (\k. k.lf_src.vs_gas_readings = k.lf_tgt.vs_gas_readings /\
    LENGTH s.vs_gas_readings <= LENGTH k.lf_src.vs_gas_readings) fs ==>
  ^focus_opt_ld_R lo P C C' vs Sigma names gn j
    (u with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  disch_then (map_every (assume_tac o BETA_RULE) o CONJUNCTS) >>
  `ld_global lo A (f::fs)` by metis_tac[] >>
  `t.vs_inst_idx = t.vs_inst_idx` by simp[] >>
  drule_all lowerDloadSafetyAllocationTheory.ld_cached_alloca_endpoint >> strip_tac >>
  drule ld_sync_active >> simp[HD] >> strip_tac >>
  drule ld_sync_control >> strip_tac >>
  `u.vs_current_bb = s.vs_current_bb` by
    (qpat_assum `step_inst fuel C' inst t = OK u` mp_tac >>
     disch_then (mp_tac o MATCH_MP (cj 1 (REWRITE_RULE[GSYM AND_IMP_INTRO]
       venomInstPropsTheory.step_preserves_control_flow))) >> simp[is_terminator_def]) >>
  `ss.vs_current_bb = s.vs_current_bb /\ ss.vs_gas_readings = s.vs_gas_readings` by
    (qpat_assum `step_inst 0 C inst s = OK ss` mp_tac >>
     simp[lowerDloadSafetyAllocationTheory.ld_alloca_step, exec_alloca_def, update_var_def] >>
     rpt strip_tac >> qpat_assum `_ = ss` (SUBST1_TAC o SYM) >> simp[]) >>
  `ss.vs_gas_readings = u.vs_gas_readings` by
    (qpat_assum `ld_nonghost _ ss u` mp_tac >> simp[NoAsms, lowerDloadSafetyKernelTheory.ld_nonghost_def]) >>
  `g.lf_serial = f.lf_serial /\ g.lf_fn = f.lf_fn /\ g.lf_supply = f.lf_supply /\
   g.lf_Q = f.lf_Q /\ g.lf_src = (ss with vs_inst_idx := SUC s.vs_inst_idx) /\
   g.lf_tgt = (u with vs_inst_idx := SUC t.vs_inst_idx)` by
    (qpat_assum `g = _` SUBST1_TAC >> simp[NoAsms, ADD1]) >>
  `gn = FST (lower_dload_function_supply f.lf_supply fn)` by simp[ld_image_def] >>
  last_x_assum (qspecl_then
    [`stk`,`PG`,`step_prov PG G inst ss`,`step_taint inst s ss tn`,`fn`,`s`,
     `A`,`f`,`fs`,`N`,`[inst]`,`t.vs_inst_idx`,`A`,`g`,`gn`,
     `u with vs_inst_idx := SUC t.vs_inst_idx`,`ss`,`j`] mp_tac) >>
  (impl_tac >- (rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
    simp[NoAsms, GSYM ADD1] >>
    rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
    qpat_assum `ss.vs_gas_readings = s.vs_gas_readings` (rewrite_tac o single) >> simp[NoAsms])) >>
  simp[ld_image_def, CONJ_ASSOC]
QED

Theorem focus_opt_ld_alloca_fresh[local]:
  ^focus_opt_ld_advance_all lo P C C' vs Sigma names /\
  ^focus_opt_ld_stable lo P Sigma names fs f A A (f::fs) /\
  ld_sync lo P C vs stk PG G tn fn inst s t A (f::fs) N /\
  o1_ctx_shape C /\ lo <= vs.vs_alloca_next /\ gn = ld_image f /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [out] /\
  MEM out (fn_ir_vars fn) /\ out IN fn_pv P fn /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE /\ ir_supply_covers_fn f.lf_supply fn /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] t.vs_inst_idx /\
  step_inst fuel C' inst t = OK u /\
  s.vs_gas_readings = t.vs_gas_readings /\
  active_inst gn j (u with vs_inst_idx := SUC t.vs_inst_idx) /\
  EVERY (\k. k.lf_src.vs_gas_readings = k.lf_tgt.vs_gas_readings /\
    LENGTH s.vs_gas_readings <= LENGTH k.lf_src.vs_gas_readings) fs ==>
  ^focus_opt_ld_R lo P C C' vs Sigma names gn j
    (u with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  disch_then (map_every (assume_tac o BETA_RULE) o CONJUNCTS) >>
  `ld_global lo A (f::fs)` by metis_tac[] >>
  drule ld_sync_source >> strip_tac >>
  drule ld_sync_active >> simp[HD] >> strip_tac >>
  drule ld_sync_control >> strip_tac >>
  drule_all lowerDloadSafetyAllocationTheory.ld_sync_original_site_fresh >> strip_tac >>
  mp_tac (Q.INST [`s` |-> `s`, `t` |-> `t`, `fuel` |-> `fuel`,
    `ts` |-> `u`] lowerDloadSafetyAllocationTheory.ld_fresh_alloca_dispatch) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `sz` (qx_choose_then `ss` strip_assume_tac)) >>
  `step_inst 0 C inst s = OK ss` by
    (qpat_assum `step_inst fuel C inst s = OK ss` mp_tac >>
     simp[lowerDloadSafetyAllocationTheory.ld_alloca_step]) >>
  `ss.vs_current_bb = s.vs_current_bb /\ u.vs_current_bb = s.vs_current_bb /\
   ss.vs_memory = s.vs_memory /\ u.vs_memory = t.vs_memory /\
   ss.vs_gas_readings = s.vs_gas_readings /\ u.vs_gas_readings = t.vs_gas_readings` by
    (qpat_assum `ss = update_var _ _ _` SUBST1_TAC >>
     qpat_assum `u = update_var _ _ _` SUBST1_TAC >> simp[update_var_def]) >>
  `gn = FST (lower_dload_function_supply f.lf_supply fn)` by simp[ld_image_def] >>
  qabbrev_tac `sn = ss with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `q = u with vs_inst_idx := SUC t.vs_inst_idx` >>
  `q.vs_current_bb = s.vs_current_bb /\ q.vs_inst_idx = t.vs_inst_idx + LENGTH [inst]` by
    simp[Abbr `q`, ADD1] >>
  `?i Y. active_inst fn i sn /\ ld_envelope f.lf_supply fn sn sn.vs_inst_idx Y q.vs_inst_idx` by
    (`active_inst gn j q` by (simp[NoAsms, Abbr `q`] >> first_assum ACCEPT_TAC) >>
     drule_at (Pat `ld_envelope _ _ _ _ _ _`)
       lowerDloadSafetyLocationsTheory.ld_envelope_successor_head >>
     disch_then (qspecl_then [`j`,`ss`,`q`,`gn`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     qpat_assum `q.vs_inst_idx = _` SUBST1_TAC >>
     simp[NoAsms, Abbr `sn`] >> metis_tac[NoAsms]) >>
  `frame_reachable vs C stk PG (step_prov PG G inst ss) (step_taint inst s ss tn) fn i sn` by
    (simp[Abbr `sn`] >> irule frame_reachable_next >> simp[is_terminator_def] >> metis_tac[]) >>
  qabbrev_tac `Ar = A |+ ((f.lf_serial,inst.inst_id),(s.vs_alloca_next,t.vs_alloca_next,w2n sz))` >>
  qabbrev_tac `H' = f.lf_H |+ (out,(f.lf_serial,inst.inst_id))` >>
  qabbrev_tac `tn' = step_taint inst s ss tn` >>
  qabbrev_tac `g = f with <|lf_src := sn; lf_tgt := q; lf_H := H'; lf_tv := tn'.t_var|>` >>
  drule ld_sync_memory >> strip_tac >>
  drule ld_sync_ghosts >> simp[HD] >> strip_tac >>
  `FRANGE f.lf_H SUBSET FDOM A` by
    (simp[pred_setTheory.SUBSET_DEF] >> metis_tac[ld_global_selected, MEM]) >>
  `step_prov PG (ld_erase A o_f f.lf_H) inst ss = ld_erase Ar o_f H' /\
   ld_vars P Ar (f with <|lf_src := ss; lf_tgt := u; lf_H := H'; lf_tv := tn'.t_var|>) /\
   ld_memory lo Ar tn' ss u /\ ld_nonghost tn' ss u /\ FRANGE H' SUBSET FDOM Ar` by
    (`Ar = A |+ ((f.lf_serial,inst.inst_id),(s.vs_alloca_next,t.vs_alloca_next,w2n sz))` by
       simp[Abbr `Ar`] >>
     qpat_assum `f.lf_src = s` (SUBST_ALL_TAC o SYM) >>
     qpat_assum `f.lf_tgt = t` (SUBST_ALL_TAC o SYM) >>
     qpat_assum `f.lf_fn = fn` (SUBST_ALL_TAC o SYM) >>
     drule_all lowerDloadSafetyAllocationTheory.ld_fresh_alloca_effect >>
     disch_then (qspecl_then [`fuel`,`PG`,`C'`,`C`] strip_assume_tac) >>
     qpat_assum `Abbrev (H' = _)` (SUBST1_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
     qpat_assum `Abbrev (tn' = _)` (SUBST1_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ld_vars P Ar g /\ ld_memory lo Ar tn' sn q /\ ld_nonghost tn' sn q` by
    (conj_tac
     >- (qpat_assum `ld_vars P Ar _` mp_tac >>
         simp[NoAsms, Abbr `g`, Abbr `sn`, Abbr `q`, ld_vars_def]) >>
     conj_tac
     >- (qpat_assum `ld_memory lo Ar tn' ss u` mp_tac >>
         simp[NoAsms, Abbr `sn`, Abbr `q`, lowerDloadSafetyKernelTheory.ld_memory_def] >>
         strip_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `ld_nonghost tn' ss u` mp_tac >>
     simp[NoAsms, Abbr `sn`, Abbr `q`, lowerDloadSafetyKernelTheory.ld_nonghost_def] >>
     strip_tac >> rpt conj_tac >> metis_tac[]) >>
  `ld_ghost_ok (dyn_floor C vs) Ar H' (step_prov PG G inst ss)` by
    (`~MEM inst.inst_opcode [PARAM; ADD; SUB; ASSIGN]` by simp[] >>
     drule_all ld_ghost_ok_step_fixed >> simp[]) >>
  `ld_dyn_agree (dyn_floor C vs) tn'.t_mem sn.vs_memory q.vs_memory` by
    (simp[Abbr `sn`, Abbr `q`, Abbr `tn'`] >>
     `source_memory_write_ranges inst s = []` by simp[codegenRelTheory.source_memory_write_ranges_def] >>
     drule ld_sync_dyn_agree >> strip_tac >> drule_all ld_dyn_agree_unwritten >> simp[]) >>
  `lo <= s.vs_alloca_next /\ lo <= t.vs_alloca_next` by
    (`raw_reachable vs C fn inst s` by metis_tac[lowerDloadReachabilityTheory.ld_frame_reachable_raw] >>
     drule lowerDloadFrontierTheory.ld_raw_reachable_frontier >> strip_tac >>
     drule ld_sync_frontier >> decide_tac) >>
  `Ar = A |+ ((f.lf_serial,inst.inst_id),(s.vs_alloca_next,t.vs_alloca_next,w2n sz)) /\
   sn = ss with vs_inst_idx := SUC s.vs_inst_idx /\ q = u with vs_inst_idx := SUC t.vs_inst_idx /\
   g = f with <|lf_src := sn; lf_tgt := q; lf_H := H'; lf_tv := tn'.t_var|>` by
    simp[Abbr `Ar`, Abbr `sn`, Abbr `q`, Abbr `g`] >>
  `ld_sync lo P C vs stk PG (step_prov PG G inst ss) tn' fn i sn q Ar (g::fs) N /\
   ld_global lo Ar (g::fs)` by
    (drule_all (SRULE [PULL_EXISTS] lowerDloadSafetyAllocationTheory.ld_sync_fresh_alloca_update) >>
     qpat_assum `g = _` SUBST1_TAC >> qpat_assum `sn = _` SUBST1_TAC >>
     qpat_assum `q = _` SUBST1_TAC >> qpat_assum `Ar = _` SUBST1_TAC >>
     disch_then ACCEPT_TAC) >>
  `g.lf_serial = f.lf_serial /\ g.lf_fn = f.lf_fn /\ g.lf_supply = f.lf_supply /\
   g.lf_Q = f.lf_Q /\ g.lf_src = sn /\ g.lf_tgt = q` by
    (qpat_assum `g = _` SUBST1_TAC >> simp[NoAsms]) >>
  `!ni. active_inst fn ni g.lf_src ==>
    ld_sync lo P C vs stk PG (step_prov PG G inst ss) tn' fn ni g.lf_src g.lf_tgt Ar (g::fs) N` by
    (qpat_assum `g.lf_src = sn` SUBST1_TAC >> qpat_assum `g.lf_tgt = q` SUBST1_TAC >>
     rpt strip_tac >>
     `ni = i` by metis_tac[REWRITE_RULE[fn_labels_def] fmpStageBlockSimCodeTheory.active_inst_unique] >>
     qpat_assum `ni = i` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `!a. a IN FDOM A ==> FLOOKUP Ar a = FLOOKUP A a` by
    (qpat_assum `Ar = _` SUBST1_TAC >> simp[NoAsms, FLOOKUP_UPDATE] >> metis_tac[]) >>
  `ss.vs_gas_readings = q.vs_gas_readings` by
    (qpat_assum `q = _` SUBST1_TAC >> simp[NoAsms] >> metis_tac[]) >>
  `LENGTH ss.vs_gas_readings <= LENGTH s.vs_gas_readings` by
    (qpat_assum `ss.vs_gas_readings = s.vs_gas_readings` (rewrite_tac o single) >> simp[NoAsms]) >>
  `g.lf_src = (ss with vs_inst_idx := SUC s.vs_inst_idx)` by metis_tac[] >>
  qpat_assum `q = _` (SUBST1_TAC o SYM) >>
  qpat_x_assum `!stk PG G tn fn s A f fs N X p Ar g gn q ss j. _`
    (qspecl_then [`stk`,`PG`,`step_prov PG G inst ss`,`tn'`,`fn`,`s`,`A`,`f`,
      `fs`,`N`,`[inst]`,`t.vs_inst_idx`,`Ar`,`g`,`gn`,`q`,`ss`,`j`] mp_tac) >>
  (impl_tac >- (rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
    simp[NoAsms, GSYM ADD1] >>
    rpt (first_assum ACCEPT_TAC ORELSE conj_tac))) >>
  `q.vs_gas_readings = t.vs_gas_readings` by metis_tac[] >>
  qpat_assum `gn = ld_image f` (fn image =>
    qpat_assum `q.vs_gas_readings = t.vs_gas_readings` (fn gas =>
      simp[NoAsms, image, gas, CONJ_ASSOC]))
QED

Theorem focus_opt_ld_alloca_next[local]:
  ^focus_opt_ld_advance_all lo P C C' vs Sigma names /\
  o1_ctx_shape C /\ lo <= vs.vs_alloca_next /\
  ^focus_opt_ld_row lo P C C' vs Sigma names gn inst t
    stk PG G tn fn inst s t A f fs N [inst] t.vs_inst_idx 0 /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  inst_wf inst /\ ir_supply_covers_fn f.lf_supply fn /\
  inst.inst_opcode = ALLOCA /\ step_inst fuel C' inst t = OK u /\
  active_inst gn j (u with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ^focus_opt_ld_R lo P C C' vs Sigma names gn j
    (u with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  disch_then (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
  qpat_assum `EVERY _ (f::fs)` (strip_assume_tac o REWRITE_RULE[EVERY_DEF]) >>
  drule ld_sync_source >> strip_tac >>
  `?out. inst.inst_outputs = [out]` by
    fs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
  drule allocaFrontierBoundTheory.active_inst_mem_fn_insts >> strip_tac >>
  `MEM out (fn_ir_vars fn)` by
    (irule lowerDloadSafetyUpdatesTheory.ld_inst_output_ir >> qexists `inst` >> simp[]) >>
  `out IN fn_pv P fn` by
    (mp_tac (Q.INST [`fn` |-> `fn`] o1LowerDloadClosureTheory.ptr_roots_subset_fn_pv) >>
     simp[pred_setTheory.SUBSET_DEF, ptr_roots_def, pointerConfinedDefsTheory.alloca_roots_def] >>
     disch_then irule >> disj1_tac >> disj1_tac >> qexists `inst` >> simp[inst_output_def]) >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id` >-
    (drule_all (BETA_RULE focus_opt_ld_alloca_fresh) >> simp[CONJ_ASSOC]) >>
  rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME allocation` >>
  PairCases_on `allocation` >> drule_all (BETA_RULE focus_opt_ld_alloca_cached) >> simp[CONJ_ASSOC]
QED

Theorem focus_opt_ld_advance_row[local]:
  ^focus_opt_ld_advance lo P C C' vs Sigma names
    stk PG G tn fn s A f fs N X p Ar g gn q ss j
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `^focus_opt_ld_stable lo P Sigma names fs g Ar Ar (g::fs)` by
    (drule_all (BETA_RULE lowerDloadReturnStableTheory.ld_stable_head_extend) >>
     simp[] >> strip_tac >> metis_tac[]) >>
  drule_all lowerDloadSafetyLocationsTheory.ld_envelope_successor_head >>
  strip_tac >>
  `active_inst fn next g.lf_src` by simp[] >>
  `ld_sync lo P C vs stk PG G tn fn next g.lf_src q Ar (g::fs) N` by
    (qpat_assum `!ni. active_inst fn ni g.lf_src ==> _`
       (qspec_then `next` mp_tac) >> gvs[]) >>
  `EVERY (\k. k.lf_src.vs_gas_readings = k.lf_tgt.vs_gas_readings /\
    LENGTH g.lf_src.vs_gas_readings <= LENGTH k.lf_src.vs_gas_readings) (g::fs)` by
    (simp[] >> fs[EVERY_MEM] >> metis_tac[LESS_EQ_TRANS]) >>
  `ld_envelope g.lf_supply fn g.lf_src g.lf_src.vs_inst_idx Y q.vs_inst_idx` by gvs[] >>
  irule (BETA_RULE focus_opt_ld_head_row) >>
  goal_assum (drule_at (Pat `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `ld_envelope _ _ _ _ _ _`)) >>
  gvs[ld_image_def] >> metis_tac[]
QED

(* The ordinary effect keeps the allocation map and takes only the given
   step. An active target successor supplies the next source location. *)
Theorem focus_opt_ld_effect_row[local]:
  ld_sync lo P C vs stk PG G tn fn inst s t A (f::fs) N /\
  ^focus_opt_ld_stable lo P Sigma names fs f A A (f::fs) /\
  o1_ctx_shape C /\ ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  gn = ld_image f /\ gn = FST (lower_dload_function_supply f.lf_supply fn) /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] t.vs_inst_idx /\
  step_inst fuel C' inst t = OK u /\
  active_inst gn j (u with vs_inst_idx := SUC t.vs_inst_idx) /\
  ^focus_opt_ld_effect lo P C vs A f tn PG G inst s t u fuel ss H' /\
  ss.vs_prev_bb = s.vs_prev_bb /\ u.vs_prev_bb = t.vs_prev_bb /\
  s.vs_gas_readings = t.vs_gas_readings /\
  EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
    LENGTH s.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) fs ==>
  ^focus_opt_ld_R lo P C C' vs Sigma names gn j
    (u with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `q = u with vs_inst_idx := SUC t.vs_inst_idx` >>
  qabbrev_tac `s1 = ss with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `g = f with <|lf_src := s1; lf_tgt := q; lf_H := H';
    lf_tv := (step_taint inst s ss tn).t_var|>` >>
  drule ld_sync_active >> simp[HD] >> strip_tac >>
  drule ld_sync_control >> strip_tac >>
  `q.vs_current_bb = s.vs_current_bb /\
   q.vs_inst_idx = t.vs_inst_idx + LENGTH [inst]` by simp[Abbr `q`, ADD1] >>
  `?next Y. active_inst fn next s1 /\
    ld_envelope f.lf_supply fn s1 (SUC s.vs_inst_idx) Y (SUC t.vs_inst_idx)` by
    (drule_at (Pat `ld_envelope _ _ _ _ _ _`)
       lowerDloadSafetyLocationsTheory.ld_envelope_successor_head >>
     disch_then (qspecl_then [`j`,`ss`,`q`,`gn`] mp_tac) >>
     simp[Abbr `s1`, ADD1, Excl "EL"] >> metis_tac[]) >>
  `ld_vars P A g` by
    (qabbrev_tac `g0 = f with <|lf_src := ss; lf_tgt := u; lf_H := H';
        lf_tv := (step_taint inst s ss tn).t_var|>` >>
     `g = g0 with <|lf_src := g0.lf_src with vs_inst_idx := SUC s.vs_inst_idx;
                    lf_tgt := g0.lf_tgt with vs_inst_idx := SUC t.vs_inst_idx|>` by
       simp[Abbr `g`, Abbr `g0`, Abbr `s1`, Abbr `q`] >>
     simp[lowerDloadSafetyAdvanceTheory.ld_vars_inst_indices]) >>
  `ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst s ss tn)
     fn next s1 q A (g::fs) N /\ ld_global lo A (g::fs)` by
    (drule lowerDloadSafetyAdvanceTheory.ld_sync_ordinary_advance >>
     metis_tac[markerTheory.Abbrev_def]) >>
  `ss.vs_gas_readings = q.vs_gas_readings` by fs[lowerDloadSafetyKernelTheory.ld_nonghost_def, Abbr `q`] >>
  `LENGTH ss.vs_gas_readings <= LENGTH s.vs_gas_readings` by
    (qspecl_then [`fuel`,`C`,`inst`,`s`] mp_tac
       (CONJUNCT1 gasCountTheory.gas_count_suffix) >>
     simp[gasCountTheory.gas_count_suffix_def, LENGTH_DROP]) >>
  `!ni. active_inst fn ni g.lf_src ==>
    ld_sync lo P C vs stk PG (step_prov PG G inst ss) (step_taint inst s ss tn)
      fn ni g.lf_src g.lf_tgt A (g::fs) N` by
    (simp[Abbr `g`] >> rpt strip_tac >>
     `ni = next` by metis_tac[REWRITE_RULE[venomInstTheory.fn_labels_def]
       fmpStageBlockSimCodeTheory.active_inst_unique] >> simp[]) >>
  `^focus_opt_ld_R lo P C C' vs Sigma names gn j q` by
    (BETA_TAC >> irule (BETA_RULE focus_opt_ld_advance_row) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl [`A`,`A`,`step_prov PG G inst ss`,`N`,`PG`,`[inst]`,
               `f`,`fn`,`fs`,`g`,`t.vs_inst_idx`,`s`,`ss`,`stk`,`step_taint inst s ss tn`] >>
     simp[Abbr `g`, Abbr `s1`] >> metis_tac[]) >>
  pop_assum (mp_tac o BETA_RULE) >> simp[CONJ_ASSOC]
QED

(* These suppliers advance the actual next fetch, including a GAS read
   whose remaining oracle may be shorter than the current row's. *)
Theorem focus_opt_ld_simple_next[local]:
  ^focus_opt_ld_row lo P C C' vs Sigma names gn ti t
    stk PG G tn fn inst s t0 A f fs N [inst] p h /\
  ALL_DISTINCT (fn_labels gn) /\
  o1_ctx_shape C /\ o1_safe_upto D lo n C vs /\
  (MEM inst.inst_opcode
     [CALLER;ADDRESS;CALLVALUE;GAS;ORIGIN;GASPRICE;CHAINID;COINBASE;
      TIMESTAMP;NUMBER;PREVRANDAO;GASLIMIT;BASEFEE;BLOBBASEFEE;
      CALLDATASIZE;RETURNDATASIZE;CODESIZE] \/
   (MEM inst.inst_opcode
      [MUL;Div;Mod;SDIV;SMOD;Exp;ADDMOD;MULMOD;SLT;SGT;ISZERO;AND;OR;XOR;
       NOT;SIGNEXTEND;BYTE;OFFSET;ADD;SUB;SHL;SHR;SAR] \/
    MEM inst.inst_opcode [ASSIGN;RETPC_PARAM;PARAM]) \/
   MEM inst.inst_opcode [LOG;SSTORE;TSTORE]) /\
  step_inst fuel C' ti t = OK u /\
  active_inst gn j (u with vs_inst_idx := SUC t.vs_inst_idx) /\
  gas_cut n vs (u with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ^focus_opt_ld_R lo P C C' vs Sigma names gn j
    (u with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `h = 0` by fs[] >> qpat_x_assum `h = 0` SUBST_ALL_TAC >>
  qpat_x_assum `ld_prefix _ _ _ _ 0 _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [lowerDloadSafetyKernelTheory.ld_prefix_zero]) >>
  `ti = inst` by fs[] >>
  qpat_x_assum `ti = inst` SUBST_ALL_TAC >>
  qpat_x_assum `t = t0` (SUBST_ALL_TAC o SYM) >>
  `?bb. lookup_block t.vs_current_bb (ld_image f).fn_blocks = SOME bb /\
        get_instruction bb t.vs_inst_idx = SOME inst` by
    (irule lowerDloadPtrRawReachableTheory.active_inst_block_lookup >> metis_tac[]) >>
  `active_inst (ld_image f) j (u with vs_inst_idx := SUC t.vs_inst_idx)` by metis_tac[] >>
  qpat_x_assum `_ \/ _ \/ _` mp_tac >>
  disch_then (DISJ_CASES_THEN2 assume_tac (DISJ_CASES_THEN assume_tac)) >>
  MAP_FIRST (drule_all o BETA_RULE o REWRITE_RULE [LET_THM])
    [gasFocusLowerDloadEnvironmentPointTheory.ld_focus_environment_point_next,
     gasFocusLowerDloadArithmeticBindingPointTheory.ld_focus_arithmetic_binding_point_next,
     gasFocusLowerDloadLogStorePointTheory.ld_focus_log_store_point_next] >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  `gn = ld_image g` by (qpat_assum `g = _` (rewrite_tac o single) >> simp[ld_image_def]) >>
  irule (BETA_RULE focus_opt_ld_head_row) >>
  goal_assum (drule_at (Pat `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `ld_envelope _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED

(* The residual singleton cases use the current cut only. *)
Theorem focus_opt_ld_data_next[local]:
  ^focus_opt_ld_row lo P C C' vs Sigma names gn ti t
    stk PG G tn fn inst s t0 A f fs N [inst] p h /\
  o1_ctx_shape C /\ pre_fmp_ops fn /\ o1_safe_upto D lo n C vs /\
  ~in_revert_forward fn s /\
  (MEM inst.inst_opcode [BLOCKHASH;BLOBHASH;CALLDATALOAD;BALANCE;
                         SELFBALANCE;EXTCODESIZE;EXTCODEHASH;SLOAD;TLOAD] \/
   MEM inst.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE;ISTORE;SHA3;INITIAL_FMP;BUMP]) /\
  step_inst fuel C' ti t = OK u /\
  active_inst gn j (u with vs_inst_idx := SUC t.vs_inst_idx) /\
  gas_cut n vs (u with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ^focus_opt_ld_R lo P C C' vs Sigma names gn j
    (u with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `h = 0` by fs[] >> qpat_x_assum `h = 0` SUBST_ALL_TAC >>
  qpat_x_assum `ld_prefix _ _ _ _ 0 _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [lowerDloadSafetyKernelTheory.ld_prefix_zero]) >>
  `ti = inst` by fs[] >> qpat_x_assum `ti = inst` SUBST_ALL_TAC >>
  qpat_x_assum `t = t0` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `t.vs_inst_idx = p` (SUBST_ALL_TAC o SYM) >>
  drule ld_sync_active >> simp[HD, Excl "MEM"] >> strip_tac >>
  drule ld_sync_source >> strip_tac >>
  drule_all ld_sync_fn_shape >> disch_then (strip_assume_tac o MATCH_MP o1_fn_shape_components) >>
  drule ld_sync_memory >> strip_tac >>
  drule ld_sync_ghosts >> simp[HD, Excl "MEM"] >> strip_tac >>
  drule ld_sync_dyn_agree >> strip_tac >>
  `MEM inst (fn_insts fn)` by metis_tac[ld_active_inst_member] >>
  `inst_wf inst` by metis_tac[fmpStepStructuralTheory.fn_inst_wf_fn_insts, EVERY_MEM] >>
  `tn.t_var = f.lf_tv` by metis_tac[] >>
  `fn_ptr_ok P fn /\ s.vs_labels = t.vs_labels` by metis_tac[ld_sync_ptr_ok, ld_sync_labels] >>
  `gn = FST (lower_dload_function_supply f.lf_supply fn)` by fs[ld_image_def] >>
  `ld_global lo A (f::fs)` by simp[] >>
  `!a. a IN FRANGE f.lf_H ==> a IN FDOM A` by metis_tac[ld_global_selected, MEM] >>
  `EVERY (\a. a.lf_src.vs_gas_readings = a.lf_tgt.vs_gas_readings /\
    LENGTH s.vs_gas_readings <= LENGTH a.lf_src.vs_gas_readings) fs` by fs[EVERY_DEF] >>
  `pre_fmp_opcode inst.inst_opcode` by fs[pre_fmp_ops_def, EVERY_MEM] >>
  `MEM inst.inst_opcode [BLOCKHASH;BLOBHASH;CALLDATALOAD;BALANCE;SELFBALANCE;
      EXTCODESIZE;EXTCODEHASH;SLOAD;TLOAD;NOP;ASSERT;ASSERT_UNREACHABLE;ISTORE;SHA3]` by
    (qpat_assum `_ \/ _` mp_tac >> qpat_assum `pre_fmp_opcode _` mp_tac >>
     simp[NoAsms, pre_fmp_opcode_def, MEM] >> metis_tac[NoAsms]) >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    (qpat_assum `MEM inst.inst_opcode (BLOCKHASH::_)` mp_tac >>
     pure_rewrite_tac[MEM] >> strip_tac >> simp[is_terminator_def]) >>
  `step_inst_base inst t = OK u` by fs[step_inst_non_invoke] >>
  `gas_cut n vs s` by
    (irule gas_cut_readings_mono >>
     qexists_tac `u with vs_inst_idx := SUC t.vs_inst_idx` >> simp[] >>
     qspecl_then [`fuel`,`C'`,`inst`,`t`] mp_tac (CONJUNCT1 gas_count_suffix) >>
     simp[gas_count_suffix_def, LENGTH_DROP]) >>
  `lo <= vs.vs_alloca_next /\ access_ok lo G fn inst s /\ taint_ok fn tn inst s` by
    (qpat_assum `o1_safe_upto _ _ _ _ _` (strip_assume_tac o
       REWRITE_RULE[o1_safe_upto_def, o1_ptr_safe_upto_def]) >>
     drule_all ptr_discipline_upto_at >> simp[] >> fs[ptr_discipline_upto_def]) >>
  Cases_on `MEM inst.inst_opcode [NOP;ASSERT;ASSERT_UNREACHABLE]`
  >- suspend "identity" >>
  `mem_inv dload_headroom_ok C vs` by fs[o1_safe_upto_def] >>
  `dload_headroom_ok C fn inst s` by metis_tac[ld_sync_source_mem_inv] >>
  `t.vs_alloca_next < dimword (:256)` by metis_tac[ld_sync_target_headroom] >>
  drule ld_sync_slots >> strip_tac >> drule ld_sync_maps >> strip_tac >>
  `!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==>
     b+sz <= s.vs_alloca_next /\ c+sz <= t.vs_alloca_next` by
    (rpt gen_tac >> strip_tac >> drule_all ld_alloc_frontiers >> simp[HD]) >>
  `!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==> c+sz < dimword (:256)` by
    (rpt gen_tac >> strip_tac >> res_tac >> decide_tac) >>
  Cases_on `inst.inst_opcode = ISTORE`
  >- suspend "istore" >>
  suspend "read"
QED

local
  val finish_data_row =
    irule (CONV_RULE (RAND_CONV (SCONV [])) (BETA_RULE focus_opt_ld_effect_row)) >>
    rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE metis_tac[])) >>
    goal_assum (drule_at (Pat `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
    goal_assum (drule_at (Pat `ld_vars _ _ (_ with <|lf_src := _;lf_tgt := _;lf_H := _;lf_tv := _|>)`)) >>
    qexists_tac `fuel` >>
    rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[NoAsms]) >> gvs[]
in
  val focus_opt_ld_finish_data_row = finish_data_row
end

Resume focus_opt_ld_data_next[identity]:
  `inst.inst_outputs = []` by
    (qpat_assum `MEM inst.inst_opcode (NOP::_)` (strip_assume_tac o REWRITE_RULE[MEM]) >> fs[inst_wf_def]) >>
  `eval_operands inst.inst_operands s = eval_operands inst.inst_operands t` by
    (`!v. MEM (Var v) inst.inst_operands ==>
        MEM v (fn_ir_vars f.lf_fn) /\ v NOTIN fn_pv P f.lf_fn` by
       (qpat_assum `f.lf_fn = fn` SUBST1_TAC >> gen_tac >> strip_tac >> conj_tac
        >- metis_tac[ld_inst_input_ir] >>
        irule ld_ptr_use_scalar >> simp[Excl "MEM"] >> qexists_tac `inst` >>
        qpat_assum `MEM inst.inst_opcode (NOP::_)` (strip_assume_tac o REWRITE_RULE[MEM]) >>
        simp[mem_read_ops_def, mem_write_ops_def, is_pointer_preserving_op_def]) >>
     `~MEM inst.inst_opcode
       [ASSIGN;PHI;RET;RETFMP;DRET;MUL;SHL;SHR;SAR;MSTORE;SSTORE;TSTORE;ISTORE]` by
       (qpat_assum `MEM inst.inst_opcode (NOP::_)` (strip_assume_tac o REWRITE_RULE[MEM]) >> simp[]) >>
     map_every (fn pat => qpat_assum pat (SUBST_ALL_TAC o SYM))
       [`f.lf_fn = fn`,`f.lf_src = s`,`f.lf_tgt = t`] >>
     metis_tac[ld_vars_numeric_operands_equal]) >>
  `u = t /\ step_inst_base inst s = OK s` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`eval_operands inst.inst_operands s = _`,`MEM inst.inst_opcode (NOP::_)`,
        `step_inst_base inst t = OK u`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     disch_tac >> disch_then (strip_assume_tac o REWRITE_RULE[MEM]) >> disch_tac >>
     qpat_assum `step_inst_base inst t = OK u` mp_tac >>
     pure_once_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[opcode_case_def] >>
     simp[Once step_inst_base_def] >>
     Cases_on `inst.inst_operands` >> simp[] >>
     rename1 `h::rest` >> Cases_on `rest` >> simp[] >>
     gvs[eval_operands_def, AllCaseEqs()] >> simp[Once step_inst_base_def] >> gvs[AllCaseEqs()]) >>
  `step_taint inst s s tn = tn /\ step_prov PG G inst s = G` by
    (qpat_assum `inst.inst_outputs = []` mp_tac >>
     qpat_assum `MEM inst.inst_opcode (NOP::_)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     disch_then (strip_assume_tac o REWRITE_RULE[MEM]) >> disch_tac >>
     simp[step_prov_def, set_prov_def, step_taint_def, mem_taint_def,
          written_taint_def, new_site_bytes_def, step_writes_def,
          codegenRelTheory.source_memory_write_ranges_def, range_bytes_def, set_var_taint_def,
          store_taint_def, adopt_reset_def, imm_taint_def,
          taint_component_equality, FLOOKUP_DEF, DRESTRICT_UNIV, SF CONJ_ss] >>
     Cases_on `inst.inst_operands` >> simp[] >>
     Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
     Cases_on `t` >> simp[] >> pred_setLib.SET_TAC[]) >>
  `step_inst fuel C inst s = OK s` by simp[step_inst_non_invoke] >>
  `f with <|lf_src := s; lf_tgt := u; lf_H := f.lf_H; lf_tv := tn.t_var|> = f` by
    (qpat_assum `u = t` SUBST1_TAC >>
     map_every (fn pat => qpat_assum pat (SUBST1_TAC o SYM))
       [`f.lf_src = s`,`f.lf_tgt = t`,`f.lf_tv = tn.t_var`] >>
     simp[NoAsms, Once ld_frame_component_equality]) >>
  `ld_vars P A (f with <|lf_src := s; lf_tgt := u; lf_H := f.lf_H;
       lf_tv := (step_taint inst s s tn).t_var|>)` by
    (map_every (fn pat => qpat_assum pat SUBST1_TAC)
       [`step_taint inst s s tn = tn`,`f with <|lf_src := s; lf_tgt := u; lf_H := f.lf_H; lf_tv := tn.t_var|> = f`] >>
     first_assum ACCEPT_TAC) >>
  `ld_memory lo A (step_taint inst s s tn) s u /\
   ld_nonghost (step_taint inst s s tn) s u /\
   ld_ghost_ok (dyn_floor C vs) A f.lf_H (step_prov PG G inst s) /\
   ld_dyn_agree (dyn_floor C vs) (step_taint inst s s tn).t_mem s.vs_memory u.vs_memory /\
   u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next /\
   u.vs_current_bb = t.vs_current_bb /\ u.vs_prev_bb = t.vs_prev_bb` by
    (map_every (fn pat => qpat_assum pat SUBST1_TAC)
       [`u = t`, `step_taint inst s s tn = tn`, `step_prov PG G inst s = G`] >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE REFL_TAC)) >>
  focus_opt_ld_finish_data_row
QED

Resume focus_opt_ld_data_next[istore]:
  `raw_reachable vs C fn inst s` by metis_tac[lowerDloadPtrRawReachableTheory.frame_reachable_raw] >>
  drule_all ld_raw_dyn_headroom >> strip_tac >>
  drule ld_raw_reachable_frontier >> strip_tac >>
  drule ld_sync_frontier >> strip_tac >>
  `lo <= dyn_floor C vs /\ s.vs_alloca_next <= dyn_floor C vs /\
     t.vs_alloca_next <= dyn_floor C vs` by
    (qpat_assum `ld_charge _ <= _` mp_tac >> decide_tac) >>
  `!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==>
     b+sz <= dyn_floor C vs /\ c+sz <= dyn_floor C vs` by
    (rpt gen_tac >> strip_tac >> res_tac >> decide_tac) >>
  `?ss. step_inst_base inst s = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := u; lf_H := f.lf_H;
      lf_tv := (step_taint inst s ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst s ss tn) ss u /\
    ld_nonghost (step_taint inst s ss tn) ss u /\
    ld_dyn_agree (dyn_floor C vs) (step_taint inst s ss tn).t_mem ss.vs_memory u.vs_memory /\
    step_prov (MAP (OPTION_MAP (ld_erase A)) f.lf_Q) (ld_erase A o_f f.lf_H) inst ss =
      ld_erase A o_f f.lf_H /\
    ss.vs_allocas = s.vs_allocas /\ ss.vs_alloca_next = s.vs_alloca_next /\
    ss.vs_current_bb = s.vs_current_bb /\ ss.vs_prev_bb = s.vs_prev_bb /\
    u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next /\
    u.vs_current_bb = t.vs_current_bb /\ u.vs_prev_bb = t.vs_prev_bb` by
    (map_every (fn pat => qpat_assum pat (SUBST_ALL_TAC o SYM))
       [`f.lf_fn = fn`,`f.lf_src = s`,`f.lf_tgt = t`] >>
     `MEM inst.inst_opcode [MSTORE;MSTORE8;ISTORE]` by simp[] >>
     drule_all ld_write2_operands >> strip_tac >>
     rename1 `inst.inst_operands = [addr; value]` >>
     `!oper. MEM oper inst.inst_operands ==> op_prov f.lf_H oper = NONE` by
       (rpt strip_tac >> Cases_on `oper` >> simp[NoAsms, op_prov_def] >>
        irule ld_vars_unselected >> qexistsl [`A`,`P`] >>
        reverse conj_tac >- first_assum ACCEPT_TAC >>
        qpat_assum `fn_ptr_ok P f.lf_fn` mp_tac >> simp[NoAsms, fn_ptr_ok_def] >>
        metis_tac[]) >>
     `op_prov f.lf_H addr = NONE /\ op_prov f.lf_H value = NONE` by simp[] >>
     `word_agree_except (op_taint tn value) x y` by
       (irule ld_write_scalar_observation >> qexistsl [`A`,`P`,`f`,`inst`] >>
        map_every (fn pat => qpat_assum pat SUBST1_TAC)
          [`inst.inst_opcode = ISTORE`,`inst.inst_operands = [addr;value]`] >>
        simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     `op_taint tn addr = {}` by metis_tac[ld_write2_taint] >>
     `dst = dst'` by
       (irule (cj 1 ld_write_address_observation) >>
        qexistsl [`A`,`P`,`f`,`inst`,`addr`,`tn`] >>
        map_every (fn pat => qpat_assum pat SUBST1_TAC)
          [`inst.inst_opcode = ISTORE`,`inst.inst_operands = [addr;value]`] >>
        simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_x_assum `dst = dst'` (SUBST_ALL_TAC o SYM) >>
     `?ops. mem_write_ops inst = SOME ops /\ ops.iao_ofst = addr` by
       simp[mem_write_ops_def] >>
     `MEM (w2n dst,32) (source_memory_write_ranges inst f.lf_src)` by
       (map_every (fn pat => qpat_assum pat SUBST1_TAC)
          [`inst.inst_opcode = ISTORE`,`inst.inst_operands = [addr;value]`] >>
        simp[codegenRelTheory.source_memory_write_ranges_def, codegenRelTheory.fixed_source_write_range_def]) >>
     `0 < (32:num)` by simp[] >>
     `(op_prov f.lf_H ops.iao_ofst = NONE ==> dst = dst) /\
      (!k. op_prov f.lf_H ops.iao_ofst = SOME k ==> ld_wordrel A (SOME k) dst dst)` by simp[] >>
     (Q.SUBGOAL_THEN
       `w2n dst+32 <= lo \/
        (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
          w2n dst=b+delta /\ w2n dst=c+delta /\ delta+32 <= sz) \/
        dyn_floor C vs <= w2n dst` assume_tac
      >- (drule_all (Q.INST [`n` |-> `32`] (cj 2 ld_access_dyn_cases)) >> metis_tac[])) >>
     `op_taint tn value SUBSET {j | j < 32}` by metis_tac[ld_reachable_op_taint_width] >>
     drule_all ld_istore_effect >> disch_then (qx_choose_then `ss` strip_assume_tac) >>
     qexists_tac `ss` >> rpt conj_tac >>
     (first_assum ACCEPT_TAC ORELSE
       (qpat_assum `ld_vars P A (f with <|lf_src := ss; lf_tgt := u; lf_tv := _|>)`
          mp_tac >> simp[NoAsms, ld_vars_def]))) >>
  `step_inst fuel C inst s = OK ss` by simp[step_inst_non_invoke] >>
  drule_all ld_sync_ghost_step >> strip_tac >>
  focus_opt_ld_finish_data_row
QED

Resume focus_opt_ld_data_next[read]:
  `MEM inst.inst_opcode [BLOCKHASH;BLOBHASH;CALLDATALOAD;BALANCE;
      SELFBALANCE;EXTCODESIZE;EXTCODEHASH;SLOAD;TLOAD;SHA3]` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`MEM inst.inst_opcode [BLOCKHASH;BLOBHASH;CALLDATALOAD;BALANCE;
         SELFBALANCE;EXTCODESIZE;EXTCODEHASH;SLOAD;TLOAD;NOP;ASSERT;ASSERT_UNREACHABLE;ISTORE;SHA3]`,
        `~MEM inst.inst_opcode (NOP::_)`,`inst.inst_opcode <> ISTORE`] >>
     simp[NoAsms, MEM] >> metis_tac[NoAsms]) >>
  `?ss. step_inst_base inst s = OK ss /\
    ld_vars P A (f with <|lf_src := ss; lf_tgt := u;
      lf_H := set_prov f.lf_H inst.inst_outputs NONE;
      lf_tv := (step_taint inst s ss tn).t_var|>) /\
    ld_memory lo A (step_taint inst s ss tn) ss u /\
    ld_nonghost (step_taint inst s ss tn) ss u /\
    step_prov (MAP (OPTION_MAP (ld_erase A)) f.lf_Q) (ld_erase A o_f f.lf_H) inst ss =
      ld_erase A o_f set_prov f.lf_H inst.inst_outputs NONE /\
    ss.vs_allocas = s.vs_allocas /\ ss.vs_alloca_next = s.vs_alloca_next /\
    ss.vs_current_bb = s.vs_current_bb /\ ss.vs_prev_bb = s.vs_prev_bb /\
    u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next /\
    u.vs_current_bb = t.vs_current_bb /\ u.vs_prev_bb = t.vs_prev_bb` by
    (map_every (fn pat => qpat_assum pat (SUBST_ALL_TAC o SYM))
       [`f.lf_fn = fn`,`f.lf_src = s`,`f.lf_tgt = t`] >>
     let
       fun finish effect =
         drule_all effect >>
         disch_then (qspec_then `MAP (OPTION_MAP (ld_erase A)) f.lf_Q`
           (qx_choose_then `ss` strip_assume_tac)) >>
         qexists_tac `ss` >> rpt conj_tac >>
         FIRST [first_assum ACCEPT_TAC, sym_tac >> first_assum ACCEPT_TAC]
     in
       Cases_on `MEM inst.inst_opcode [BLOCKHASH;BLOBHASH;CALLDATALOAD]`
       >- finish ld_keyed_environment_read_effect >>
       Cases_on `MEM inst.inst_opcode [BALANCE;SELFBALANCE;EXTCODESIZE;EXTCODEHASH]`
       >- finish ld_account_read_effect >>
       Cases_on `MEM inst.inst_opcode [SLOAD;TLOAD]`
       >- finish ld_storage_read_effect >>
       `inst.inst_opcode = SHA3` by
         (map_every (fn pat => qpat_assum pat mp_tac)
            [`MEM inst.inst_opcode [BLOCKHASH;BLOBHASH;CALLDATALOAD;BALANCE;
                SELFBALANCE;EXTCODESIZE;EXTCODEHASH;SLOAD;TLOAD;SHA3]`,
             `~MEM inst.inst_opcode (BLOCKHASH::_)`,`~MEM inst.inst_opcode (BALANCE::_)`,
             `~MEM inst.inst_opcode (SLOAD::_)`] >>
          simp[NoAsms, MEM] >> metis_tac[NoAsms]) >>
       drule_all ld_sha3_operands >> strip_tac >> finish ld_sha3_effect
     end) >>
  `step_inst fuel C inst s = OK ss` by simp[step_inst_non_invoke] >>
  drule_all ld_sync_ghost_step >> strip_tac >>
  `!a. a IN FRANGE (set_prov f.lf_H inst.inst_outputs NONE) ==> a IN FDOM A` by
    (rpt strip_tac >>
     drule (SRULE [pred_setTheory.SUBSET_DEF]
       (Q.INST [`q` |-> `NONE`] ld_set_prov_range)) >> simp[] >> metis_tac[]) >>
  `~is_alloca_op inst.inst_opcode /\ Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
   source_memory_write_ranges inst s = []` by
    (qpat_assum `MEM inst.inst_opcode (BLOCKHASH::_)` mp_tac >>
     pure_rewrite_tac[MEM] >> strip_tac >>
     qpat_assum `inst.inst_opcode = _` (fn eq =>
       simp[NoAsms, eq, is_alloca_op_def, write_effects_def, empty_effects_def,
            codegenRelTheory.source_memory_write_ranges_def])) >>
  drule_all ld_sync_dyn_agree_unwritten >> strip_tac >>
  focus_opt_ld_finish_data_row
QED

Finalise focus_opt_ld_data_next[local]

(* The synchronized frame accounts for the extra LowerDload allocation
   slots within the source instruction's reserved headroom. *)
Theorem focus_opt_ld_access_headroom[local]:
  ld_sync lo P C vs stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\
  mem_inv dload_headroom_ok C vs /\ lo <= vs.vs_alloca_next /\
  raw_reachable vs C fn inst s ==>
  lo <= dyn_floor C vs /\
  (!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==>
     b+sz <= dyn_floor C vs /\ c+sz <= dyn_floor C vs /\ c+sz < dimword(:256))
Proof
  strip_tac >>
  drule_all lowerDloadDynHeadroomTheory.ld_raw_dyn_headroom >> strip_tac >>
  drule lowerDloadFrontierTheory.ld_raw_reachable_frontier >> strip_tac >>
  drule ld_sync_frontier >> strip_tac >>
  `t.vs_alloca_next <= dyn_floor C vs` by decide_tac >>
  `dload_headroom_ok C fn inst s` by
    (drule_all ld_sync_source_mem_inv >> simp[]) >>
  `t.vs_alloca_next < dimword(:256)` by
    (drule_all ld_sync_target_headroom >> simp[]) >>
  `lo <= dyn_floor C vs` by decide_tac >> simp[] >>
  drule lowerDloadOracleCallAssemblyTheory.ld_sync_slots >> strip_tac >>
  drule lowerDloadOracleCallAssemblyTheory.ld_sync_maps >> strip_tac >>
  drule ld_sync_active >> simp[HD] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  drule_all lowerDloadSafetyAllocBoundsTheory.ld_alloc_frontiers >>
  simp[] >> decide_tac
QED

(* Point effects for the singleton access opcodes, using only safety up to
   this point and the successful step that has already been taken. *)
Theorem focus_opt_ld_access_effect[local]:
  ld_sync lo P C vs stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ o1_safe_upto D lo n C vs /\
  ~in_revert_forward fn s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ s.vs_gas_readings = t.vs_gas_readings /\
  gas_cut n vs t /\ step_inst fuel C' inst t = OK u /\
  (MEM inst.inst_opcode [MLOAD;ILOAD;LT;GT;EQ] \/
   MEM inst.inst_opcode [MSTORE;MSTORE8;MCOPY] \/
   MEM inst.inst_opcode [CODECOPY;CALLDATACOPY;RETURNDATACOPY;EXTCODECOPY] \/
   inst.inst_opcode = DALLOCA) ==>
  ?ss H'. ^focus_opt_ld_effect lo P C vs A f tn PG G inst s t u fuel ss H' /\
    ss.vs_prev_bb = s.vs_prev_bb /\ u.vs_prev_bb = t.vs_prev_bb
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ld_sync_source >> strip_tac >>
  `gas_cut n vs s` by fs[gas_cut_def] >>
  `raw_reachable vs C fn inst s` by
    (drule_all lowerDloadReachabilityTheory.ld_frame_reachable_raw >> simp[]) >>
  qpat_assum `o1_safe_upto _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[o1_safe_upto_def, o1_ptr_safe_upto_def]) >>
  drule_all concretizeLayoutCutSafeTheory.ptr_discipline_upto_at >> strip_tac >>
  `lo <= vs.vs_alloca_next` by fs[ptr_discipline_upto_def] >>
  drule_all focus_opt_ld_access_headroom >> strip_tac >>
  qpat_x_assum `MEM inst.inst_opcode [MLOAD;ILOAD;LT;GT;EQ] \/ _` strip_assume_tac
  >- (`MEM inst.inst_opcode [MLOAD;ILOAD] ==> ~in_revert_forward fn s` by simp[] >>
      `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> b+sz <= dyn_floor C vs` by metis_tac[] >>
      `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256)` by metis_tac[] >>
      drule_all lowerDloadClassifiedReadPointEffectTheory.ld_sync_classified_read_effect_at >>
      disch_then (qx_choosel_then [`ss`,`H'`] (map_every assume_tac o CONJUNCTS)) >>
      drule_all ld_sync_ghost_step >> strip_tac >>
      `~is_alloca_op inst.inst_opcode /\ Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
       source_memory_write_ranges inst s = []` by
        (qpat_assum `MEM inst.inst_opcode [MLOAD;ILOAD;LT;GT;EQ]` mp_tac >>
         pure_rewrite_tac[MEM] >> strip_tac >>
         qpat_assum `inst.inst_opcode = _` (fn eq =>
           simp[NoAsms, eq, is_alloca_op_def, venomEffectsTheory.write_effects_def,
                venomEffectsTheory.empty_effects_def, codegenRelTheory.source_memory_write_ranges_def])) >>
      drule_all ld_sync_dyn_agree_unwritten >> strip_tac >>
      qexistsl [`ss`,`H'`] >> simp[])
  >- (`fn_shape_ok fn /\ fn_inst_wf fn` by
        (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
      `s.vs_labels = t.vs_labels` by metis_tac[ld_sync_labels] >>
      drule ld_sync_active >> simp[HD] >> strip_tac >>
      drule_all lowerDloadMemoryWritePointEffectTheory.ld_sync_memory_write_effect_at >>
      disch_then (qx_choose_then `ss` (map_every assume_tac o CONJUNCTS)) >>
      `ld_ghost_ok (dyn_floor C vs) A f.lf_H (step_prov PG G inst ss)` by
        (qpat_assum `step_prov PG G inst ss = G` (rewrite_tac o single) >>
         drule ld_sync_ghosts >> simp[HD]) >>
      qexistsl [`ss`,`f.lf_H`] >> simp[] >>
      qpat_assum `ld_vars P A _` mp_tac >> simp[NoAsms, ld_vars_def])
  >- (`!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==>
          b+sz <= dyn_floor C vs /\ c+sz <= dyn_floor C vs` by metis_tac[] >>
      `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256)` by metis_tac[] >>
      drule_all lowerDloadPublicCopyPointEffectTheory.ld_sync_public_copy_effect_at >>
      disch_then (qx_choosel_then [`ss`,`H'`] (map_every assume_tac o CONJUNCTS)) >>
      drule_all ld_sync_ghost_step >> strip_tac >>
      qexistsl [`ss`,`H'`] >> simp[]) >>
  `ctx_has_dalloca C` by
    (simp[NoAsms, ctx_has_dalloca_def, EXISTS_MEM] >>
     metis_tac[lowerDloadOracleCallAssemblyTheory.ld_active_inst_member,
               frameAllocationOwnershipTheory.frame_reachable_functions_member]) >>
  `w2n vs.vs_initial_fmp <= w2n s.vs_fmp` by
    (drule ptrDisciplineEmptyTaintTheory.frame_reachable_initial_fmp >> strip_tac >>
     fs[allocas_below_fmp_def]) >>
  drule_all lowerDloadOrdinaryEndpointTheory.ld_sync_dalloca_effect_at >>
  simp[CONJ_ASSOC]
QED

Theorem focus_opt_ld_block_row[local]:
  ^focus_opt_ld_R lo P C C' vs Sigma names gn ti t /\
  o1_ctx_shape C /\ o1_initial_state_ok vs /\
  vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  callee_first names C.ctx_functions /\
  (!f. MEM f C.ctx_functions ==>
    ir_supply_covers_fn (Sigma f.fn_name) f /\
    lookup_function f.fn_name C'.ctx_functions =
      SOME (FST (lower_dload_function_supply (Sigma f.fn_name) f))) /\
  o1_safe_upto D lo n C vs /\ gas_cut n vs t /\
  is_terminator ti.inst_opcode /\ step_inst fuel C' ti t = OK u /\
  ~u.vs_halted /\ enters_block gn u tp /\ active_inst gn j tp ==>
  ^focus_opt_ld_R lo P C C' vs Sigma names gn j tp
Proof
  BETA_TAC >> disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (drule_all lowerDloadSafetyAmbientTheory.ld_sync_fn_shape >> strip_tac >>
     drule o1_fn_shape_components >> simp[]) >>
  drule ld_sync_source >> strip_tac >>
  `inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES` by
    (conj_tac >> strip_tac >>
     `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
       simp[is_terminator_def] >>
     drule_all lowerDloadEnvelopeControlTheory.ld_envelope_nonterminal >> strip_tac >>
     fs[EVERY_EL] >> metis_tac[]) >>
  drule_all lowerDloadSafetyLocationsTheory.ld_envelope_ordinary >> strip_tac >>
  `h = 0` by fs[] >>
  `t0 = t /\ ti = inst` by fs[lowerDloadSafetyKernelTheory.ld_prefix_zero] >>
  qpat_x_assum `t0 = t` SUBST_ALL_TAC >>
  qpat_x_assum `ti = inst` SUBST_ALL_TAC >>
  drule_all o1LowerDloadRunnerBoundaryTheory.ld_terminator_ok_branch >> strip_tac >>
  `gas_cut n vs s` by fs[gas_cut_def] >>
  `raw_reachable vs C fn inst s` by
    (irule lowerDloadReachabilityTheory.ld_frame_reachable_raw >> metis_tac[]) >>
  qpat_assum `o1_safe_upto _ _ _ _ _` (strip_assume_tac o REWRITE_RULE[o1_safe_upto_def]) >>
  `raw_mem_ok C fn inst s /\ dload_offset_ok C fn inst s` by metis_tac[] >>
  qpat_x_assum `o1_ptr_safe_upto _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[o1_ptr_safe_upto_def, ptr_discipline_upto_def]) >>
  `taint_ok fn tn inst s` by metis_tac[] >>
  `gn = FST (lower_dload_function_supply (Sigma fn.fn_name) fn)` by
    (drule ld_sync_head >> strip_tac >> fs[ld_image_def]) >>
  `!k. MEM k C.ctx_functions ==> ir_supply_covers_fn (Sigma k.fn_name) k` by metis_tac[] >>
  `!k. MEM k C.ctx_functions ==>
    lookup_function k.fn_name C'.ctx_functions =
      SOME (FST (lower_dload_function_supply (Sigma k.fn_name) k))` by metis_tac[] >>
  drule_all (BETA_RULE gasFocusLowerDloadControlEntryTheory.ld_focus_control_entry) >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  irule (BETA_RULE focus_opt_ld_head_row) >>
  goal_assum (drule_at (Pat `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `ld_envelope _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[lowerDloadSafetyKernelTheory.ld_prefix_bound]
QED

(* A successful raw expansion step needs no successful suffix. *)
Theorem focus_opt_ld_expansion_next[local]:
  ^focus_opt_ld_row lo P C C' vs Sigma names gn ti t
    stk PG G tn fn inst s t0 A f fs N X p h /\
  o1_ctx_shape C /\ o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\
  code_layout_valid vs /\ o1_safe_upto D lo n C vs /\ gas_cut n vs t /\
  ir_supply_covers_fn f.lf_supply fn /\
  ~is_terminator ti.inst_opcode /\ ti.inst_opcode <> INVOKE /\
  step_inst fuel C' ti t = OK u /\
  active_inst gn j (u with vs_inst_idx := SUC t.vs_inst_idx) /\
  (SUC h < LENGTH X \/
   (SUC h = LENGTH X /\ ~in_revert_forward fn s /\
    (inst.inst_opcode = DLOAD \/ inst.inst_opcode = DLOADBYTES) /\
    ^focus_opt_ld_advance_all lo P C C' vs Sigma names)) ==>
  ^focus_opt_ld_R lo P C C' vs Sigma names gn j
    (u with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `q = u with vs_inst_idx := SUC t.vs_inst_idx` >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  drule ld_sync_source >> strip_tac >>
  `gn = FST (lower_dload_function_supply f.lf_supply fn)` by
    (drule ld_sync_active >> fs[ld_image_def]) >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    metis_tac[lowerDloadReturnInteriorTheory.ld_envelope_source_nonterminal] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) X` by
    (drule_all lowerDloadEnvelopeControlTheory.ld_envelope_nonterminal >> simp[EVERY_MEM]) >>
  `q.vs_current_bb = s.vs_current_bb` by
    (simp[Abbr `q`] >> metis_tac[lowerDloadEnvelopeControlTheory.ld_prefix_control,
       ld_sync_control, venomInstPropsTheory.step_preserves_control_flow]) >>
  `t.vs_inst_idx = p + h` by metis_tac[lowerDloadSafetyKernelTheory.ld_prefix_position] >>
  qpat_x_assum `SUC h < LENGTH X \/ _`
    (DISJ_CASES_THEN2 assume_tac (map_every assume_tac o CONJUNCTS))
  >- suspend "interior" >>
  `gas_cut n vs s` by fs[gas_cut_def, Abbr `q`] >>
  `inst_wf inst` by
    (drule_all ld_sync_fn_shape >>
     metis_tac[o1_fn_shape_components, fmpStepStructuralTheory.fn_inst_wf_fn_insts,
               lowerDloadOracleCallAssemblyTheory.ld_active_inst_member, EVERY_MEM]) >>
  `EVERY (\k. k.lf_src.vs_gas_readings = k.lf_tgt.vs_gas_readings /\
    LENGTH s.vs_gas_readings <= LENGTH k.lf_src.vs_gas_readings) fs` by fs[] >>
  `q.vs_inst_idx = p + LENGTH X` by simp[Abbr `q`, ADD1] >>
  Cases_on `inst.inst_opcode = DLOAD`
  >- suspend "scratch" >>
  `inst.inst_opcode = DLOADBYTES` by metis_tac[] >>
  suspend "bytes"
QED

Resume focus_opt_ld_expansion_next[interior]:
  `active_inst gn (EL (SUC h) X) q` by
    (qpat_assum `gn = FST _` SUBST1_TAC >>
     irule lowerDloadReturnInteriorTheory.ld_envelope_target_at >>
     simp[] >> qexistsl [`s.vs_inst_idx`,`p`,`s`] >> simp[Abbr `q`, ADD1]) >>
  `ALL_DISTINCT (fn_labels gn)` by
    (Cases_on `lower_dload_function_supply f.lf_supply fn` >>
     drule o1ContractLowerDloadTheory.lower_dload_function_supply_labels >> fs[fn_labels_def]) >>
  `j = EL (SUC h) X` by metis_tac[fmpStageBlockSimCodeTheory.active_inst_unique] >>
  `step_inst 0 C' (EL h X) t = OK u` by metis_tac[step_inst_non_invoke] >>
  `ld_prefix C' gn X p (SUC h) t0 q` by
    (unabbrev_all_tac >> metis_tac[lowerDloadSafetyKernelTheory.ld_prefix_next]) >>
  `q.vs_gas_readings = t0.vs_gas_readings` by
    metis_tac[gasFocusLowerDloadCutGuardsTheory.ld_expansion_prefix_readings] >>
  qexistsl [`stk`,`PG`,`G`,`tn`,`fn`,`inst`,`s`,`t0`,`A`,`f`,`fs`,`N`,`X`,`p`,`SUC h`] >>
  simp[] >> metis_tac[]
QED

Resume focus_opt_ld_expansion_next[scratch]:
  `?off out. inst.inst_operands = [off] /\ inst.inst_outputs = [out]` by
    fs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
  `ld_prefix C' (ld_image f) X p h t0 t /\
   step_inst fuel C' (EL h X) t = OK u` by metis_tac[] >>
  drule_all gasFocusLowerDloadScratchNextTheory.ld_focus_dload_scratch_next >>
  disch_then (qx_choosel_then [`ss`,`v`,`g`,`c`] (map_every assume_tac o CONJUNCTS)) >>
  `ss.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
  qpat_assum `!stk PG G tn fn s A f fs N X p Ar g gn q ss j. _` irule >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl [`A`,`A`,`step_prov PG G inst ss`,`N`,`PG`,`X`,`f`,`fn`,`fs`,`g`,`p`,
    `s`,`ss`,`stk`,`step_taint inst s ss tn`] >>
  simp[Abbr `q`] >> metis_tac[]
QED

Resume focus_opt_ld_expansion_next[bytes]:
  `?dest off len. inst.inst_operands = [dest;off;len]` by
    fs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
  `LENGTH X = 2` by
    (drule_all lowerDloadPublicTraceTheory.ld_dloadbytes_envelope_temporary >>
     strip_tac >> simp[]) >>
  `h = 1` by decide_tac >>
  `ld_prefix C' gn X p 1 t0 t /\ step_inst fuel C' (EL 1 X) t = OK u` by metis_tac[] >>
  drule_all gasFocusLowerDloadBytesWriteTheory.ld_focus_bytes_classified_write >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  `lo <= vs.vs_alloca_next /\ mem_inv dload_headroom_ok C vs` by
    fs[o1_safe_upto_def, o1_ptr_safe_upto_def, ptr_discipline_upto_def] >>
  drule_all (REWRITE_RULE [LET_THM] gasFocusLowerDloadBytesNextTheory.ld_focus_bytes_classified_next) >>
  disch_then (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
  `ss.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
  qpat_x_assum `t = (update_var _ _ _ with vs_inst_idx := _)` kall_tac >>
  qpat_x_assum `ss = write_memory_with_expansion _ _ _` kall_tac >>
  qpat_x_assum `u = write_memory_with_expansion _ _ _` kall_tac >>
  qpat_x_assum `step_taint _ _ _ _ = _` kall_tac >>
  qpat_x_assum `step_prov _ _ _ _ = _` kall_tac >>
  qabbrev_tac `g = f with <|lf_src := ss with vs_inst_idx := SUC s.vs_inst_idx;
                            lf_tgt := q|>` >>
  qpat_assum `!stk PG G tn fn s A f fs N X p Ar g gn q ss j. _` irule >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl [`A`,`A`,`step_prov PG G inst ss`,`N`,`PG`,`X`,`f`,`fn`,`fs`,`g`,`p`,
    `s`,`ss`,`stk`,`step_taint inst s ss tn`] >>
  simp[Abbr `g`, Abbr `q`] >> metis_tac[]
QED

Finalise focus_opt_ld_expansion_next[local]

Theorem focus_row_visit_inverse[local]:
  !xs be.
    DROP be.vs_inst_idx bt.bb_instructions = xs /\
    MEM ((a,e,i.inst_id),tf,i,t)
      (trace_block a e fuel C tf bt be) ==>
    ?pre rest. xs = pre ++ i::rest /\
      t.vs_inst_idx = be.vs_inst_idx + LENGTH pre /\
      EVERY (\x. ~is_terminator x.inst_opcode) pre /\
      FOLDR (dft_exec_cons fuel C) OK pre be = OK t
Proof
  Induct
  >- (rpt strip_tac >>
      `LENGTH bt.bb_instructions <= be.vs_inst_idx` by
        (gvs[GSYM LENGTH_NIL, LENGTH_DROP]) >>
      fs[Once (cj 2 trace_defs), get_instruction_def]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `DROP be.vs_inst_idx bt.bb_instructions = head::xs` >>
  `be.vs_inst_idx < LENGTH bt.bb_instructions` by
    (qpat_assum `DROP _ _.bb_instructions = _::_`
       (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[NoAsms, LENGTH_DROP]) >>
  `get_instruction bt be.vs_inst_idx = SOME head /\
   DROP (SUC be.vs_inst_idx) bt.bb_instructions = xs` by
    (drule DROP_BY_DROP_SUC >> simp[get_instruction_def]) >>
  drule_then assume_tac trace_block_visit >>
  qpat_x_assum `MEM _ (trace_block _ _ _ _ _ _ _)` mp_tac >>
  asm_rewrite_tac[MEM, MEM_APPEND, pairTheory.PAIR_EQ] >> strip_tac
  >- (gvs[] >> qexistsl [`[]`,`xs`] >> simp[])
  >- (`MEM (a,e,i.inst_id) (MAP FST (trace_step a e fuel C tf head be))` by
        (simp[MEM_MAP] >> metis_tac[pairTheory.FST]) >>
      metis_tac[dftGasFromListTraceNamesTheory.trace_step_not_root]) >>
  Cases_on `step_inst fuel C head be` >> gvs[] >>
  Cases_on `is_terminator head.inst_opcode` >> gvs[] >>
  rename1 `step_inst fuel C head be = OK post` >>
  qpat_x_assum `!s. DROP _ _ = _ /\ MEM _ _ ==> _`
    (qspec_then `post with vs_inst_idx := SUC be.vs_inst_idx` mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl [`head::pre`,`rest`] >> simp[dftIndexedExecTheory.dft_exec_cons_def]
QED

(* A child frame keeps its call site throughout the child's trace. Changing
   the selected instruction ID does not move that frame to another site. *)
Theorem focus_child_row_excludes[local]:
  MEM ((p,d,id),fn,i,t) (trace_step P D fuel C f head s) /\
  ~MEM head.inst_id (MAP (\x. x.inst_id) (DROP post.vs_inst_idx bb.bb_instructions)) ==>
  !id' g j u. ~MEM ((p,d,id'),g,j,u) (trace_block P D fuel C f bb post)
Proof
  rpt strip_tac >>
  drule (REWRITE_RULE [EVERY_MEM] (cj 1 dftGasFromListTraceNamesTheory.trace_regions)) >>
  simp[] >> strip_tac >>
  `block_region P D [head.inst_id] (p,d,id')` by
    (irule dftGasFromListTraceNamesTheory.below_call_region >> simp[] >>
     qexists `head.inst_id` >> simp[]) >>
  drule dftGasFromListTraceNamesTheory.trace_block_region >> simp[] >> strip_tac >>
  metis_tac[dftGasFromListTraceNamesTheory.block_regions_disjoint, MEM]
QED

Theorem focus_later_row_excludes[local]:
  MEM ((p,d,id),fn,i,t) (trace_block P D fuel C f bb s) ==>
  !id' g j u. ~MEM ((p,d,id'),g,j,u) (trace_blocks P D fuel C f post)
Proof
  rpt strip_tac >>
  drule dftGasFromListTraceNamesTheory.trace_blocks_region >> simp[] >> strip_tac >>
  `later_region P D (p,d,id)` by
    fs[dftGasFromListTraceNamesTheory.later_region_def] >>
  drule dftGasFromListTraceNamesTheory.trace_block_region >> simp[] >>
  metis_tac[dftGasFromListTraceNamesTheory.block_later_disjoint]
QED

Theorem focus_row_continuations[local]:
  (!P D fuel C f inst s. !h p d id fn i t.
    EVERY (\g. EVERY (\b. ALL_DISTINCT (MAP (\x. x.inst_id) b.bb_instructions))
                     g.fn_blocks) C.ctx_functions /\
    h < LENGTH (trace_step P D fuel C f inst s) /\
    EL h (trace_step P D fuel C f inst s) = ((p,d,id),fn,i,t) ==>
    ?bt rest. lookup_block t.vs_current_bb fn.fn_blocks = SOME bt /\
      get_instruction bt t.vs_inst_idx = SOME i /\ id = i.inst_id /\
      d <= D + fuel /\
      DROP h (trace_step P D fuel C f inst s) =
        trace_block p d (D + fuel - d) C fn bt t ++ rest /\
      (!id' g j u. ~MEM ((p,d,id'),g,j,u) rest)) /\
  (!P D fuel C f bb s. !h p d id fn i t.
    EVERY (\g. EVERY (\b. ALL_DISTINCT (MAP (\x. x.inst_id) b.bb_instructions))
                     g.fn_blocks) C.ctx_functions /\
    ALL_DISTINCT (MAP (\x. x.inst_id) bb.bb_instructions) /\
    lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
    h < LENGTH (trace_block P D fuel C f bb s) /\
    EL h (trace_block P D fuel C f bb s) = ((p,d,id),fn,i,t) ==>
    ?bt rest. lookup_block t.vs_current_bb fn.fn_blocks = SOME bt /\
      get_instruction bt t.vs_inst_idx = SOME i /\ id = i.inst_id /\
      d <= D + fuel /\
      DROP h (trace_block P D fuel C f bb s) =
        trace_block p d (D + fuel - d) C fn bt t ++ rest /\
      (!id' g j u. ~MEM ((p,d,id'),g,j,u) rest)) /\
  (!P D fuel C f s. !h p d id fn i t.
    EVERY (\g. EVERY (\b. ALL_DISTINCT (MAP (\x. x.inst_id) b.bb_instructions))
                     g.fn_blocks) C.ctx_functions /\
    EVERY (\b. ALL_DISTINCT (MAP (\x. x.inst_id) b.bb_instructions)) f.fn_blocks /\
    h < LENGTH (trace_blocks P D fuel C f s) /\
    EL h (trace_blocks P D fuel C f s) = ((p,d,id),fn,i,t) ==>
    ?bt rest. lookup_block t.vs_current_bb fn.fn_blocks = SOME bt /\
      get_instruction bt t.vs_inst_idx = SOME i /\ id = i.inst_id /\
      d <= D + fuel /\
      DROP h (trace_blocks P D fuel C f s) =
        trace_block p d (D + fuel - d) C fn bt t ++ rest /\
      (!id' g j u. ~MEM ((p,d,id'),g,j,u) rest))
Proof
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume focus_row_continuations[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE` >> gvs[cj 1 trace_defs] >>
  Cases_on `decode_invoke inst` >> gvs[] >>
  rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
  Cases_on `lookup_function pair0 C.ctx_functions` >> gvs[] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  Cases_on `eval_operands pair1 s` >> gvs[] >>
  rename1 `eval_operands _ _ = SOME args` >>
  Cases_on `setup_callee callee args s` >> gvs[] >>
  first_x_assum irule >> simp[] >>
  gvs[EVERY_MEM] >> metis_tac[venomInstTheory.lookup_function_MEM]
QED

Resume focus_row_continuations[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `h < _` mp_tac >> simp[Once (cj 2 trace_defs)]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME head` >>
  drule_then assume_tac trace_block_visit >>
  Cases_on `h`
  >- (gvs[] >> qexists_tac `bb` >> qexists_tac `[]` >> simp[]) >>
  rename1 `SUC k` >>
  gvs[] >>
  Cases_on `k < LENGTH (trace_step P D fuel C f head s)`
  >- (gvs[EL_APPEND] >>
      qpat_x_assum `!h p d id fn i t. _` drule_all >> strip_tac >>
      qexists_tac `bt` >>
      qmatch_goalsub_abbrev_tac `DROP k (ts ++ tail)` >>
      qexists_tac `rest ++ tail` >>
      simp[DROP_APPEND1, Abbr `ts`, APPEND_ASSOC, MEM_APPEND] >>
      Cases_on `step_inst fuel C head s` >> gvs[Abbr `tail`] >>
      rename1 `step_inst _ _ _ _ = OK post` >>
      Cases_on `is_terminator head.inst_opcode` >> gvs[] >>
      irule focus_child_row_excludes >>
      `ALL_DISTINCT (MAP (\x. x.inst_id) (DROP s.vs_inst_idx bb.bb_instructions))` by
        (rewrite_tac[MAP_DROP] >> irule ALL_DISTINCT_DROP >> simp[]) >>
      qpat_assum `get_instruction bb s.vs_inst_idx = SOME head`
        (mp_tac o MATCH_MP dftGasFromListTraceNamesTheory.remaining_ids_step) >>
      strip_tac >> gvs[] >>
      `MEM ((p,d,i.inst_id),fn,i,t) (trace_step P D fuel C f head s)` by
        (simp[MEM_EL] >> qexists `k` >> simp[]) >>
      goal_assum $ drule_at Any >> simp[]) >>
  Cases_on `step_inst fuel C head s` >> gvs[] >>
  rename1 `step_inst _ _ _ _ = OK post` >>
  Cases_on `is_terminator head.inst_opcode` >> gvs[] >>
  drule_all venomInstProofsTheory.step_preserves_control_flow >> strip_tac >>
  gvs[EL_APPEND, DROP_APPEND2] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Resume focus_row_continuations[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `fuel` >- gvs[] >>
  rename1 `trace_blocks P D (SUC n) C f s` >>
  Cases_on `lookup_block s.vs_current_bb f.fn_blocks`
  >- (qpat_x_assum `h < _` mp_tac >> simp[Once (cj 3 trace_defs)]) >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >> gvs[] >>
  qpat_x_assum `h < _` mp_tac >>
  once_rewrite_tac[cj 3 trace_defs] >> simp[] >> strip_tac >>
  rename1 `eval_phis _ _ = OK sp` >>
  drule_all trace_blocks_enter >> disch_then assume_tac >> gvs[] >>
  `sp.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
  `ALL_DISTINCT (MAP (\x. x.inst_id) bb.bb_instructions)` by
    (gvs[EVERY_MEM] >> metis_tac[venomExecProofsTheory.lookup_block_MEM]) >>
  qmatch_asmsub_abbrev_tac `exec_block n C bb start` >>
  Cases_on `h < LENGTH (trace_block P (SUC D) n C f bb start)`
  >- (gvs[EL_APPEND, Abbr `start`] >>
      qpat_x_assum `!h p d id fn i t. _` drule_all >> strip_tac >>
      qexists_tac `bt` >>
      qmatch_goalsub_abbrev_tac `DROP h (ts ++ tail)` >>
      qexists_tac `rest ++ tail` >>
      simp[DROP_APPEND1, Abbr `ts`, APPEND_ASSOC, ADD_CLAUSES, MEM_APPEND] >>
      Cases_on `exec_block n C bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
      gvs[Abbr `tail`] >>
      rename1 `exec_block _ _ _ _ = OK post` >>
      Cases_on `post.vs_halted` >> gvs[] >>
      metis_tac[focus_later_row_excludes, MEM_EL]) >>
  Cases_on `exec_block n C bb start` >> gvs[] >>
  rename1 `exec_block _ _ _ _ = OK post` >>
  Cases_on `post.vs_halted` >> gvs[] >>
  gvs[EL_APPEND, DROP_APPEND2, ADD_CLAUSES] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Finalise focus_row_continuations[local]

Theorem focus_row_continuation[local]:
  !P D fuel C f s h p d id fn i t.
    EVERY (\g. EVERY (\b. ALL_DISTINCT (MAP (\x. x.inst_id) b.bb_instructions))
                     g.fn_blocks) C.ctx_functions /\
    EVERY (\b. ALL_DISTINCT (MAP (\x. x.inst_id) b.bb_instructions)) f.fn_blocks /\
    h < LENGTH (trace_blocks P D fuel C f s) /\
    EL h (trace_blocks P D fuel C f s) = ((p,d,id),fn,i,t) ==>
    ?bt rest. lookup_block t.vs_current_bb fn.fn_blocks = SOME bt /\
      get_instruction bt t.vs_inst_idx = SOME i /\ id = i.inst_id /\
      d <= D + fuel /\
      DROP h (trace_blocks P D fuel C f s) =
        trace_block p d (D + fuel - d) C fn bt t ++ rest /\
      (!id' g j u. ~MEM ((p,d,id'),g,j,u) rest)
Proof
  ACCEPT_TAC (cj 3 focus_row_continuations)
QED

(* The later indexed visit belongs to the direct row (not the residual
   continuation), even when child traces intervene between the two visits. *)
Theorem focus_row_visit_between[local]:
  EVERY (\g. EVERY (\b. ALL_DISTINCT (MAP (\x. x.inst_id) b.bb_instructions))
                    g.fn_blocks) C.ctx_functions /\
  EVERY (\b. ALL_DISTINCT (MAP (\x. x.inst_id) b.bb_instructions)) root.fn_blocks /\
  R = trace_blocks [] 0 N C root entry /\
  m <= n /\ n < LENGTH R /\
  EL m R = ((a,e,first.inst_id),tf,first,s) /\
  EL n R = ((a,e,i.inst_id),tf,i,t) ==>
  ?bt rest pre post.
    lookup_block s.vs_current_bb tf.fn_blocks = SOME bt /\
    get_instruction bt s.vs_inst_idx = SOME first /\
    R = TAKE m R ++ trace_block a e (N-e) C tf bt s ++ rest /\
    DROP s.vs_inst_idx bt.bb_instructions = pre ++ i::post /\
    t.vs_inst_idx = s.vs_inst_idx + LENGTH pre /\
    EVERY (\x. ~is_terminator x.inst_opcode) pre /\
    FOLDR (dftIndexedExec$dft_exec_cons (N-e) C) OK pre s = OK t
Proof
  strip_tac >>
  `?bt rest. lookup_block s.vs_current_bb tf.fn_blocks = SOME bt /\
     get_instruction bt s.vs_inst_idx = SOME first /\ e <= N /\
     DROP m R = trace_block a e (N-e) C tf bt s ++ rest /\
     (!id' g j u. ~MEM ((a,e,id'),g,j,u) rest)` by
    (qpat_x_assum `EL n R = _` kall_tac >> gvs[] >>
     `m < LENGTH (trace_blocks [] 0 N C root entry)` by decide_tac >>
     drule_all focus_row_continuation >> simp[]) >>
  `MEM ((a,e,i.inst_id),tf,i,t) (DROP m R)` by
    (qpat_x_assum `DROP m R = _` kall_tac >>
     qpat_x_assum `R = trace_blocks _ _ _ _ _ _` kall_tac >>
     `n-m + m = n` by decide_tac >>
     simp[MEM_EL] >> qexists `n-m` >>
     conj_tac >- (simp[LENGTH_DROP] >> decide_tac) >>
     dep_rewrite.DEP_REWRITE_TAC[listTheory.EL_DROP] >> simp[]) >>
  `MEM ((a,e,i.inst_id),tf,i,t) (trace_block a e (N-e) C tf bt s)` by
    (qpat_assum `DROP m R = _` (fs o single) >> metis_tac[MEM_APPEND]) >>
  `?pre post. DROP s.vs_inst_idx bt.bb_instructions = pre ++ i::post /\
     t.vs_inst_idx = s.vs_inst_idx + LENGTH pre /\
     EVERY (\x. ~is_terminator x.inst_opcode) pre /\
     FOLDR (dftIndexedExec$dft_exec_cons (N-e) C) OK pre s = OK t` by
    metis_tac[focus_row_visit_inverse] >>
  qexistsl [`bt`,`rest`,`pre`,`post`] >>
  rewrite_tac[GSYM APPEND_ASSOC] >>
  qpat_x_assum `DROP m R = _` (rewrite_tac o single o GSYM) >> simp[]
QED

Theorem focus_history_target_slice[local]:
  o1_ctx_shape C /\ MEM root C.ctx_functions /\
  R = trace_blocks [] 0 N C root entry /\
  h < j /\ hbe <= j /\ j < LENGTH R /\
  EL hbe R = ((a,e,(HD ys).inst_id),tf,HD ys,be) /\
  EL h R = ((a,e,inst.inst_id),tf,inst,t) /\
  lookup_block be.vs_current_bb tf.fn_blocks = SOME bt /\
  bt.bb_instructions = ps ++ ys /\
  be.vs_inst_idx = LENGTH ps /\ LENGTH ps <= t.vs_inst_idx /\
  k = t.vs_inst_idx - LENGTH ps /\ obs = trace_gas (TAKE j R) ==>
  hbe <= h /\
  (?post. ys = TAKE k ys ++ inst::post) /\
  EVERY (\x. ~is_terminator x.inst_opcode) (TAKE k ys) /\
  FOLDR (dftIndexedExec$dft_exec_cons (N-e) C) OK (TAKE k ys) be = OK t /\
  EVERY (\kw. MEM kw obs)
    (trace_gas (trace_block a e (N-e) C tf
      (bt with bb_instructions := TAKE (LENGTH ps + LENGTH (TAKE k ys)) bt.bb_instructions) be))
Proof
  strip_tac >>
  `EVERY (\g. EVERY (\b. ALL_DISTINCT (MAP (\x. x.inst_id) b.bb_instructions))
                    g.fn_blocks) C.ctx_functions` by
    (drule dftContractGasTheory.o1_ctx_shape_wf_functions >>
     simp[EVERY_MEM] >> metis_tac[dftCorrectnessTheory.bb_inst_ids_distinct]) >>
  `EVERY (\b. ALL_DISTINCT (MAP (\x. x.inst_id) b.bb_instructions)) root.fn_blocks` by
    (qpat_assum `EVERY _ C.ctx_functions`
      (qspec_then `root` mp_tac o PURE_ONCE_REWRITE_RULE [EVERY_MEM]) >> simp[]) >>
  `ALL_DISTINCT (MAP FST R)` by
    (simp[] >> irule (cj 3 dftGasFromListTraceNamesTheory.trace_names_distinct) >> simp[]) >>
  `hbe <= h` by
    (spose_not_then assume_tac >>
     `h <= hbe /\ hbe < LENGTH R` by decide_tac >>
     drule_all focus_row_visit_between >> strip_tac >>
     qpat_x_assum `R = TAKE h R ++ _ ++ _` kall_tac >>
     `LENGTH pre = 0` by decide_tac >>
     `pre = []` by metis_tac[LENGTH_NIL] >>
     `HD ys = inst` by
       (qpat_x_assum `DROP t.vs_inst_idx _ = _` mp_tac >>
        qpat_x_assum `get_instruction _ t.vs_inst_idx = _` mp_tac >>
        simp[get_instruction_def, DROP_CONS_EL]) >>
     qpat_x_assum `R = trace_blocks _ _ _ _ _ _` kall_tac >>
     `h < LENGTH R` by decide_tac >>
     `EL hbe (MAP FST R) = EL h (MAP FST R)` by simp[EL_MAP] >>
     qspecl_then [`MAP FST R`,`hbe`,`h`] mp_tac ALL_DISTINCT_EL_IMP >> simp[]) >>
  `h < LENGTH R` by decide_tac >>
  drule_all focus_row_visit_between >> strip_tac >>
  `bt' = bt` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `bt' = bt` SUBST_ALL_TAC >>
  qpat_x_assum `R = trace_blocks _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `R = TAKE hbe R ++ _ ++ _` (mk_asm "embed") >>
  `ys = pre ++ inst::post /\ k = LENGTH pre` by
    (qpat_x_assum `DROP be.vs_inst_idx _ = _` mp_tac >>
     simp[DROP_LENGTH_APPEND]) >>
  `TAKE k ys = pre` by simp[TAKE_LENGTH_APPEND] >>
  simp[] >>
  `hbe <= LENGTH R /\ be.vs_inst_idx + LENGTH pre < LENGTH bt.bb_instructions` by
    (simp[] >> decide_tac) >>
  `get_instruction bt t.vs_inst_idx = SOME inst` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  `TAKE h R = TAKE hbe R ++ trace_block a e (N-e) C tf
      (bt with bb_instructions := TAKE (be.vs_inst_idx + LENGTH pre) bt.bb_instructions) be` by
    (irule dftPacketNativeSliceTheory.native_trace_embedded_prefix_cut >>
     simp[DROP_LENGTH_APPEND, TAKE_LENGTH_APPEND] >>
     asm_x "embed" (fn th => metis_tac[th])) >>
  qmatch_asmsub_abbrev_tac `TAKE h R = TAKE hbe R ++ target` >>
  `TAKE j R = TAKE h R ++ TAKE (j-h) (DROP h R)` by
    simp[rich_listTheory.take_drop_partition] >>
  simp[Abbr `target`, EVERY_MEM, dftGasFromListReadingsTheory.trace_gas_append, MEM_APPEND]
QED

Theorem focus_fmp_inst_no_dload[local]:
  i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES /\
  fmp_lower_inst infos ctx runner s i = SOME (out,t) ==>
  EVERY (\j. j.inst_opcode <> DLOAD /\ j.inst_opcode <> DLOADBYTES) out
Proof
  rpt strip_tac >> gvs[fmp_lower_inst_def, AllCaseEqs(), mk_inst_def]
QED

Theorem focus_fmp_function_no_dload[local]:
  fmp_lower_function ctx s f = SOME (g,t) /\
  EVERY (\i. i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES) (fn_insts f) ==>
  EVERY (\i. i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES) (fn_insts g)
Proof
  strip_tac >> drule fmpStepPredicateTransportTheory.fmp_lower_function_every >>
  disch_then (qspec_then `\i. i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES` mp_tac) >>
  simp[] >> impl_tac
  >- (conj_tac
      >- (rpt strip_tac >>
          `i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES` by
            fs[EVERY_MEM] >>
          drule_all focus_fmp_inst_no_dload >> simp[]) >>
      conj_tac
      >- (rpt strip_tac >>
          drule_at (Pat `fmp_emit_restores _ _ _ = _`) fmpStepRewriteTheory.fmp_emit_restores_every >>
          disch_then irule >> simp[mk_inst_def]) >>
      rpt strip_tac >>
      gvs[fmp_make_root_layout_def, AllCaseEqs(), mk_inst_def,
          set_param_index_def, OPTION_TO_LIST_def] >>
      drule fmpStepRestrictionClosureTheory.split_fmp_entry_retpc_restrictions >>
      rw[EVERY_MEM] >> gvs[OPTION_TO_LIST_def]) >>
  simp[]
QED

(* Each of these rows preserves exclusion of the already lowered opcodes. *)
Theorem focus_step_no_dload[local]:
  (pass = CFP_Simple VP_ConcretizeMemLoc \/ pass = CFP_Simple VP_FmpLowering \/
   pass = CFP_Simple VP_MakeSSA \/ pass = CFP_Simple VP_SimplifyCFG \/
   pass = CFP_Simple VP_SingleUseExpansion) /\
  fn_pass_step rp pass observed s f out /\
  EVERY (\i. i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES) (fn_insts f) ==>
  EVERY (\i. i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES)
    (fn_insts out.fpo_function)
Proof
  disch_then (CONJUNCTS_THEN2 STRIP_ASSUME_TAC STRIP_ASSUME_TAC) >> gvs[]
  >- (drule_at (Pat `fn_pass_step _ _ _ _ _ _`)
        (Q.INST [`P` |-> `\op. op <> DLOAD /\ op <> DLOADBYTES`]
          concretize_fn_pass_opcode_property) >> fs[EVERY_MEM])
  >- (drule fmp_fn_pass_step_result >> strip_tac >>
      drule_all focus_fmp_function_no_dload >> simp[])
  >- (drule make_ssa_pass_step_replay >> strip_tac >>
      drule_at (Pat `make_ssa_current_fn _ _ = _`)
        (Q.INST [`P` |-> `\op. op <> DLOAD /\ op <> DLOADBYTES`]
          make_ssa_current_fn_opcode_property) >> simp[])
  >- (drule simplify_cfg_pass_step_function >> disch_then SUBST1_TAC >>
      simp[simplify_cfg_fn_def] >>
      mp_tac (Q.INST [`R` |-> `\op. op <> DLOAD /\ op <> DLOADBYTES`]
        simplify_cfg_fn_with_labels_opcodes) >> simp[]) >>
  drule sue_pass_step_replay >> strip_tac >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  drule_all sue_expand_function_supply_label_projection >>
  strip_tac >> fs[] >> metis_tac[]
QED

Theorem focus_raw_reachable_members[local]:
  !V C f i u. raw_reachable V C f i u ==>
    MEM f C.ctx_functions /\ MEM i (fn_insts f)
Proof
  ho_match_mp_tac raw_reachable_ind >>
  rpt strip_tac >> metis_tac[lookup_function_MEM, active_inst_mem_fn_insts]
QED

Theorem focus_opt_c7_section_from_image[local]:
  (!k. k < 9 ==> ctx_pass_stage rp (EL k o1_fn_passes) (o1_walk_view rp k)
      (stage k) (stage (SUC k))) /\
  (!g j. MEM g (stage 2).ctx_functions /\ MEM j (fn_insts g) ==>
    j.inst_opcode <> DLOAD /\ j.inst_opcode <> DLOADBYTES) /\
  raw_reachable V (stage 7) sf i u ==>
  inst_dload_in_section i u
Proof
  strip_tac >>
  `!k. 2 <= k /\ k <= 7 ==>
    EVERY (\f. EVERY (\i. i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES)
      (fn_insts f)) (stage k).ctx_functions` by
    (Induct >- simp[] >> strip_tac >>
     Cases_on `k < 2`
     >- (`SUC k = 2` by decide_tac >> gvs[EVERY_MEM] >> metis_tac[]) >>
     `ctx_pass_stage rp (EL k o1_fn_passes) (o1_walk_view rp k)
          (stage k) (stage (SUC k))` by (first_x_assum irule >> decide_tac) >>
     `2 <= k /\ k <= 7` by decide_tac >>
     drule_at (Pat `ctx_pass_stage _ _ _ _ _`)
       (Q.INST [`P` |-> `\f. EVERY (\i. i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES)
                               (fn_insts f)`] ctx_pass_stage_every) >>
     disch_then irule >> simp[] >> rpt strip_tac >>
     drule_at (Pat `fn_pass_step _ _ _ _ _ _`) focus_step_no_dload >> simp[] >>
     `k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6` by decide_tac >>
     pop_assum strip_assume_tac >> simp[o1_fn_passes_def]) >>
  drule focus_raw_reachable_members >> strip_tac >>
  irule inst_dload_in_section_other >>
  qpat_x_assum `!k. 2 <= k /\ k <= 7 ==> _` (qspec_then `7` mp_tac) >>
  simp[EVERY_MEM] >> metis_tac[]
QED

(* Reflect the selected scalar read after the paired history has been supplied. *)
Theorem focus_concretize_cut_read[local]:
  o1_ctx_shape C /\ o1_ctx_shape Ct /\ o1_ptr_safe_upto D lo n C V /\
  (?R lp positions.
    ptr_stage_placements Ct positions /\
    !ht at. ptr_chrono_history V Ct ht at ==> gas_cut n V at.po_state ==>
      (?h a done tokens registry births PT TG saved entries H calls ws.
        ptr_paired_prefix R lp positions lo V C Ct
          h a ht at done tokens registry births PT TG saved entries H calls ws /\
        EVERY (\i. ~in_revert_forward (EL i h).po_fn (EL i h).po_state) done /\
        a.po_inst.inst_opcode <> NOP /\
        at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst) \/
      (?bb i j. lookup_block at.po_state.vs_current_bb at.po_fn.fn_blocks = SOME bb /\
        revert_forward_pair bb i j /\
        i < at.po_state.vs_inst_idx /\ at.po_state.vs_inst_idx <= j)) /\
  raw_reachable V Ct ft j t /\ gas_cut n V t /\
  j.inst_opcode = CODECOPY /\ j.inst_operands = [dst; Var x; sz] /\
  code_end_var ft x /\ eval_operand (Var x) t = SOME w ==>
  ?f i s. raw_reachable V C f i s /\ gas_cut n V s /\
    i.inst_opcode = CODECOPY /\ i.inst_operands = [dst; Var x; sz] /\
    code_end_var f x /\ eval_operand (Var x) s = SOME w /\
    s.vs_labels = t.vs_labels
Proof
  rpt gen_tac >> strip_tac >>
  `ptr_discipline_upto lo n C V` by fs[o1_ptr_safe_upto_def] >>
  drule ptr_raw_reachable_frame >> strip_tac >>
  drule ptr_reachable_has_chrono_history >> strip_tac >>
  qpat_x_assum `!ht at. ptr_chrono_history _ _ ht at ==> _` drule >>
  (impl_tac >- simp[ptr_observe_def]) >> strip_tac
  >- suspend "paired" >>
  suspend "corridor"
QED

Resume focus_concretize_cut_read[paired]:
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  `gas_cut n V (ptr_observe stk PG G tn ft j t).po_state` by simp[ptr_observe_def] >>
  drule_all ptr_paired_endpoint_cut_safety >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `MEM a.po_fn C.ctx_functions` by metis_tac[ptr_frame_context_membership] >>
  `MEM a.po_inst (fn_insts a.po_fn)` by metis_tac[ptr_frame_operand_instructions] >>
  `fn_shape_ok a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `a.po_inst.inst_opcode <> ALLOCA` by
    (strip_tac >> gvs[concretize_inst_with_positions_def, AllCaseEqs(),
                     mk_nop_inst_def, mk_assign_inst_def, ptr_observe_def]) >>
  `j = a.po_inst` by fs[ptr_observe_def, concretize_positions_unchanged] >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn ft
     a.po_state t /\ a.po_state.vs_labels = t.vs_labels` by
    (fs[ptr_paired_sample_def, ptr_observe_def] >> metis_tac[ptr_history_content_labels]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >>
     metis_tac[]) >>
  drule_all ptr_source_ownership_erases_upto >> strip_tac >>
  drule ptr_discipline_upto_fn_ptr_ok >> strip_tac >>
  drule_all ptr_frame_current_static >> strip_tac >>
  `FDOM a.po_prov SUBSET fn_pv P a.po_fn` by
    (fs[ptr_static_support_def, SUBSET_DEF, FLOOKUP_DEF] >>
     metis_tac[optionTheory.NOT_NONE_SOME]) >>
  `opaque_use_ok a.po_fn /\ fn_ptr_ok P a.po_fn` by fs[fn_shape_ok_def, EVERY_MEM] >>
  `eval_operand (Var x) a.po_state = eval_operand (Var x) t` by
    (irule code_end_concretize_read_value >> metis_tac[]) >>
  `code_end_var (concretize_function_with_positions (lp a.po_fn) a.po_fn) x` by
    (fs[ptr_paired_code_def, ptr_observe_def] >> metis_tac[code_end_var_same_blocks]) >>
  `code_end_var a.po_fn x` by metis_tac[concretize_code_end_backward] >>
  qexistsl [`a.po_fn`, `a.po_inst`, `a.po_state`] >> simp[] >>
  metis_tac[ld_frame_reachable_raw]
QED

Resume focus_concretize_cut_read[corridor]:
  fs[ptr_observe_def] >>
  drule raw_reachable_active >>
  rewrite_tac[active_inst_def] >>
  disch_then (qx_choose_then `active_bb` strip_assume_tac) >>
  `MEM ft Ct.ctx_functions` by metis_tac[ptr_frame_context_membership] >>
  `ALL_DISTINCT (fn_labels ft)` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  `lookup_block t.vs_current_bb ft.fn_blocks = SOME active_bb` by
    (irule MEM_lookup_block >> fs[fn_labels_def]) >>
  `active_bb = bb` by metis_tac[optionTheory.SOME_11] >>
  `get_instruction bb t.vs_inst_idx = SOME j` by fs[get_instruction_def] >>
  drule_all ld_revert_pair_suffix_opcode >> simp[]
QED

Finalise focus_concretize_cut_read

Theorem focus_opt_scfg_read_origin[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_SimplifyCFG) view C Ct /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  V.vs_vars = FEMPTY /\ ~V.vs_halted /\ raw_reachable V Ct g j t /\
  j.inst_opcode = CODECOPY ==>
  ?f s. raw_reachable V C f j s /\ MEM f C.ctx_functions /\
    g = simplify_cfg_fn f /\ scfg_payload s t
Proof
  strip_tac >>
  `EVERY simplify_cfg_fn_ok C.ctx_functions` by
    (fs[o1_ctx_shape_def, EVERY_MEM] >> rpt strip_tac >>
     irule simplify_cfg_fn_ok_ssa >> metis_tac[o1_fn_shape_def]) >>
  drule simplify_cfg_stage_functions >> strip_tac >>
  `ctx_bisim C Ct` by metis_tac[simplify_cfg_stage_bisim] >>
  `LIST_REL (\f g. g.fn_name = f.fn_name /\ fn_entry_label g = fn_entry_label f /\
    frame_sim V.vs_labels C Ct f g /\ g = simplify_cfg_fn f /\ scfg_static f)
    C.ctx_functions Ct.ctx_functions` by
    (simp[LIST_REL_MAP2, LIST_REL_EL_EQN] >> rpt gen_tac >> strip_tac >> simp[EL_MAP] >>
     `MEM (EL n C.ctx_functions) C.ctx_functions` by metis_tac[MEM_EL] >>
     `o1_fn_shape C (EL n C.ctx_functions) /\ simplify_cfg_fn_ok (EL n C.ctx_functions)` by
       fs[o1_ctx_shape_def, EVERY_MEM] >>
     `fn_bisim (EL n C.ctx_functions) (simplify_cfg_fn (EL n C.ctx_functions))` by
       (irule simplify_cfg_fn_correct >> fs[o1_fn_shape_def]) >>
     fs[fn_bisim_def] >> conj_tac
     >- (irule simplify_cfg_frame_sim >> fs[o1_fn_shape_def]) >>
     fs[scfg_static_def, o1_fn_shape_def] >> metis_tac[fn_shape_ok_scfg_shape]) >>
  `frame_origin V C Ct g j t` by
    (irule frame_sim_raw_origins >> fs[ctx_pass_stage_def] >>
     qpat_x_assum `LIST_REL (\fn fn'. ?observed s out. _) _ _` kall_tac >>
     qpat_x_assum `LIST_REL _ _ _` mp_tac >>
     qpat_x_assum `Ct.ctx_functions = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     simp[LIST_REL_EL_EQN] >> metis_tac[]) >>
  qpat_x_assum `frame_origin _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[frame_origin_def] >>
  disch_then (qx_choosel_then [`f`,`s0`] strip_assume_tac) >>
  `g = simplify_cfg_fn f /\ scfg_static f` by
    (drule list_rel_lookup_function >> simp[] >>
     disch_then (qspec_then `nm` mp_tac) >> simp[optionTheory.OPTREL_def] >>
     strip_tac >> gvs[]) >>
  `frame_reach C g s0 j t` by metis_tac[frame_reach_ctx_bisim] >>
  `?s. frame_reach C f s0 j s /\ scfg_payload s t` by
    (irule o1_code_end_iter_reach_back >>
     conj_tac >- metis_tac[scfg_collapse_frame_observation_joint] >>
     simp[is_terminator_def] >> qexists_tac `LENGTH f.fn_blocks` >>
     qpat_x_assum `g = simplify_cfg_fn f` SUBST_ALL_TAC >>
     fs[simplify_cfg_fn_def, simplify_cfg_fn_with_labels_def]) >>
  qexistsl_tac [`f`,`s`] >> simp[] >>
  metis_tac[frame_reach_raw_reachable, lookup_function_MEM]
QED

Theorem focus_history_native_fuel_prefix[local]:
  n <= m ==>
  ?rest. trace_blocks a e m C fn ent = trace_blocks a e n C fn ent ++ rest
Proof
  simp[dftGasFromListTracePrefixTheory.trace_prefix]
QED

(* Propagate a visit invariant through a single native row. The state at any
   subsequent fetch is given by the fold on exactly the preceding instructions. *)
Theorem focus_history_native_row_every[local]:
  !xs s.
    DROP s.vs_inst_idx bt.bb_instructions = xs /\
    (!k i t. k < LENGTH xs /\ i = EL k xs /\
       t.vs_inst_idx = s.vs_inst_idx + k /\
       FOLDR (dftIndexedExec$dft_exec_cons fuel C) OK (TAKE k xs) s = OK t ==>
       P ((a,e,i.inst_id),tf,i,t) /\ EVERY P (trace_step a e fuel C tf i t)) ==>
    EVERY P (trace_block a e fuel C tf bt s)
Proof
  Induct
  >- (rpt strip_tac >>
      `LENGTH bt.bb_instructions <= s.vs_inst_idx` by
        (gvs[GSYM LENGTH_NIL, LENGTH_DROP]) >>
      simp[Once (cj 2 trace_defs), get_instruction_def]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `DROP s.vs_inst_idx bt.bb_instructions = i::xs` >>
  `s.vs_inst_idx < LENGTH bt.bb_instructions` by
    (qpat_assum `DROP _ _.bb_instructions = _::_`
       (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[NoAsms, LENGTH_DROP]) >>
  `get_instruction bt s.vs_inst_idx = SOME i /\
   DROP (SUC s.vs_inst_idx) bt.bb_instructions = xs` by
    (drule DROP_BY_DROP_SUC >> simp[get_instruction_def]) >>
  drule_then (fn th => once_rewrite_tac[th]) trace_block_visit >>
  `P ((a,e,i.inst_id),tf,i,s) /\ EVERY P (trace_step a e fuel C tf i s)` by
    (qpat_assum `!k i' t. _` (qspecl_then [`0`,`i`,`s`] mp_tac) >> simp[NoAsms]) >>
  simp[EVERY_APPEND] >>
  Cases_on `step_inst fuel C i s` >> simp[] >>
  Cases_on `is_terminator i.inst_opcode` >> simp[] >>
  first_x_assum irule >> simp[] >>
  rpt strip_tac >>
  qpat_assum `!k i' t. _`
    (qspecl_then [`SUC k`,`EL k xs`,`t`] mp_tac) >>
  simp[dftIndexedExecTheory.dft_exec_cons_def]
QED

(* A partial row ends at the cursor, before its step and before any child
   trace entered by that step. *)
Theorem focus_history_native_partial_row[local]:
  xs = DROP s.vs_inst_idx bt.bb_instructions /\
  s.vs_inst_idx + k <= LENGTH bt.bb_instructions /\
  EVERY (\x. ~is_terminator x.inst_opcode) (TAKE k xs) /\
  FOLDR (dftIndexedExec$dft_exec_cons fuel C) OK (TAKE k xs) s = OK t /\
  get_instruction bt t.vs_inst_idx = SOME i /\
  (!r x u. r < k /\ x = EL r xs /\
    u.vs_inst_idx = s.vs_inst_idx + r /\
    FOLDR (dftIndexedExec$dft_exec_cons fuel C) OK (TAKE r xs) s = OK u ==>
    P ((a,e,x.inst_id),tf,x,u) /\ EVERY P (trace_step a e fuel C tf x u)) ==>
  ?before after.
    trace_block a e fuel C tf bt s =
      before ++ ((a,e,i.inst_id),tf,i,t)::(trace_step a e fuel C tf i t ++ after) /\
    EVERY P before
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `xs = DROP _ _` SUBST_ALL_TAC >>
  drule_all dftPacketNativeSliceTheory.native_trace_block_prefix_split >>
  disch_then (qspecl_then [`a`,`tf`,`e`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `trace_block a e fuel C tf bt' s ++ _` >>
  `EVERY P (trace_block a e fuel C tf bt' s)` by
    (irule focus_history_native_row_every >>
     qexists `TAKE k (DROP s.vs_inst_idx bt.bb_instructions)` >>
     reverse conj_tac
     >- simp[Abbr `bt'`, listTheory.TAKE_DROP_SWAP, arithmeticTheory.ADD_COMM] >>
     simp[LENGTH_TAKE] >>
     qx_gen_tac `r` >> qx_gen_tac `u` >> strip_tac >>
     qpat_assum `!r x u. _ ==> _`
       (qspecl_then [`r`,`EL r (DROP s.vs_inst_idx bt.bb_instructions)`,`u`] mp_tac) >>
     gvs[EL_TAKE, TAKE_TAKE]) >>
  qexists `trace_block a e fuel C tf bt' s` >> simp[] >>
  drule trace_block_visit >>
  disch_then (qspecl_then [`a`,`fuel`,`tf`,`e`,`C`] SUBST1_TAC) >> simp[]
QED

(* Lift a row-local prefix certificate past the preceding complete rows of
   the same activation. [row] identifies the next entered row and its input. *)
Theorem focus_history_native_rows[local]:
  !fuel a inc s.
    row a (SUC inc) s /\
    (!e t. row a e t /\ e <= inc + fuel ==>
       (?before after. trace_blocks a (e-1) (inc+fuel-(e-1)) C tf t =
          before ++ focus::after /\ EVERY P before) \/
       ?bb sp post. lookup_block t.vs_current_bb tf.fn_blocks = SOME bb /\
         eval_phis t bb.bb_instructions = OK sp /\
         EVERY P (trace_block a e (inc+fuel-e) C tf bb
           (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)) /\
         exec_block (inc+fuel-e) C bb
           (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK post /\
         ~post.vs_halted /\ row a (SUC e) post) /\
    inc < last /\ last <= inc + fuel /\
    (!e t. row a e t ==> e <= last) ==>
    ?before after. trace_blocks a inc fuel C tf s = before ++ focus::after /\
      EVERY P before
Proof
  Induct >- simp[] >>
  rpt gen_tac >> strip_tac >>
  rename1 `trace_blocks a inc (SUC fuel) C tf s = _` >>
  qpat_assum `!e t. row _ _ _ /\ _ ==> _` (qspecl_then [`SUC inc`,`s`] mp_tac) >>
  impl_tac >- simp[] >>
  `SUC inc - 1 = inc /\ inc + SUC fuel - inc = SUC fuel` by decide_tac >>
  disch_then (DISJ_CASES_THEN strip_assume_tac)
  >- (qexistsl [`before`,`after`] >> gvs[]) >>
  rename1 `exec_block _ C bb (sp with vs_inst_idx := _) = OK post` >>
  `SUC inc < last` by
    (qpat_assum `!e t. row _ _ _ ==> _` (qspecl_then [`SUC (SUC inc)`,`post`] mp_tac) >> simp[]) >>
  `SUC inc + fuel = inc + SUC fuel /\ inc + SUC fuel - SUC inc = fuel` by decide_tac >>
  drule_all trace_blocks_enter >>
  disch_then (fn th => once_rewrite_tac[th]) >> simp[] >>
  first_x_assum (qspecl_then [`a`,`SUC inc`,`post`] mp_tac) >>
  impl_tac >-
    (simp[] >> conj_tac >> first_assum (fn th => MATCH_ACCEPT_TAC (SRULE [] th))) >>
  strip_tac >>
  qmatch_goalsub_abbrev_tac `head ++ _` >>
  qexistsl [`head ++ before`,`after`] >> gvs[EVERY_APPEND, Abbr `head`]
QED

(* At a processed INVOKE, the immutable call record is the call made
   by the target fold: its fetched ID fixes the index and hence the state. *)
Theorem focus_history_processed_step[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,ord,hin,h0,SOME (be,hbe),ct,front,closed,brest) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bt.bb_instructions) /\
  r < ct /\ u.vs_inst_idx = LENGTH ps + r /\
  get_instruction bt u.vs_inst_idx = SOME i /\ i = EL r ys /\
  FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK (TAKE r ys) be = OK u /\
  (!a sf tf inc entry order ir out rest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME (IntRet ir out),SOME rest) ==>
    EVERY P (trace_blocks a inc (N-inc) C8 tf entry)) ==>
  EVERY P (trace_step a e (N-e) C8 tf i u)
Proof
  strip_tac >> reverse (Cases_on `i.inst_opcode = INVOKE`)
  >- simp[trace_step_noninvoke] >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_assum `FLOOKUP blocks (a,e) = SOME (_,bt,ps,xs,ys,ord,_,_,_,ct,_,_,_)`
    (fn row => qpat_assum
      `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
        FLOOKUP blocks (a,e) = _ ==> _`
      (strip_assume_tac o C MATCH_MP row)) >>
  `r < LENGTH ys` by decide_tac >>
  `LENGTH ord = LENGTH ys` by (drule LIST_REL_LENGTH >> simp[]) >>
  `EL r ord < LENGTH xs /\ (EL r ys).inst_id = (EL (EL r ord) xs).inst_id /\
   dftStructural$from_block [EL (EL r ord) xs] (EL r ys)` by
    (qpat_assum `LIST_REL _ ord ys`
       (qspec_then `r` mp_tac o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >> simp[]) >>
  `(EL r ys).inst_opcode = INVOKE` by
    (qpat_assum `i = EL r ys` (SUBST1_TAC o SYM) >> asm_rewrite_tac[]) >>
  `EL r ys = EL (EL r ord) xs` by
    (`!xs i. dftStructural$from_block xs i /\ i.inst_opcode = INVOKE ==> MEM i xs` by
       (POP_ASSUM_LIST (K all_tac) >>
        rw[dftStructuralTheory.from_block_def] >>
        Cases_on `j.inst_operands` >> gvs[dftDefsTheory.flip_operands_def] >>
        Cases_on `t` >> gvs[dftDefsTheory.flip_operands_def] >>
        Cases_on `t'` >> gvs[dftDefsTheory.flip_operands_def] >>
        Cases_on `j.inst_opcode` >>
        gvs[dftDefsTheory.is_flippable_def, venomEffectsTheory.is_commutative_def,
          passSharedDefsTheory.is_comparator_def, passSharedDefsTheory.flip_comparison_opcode_def]) >>
     first_x_assum (drule_all_then mp_tac) >> simp[]) >>
  `MEM (EL r ord) (TAKE ct ord)` by
    (simp[Once listTheory.MEM_EL] >> qexists `r` >>
     simp[LENGTH_TAKE, EL_TAKE]) >>
  `(EL (EL r ord) xs).inst_opcode = INVOKE` by
    (qpat_assum `EL r ys = EL (EL r ord) xs` (SUBST1_TAC o SYM) >> simp[]) >>
  qpat_assum `FLOOKUP blocks (a,e) = SOME (_,bt,ps,xs,ys,ord,_,_,_,ct,_,_,_)`
    (fn row => qpat_assum
      `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest.
         FLOOKUP blocks (a,e) = _ ==> !q. _ ==> _`
      (qspec_then `EL r ord` mp_tac o C MATCH_MP row)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_assum `!a e cid q h b0 done_at_call child_entry ret.
       FLOOKUP calls (a,e,cid) = _ ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `FLOOKUP blocks (a,e) = SOME (_,bt,ps,xs,ys,ord,_,_,_,ct,_,_,_)`
    (fn row => qpat_x_assum `FLOOKUP blocks (a,e) = _`
      (map_every (SUBST_ALL_TAC o SYM) o CONJUNCTS o SRULE [row])) >>
  qpat_x_assum `c = EL (EL r ord) xs` SUBST_ALL_TAC >>
  qpat_x_assum `i = EL r ys` SUBST_ALL_TAC >>
  qpat_x_assum `EL r ys = EL (EL r ord) xs` SUBST_ALL_TAC >>
  `b0.vs_inst_idx = u.vs_inst_idx` by
    (qpat_assum `ALL_DISTINCT (MAP _ bt.bb_instructions)` mp_tac >>
     qpat_assum `get_instruction bt b0.vs_inst_idx = _` mp_tac >>
     qpat_assum `get_instruction bt u.vs_inst_idx = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[get_instruction_def, AllCaseEqs()] >> rpt strip_tac >>
     qspecl_then [`MAP (\i. i.inst_id) bt.bb_instructions`, `b0.vs_inst_idx`, `u.vs_inst_idx`]
       mp_tac ALL_DISTINCT_EL_IMP >> simp[EL_MAP]) >>
  `b0 = u` by
    (`b0.vs_inst_idx - LENGTH ps = r` by simp[] >>
     qpat_assum `b0.vs_inst_idx - LENGTH ps = r`
       (fn idx => qpat_assum `!F. N <= F ==> FOLDR _ _ _ _ = OK b0`
          (qspec_then `N` (mp_tac o REWRITE_RULE [idx]))) >>
     qpat_assum `FOLDR _ _ (TAKE r ys) be = OK u` (fn th => simp[NoAsms, th])) >>
  pop_assum SUBST_ALL_TAC >>
  drule_all trace_step_invoke >> disch_then (fn th => once_rewrite_tac[th]) >>
  qpat_assum `case SOME (_,_,_) of NONE => _ | SOME _ => _`
    (strip_assume_tac o SRULE []) >>
  rename1 `FLOOKUP acts ((e,_)::a) = SOME (_,_,_,_,_,_,child_rest)` >>
  `child_rest <> NONE` by
    (qpat_assum `FLOOKUP acts ((e,_)::a) = SOME _`
      (fn lookup => qpat_assum
        `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
        (mp_tac o C MATCH_MP lookup)) >> simp[]) >>
  Cases_on `child_rest` >- (qpat_x_assum `NONE <> NONE` mp_tac >> simp[]) >>
  qpat_x_assum `child_res = SOME (IntRet _ _)` SUBST_ALL_TAC >>
  first_assum (drule_then ACCEPT_TAC)
QED

(* Direct visits use the index in the full block; only the body part of
   the fold can include a returned child. *)
Theorem focus_history_row_prior_step[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,ord,hin,h0,body_ent,ct,front,closed,brest) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bt.bb_instructions) /\
  bt.bb_instructions = ps ++ ys /\ EVERY (\i. is_pseudo i.inst_opcode) ps /\
  start.vs_inst_idx <= LENGTH ps /\ u.vs_inst_idx = start.vs_inst_idx + r /\
  get_instruction bt u.vs_inst_idx = SOME i /\
  FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK
    (TAKE r (DROP start.vs_inst_idx bt.bb_instructions)) start = OK u /\
  (LENGTH ps <= u.vs_inst_idx ==>
    ?be hbe. body_ent = SOME (be,hbe) /\ u.vs_inst_idx - LENGTH ps < ct /\
      FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK
        (DROP start.vs_inst_idx ps) start = OK be) /\
  (!a sf tf inc entry order ir out rest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME (IntRet ir out),SOME rest) ==>
    EVERY P (trace_blocks a inc (N-inc) C8 tf entry)) ==>
  EVERY P (trace_step a e (N-e) C8 tf i u)
Proof
  strip_tac >> Cases_on `u.vs_inst_idx < LENGTH ps`
  >- (`is_pseudo i.inst_opcode` by
        (`LENGTH ps + LENGTH ys > u.vs_inst_idx` by decide_tac >>
         `EL u.vs_inst_idx ps = i` by
           (qpat_x_assum `u.vs_inst_idx = _` kall_tac >>
            qpat_x_assum `get_instruction _ _ = _` mp_tac >>
            simp[get_instruction_def, EL_APPEND_EQN]) >>
         qpat_assum `EVERY _ ps`
           (qspec_then `u.vs_inst_idx` mp_tac o REWRITE_RULE [EVERY_EL]) >>
         simp[]) >>
      `i.inst_opcode <> INVOKE` by (strip_tac >> fs[is_pseudo_def]) >>
      simp[trace_step_noninvoke]) >>
  `LENGTH ps <= u.vs_inst_idx` by decide_tac >>
  first_x_assum (drule_then strip_assume_tac) >>
  `TAKE r (DROP start.vs_inst_idx bt.bb_instructions) =
    DROP start.vs_inst_idx ps ++ TAKE (u.vs_inst_idx - LENGTH ps) ys` by
    (`LENGTH (DROP start.vs_inst_idx ps) <= r /\
      r - LENGTH (DROP start.vs_inst_idx ps) = u.vs_inst_idx - LENGTH ps` by
      (simp[LENGTH_DROP] >> decide_tac) >>
     `start.vs_inst_idx - LENGTH ps = 0` by decide_tac >>
     simp[DROP_APPEND, rich_listTheory.TAKE_APPEND2]) >>
  `i = EL (u.vs_inst_idx - LENGTH ps) ys` by
    (qpat_x_assum `u.vs_inst_idx = _` kall_tac >>
     gvs[get_instruction_def, EL_APPEND_EQN, AllCaseEqs()]) >>
  qabbrev_tac `k = u.vs_inst_idx - LENGTH ps` >>
  `u.vs_inst_idx = LENGTH ps + k` by (fs[Abbr `k`] >> decide_tac) >>
  `FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK (TAKE k ys) be = OK u` by
    (qpat_x_assum `FOLDR _ _ (TAKE r (DROP _ _)) _ = _` mp_tac >>
     `EVERY (\i. ~is_terminator i.inst_opcode) (DROP start.vs_inst_idx ps)` by
       (simp[EVERY_MEM] >> rpt strip_tac >>
        `MEM i' ps` by metis_tac[MEM_DROP_IMP] >>
        qpat_assum `EVERY _ ps` (drule_then assume_tac o REWRITE_RULE [EVERY_MEM]) >>
        Cases_on `i'.inst_opcode` >> gvs[is_pseudo_def, is_terminator_def]) >>
     simp[FOLDR_APPEND, dftRunRelTheory.dft_exec_prefix_continue]) >>
  irule focus_history_processed_step >>
  qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
  qpat_assum `FLOOKUP blocks (a,e) = _`
    (irule_at Any o SRULE [ASSUME ``body_ent = SOME (be:venom_state,hbe:num)``]) >>
  qexists `k` >> simp[]
QED

(* Geometry of a post-PHI row prefix. A fetch at the following index
   excludes the terminal instruction from every earlier prefix. *)
Theorem focus_history_row_fetch[local]:
  bb_well_formed bt /\ r < LENGTH (DROP start.vs_inst_idx bt.bb_instructions) /\
  u.vs_inst_idx = start.vs_inst_idx + r /\
  i = EL r (DROP start.vs_inst_idx bt.bb_instructions) ==>
  get_instruction bt u.vs_inst_idx = SOME i /\
  EVERY (\x. ~is_terminator x.inst_opcode)
    (TAKE r (DROP start.vs_inst_idx bt.bb_instructions))
Proof
  rw[LENGTH_DROP, EL_DROP, get_instruction_def, EVERY_EL, LENGTH_TAKE, EL_TAKE,
     bb_well_formed_def] >>
  `start.vs_inst_idx + r < LENGTH bt.bb_instructions` by decide_tac >>
  simp[] >> strip_tac >>
  `n + start.vs_inst_idx < LENGTH bt.bb_instructions` by decide_tac >>
  `n + start.vs_inst_idx = PRE (LENGTH bt.bb_instructions)` by
    (qpat_assum `!i. _ /\ is_terminator _ ==> _`
      (qspec_then `n + start.vs_inst_idx` mp_tac) >> simp[]) >>
  fs[arithmeticTheory.PRE_SUB1] >> decide_tac
QED

Theorem focus_history_phi_le_pseudos[local]:
  !ps ys. EVERY (\i. ~is_pseudo i.inst_opcode) ys ==>
    phi_prefix_length (ps ++ ys) <= LENGTH ps
Proof
  Induct >-
    (Cases >> simp[phi_prefix_length_def] >> strip_tac >>
     IF_CASES_TAC >> fs[is_pseudo_def]) >>
  simp[phi_prefix_length_def] >> rw[]
QED

Theorem focus_history_packet_row_setup[local]:
  !sf tf inc entry order res nrest bb bt ps xs ys rho hin h0 body_ent ct front closed brest.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h0,body_ent,ct,front,closed,brest) ==>
  ?sp.
    lookup_block hin.vs_current_bb tf.fn_blocks = SOME bt /\
    eval_phis hin bt.bb_instructions = OK sp /\
    sp.vs_current_bb = hin.vs_current_bb /\
    bt.bb_instructions = ps ++ ys /\
    EVERY (\i. is_pseudo i.inst_opcode) ps /\
    bb_well_formed bt /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bt.bb_instructions) /\
    phi_prefix_length bt.bb_instructions <= LENGTH ps /\
    ct <= LENGTH ys /\
    (case body_ent of
       NONE => a = p /\ e = d /\ ct = 0
     | SOME (be,hbe) =>
       FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK
         (DROP (phi_prefix_length bt.bb_instructions) ps)
         (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK be /\
       FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK (TAKE ct ys) be = front /\
       (closed ==> ct = LENGTH ys))
Proof
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_assum `FLOOKUP blocks (a,e) = SOME _`
    (fn row => qpat_assum
      `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
        FLOOKUP blocks (a,e) = _ ==> _`
      (strip_assume_tac o C MATCH_MP row)) >>
  qpat_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`
    (fn row => qpat_x_assum `FLOOKUP acts a = _`
      (map_every (SUBST_ALL_TAC o SYM) o CONJUNCTS o SRULE [row])) >>
  `wf_function tf` by
    (`MEM tf C8.ctx_functions` by
       (qpat_assum `FLOOKUP acts a = SOME _`
          (fn row => qpat_assum
            `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
            (strip_assume_tac o C MATCH_MP row)) >>
        qpat_assum `LIST_REL (\f g. g = dft_fn f) C7.ctx_functions C8.ctx_functions` mp_tac >>
        qpat_assum `MEM sf C7.ctx_functions` mp_tac >>
        qpat_assum `tf = dft_fn sf` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
        drule_all_then (strip_assume_tac o BETA_RULE) LIST_REL_MEM_IMP >> gvs[]) >>
     drule_all lowerDloadPtrRawReachableTheory.o1_ctx_shape_function_wf >> simp[]) >>
  `hin.vs_current_bb = bb.bb_label` by
    (drule venomExecProofsTheory.lookup_block_label >> simp[]) >>
  `MEM bt tf.fn_blocks` by
    (qpat_assum `lookup_block bb.bb_label tf.fn_blocks = SOME bt`
      (mp_tac o MATCH_MP lookup_block_MEM) >> simp[]) >>
  `bb_well_formed bt` by
    (qpat_assum `wf_function tf` (strip_assume_tac o REWRITE_RULE [wf_function_def]) >>
     first_x_assum irule >> simp[]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bt.bb_instructions)` by
    (drule_all dftWfTheory.wf_fn_block_inst_ids_distinct >> simp[]) >>
  drule venomExecProofsTheory.eval_phis_preserves_current_bb >> strip_tac >>
  qexists `sp` >> simp[focus_history_phi_le_pseudos] >>
  qpat_x_assum `case body_ent of NONE => _ | SOME _ => _` mp_tac >>
  Cases_on `body_ent` >> simp[] >> PairCases_on `x` >> simp[]
QED

(* A prior direct fetch and its possible returned child are both covered
   whenever the full-block index is strictly below the retained frontier. *)
Theorem focus_history_packet_row_scan_step[local]:
  !sf tf inc entry order res nrest bb bt ps xs ys ord hin h0 body_ent ct front closed brest.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,ord,hin,h0,body_ent,ct,front,closed,brest) /\
  eval_phis hin bt.bb_instructions = OK sp /\
  start = (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) /\
  r < LENGTH (DROP start.vs_inst_idx bt.bb_instructions) /\
  i = EL r (DROP start.vs_inst_idx bt.bb_instructions) /\
  u.vs_inst_idx = start.vs_inst_idx + r /\
  u.vs_inst_idx < LENGTH ps + ct /\
  FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK
    (TAKE r (DROP start.vs_inst_idx bt.bb_instructions)) start = OK u /\
  (!i u. lookup_block u.vs_current_bb tf.fn_blocks = SOME bt /\
    get_instruction bt u.vs_inst_idx = SOME i /\
    u.vs_inst_idx <= LENGTH ps + ct /\
    (body_ent = NONE ==> u.vs_inst_idx < LENGTH ps) ==> P ((a,e,i.inst_id),tf,i,u)) /\
  (!a sf tf inc entry order ir out rest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME (IntRet ir out),SOME rest) ==>
    EVERY P (trace_blocks a inc (N-inc) C8 tf entry)) ==>
  P ((a,e,i.inst_id),tf,i,u) /\ EVERY P (trace_step a e (N-e) C8 tf i u)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac focus_history_packet_row_setup >>
  `sp' = sp` by
    (qpat_x_assum `eval_phis hin bt.bb_instructions = OK sp'` mp_tac >> simp[]) >>
  pop_assum SUBST_ALL_TAC >>
  drule_all_then strip_assume_tac focus_history_row_fetch >>
  `u.vs_current_bb = start.vs_current_bb` by
    (drule_all_then strip_assume_tac dftAvailabilityTheory.dft_prefix_frame >> simp[]) >>
  `lookup_block u.vs_current_bb tf.fn_blocks = SOME bt` by simp[] >>
  conj_tac >-
    (`u.vs_inst_idx <= LENGTH ps + ct` by decide_tac >>
     `(body_ent = NONE ==> u.vs_inst_idx < LENGTH ps)` by
       (strip_tac >> qpat_x_assum `case body_ent of NONE => _ | SOME _ => _` mp_tac >>
        simp[AllCaseEqs()] >> (gvs[])) >>
     qpat_assum `!i u. _ ==> P _` irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  irule focus_history_row_prior_step >>
  qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
  qpat_assum `FLOOKUP blocks (a,e) = SOME _` (irule_at Any) >>
  qpat_assum `FOLDR _ _ (TAKE r (DROP _ _)) _ = OK u` (irule_at Any) >>
  gvs[] >> strip_tac >>
  Cases_on `body_ent` >- (fs[] >> decide_tac) >>
  PairCases_on `x` >> fs[] >> decide_tac
QED

Theorem focus_history_row_body_fold[local]:
  start.vs_inst_idx <= LENGTH ps /\ EVERY (\i. is_pseudo i.inst_opcode) ps /\
  FOLDR (dftIndexedExec$dft_exec_cons fuel C) OK (DROP start.vs_inst_idx ps) start = OK be ==>
  FOLDR (dftIndexedExec$dft_exec_cons fuel C) OK
    (TAKE (LENGTH ps + k - start.vs_inst_idx)
      (DROP start.vs_inst_idx (ps ++ ys))) start =
  FOLDR (dftIndexedExec$dft_exec_cons fuel C) OK (TAKE k ys) be
Proof
  strip_tac >>
  `LENGTH ps + k - start.vs_inst_idx = LENGTH (DROP start.vs_inst_idx ps) + k` by
    (simp[LENGTH_DROP] >> decide_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (DROP start.vs_inst_idx ps)` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     `MEM i ps` by metis_tac[MEM_DROP_IMP] >>
     qpat_assum `EVERY _ ps` (drule_then assume_tac o REWRITE_RULE [EVERY_MEM]) >>
     Cases_on `i.inst_opcode` >> gvs[is_pseudo_def, is_terminator_def]) >>
  `start.vs_inst_idx - LENGTH ps = 0` by decide_tac >>
  simp[DROP_APPEND, rich_listTheory.TAKE_APPEND2, FOLDR_APPEND,
    dftRunRelTheory.dft_exec_prefix_continue]
QED

Theorem focus_history_packet_row_complete[local]:
  !sf tf inc entry order res nrest bb bt ps xs ys ord hin h0 be hbe ct front brest.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,ord,hin,h0,SOME (be,hbe),ct,front,T,brest) /\
  (!i u. lookup_block u.vs_current_bb tf.fn_blocks = SOME bt /\
    get_instruction bt u.vs_inst_idx = SOME i /\
    u.vs_inst_idx <= LENGTH ps + ct ==> P ((a,e,i.inst_id),tf,i,u)) /\
  (!a sf tf inc entry order ir out rest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME (IntRet ir out),SOME rest) ==>
    EVERY P (trace_blocks a inc (N-inc) C8 tf entry)) ==>
  ?sp. lookup_block hin.vs_current_bb tf.fn_blocks = SOME bt /\
    eval_phis hin bt.bb_instructions = OK sp /\
    EVERY P (trace_block a e (N-e) C8 tf bt
      (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions)) /\
    exec_block (N-e) C8 bt (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = front
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (strip_assume_tac o SRULE []) focus_history_packet_row_setup >>
  qabbrev_tac `start = sp with vs_inst_idx := phi_prefix_length bt.bb_instructions` >>
  `start.vs_inst_idx <= LENGTH ps` by simp[Abbr `start`, IgnAsm `bt.bb_instructions = _`] >>
  `ys <> []` by
    (strip_tac >>
     `ps <> [] /\ is_terminator (LAST ps).inst_opcode` by
       (qpat_assum `bb_well_formed bt` mp_tac >>
        fs[bb_well_formed_def] >> metis_tac[]) >>
     `is_pseudo (LAST ps).inst_opcode` by
       (qpat_assum `EVERY _ ps` (qspec_then `LAST ps` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
        simp[rich_listTheory.MEM_LAST_NOT_NIL]) >>
     qpat_x_assum `is_pseudo _` mp_tac >>
     qpat_x_assum `is_terminator _` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     Cases_on `(LAST ps).inst_opcode` >> simp[is_pseudo_def, is_terminator_def]) >>
  `start.vs_inst_idx < LENGTH bt.bb_instructions` by
    (simp[] >> Cases_on `ys` >> fs[]) >>
  qexists `sp` >> simp[GSYM markerTheory.Abbrev_def] >>
  reverse conj_tac
  >- (`DROP start.vs_inst_idx bt.bb_instructions <> [] /\
       is_terminator (LAST (DROP start.vs_inst_idx bt.bb_instructions)).inst_opcode` by
        (qpat_assum `bb_well_formed bt` (strip_assume_tac o REWRITE_RULE [bb_well_formed_def]) >>
         simp[DROP_EQ_NIL, listTheory.last_drop, IgnAsm `bt.bb_instructions = _`]) >>
      `exec_block (N-e) C8 bt start =
       FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK
         (DROP start.vs_inst_idx bt.bb_instructions) start` by
        (irule dftPacketClosedRowNativeTheory.native_exec_block_terminated_fold >> simp[]) >>
      `FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK
         (DROP start.vs_inst_idx ps) start = OK be` by
        (simp[Abbr `start`, IgnAsm `bt.bb_instructions = _`]) >>
      simp[] >>
      drule_all focus_history_row_body_fold >>
      disch_then (qspecl_then [`ys`,`LENGTH ys`] mp_tac) >>
      simp[TAKE_LENGTH_TOO_LONG, LENGTH_DROP] >>
      fs[TAKE_LENGTH_TOO_LONG]) >>
  irule focus_history_native_row_every >>
  qexists `DROP start.vs_inst_idx bt.bb_instructions` >> simp[NoAsms] >>
  rpt gen_tac >> strip_tac >>
  irule focus_history_packet_row_scan_step >>
  qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
  qpat_assum `FLOOKUP acts a = SOME _` (irule_at Any) >>
  qpat_assum `FLOOKUP blocks (a,e) = SOME _` (irule_at Any) >>
  qpat_assum `FOLDR _ _ (TAKE _ (DROP _ _)) _ = OK _` (irule_at Any) >>
  qexists `sp` >> gvs[LENGTH_DROP, Abbr `start`] >> decide_tac
QED

Theorem focus_history_packet_row_partial[local]:
  !sf tf inc entry order res nrest bb bt ps xs ys ord hin h0 body_ent ct closed brest.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,ord,hin,h0,body_ent,ct,OK t,closed,brest) /\
  get_instruction bt t.vs_inst_idx = SOME i /\
  (case body_ent of
     NONE => phi_prefix_length bt.bb_instructions <= t.vs_inst_idx /\
       t.vs_inst_idx < LENGTH ps /\
       (!sp. eval_phis hin bt.bb_instructions = OK sp ==>
         FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK
           (DROP (phi_prefix_length bt.bb_instructions) (TAKE t.vs_inst_idx ps))
           (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK t)
   | SOME _ => t.vs_inst_idx = LENGTH ps + ct) /\
  (!i u. lookup_block u.vs_current_bb tf.fn_blocks = SOME bt /\
    get_instruction bt u.vs_inst_idx = SOME i /\
    u.vs_inst_idx <= LENGTH ps + ct /\
    (body_ent = NONE ==> u.vs_inst_idx < LENGTH ps) ==> P ((a,e,i.inst_id),tf,i,u)) /\
  (!a sf tf inc entry order ir out rest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME (IntRet ir out),SOME rest) ==>
    EVERY P (trace_blocks a inc (N-inc) C8 tf entry)) ==>
  ?sp before after. lookup_block hin.vs_current_bb tf.fn_blocks = SOME bt /\
    eval_phis hin bt.bb_instructions = OK sp /\
    trace_block a e (N-e) C8 tf bt
      (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) =
      before ++ ((a,e,i.inst_id),tf,i,t)::(trace_step a e (N-e) C8 tf i t ++ after) /\
    EVERY P before /\ P ((a,e,i.inst_id),tf,i,t)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac focus_history_packet_row_setup >>
  qabbrev_tac `start = sp with vs_inst_idx := phi_prefix_length bt.bb_instructions` >>
  `start.vs_inst_idx = phi_prefix_length bt.bb_instructions` by
    simp[Abbr `start`, IgnAsm `bt.bb_instructions = _`] >>
  `start.vs_inst_idx <= LENGTH ps` by simp[IgnAsm `bt.bb_instructions = _`] >>
  `start.vs_inst_idx <= t.vs_inst_idx /\ t.vs_inst_idx <= LENGTH ps + ct` by
    (Cases_on `body_ent` >> gvs[]) >>
  qabbrev_tac `k = t.vs_inst_idx - start.vs_inst_idx` >>
  `t.vs_inst_idx = start.vs_inst_idx + k` by
    (qpat_assum `start.vs_inst_idx <= t.vs_inst_idx` mp_tac >> simp[NoAsms, Abbr `k`] >> decide_tac) >>
  `k < LENGTH (DROP start.vs_inst_idx bt.bb_instructions)` by
    (qpat_assum `get_instruction bt t.vs_inst_idx = SOME i` mp_tac >>
     simp[NoAsms, get_instruction_def, LENGTH_DROP, AllCaseEqs()] >>
     qpat_assum `t.vs_inst_idx = start.vs_inst_idx + k` mp_tac >> (simp[])) >>
  `i = EL k (DROP start.vs_inst_idx bt.bb_instructions)` by
    ((qpat_assum `get_instruction bt t.vs_inst_idx = SOME i` mp_tac >>
     simp[NoAsms, get_instruction_def, AllCaseEqs()] >> strip_tac >>
     simp[EL_DROP] >> (gvs[NoAsms, get_instruction_def, AllCaseEqs(), EL_DROP]))) >>
  `FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK
     (TAKE k (DROP start.vs_inst_idx bt.bb_instructions)) start = OK t` by
    (Cases_on `body_ent`
     >- (qpat_x_assum `case NONE of NONE => _ /\ t.vs_inst_idx < LENGTH ps /\ _ | SOME _ => _`
          (strip_assume_tac o SRULE []) >>
         `TAKE k (DROP start.vs_inst_idx bt.bb_instructions) =
          DROP (phi_prefix_length bt.bb_instructions) (TAKE t.vs_inst_idx ps)` by
           (once_rewrite_tac[listTheory.TAKE_DROP_SWAP] >>
            `k + start.vs_inst_idx = t.vs_inst_idx` by decide_tac >>
            pop_assum (fn th => pure_once_rewrite_tac [th]) >>
            simp[TAKE_APPEND1, IgnAsm `t.vs_inst_idx = _`]) >>
         pop_assum SUBST1_TAC >>
         simp[Abbr `start`, IgnAsm `t.vs_inst_idx = _`] >>
         qpat_assum `!sp. eval_phis hin bt.bb_instructions = OK sp ==> _`
           (drule_then mp_tac) >>
         simp[IgnAsm `t.vs_inst_idx = _`]) >>
     PairCases_on `x` >>
     rpt (qpat_x_assum `case SOME _ of NONE => _ | SOME _ => _`
          (strip_assume_tac o SRULE [])) >>
     `FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK
        (DROP start.vs_inst_idx ps) start = OK x0` by
       simp[IgnAsm `bt.bb_instructions = _`] >>
     drule_all focus_history_row_body_fold >>
     disch_then (qspecl_then [`ys`,`ct`] mp_tac) >> simp[Abbr `k`]) >>
  drule_all_then strip_assume_tac focus_history_row_fetch >>
  `t.vs_current_bb = start.vs_current_bb` by
    (drule_all_then strip_assume_tac dftAvailabilityTheory.dft_prefix_frame >> simp[]) >>
  `lookup_block t.vs_current_bb tf.fn_blocks = SOME bt` by
    simp[Abbr `start`, IgnAsm `bt.bb_instructions = _`] >>
  `P ((a,e,i.inst_id),tf,i,t)` by
    (qpat_assum `!i u. _ ==> P _` irule >> simp[] >> Cases_on `body_ent` >> fs[]) >>
  qexists `sp` >> simp[GSYM markerTheory.Abbrev_def, IgnAsm `i = _`] >>
  irule (SRULE [] focus_history_native_partial_row) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  qexistsl [`k`,`DROP start.vs_inst_idx bt.bb_instructions`] >>
  reverse conj_tac >-
    (qpat_assum `k < LENGTH (DROP _ _)` mp_tac >>
     simp[NoAsms, LENGTH_DROP] >> strip_tac >>
     `start.vs_inst_idx + k <= LENGTH bt.bb_instructions` by decide_tac >>
     simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  irule focus_history_packet_row_scan_step >>
  qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
  qpat_assum `FLOOKUP acts a = SOME _` (irule_at Any) >>
  qpat_assum `FLOOKUP blocks (a,e) = SOME _` (irule_at Any) >>
  qpat_assum `FOLDR _ _ (TAKE r (DROP _ _)) _ = OK u` (irule_at Any) >>
  qexists `sp` >> gvs[LENGTH_DROP, Abbr `start`] >> decide_tac
QED

(* The final-row certificate extends backwards over each complete row. *)
Theorem focus_history_packet_live_rows[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  (!bb bt ps xs ys rho hin h0 body count front closed brest i u e.
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h0,body,count,front,closed,brest) /\
    lookup_block u.vs_current_bb tf.fn_blocks = SOME bt /\
    get_instruction bt u.vs_inst_idx = SOME i /\
    u.vs_inst_idx <= LENGTH ps + count /\
    (body = NONE ==> u.vs_inst_idx < LENGTH ps) ==> P ((a,e,i.inst_id),tf,i,u)) /\
  (!a sf tf inc entry order ir out rest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME (IntRet ir out),SOME rest) ==>
    EVERY P (trace_blocks a inc (N-inc) C8 tf entry)) /\
  (?bb bt ps xs ys rho hin h0 body count front closed brest before after.
    FLOOKUP blocks (a,LAST order) =
      SOME (bb,bt,ps,xs,ys,rho,hin,h0,body,count,front,closed,brest) /\
    trace_blocks a (LAST order-1) (N-(LAST order-1)) C8 tf hin =
      before ++ focus::after /\ EVERY P before) ==>
  ?before after. trace_blocks a inc (N-inc) C8 tf entry = before ++ focus::after /\ EVERY P before
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?bb bt ps xs ys rho hin h0 body count front closed brest before after. _`
    strip_assume_tac >>
  qhdtm_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE[dft_focus_packet_rel_def]) >>
  qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
    (fn th => qpat_assum `FLOOKUP acts a = SOME _` (strip_assume_tac o MATCH_MP th)) >>
  `0 < LENGTH order` by (qpat_assum `order <> []` mp_tac >> simp[NoAsms, GSYM LENGTH_NON_NIL]) >>
  `LAST order = inc + LENGTH order` by
    (`PRE (LENGTH order) < LENGTH order` by decide_tac >>
     simp[LAST_EL, IgnAsm `order = GENLIST _ _`] >>
     qpat_assum `order = GENLIST _ _`
       (fn th => CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV th)))) >>
     simp[EL_GENLIST, IgnAsm `order = GENLIST _ _`] >> decide_tac) >>
  `!e. MEM e order <=> inc < e /\ e <= LAST order` by
    (gen_tac >>
     `MEM e order = MEM e (GENLIST (\i. inc + SUC i) (LENGTH order))` by
       (ntac 2 AP_TERM_TAC >> first_assum ACCEPT_TAC) >>
     pop_assum SUBST1_TAC >>
     simp[MEM_GENLIST, IgnAsm `order = GENLIST _ _`] >>
     eq_tac >> strip_tac >- decide_tac >> qexists `e - inc - 1` >> decide_tac) >>
  qpat_x_assum `order = GENLIST _ _` kall_tac >>
  `!e. inc < e /\ e <= LAST order ==>
     ?bb bt ps xs ys rho hin h0 body count front closed brest.
       FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h0,body,count,front,closed,brest)` by
    (rpt strip_tac >>
     `MEM e order` by simp[] >>
     qpat_assum `!e. MEM e order <=> (a,e) IN FDOM blocks` (drule_then mp_tac o iffLR) >>
     simp[NoAsms, venomExecProofsTheory.FDOM_FLOOKUP, pairTheory.EXISTS_PROD]) >>
  `inc < LAST order` by decide_tac >>
  `LAST order <= N` by
    (qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest. _`
      (fn th => qpat_assum `FLOOKUP blocks (a,LAST order) = SOME _`
        (strip_assume_tac o MATCH_MP th)) >> first_assum ACCEPT_TAC) >>
  `inc + (N-inc) = N` by decide_tac >>
  irule focus_history_native_rows >>
  qexistsl [`LAST order`, `\a e t. inc < e /\ e <= LAST order /\
      ?bb bt ps xs ys rho h0 body count front closed brest.
        FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,t,h0,body,count,front,closed,brest)`] >>
  simp[IgnAsm `inc = _`, IgnAsm `tf = dft_fn sf`, IgnAsm `LAST order = _`] >>
  reverse conj_tac
  >- (qpat_assum `!e. inc < e /\ e <= LAST order ==> _`
        (qspec_then `SUC inc` mp_tac) >>
      (impl_tac >- decide_tac) >> strip_tac >>
      qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest. _`
        (fn th => qpat_assum `FLOOKUP blocks (a,SUC inc) = SOME _`
          (mp_tac o MATCH_MP th)) >>
      qpat_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`
        (fn th => simp[NoAsms,th]) >>
      strip_tac >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `e = LAST order`
  >- (disj1_tac >>
      `t = hin` by
        (qpat_assum `FLOOKUP blocks (a,e) = SOME _` mp_tac >>
         qpat_assum `e = LAST order` SUBST1_TAC >>
         qpat_assum `FLOOKUP blocks (a,LAST order) = SOME _`
           (fn th => simp[NoAsms,th])) >>
      `N + 1 - e = N - (LAST order - 1)` by decide_tac >>
      qexistsl [`before`,`after`] >>
      qpat_assum `N + 1 - e = _` SUBST1_TAC >>
      qpat_assum `e = LAST order` SUBST1_TAC >>
      qpat_assum `t = hin` SUBST1_TAC >>
      conj_tac >-
        (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> first_assum ACCEPT_TAC) >>
      first_assum ACCEPT_TAC) >>
  disj2_tac >>
  `SUC e <= LAST order` by decide_tac >>
  qpat_assum `!e. inc < e /\ e <= LAST order ==> _` (qspec_then `SUC e` mp_tac) >>
  (impl_tac >- decide_tac) >> strip_tac >>
  qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest. _`
    (fn th => qpat_assum `FLOOKUP blocks (a,SUC e) = SOME _` (mp_tac o MATCH_MP th)) >>
  `e <> inc` by decide_tac >>
  qpat_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`
    (fn th => qpat_assum `e <> inc` (fn ne => simp[NoAsms,th,ne])) >>
  strip_tac >>
  qpat_assum `FLOOKUP blocks (a,e) = SOME (_,_,_,_,_,_,_,_,_,_,OK _,T,SOME _)`
    (fn th => qpat_assum `FLOOKUP blocks (a,e) = SOME (_,_,_,_,_,_,t,_,_,_,_,_,_)`
      (mp_tac o REWRITE_RULE [th])) >>
  disch_then (strip_assume_tac o SRULE []) >>
  `?be hbe. pbe = SOME (be,hbe)` by
    (Cases_on `pbe`
     >- (qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest. _`
           (fn th => qpat_assum `FLOOKUP blocks (a,e) = SOME (_,_,_,_,_,_,_,_,NONE,_,OK _,T,_)`
             (strip_assume_tac o MATCH_MP th)) >>
         qpat_x_assum `case NONE of NONE => _ | SOME _ => _`
           (strip_assume_tac o SRULE []) >>
         qpat_assum `FLOOKUP blocks (a,e) = SOME (_,_,_,_,_,_,_,_,NONE,_,OK _,T,_)` mp_tac >>
         qpat_assum `a = p` SUBST1_TAC >> qpat_assum `e = d` SUBST1_TAC >>
         qpat_assum `FLOOKUP blocks (p,d) = SOME (_,_,_,_,_,_,_,_,_,_,_,F,_)`
           (fn th => simp[NoAsms,th])) >>
     PairCases_on `x` >> simp[]) >>
  qpat_x_assum `pbe = SOME _` SUBST_ALL_TAC >>
  `?sp. lookup_block pin.vs_current_bb tf.fn_blocks = SOME pt /\
    eval_phis pin pt.bb_instructions = OK sp /\
    EVERY P (trace_block a e (N-e) C8 tf pt
      (sp with vs_inst_idx := phi_prefix_length pt.bb_instructions)) /\
    exec_block (N-e) C8 pt (sp with vs_inst_idx := phi_prefix_length pt.bb_instructions) = OK hin'` by
    (irule focus_history_packet_row_complete >>
     qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
     qpat_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)` (irule_at Any) >>
     qpat_assum `FLOOKUP blocks (a,e) = SOME (pb,pt,pps,pxs,pys,prho,pin,ph,SOME _,pc,OK hin',T,SOME pu)`
       (irule_at Any) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `!bb bt ps xs ys rho hin h0 body count front closed brest i u e. _ ==> P _` irule >>
     qpat_assum `FLOOKUP blocks (a,e) = SOME (pb,pt,pps,pxs,pys,prho,pin,ph,SOME _,pc,OK hin',T,SOME pu)`
       (irule_at Any) >> simp[]) >>
  qpat_assum `pin = t` (SUBST1_TAC o SYM) >>
  qpat_assum `pt = bt''` (SUBST1_TAC o SYM) >>
  qexistsl [`pt`,`sp'`,`hin'`] >> simp[run_block_non_phis_def]
QED

Theorem focus_history_packet_last_row[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,ord,hin,h0,body_ent,ct,OK t,closed,brest) /\
  0 < e /\ e <= N /\ get_instruction bt t.vs_inst_idx = SOME i /\
  (case body_ent of
     NONE => phi_prefix_length bt.bb_instructions <= t.vs_inst_idx /\
       t.vs_inst_idx < LENGTH ps /\
       (!sp. eval_phis hin bt.bb_instructions = OK sp ==>
         FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK
           (DROP (phi_prefix_length bt.bb_instructions) (TAKE t.vs_inst_idx ps))
           (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK t)
   | SOME _ => t.vs_inst_idx = LENGTH ps + ct) /\
  (!i u. lookup_block u.vs_current_bb tf.fn_blocks = SOME bt /\
    get_instruction bt u.vs_inst_idx = SOME i /\
    u.vs_inst_idx <= LENGTH ps + ct /\
    (body_ent = NONE ==> u.vs_inst_idx < LENGTH ps) ==> P ((a,e,i.inst_id),tf,i,u)) /\
  (!a sf tf inc entry order ir out rest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME (IntRet ir out),SOME rest) ==>
    EVERY P (trace_blocks a inc (N-inc) C8 tf entry)) ==>
  ?before after.
    trace_blocks a (e-1) (N-(e-1)) C8 tf hin =
      before ++ ((a,e,i.inst_id),tf,i,t)::(trace_step a e (N-e) C8 tf i t ++ after) /\
    EVERY P before /\ P ((a,e,i.inst_id),tf,i,t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac focus_history_packet_row_partial >>
  drule_all trace_blocks_enter >> disch_then (qspecl_then [`a`,`N-e`,`e-1`,`C8`] mp_tac) >>
  `SUC (e-1) = e /\ SUC (N-e) = N-(e-1)` by decide_tac >>
  simp[] >> strip_tac >>
  qexists `before` >> simp[GSYM APPEND_ASSOC]
QED

(* A last row may end at the focus itself or enter a live child whose
   prefix reaches the focus. The unprocessed suffix is never inspected. *)
Theorem focus_history_packet_at_front[local]:
  !rho body.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h0,body,ct,OK t,closed,brest) /\
  e = LAST order /\ get_instruction bt t.vs_inst_idx = SOME i /\
  (case body of
     NONE => phi_prefix_length bt.bb_instructions <= t.vs_inst_idx /\
       t.vs_inst_idx < LENGTH ps /\
       (!sp. eval_phis hin bt.bb_instructions = OK sp ==>
         FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK
           (DROP (phi_prefix_length bt.bb_instructions) (TAKE t.vs_inst_idx ps))
           (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK t)
   | SOME _ => t.vs_inst_idx = LENGTH ps + ct) /\
  (!e bb bt ps xs ys rho hin h0 body count front closed brest i u.
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h0,body,count,front,closed,brest) /\
    lookup_block u.vs_current_bb tf.fn_blocks = SOME bt /\
    get_instruction bt u.vs_inst_idx = SOME i /\
    u.vs_inst_idx <= LENGTH ps + count /\
    (body = NONE ==> u.vs_inst_idx < LENGTH ps) ==> P ((a,e,i.inst_id),tf,i,u)) /\
  (!a sf tf inc entry order ir out rest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME (IntRet ir out),SOME rest) ==>
    EVERY P (trace_blocks a inc (N-inc) C8 tf entry)) /\
  ((focus = ((a,e,i.inst_id),tf,i,t)) \/
   (?b c. trace_step a e (N-e) C8 tf i t = b ++ focus::c /\ EVERY P b)) ==>
  ?before after. trace_blocks a inc (N-inc) C8 tf entry = before ++ focus::after /\ EVERY P before
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `0 < e /\ e <= N` by
    (qhdtm_x_assum `dft_focus_packet_rel`
       (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     conj_tac >-
       (qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
          (fn th => qpat_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`
            (strip_assume_tac o MATCH_MP th)) >>
        `MEM e order` by
          (qpat_assum `e = LAST order` SUBST1_TAC >>
           irule MEM_LAST_NOT_NIL >> first_assum ACCEPT_TAC) >>
        qpat_x_assum `MEM e order` mp_tac >>
        qpat_assum `order = GENLIST _ _` (fn th => PURE_ONCE_REWRITE_TAC[th]) >>
        simp[NoAsms, MEM_GENLIST]) >>
     qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest. _`
       (fn th => qpat_assum `FLOOKUP blocks (a,e) = SOME _` (strip_assume_tac o MATCH_MP th)) >>
     first_assum ACCEPT_TAC) >>
  `?b c. trace_blocks a (e-1) (N-(e-1)) C8 tf hin =
      b ++ ((a,e,i.inst_id),tf,i,t)::(trace_step a e (N-e) C8 tf i t ++ c) /\
      EVERY P b /\ P ((a,e,i.inst_id),tf,i,t)` by
    (irule focus_history_packet_last_row >>
     qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
     qpat_assum `FLOOKUP acts a = SOME _` (irule_at Any) >>
     qpat_assum `FLOOKUP blocks (a,e) = SOME _` (irule_at Any) >>
     simp[IgnAsm `e = LAST order`] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  `?b' c'. trace_blocks a (e-1) (N-(e-1)) C8 tf hin = b' ++ focus::c' /\
    EVERY P b'` by
    (qpat_x_assum `focus = _ \/ _` strip_assume_tac
     >- (qexists `b` >> simp[IgnAsm `e = LAST order`]) >>
     rename1 `trace_step a e (N-e) C8 tf i t = cb ++ focus::ca` >>
     qexistsl [`b ++ ((a,e,i.inst_id),tf,i,t)::cb`, `ca ++ c`] >>
     simp[]) >>
  irule focus_history_packet_live_rows >>
  qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
  qpat_assum `FLOOKUP acts a = SOME _` (irule_at Any) >>
  qpat_assum `e = LAST order` (SUBST1_TAC o SYM) >>
  qpat_assum `FLOOKUP blocks (a,e) = SOME _` (irule_at Any) >>
  rpt (first_assum (irule_at Any)) >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem focus_history_packet_spine[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst st oms om hs hist) raw_slots sites unused /\
  (!a sf tf inc entry order res nrest e bb bt ps xs ys rho hin h0 body count front closed brest i u.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h0,body,count,front,closed,brest) /\
    lookup_block u.vs_current_bb tf.fn_blocks = SOME bt /\
    get_instruction bt u.vs_inst_idx = SOME i /\
    u.vs_inst_idx <= LENGTH ps + count /\
    (body = NONE ==> u.vs_inst_idx < LENGTH ps) ==> P ((a,e,i.inst_id),tf,i,u)) /\
  (!a sf tf inc entry order ir out rest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME (IntRet ir out),SOME rest) ==>
    EVERY P (trace_blocks a inc (N-inc) C8 tf entry)) ==>
  !k. k <= LENGTH p ==>
    ?sf tf inc entry order before after.
      FLOOKUP acts (DROP k p) = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
      trace_blocks (DROP k p) inc (N-inc) C8 tf entry =
        before ++ ((p,d,inst.inst_id),fn,inst,st)::after /\
      EVERY P before
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def] o
     SPEC_ALL) >>
  qpat_x_assum `JointConfig _ _ _ _ _ _ _ _ _ _ _ = _`
    (map_every (SUBST_ALL_TAC o SYM) o CONJUNCTS o SRULE []) >>
  Induct_on `k` >-
    (strip_tac >> pure_rewrite_tac[DROP_0] >>
     qpat_assum `FLOOKUP acts p = SOME (_,fn,_,_,_,NONE,NONE)`
       (irule_at Any) >>
     irule focus_history_packet_at_front >>
     qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
     qpat_assum `FLOOKUP acts p = SOME (_,fn,_,_,_,NONE,NONE)` (irule_at Any) >>
     qpat_assum `FLOOKUP blocks (p,d) = SOME _` (irule_at Any) >>
     simp[] >>
     Cases_on `body_entry` >>
     qpat_x_assum `case _ of NONE => _ | SOME _ => _` (strip_assume_tac o SRULE []) >>
     simp[ADD_COMM] >> rpt strip_tac >>
     qpat_assum `FOLDR _ _ _ _ = OK st` mp_tac >>
     qpat_assum `eval_phis in_state bt.bb_instructions = OK _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  strip_tac >>
  `k <= LENGTH p /\ k < LENGTH p` by decide_tac >>
  qpat_x_assum `k <= LENGTH p ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!k. k < LENGTH p ==> ?sf tf inc entry order bb bt ps xs ys rho hin h0 be hbe count q h b0 done_at_call child_entry cid e a. _`
    (drule_then strip_assume_tac) >>
  `DROP k p = (e,cid)::a` by
    (drule DROP_CONS_EL >> simp[]) >>
  rename1 `FLOOKUP blocks (a,e) = SOME (_,parent_bt,parent_ps,parent_xs,_,_,_,_,SOME _,parent_count,OK b0,F,NONE)` >>
  rename1 `FLOOKUP acts a = SOME (_,parent_tf,_,_,_,NONE,NONE)` >>
  `?b c. trace_step a e (N-e) C8 parent_tf (EL q parent_xs) b0 =
      b ++ ((p,d,inst.inst_id),fn,inst,st)::c /\ EVERY P b` by
    (qpat_assum `!a e cid q h b0 done_at_call child_entry ret. FLOOKUP calls (a,e,cid) = _ ==> _`
       (drule_then strip_assume_tac) >>
     qpat_assum `FLOOKUP blocks (a,e) = SOME (_,_,_,parent_xs,_,_,_,_,_,_,_,_,_)`
       (fn th => qpat_assum `FLOOKUP blocks (a,e) = SOME (_,_,_,xs',_,_,_,_,_,_,_,_,_)`
         (strip_assume_tac o SRULE[th])) >>
     qpat_assum `DROP k p = (e,cid)::a` SUBST_ALL_TAC >>
     qpat_assum `FLOOKUP acts ((e,cid)::a) = SOME (_,_,e,child_entry,_,_,_)`
       (fn th => qpat_assum `FLOOKUP acts ((e,cid)::a) = SOME (_,_,_,_,_,NONE,NONE)`
         (strip_assume_tac o SRULE[th])) >>
     qpat_assum `e = inc'` SUBST_ALL_TAC >>
     qexistsl [`before`,`after`] >>
     drule_all dftGasFromListTraceDefsTheory.trace_step_invoke >>
     simp[IgnAsm `a = DROP (SUC k) p`]) >>
  qpat_assum `a = DROP (SUC k) p` (SUBST1_TAC o SYM) >>
  qpat_assum `FLOOKUP acts a = SOME (_,_,_,_,_,NONE,NONE)` (irule_at Any) >>
  irule focus_history_packet_at_front >>
  qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
  qpat_assum `FLOOKUP acts a = SOME (_,_,_,_,_,NONE,NONE)` (irule_at Any) >>
  qpat_assum `FLOOKUP blocks (a,e) = SOME _` (irule_at Any) >>
  qexists `EL q parent_xs` >> simp[] >>
  disj2_tac >> qexistsl [`b`,`c`] >> simp[]
QED

Theorem focus_history_packet_root_prefix[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst st oms om hs hist) raw_slots sites unused /\
  (!a sf tf inc entry order res nrest e bb bt ps xs ys rho hin h0 body count front closed brest i u.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h0,body,count,front,closed,brest) /\
    lookup_block u.vs_current_bb tf.fn_blocks = SOME bt /\
    get_instruction bt u.vs_inst_idx = SOME i /\
    u.vs_inst_idx <= LENGTH ps + count /\
    (body = NONE ==> u.vs_inst_idx < LENGTH ps) ==> P ((a,e,i.inst_id),tf,i,u)) /\
  (!a sf tf inc entry order ir out rest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME (IntRet ir out),SOME rest) ==>
    EVERY P (trace_blocks a inc (N-inc) C8 tf entry)) /\
  ALL_DISTINCT (MAP FST (trace_blocks [] 0 N C8 root_tf root_entry)) /\
  j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) /\
  EL j (trace_blocks [] 0 N C8 root_tf root_entry) = ((p,d,inst.inst_id),fn,inst,st) ==>
  EVERY P (TAKE j (trace_blocks [] 0 N C8 root_tf root_entry))
Proof
  strip_tac >>
  `?sf tf inc entry order before after.
     FLOOKUP acts [] = SOME (sf,tf,inc,entry,order,NONE,NONE) /\
     trace_blocks [] inc (N-inc) C8 tf entry =
       before ++ ((p,d,inst.inst_id),fn,inst,st)::after /\ EVERY P before` by
    (mp_tac (DISCH_ALL (Q.SPEC `LENGTH (p : (num # num) list)`
       (UNDISCH focus_history_packet_spine))) >> simp[DROP_LENGTH_NIL]) >>
  `?order. FLOOKUP acts [] = SOME (root_sf,root_tf,0,root_entry,order,NONE,NONE)` by
    (qhdtm_assum `dft_focus_packet_rel`
       (strip_assume_tac o REWRITE_RULE[dft_focus_packet_rel_def]) >>
     qpat_assum `FLOOKUP acts [] = SOME (root_sf,root_tf,0,root_entry,_,NONE,NONE)`
       (irule_at Any)) >>
  qpat_assum `FLOOKUP acts [] = SOME (root_sf,root_tf,0,root_entry,_,NONE,NONE)`
    (fn th => qpat_x_assum `FLOOKUP acts [] = SOME (sf,tf,inc,entry,_,NONE,NONE)`
      (strip_assume_tac o SRULE[th])) >>
  gvs[] >>
  `j = LENGTH before` by
    (qmatch_asmsub_abbrev_tac `visits = before ++ [focus] ++ after` >>
     `j = LENGTH (MAP FST before)` suffices_by simp[] >>
     irule rich_listTheory.ALL_DISTINCT_EL_APPEND >>
     qexistsl [`MAP FST after`, `MAP FST visits`] >>
     simp[EL_MAP, Abbr `visits`, Abbr `focus`]) >>
  qpat_x_assum `j = LENGTH before` SUBST1_TAC >>
  pure_once_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[rich_listTheory.TAKE_LENGTH_APPEND]
QED

Theorem focus_history_guarded_row_index[local]:
  !rho body count.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h0,body,count,front,closed,brest) /\
  get_instruction bt s.vs_inst_idx = SOME i /\
  s.vs_inst_idx <= LENGTH ps + count /\
  (body = NONE ==> s.vs_inst_idx < LENGTH ps) /\
  (inv_memory_observation i.inst_opcode \/ is_fallible i \/ i.inst_opcode = INVOKE) ==>
  IS_SOME body /\ LENGTH ps <= s.vs_inst_idx /\
  s.vs_inst_idx - LENGTH ps < LENGTH ys /\ s.vs_inst_idx - LENGTH ps <= count
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `~is_pseudo i.inst_opcode` by
    (Cases_on `i.inst_opcode` >>
     gvs[is_pseudo_def, dftDefsTheory.is_fallible_def,
         venomEffectsTheory.opcode_fail_class_def,
         dftGasInvCrossingProbeTheory.inv_memory_observation_def]) >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE[dft_focus_packet_rel_def]) >>
  qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest. _`
    (fn th => qpat_assum `FLOOKUP blocks (a,e) = SOME _`
      (strip_assume_tac o MATCH_MP th)) >>
  qpat_assum `bt.bb_instructions = ps ++ ys` (mk_asm "row") >>
  qpat_assum `EVERY _ ps` (mk_asm "pseudo") >>
  qpat_assum `get_instruction bt s.vs_inst_idx = SOME i` (mk_asm "fetch") >>
  qpat_assum `s.vs_inst_idx <= LENGTH ps + _` (mk_asm "bound") >>
  qpat_assum `_ = NONE ==> s.vs_inst_idx < LENGTH ps` (mk_asm "none") >>
  qpat_assum `~is_pseudo i.inst_opcode` (mk_asm "not_pseudo") >>
  POP_ASSUM_LIST (map_every assume_tac o List.filter (fn th =>
    can markerSyntax.dest_label (concl th))) >>
  asm_x "row" assume_tac >> asm_x "pseudo" assume_tac >>
  asm_x "bound" assume_tac >> asm_x "none" assume_tac >> asm_x "not_pseudo" assume_tac >>
  asm_x "fetch" mp_tac >> simp[get_instruction_def, AllCaseEqs()] >> strip_tac >>
  `LENGTH ps <= s.vs_inst_idx` by
    (spose_not_then assume_tac >>
     `s.vs_inst_idx < LENGTH ps` by decide_tac >>
     `i = EL s.vs_inst_idx ps` by gvs[EL_APPEND_EQN] >>
     `MEM i ps` by simp[EL_MEM] >>
     qpat_assum `EVERY _ ps` (drule_then mp_tac o REWRITE_RULE[EVERY_MEM]) >> simp[]) >>
  simp[optionTheory.IS_SOME_EQ_NOT_NONE] >> strip_tac >> gvs[]
QED

Theorem focus_history_prefix_row_coverage[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst st oms om hs hist) raw_slots sites unused /\
  ALL_DISTINCT (MAP FST (trace_blocks [] 0 N C8 root_tf root_entry)) /\
  j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) /\
  EL j (trace_blocks [] 0 N C8 root_tf root_entry) = ((p,d,inst.inst_id),fn,inst,st) /\
  (!a0 sf0 tf0 inc0 entry0 order0 ir out rest a e id tf i s.
    FLOOKUP acts a0 = SOME (sf0,tf0,inc0,entry0,order0,SOME (IntRet ir out),SOME rest) /\
    MEM ((a,e,id),tf,i,s) (trace_blocks a0 inc0 (N-inc0) C8 tf0 entry0) ==>
    ?sf inc entry order res nrest bb bt ps xs ys rho hin h0 body count front closed brest.
      FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
      FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h0,body,count,front,closed,brest) /\
      id = i.inst_id /\ lookup_block s.vs_current_bb tf.fn_blocks = SOME bt /\
      get_instruction bt s.vs_inst_idx = SOME i /\
      (LENGTH ps <= s.vs_inst_idx ==> IS_SOME body /\
        s.vs_inst_idx - LENGTH ps < LENGTH ys /\ s.vs_inst_idx - LENGTH ps < count)) /\
  h < j /\
  EL h (trace_blocks [] 0 N C8 root_tf root_entry) = ((a,e,id),tf,i,s) ==>
  ?sf inc entry order res nrest bb bt ps xs ys rho hin h0 body count front closed brest.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
    FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho,hin,h0,body,count,front,closed,brest) /\
    id = i.inst_id /\ lookup_block s.vs_current_bb tf.fn_blocks = SOME bt /\
    get_instruction bt s.vs_inst_idx = SOME i /\
    (body = NONE ==> s.vs_inst_idx < LENGTH ps) /\
    (inv_memory_observation i.inst_opcode \/ is_fallible i \/ i.inst_opcode = INVOKE ==>
      IS_SOME body /\ LENGTH ps <= s.vs_inst_idx /\
      s.vs_inst_idx - LENGTH ps < LENGTH ys /\ s.vs_inst_idx - LENGTH ps <= count)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `P = \((path,depth,key),f,ins,state).
    ?sf inc entry order res nrest bb bt ps xs ys rho hin h0 body count front closed brest.
      FLOOKUP acts path = SOME (sf,f,inc,entry,order,res,nrest) /\
      FLOOKUP blocks (path,depth) = SOME (bb,bt,ps,xs,ys,rho,hin,h0,body,count,front,closed,brest) /\
      key = ins.inst_id /\ lookup_block state.vs_current_bb f.fn_blocks = SOME bt /\
      get_instruction bt state.vs_inst_idx = SOME ins /\
      state.vs_inst_idx <= LENGTH ps + count /\
      (body = NONE ==> state.vs_inst_idx < LENGTH ps)` >>
  `EVERY P (TAKE j (trace_blocks [] 0 N C8 root_tf root_entry))` by
    (irule focus_history_packet_root_prefix >>
     rpt (first_assum (irule_at Any)) >>
     reverse conj_tac
     >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
         simp[Abbr `P`] >> rpt (first_assum (irule_at Any))) >>
     simp[EVERY_MEM] >> rpt gen_tac >> disch_tac >>
     qx_gen_tac `v` >> disch_tac >>
     PairCases_on `v` >>
     qpat_assum `!a0 sf0 tf0 inc0 entry0 order0 ir out rest a e id tf i s. _`
       (drule_all_then strip_assume_tac) >>
     rename1 `get_instruction bt' sv.vs_inst_idx = SOME iv` >>
     rename1 `FLOOKUP blocks _ = SOME (_,bt',prefix,_,_,_,_,_,_,_,_,_,_)` >>
     simp[Abbr `P`] >> rpt (first_assum (irule_at Any)) >>
     Cases_on `LENGTH prefix <= sv.vs_inst_idx` >>
     gvs[optionTheory.IS_SOME_EQ_NOT_NONE] >> decide_tac) >>
  `P ((a,e,id),tf,i,s)` by
    (qpat_x_assum `EVERY P _` mp_tac >>
     simp[EVERY_EL, LENGTH_TAKE, EL_TAKE] >>
     disch_then (qspec_then `h` mp_tac) >> simp[]) >>
  pop_assum mp_tac >> simp[Abbr `P`] >> strip_tac >>
  rpt (first_assum (irule_at Any)) >>
  conj_tac >- (first_assum ACCEPT_TAC) >> disch_tac >>
  rename1 `FLOOKUP blocks (a,e) = SOME (_,_,ps,_,_,_,_,_,_,ct,_,_,_)` >>
  `s.vs_inst_idx <= LENGTH ps + ct` by decide_tac >>
  drule_all focus_history_guarded_row_index >> simp[]
QED

(* Scratch statement for elaboration and independent review.
   Use the actual stopped six tables and their C8 chronology. Split a
   compatible raw at Mcut, with the unread suffix and [0w] as tail.
   The bounded lowered-memory conclusion is separate from the original
   conditional static-memory clause. *)
Theorem focus_source_cut_provider:
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    o1_source_unit_ok unit /\ unit_entry_no_params unit /\
    unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
    o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp /\
    code_layout_valid vs0 /\
    unit_shape_ok out.po_unit /\
    generate_context_plan out.po_unit.cu_context = SOME cpl /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
    (fin = asm_opt_finalizer ==>
       label_flow_ok unit.cu_context /\
       (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
                  ~MEM (Label "code_end") inst.inst_operands) /\
       EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                         ds.ds_items) unit.cu_data_segment /\
       ((?fn inst. MEM fn unit.cu_context.ctx_functions /\
                   MEM inst (fn_insts fn) /\
                   MEM (Label "runtime_begin") inst.inst_operands) ==>
        EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment) /\
       LENGTH vs0.vs_data_section < dimword (:256) DIV 2) /\
    (vs0.vs_call_ctx.cc_static ==>
       !fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
                 ~MEM (Label "runtime_begin") inst.inst_operands) /\
    vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
    codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
    asm_frame_rel_tail [] prog' vs0.vs_data_section es0
      (entry_asm_state vs0 es0 with
        as_code := assemble prog' ++ vs0.vs_data_section) es0 /\
    unit.cu_context.ctx_entry = SOME nm /\
    lookup_function nm unit.cu_context.ctx_functions = SOME entryfn /\
    fn_entry_label entryfn = SOME lbl /\
    w2n vs0.vs_initial_fmp <= w2n fmp /\ w2n fmp < 2 ** 254 /\
    unit_alloca_budget unit.cu_context +
      32 * ctx_dload_count unit.cu_context <= w2n fmp /\
    (!gs. ?D f extra.
      dead_wf D /\
      (fin = asm_opt_finalizer ==>
         !fn inst s.
           raw_reachable (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>)
             unit.cu_context fn inst s /\
           gas_cut (MIN (LENGTH (markf gs)) (LENGTH gs))
             (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>) s ==>
           inst_dload_in_section inst s) /\
      o1_safe_upto D lo (MIN (LENGTH (markf gs)) (LENGTH gs))
        unit.cu_context (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
      MAP project
        (gas_events_blocks f unit.cu_context entryfn
          (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp;
                      vs_prev_bb := NONE;
                      vs_current_bb := lbl; vs_inst_idx := 0|>)) =
        markf gs ++ extra) /\
    run_call es0 = SOME (result,final) /\
    ~frame_resource_starved es0 result final /\
    run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit
      (init_ir_supply unit) = SOME (pre,t) /\
    pre.cu_context.ctx_entry = SOME nm /\
    run_callee_first rpolicy o1_fn_passes
      (fcg_postorder (fcg_analyze pre.cu_context) nm)
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)) t =
      SOME (out.po_unit,t') /\
    stage 0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
    stage 9 = out.po_unit.cu_context /\
    (!k. k < 9 ==> ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
      (stage k) (stage (SUC k))) /\
    (!k. k <= 9 ==> o1_ctx_shape (stage k) /\
      EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  0 < N /\
  root_entry = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl7; vs_inst_idx := 0|> /\
  (stage 7).ctx_entry = SOME nm /\ (stage 8).ctx_entry = SOME nm /\
  lookup_function nm (stage 7).ctx_functions = SOME root_sf /\
  lookup_function nm (stage 8).ctx_functions = SOME root_tf /\
  fn_entry_label root_sf = SOME lbl7 /\ fn_entry_label root_tf = SOME lbl7 /\
  joint_initial vs0 (stage 8) q80 /\ joint_initial vs0 (stage 9) q90 /\
  joint_trace vs0 (stage 8) q80 evs8 qs8 (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8) /\
  joint_trace vs0 (stage 9) q90 evs9 qs9 (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) /\
  cfg_norm_joint_cursors (stage 8) (stage 9) (schedules,current,saved) (JointConfig stk8 PG8 G8 tn8 fn8
    inst8 s8 oms8 om8 hs8 hist8) (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) /\
  asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    prog asm_fuel (entry_asm_state vs0 es0) = AsmOK ast /\
  (fin = K SOME ==> normal_frame_plan rpolicy out.po_unit cpl prog (vs0 with
    <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp; vs_return_pc_token := 0w;
    vs_inst_idx := 0|>) es0 (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) ast) /\
  (fin = asm_opt_finalizer ==>
    sym_steps prog (asm_data_env prog vs0.vs_code) asm_fuel (sym_init (entry_asm_state vs0 es0)) = SymOK ss /\
    normal_frame_symbolic_plan (asm_data_env prog vs0.vs_code) rpolicy out.po_unit cpl prog vs0 es0
      (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) ast ss) /\
  dft_focus_packet_rel N (stage 7) (stage 8) root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8
      om8 hs8 hist8) raw_slots sites unused /\
  j = LENGTH evs8 /\ LENGTH evs8 <= LENGTH evs9 /\ LENGTH (TAKE j (dftGasFromListTraceDefs$trace_blocks []
    0 N (stage 8) root_tf root_entry)) = j /\
  j < LENGTH (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8) root_tf root_entry) /\ obs =
    dftGasFromListTraceDefs$trace_gas (TAKE j (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8)
    root_tf root_entry)) /\
  EL j (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8) root_tf root_entry) =
    ((p,d,inst8.inst_id),fn8,inst8,s8) /\
  LENGTH raw_slots = LENGTH sites /\
  PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es0) ==>
  (?sf inc entry order res nrest bb bt ps xs ys rho in_state h0
      body_entry count front closed brest.
      FLOOKUP acts p = SOME (sf,fn8,inc,entry,order,res,nrest) /\
      FLOOKUP blocks (p,d) =
        SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
      get_instruction bt s8.vs_inst_idx = SOME inst8 /\
      ((inv_memory_observation inst8.inst_opcode \/ is_fallible inst8 \/
        inst8.inst_opcode = INVOKE \/ is_terminator inst8.inst_opcode) ==>
      ?q z src_inst cuts levels Mcut Ecut Kcut mr er kr.
        src_inst = EL (LENGTH z)
          (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
        ((IS_SOME body_entry /\ LENGTH ps <= s8.vs_inst_idx /\
          s8.vs_inst_idx - LENGTH ps < LENGTH rho /\
          q = EL (s8.vs_inst_idx - LENGTH ps) rho /\ q < LENGTH xs /\
          EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
          (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)) /\
          EL q xs = inst8 /\
          z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs) \/
         (p = p /\ d = d /\ s8 = s8 /\ body_entry = NONE /\
          s8.vs_inst_idx < LENGTH ps /\ q = 0 /\
          z = DROP (phi_prefix_length bb.bb_instructions) (TAKE s8.vs_inst_idx ps))) /\
        MAP (\(ai,ds,ei,qi,zi). ai) cuts =
          REVERSE (GENLIST (\i. DROP i p) (SUC (LENGTH p))) /\
        LENGTH cuts = LENGTH levels /\
        (!i ai ds ei qi zi.
          i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
          ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
            ini hi bei counti fronti closedi resti later.
            FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
            FLOOKUP blocks (ai,ei) =
              SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
            orderi = ds ++ ei::later /\
            (if SUC i = LENGTH cuts then
              ai = p /\ ei = d /\ qi = q /\ zi = z
            else
              ?cid h b0 done_at_call child_entry ret.
                EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
                FLOOKUP calls (ai,ei,cid) =
                  SOME (qi,h,b0,done_at_call,child_entry,ret) /\
                qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
                zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
                EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
                (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==>
                  MEM r done_at_call)) /\
            EL i levels =
              (sfi,
               MAP (\f.
                 (FST (THE (FLOOKUP blocks (ai,f))),f,
                  DROP (phi_prefix_length
                    (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
                    (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
                 [(bbi,ei,zi)],
               if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
        Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
        Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cuts) /\
        Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cuts) /\
        raw_slots = Mcut ++ mr /\ sites = Ecut ++ er /\ (FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab
          ([],e)))) (FST (SND (SND (SND (SND (THE (FLOOKUP acts []))))))))) = Kcut ++ kr /\
        LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
        (!F gs tail.
          N <= F /\
          LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
          (?extra. Ecut = FST (rooted_eval F (stage 7) levels
            (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
          (case SND (rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail)) of
            OK u =>
              FST (rooted_eval F (stage 7) levels
                (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
              u.vs_gas_readings = tail /\
              (?before after.
                dftGasFromListTraceDefs$trace_blocks [] 0 F (stage 7) root_sf
                  (root_entry with vs_gas_readings := gs ++ tail) =
                  before ++ [((p,d,(EL (LENGTH z)
                    (DROP (phi_prefix_length bb.bb_instructions)
                      bb.bb_instructions)).inst_id),sf,
                    EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
                      bb.bb_instructions),u)] ++ after /\
                dftGasFromListTraceDefs$trace_gas before = ZIP (Kcut,gs)) /\
              (!tail'. rooted_eval F (stage 7) levels
                (root_entry with vs_gas_readings := gs ++ tail') =
                  (Ecut,OK (u with vs_gas_readings := tail'))) /\
              (body_entry = NONE ==>
                u with vs_gas_readings := s8.vs_gas_readings = s8) /\
              (p = p /\ d = d /\ IS_SOME body_entry /\
               inv_memory_observation inst8.inst_opcode /\ EL q xs = inst8 ==>
                (!op. MEM op inst8.inst_operands ==>
                  eval_operand op u = eval_operand op s8) /\
                u.vs_initial_fmp = s8.vs_initial_fmp)
          | stopped =>
              run_blocks F (stage 7) root_sf
                (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
              gas_events_blocks F (stage 7) root_sf
                (root_entry with vs_gas_readings := gs ++ tail) =
                  FST (rooted_eval F (stage 7) levels
                    (root_entry with vs_gas_readings := gs ++ tail)))) /\
        (!F gs tail n u.
          N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
          LENGTH Mcut < n /\
          mem_inv (\ctx src_fn src_inst src_state.
            gas_cut n (root_entry with vs_gas_readings := gs ++ tail) src_state ==>
              static_mem_ok cpl.cp_max_static_eom ctx src_fn src_inst src_state)
            (stage 7) (root_entry with vs_gas_readings := gs ++ tail) /\
          rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail) =
            (Ecut,OK u) ==>
          static_mem_ok cpl.cp_max_static_eom (stage 7) sf src_inst u /\
          (~in_revert_forward fn8 s8 ==> ~in_revert_forward sf u) /\
          (inv_memory_observation src_inst.inst_opcode ==>
            (!op. MEM op src_inst.inst_operands ==> eval_operand op u = eval_operand op s8) /\
            u.vs_initial_fmp = s8.vs_initial_fmp)) /\
  (!raw F u.
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw ==>

    N <= F /\ LENGTH Mcut < (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++ [0w]))) /\
    rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := (TAKE (LENGTH Mcut) raw) ++ (DROP
      (LENGTH Mcut) raw ++ [0w])) = (Ecut,OK u) ==>
    raw_reachable (root_entry with vs_gas_readings := (TAKE (LENGTH Mcut) raw) ++ (DROP (LENGTH Mcut) raw
      ++ [0w])) (stage 7) sf src_inst u /\ gas_cut (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++
      [0w]))) (root_entry with vs_gas_readings := (TAKE (LENGTH Mcut) raw) ++ (DROP (LENGTH Mcut) raw ++
      [0w])) u /\
    lowered_mem_fact cpl.cp_max_static_eom (stage 7) sf src_inst u /\
    u.vs_gas_readings = (DROP (LENGTH Mcut) raw ++ [0w]) /\
    (fin = asm_opt_finalizer ==>
      inst_dload_in_section src_inst u /\
      code_end_offset_ok (\ctx fn i s. fn = sf /\ i = src_inst /\ s = u) (stage 7)) /\
    (~in_revert_forward fn8 s8 ==> ~in_revert_forward sf u) /\
    (inv_memory_observation inst8.inst_opcode ==>
      (!op. MEM op inst8.inst_operands ==> eval_operand op u = eval_operand op s8) /\
      u.vs_initial_fmp = s8.vs_initial_fmp)))) /\
  (!h. h < j ==>
    ?a e tf inst visit_state stk PG G tn oms om hs hist.
      EL h (TAKE j (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8) root_tf root_entry)) =
        ((a,e,inst.inst_id),tf,inst,visit_state) /\
      EL h (q80::qs8) = JointConfig stk PG G tn tf inst visit_state oms om hs hist /\
      ?sf inc entry order res nrest bb bt ps xs ys rho in_state h0
        body_entry count front closed brest.
        FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
        FLOOKUP blocks (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
        get_instruction bt visit_state.vs_inst_idx = SOME inst /\
        ((inv_memory_observation inst.inst_opcode \/ is_fallible inst \/
          inst.inst_opcode = INVOKE) /\ ~in_revert_forward tf visit_state ==>
          ?q z src_inst cuts levels Mcut Ecut Kcut mr er kr.
            src_inst = EL (LENGTH z)
              (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
            ((IS_SOME body_entry /\ LENGTH ps <= visit_state.vs_inst_idx /\
              visit_state.vs_inst_idx - LENGTH ps < LENGTH rho /\
              q = EL (visit_state.vs_inst_idx - LENGTH ps) rho /\ q < LENGTH xs /\
              (a <> p \/ e <> d \/ visit_state <> s8 \/
                (EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
                 (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)))) /\
              (inv_memory_observation inst.inst_opcode \/ is_fallible inst \/
                 inst.inst_opcode = INVOKE ==> EL q xs = inst) /\
              z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs) \/
             (a = p /\ e = d /\ visit_state = s8 /\ body_entry = NONE /\
              visit_state.vs_inst_idx < LENGTH ps /\ q = 0 /\
              z = DROP (phi_prefix_length bb.bb_instructions) (TAKE visit_state.vs_inst_idx ps))) /\
            MAP (\(ai,ds,ei,qi,zi). ai) cuts =
              REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
            LENGTH cuts = LENGTH levels /\
            (!i ai ds ei qi zi.
              i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
              ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
                ini hi bei counti fronti closedi resti later.
                FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
                FLOOKUP blocks (ai,ei) =
                  SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
                orderi = ds ++ ei::later /\
                (if SUC i = LENGTH cuts then
                  ai = a /\ ei = e /\ qi = q /\ zi = z
                else
                  ?cid h b0 done_at_call child_entry ret.
                    EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
                    FLOOKUP calls (ai,ei,cid) =
                      SOME (qi,h,b0,done_at_call,child_entry,ret) /\
                    qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
                    zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
                    EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
                    (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==>
                      MEM r done_at_call)) /\
                EL i levels =
                  (sfi,
                   MAP (\f.
                     (FST (THE (FLOOKUP blocks (ai,f))),f,
                      DROP (phi_prefix_length
                        (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
                        (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
                     [(bbi,ei,zi)],
                   if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
            Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
              FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
              FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
            Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
              FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
              FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cuts) /\
            Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
              FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
              FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cuts) /\
            raw_slots = Mcut ++ mr /\ sites = Ecut ++ er /\ (FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab
              ([],e)))) (FST (SND (SND (SND (SND (THE (FLOOKUP acts []))))))))) = Kcut ++ kr /\
            LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
            (!F gs tail.
              N <= F /\
              LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
              (?extra. Ecut = FST (rooted_eval F (stage 7) levels
                (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
              (case SND (rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail)) of
                OK u =>
                  FST (rooted_eval F (stage 7) levels
                    (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
                  u.vs_gas_readings = tail /\
                  (?before after.
                    dftGasFromListTraceDefs$trace_blocks [] 0 F (stage 7) root_sf
                      (root_entry with vs_gas_readings := gs ++ tail) =
                      before ++ [((a,e,(EL (LENGTH z)
                        (DROP (phi_prefix_length bb.bb_instructions)
                          bb.bb_instructions)).inst_id),sf,
                        EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
                          bb.bb_instructions),u)] ++ after /\
                    dftGasFromListTraceDefs$trace_gas before = ZIP (Kcut,gs)) /\
                  (!tail'. rooted_eval F (stage 7) levels
                    (root_entry with vs_gas_readings := gs ++ tail') =
                      (Ecut,OK (u with vs_gas_readings := tail'))) /\
                  (body_entry = NONE ==>
                    u with vs_gas_readings := visit_state.vs_gas_readings = visit_state) /\
                  (a = p /\ e = d /\ IS_SOME body_entry /\
                   inv_memory_observation inst.inst_opcode /\ EL q xs = inst ==>
                    (!op. MEM op inst.inst_operands ==>
                      eval_operand op u = eval_operand op visit_state) /\
                    u.vs_initial_fmp = visit_state.vs_initial_fmp)
              | stopped =>
                  run_blocks F (stage 7) root_sf
                    (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
                  gas_events_blocks F (stage 7) root_sf
                    (root_entry with vs_gas_readings := gs ++ tail) =
                      FST (rooted_eval F (stage 7) levels
                        (root_entry with vs_gas_readings := gs ++ tail)))) /\
            (!F gs tail n u.
              N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
              LENGTH Mcut < n /\
              mem_inv (\ctx src_fn src_inst src_state.
                gas_cut n (root_entry with vs_gas_readings := gs ++ tail) src_state ==>
                  static_mem_ok cpl.cp_max_static_eom ctx src_fn src_inst src_state)
                (stage 7) (root_entry with vs_gas_readings := gs ++ tail) /\
              rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail) =
                (Ecut,OK u) ==>
              static_mem_ok cpl.cp_max_static_eom (stage 7) sf src_inst u /\
              ~in_revert_forward sf u /\
              (inv_memory_observation src_inst.inst_opcode ==>
                (!op. MEM op src_inst.inst_operands ==> eval_operand op u = eval_operand op visit_state) /\
                u.vs_initial_fmp = visit_state.vs_initial_fmp)) /\
  (!raw F u.
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw ==>

    N <= F /\ LENGTH Mcut < (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++ [0w]))) /\
    rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := (TAKE (LENGTH Mcut) raw) ++ (DROP
      (LENGTH Mcut) raw ++ [0w])) = (Ecut,OK u) ==>
    raw_reachable (root_entry with vs_gas_readings := (TAKE (LENGTH Mcut) raw) ++ (DROP (LENGTH Mcut) raw
      ++ [0w])) (stage 7) sf src_inst u /\ gas_cut (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++
      [0w]))) (root_entry with vs_gas_readings := (TAKE (LENGTH Mcut) raw) ++ (DROP (LENGTH Mcut) raw ++
      [0w])) u /\
    lowered_mem_fact cpl.cp_max_static_eom (stage 7) sf src_inst u /\
    u.vs_gas_readings = (DROP (LENGTH Mcut) raw ++ [0w]) /\
    (fin = asm_opt_finalizer ==>
      inst_dload_in_section src_inst u /\
      code_end_offset_ok (\ctx fn i s. fn = sf /\ i = src_inst /\ s = u) (stage 7)) /\
    (~in_revert_forward tf visit_state ==> ~in_revert_forward sf u) /\
    (inv_memory_observation inst.inst_opcode ==>
      (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op visit_state) /\
      u.vs_initial_fmp = visit_state.vs_initial_fmp)))) /\
  (!raw.
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw ==>
    ?f7 f extra.
      MAP project (gas_events_blocks f unit.cu_context entryfn (vs0 with <|vs_gas_readings := raw ++ [0w];
        vs_fmp := fmp; vs_initial_fmp := fmp; vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) =
        markf (raw ++ [0w]) ++ extra /\
      (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++ [0w]))) <= LENGTH (gas_events_blocks f7 (stage
        7) root_sf (root_entry with vs_gas_readings := raw ++ [0w])) /\
      TAKE (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++ [0w]))) (gas_events_blocks f7 (stage 7)
        root_sf (root_entry with vs_gas_readings := raw ++ [0w])) =
        TAKE (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++ [0w]))) (gas_events_blocks f
          unit.cu_context entryfn (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp;
          vs_initial_fmp := fmp; vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)))
Proof
  PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >> strip_tac >>
  sg `mem_inv (\ctx fn inst u.
         gas_cut (MIN (LENGTH (markf (gs ++ tail))) (LENGTH (gs ++ tail)))
           (root_entry with vs_gas_readings := gs ++ tail) u ==>
         lowered_mem_fact cpl.cp_max_static_eom ctx fn inst u)
       (stage 7) (root_entry with vs_gas_readings := gs ++ tail)`
  >- (irule (DISCH_ALL (CONJUNCT1 (UNDISCH
          (CONV_RULE (DEPTH_CONV BETA_CONV) (PURE_REWRITE_RULE [LET_THM] focus_source_stages_cut))))) >> cheat) >>
  cheat
QED

Theorem focus_history_source_slice[local]:
  !N C7 C8 root_sf root_tf root_entry j obs acts blocks calls ms_tab es_tab ks_tab
    rooted_eval p d q8 raw_slots sites unused a e sf tf inc entry order res nrest
    bb bt ps xs ys rho hin h0 be hbe count front closed brest ms ks
    q z cuts levels Mcut F gs tail events u.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,closed,brest) /\
  FLOOKUP ms_tab (a,e) = SOME ms /\ FLOOKUP ks_tab (a,e) = SOME ks /\
  q < LENGTH xs /\ z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)) /\
  MAP (\(ai,ds,ei,qi,zi). ai) cuts =
    REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
  LENGTH cuts = LENGTH levels /\
  (!i ai ds ei qi zi.
    i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
    ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
      ini hi bei counti fronti closedi resti later.
      FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
      FLOOKUP blocks (ai,ei) =
        SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
      orderi = ds ++ ei::later /\
      (if SUC i = LENGTH cuts then
        ai = a /\ ei = e /\ qi = q /\ zi = z
       else
        ?cid call_h b0 done_at_call child_entry ret.
          EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
          FLOOKUP calls (ai,ei,cid) = SOME (qi,call_h,b0,done_at_call,child_entry,ret) /\
          qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
          zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
          EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
          (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==> MEM r done_at_call)) /\
      EL i levels =
        (sfi, MAP (\f. (FST (THE (FLOOKUP blocks (ai,f))),f,
          DROP (phi_prefix_length (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
            (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
          [(bbi,ei,zi)], if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
  Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
    FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
    FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
  N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
  rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail) =
    (events,OK u) ==>
  ALL_DISTINCT (MAP FST obs) /\
  ALL_DISTINCT (FLAT (TAKE q ks)) /\
  LIST_REL (\key slot. slot = ALOOKUP obs key) (FLAT (TAKE q ks)) (FLAT (TAKE q ms)) /\
  ?Mbefore gpre vals.
    Mcut = Mbefore ++ FLAT (TAKE q ms) /\ gs = gpre ++ vals /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mbefore gpre /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT (TAKE q ms)) vals /\
    FOLDR (dft_exec_cons (F-e) C7) OK (TAKE q xs)
      (be with vs_gas_readings := vals ++ tail) = OK u /\
    trace_gas (trace_block a e (F-e) C7 sf
        (bb with bb_instructions := TAKE (LENGTH ps + q) bb.bb_instructions)
        (be with vs_gas_readings := vals ++ tail)) = ZIP (FLAT (TAKE q ks),vals)
Proof
  rpt gen_tac >> strip_tac >>
  `!q. LIST_REL (\key slot. slot = ALOOKUP obs key)
        (FLAT (TAKE q ks)) (FLAT (TAKE q ms))` by
    (drule_all dft_packet_retained_prefix_lookup >> simp[]) >>
  `ALL_DISTINCT (MAP FST obs) /\ ALL_DISTINCT (FLAT ks)` by
    (qhdtm_x_assum `dft_focus_packet_rel`
       (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
     conj_tac >-
       (qpat_assum `(j,obs) = _` mp_tac >>
        qpat_assum `ALL_DISTINCT (MAP FST _)` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[]) >>
     qpat_x_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest ms ess ks.
        FLOOKUP blocks (a,e) = _ /\ FLOOKUP ms_tab (a,e) = _ /\ FLOOKUP es_tab (a,e) = _ /\
        FLOOKUP ks_tab (a,e) = _ ==> _` (mp_tac o cj 6) >>
     `?ess. FLOOKUP es_tab (a,e) = SOME ess` by
       (qpat_assum `FDOM blocks = FDOM es_tab` mp_tac >>
        qpat_assum `FLOOKUP blocks (a,e) = _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
        Cases_on `FLOOKUP es_tab (a,e)` >> gvs[FLOOKUP_DEF]) >>
     disch_then (drule_all_then ACCEPT_TAC)) >>
  `ALL_DISTINCT (FLAT (TAKE q ks))` by
    (`ALL_DISTINCT (FLAT (TAKE q ks) ++ FLAT (DROP q ks))` by
       (pure_rewrite_tac[GSYM FLAT_APPEND, TAKE_DROP] >> first_assum ACCEPT_TAC) >>
     pop_assum (mp_tac o REWRITE_RULE [ALL_DISTINCT_APPEND]) >> simp[NoAsms]) >>
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE metis_tac[])) >>
  `FDOM ms_tab = FDOM ms_tab` by REFL_TAC >>
  `!key old new. FLOOKUP ms_tab key = SOME old /\ FLOOKUP ms_tab key = SOME new ==>
    LIST_REL (LIST_REL (\old new. old = NONE \/ old = new)) old new` by
    (POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[LIST_REL_refl]) >>
  drule dft_packet_cut_row_trace >>
  disch_then (qspec_then `ms_tab` (drule_all_then strip_assume_tac)) >>
  rename1 `gs = gpre ++ FLAT vals` >>
  qpat_assum `FLOOKUP ms_tab (a,e) = SOME ms` (fn m =>
    qpat_assum `FLOOKUP ks_tab (a,e) = SOME ks` (fn k =>
      qpat_assum `FLOOKUP acts a = SOME _` (fn act =>
        RULE_ASSUM_TAC (REWRITE_RULE [m,k,act,optionTheory.THE_DEF,pairTheory.FST])))) >>
  `LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
     (FLAT (TAKE q ms)) (FLAT vals)` by
    (qpat_assum `LIST_REL _ Mcut gs` mp_tac >>
     qpat_assum `Mcut = Mbefore ++ _` (fn m =>
       qpat_assum `gs = gpre ++ FLAT vals`
         (fn g => rewrite_tac[m,g])) >>
     qpat_assum `LIST_REL _ Mbefore gpre` (mp_tac o MATCH_MP LIST_REL_LENGTH) >>
     rpt strip_tac >> drule_all LIST_REL_APPEND_IMP >> simp[]) >>
  qexistsl [`Mbefore`,`gpre`,`FLAT vals`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem focus_c4_inst_protected[local]:
  fmp_lower_inst infos ctx runner s i = SOME (out,s') /\
  pre_fmp_opcode i.inst_opcode /\ MEM x s.irs_used_vars /\ x <> runner /\
  (MEM x i.inst_outputs ==> i = d) /\ d.inst_opcode = ADD /\
  (MEM (Var x) i.inst_operands ==> i.inst_opcode = CODECOPY) /\
  MEM j out /\ (MEM x j.inst_outputs \/ MEM (Var x) j.inst_operands) ==>
  j = i
Proof
  strip_tac
  >- (Cases_on `i.inst_opcode = DALLOCA`
      >- (gvs[fmp_lower_inst_def, AllCaseEqs(), mk_inst_def] >>
          imp_res_tac fresh_ir_var_contract >> gvs[] >> metis_tac[MEM]) >>
      Cases_on `i.inst_opcode = INVOKE`
      >- (gvs[fmp_lower_inst_def, AllCaseEqs(), MEM_APPEND] >>
          BasicProvers.EVERY_CASE_TAC >> fs[]) >>
      gvs[fmp_lower_inst_def, pre_fmp_opcode_def, AllCaseEqs()]) >>
  drule_all fmp_lower_inst_var_operand_origin >> strip_tac >> gvs[] >>
  gvs[fmp_lower_inst_def, AllCaseEqs()]
QED

Theorem focus_c4_indexed_protected[local]:
  fmp_lower_indexed infos ctx runner lbl k s restores is = SOME (out,left,s') /\
  MEM x s.irs_used_vars /\ x <> runner /\ d.inst_opcode = ADD /\
  (!pt. ~MEM (pt,x) restores) /\
  (!i. MEM i is ==> pre_fmp_opcode i.inst_opcode /\
    (MEM x i.inst_outputs ==> i = d) /\
    (MEM (Var x) i.inst_operands ==> i.inst_opcode = CODECOPY)) ==>
  !j. MEM j out /\ (MEM x j.inst_outputs \/ MEM (Var x) j.inst_operands) ==> MEM j is
Proof
  map_every qid_spec_tac [`s'`, `left`, `out`, `restores`, `s`, `k`] >>
  Induct_on `is` >- simp[fmp_lower_indexed_def] >>
  simp[fmp_lower_indexed_cons] >> rpt gen_tac >> strip_tac >>
  drule fmp_control_emit_vars_mono >> strip_tac >>
  drule fmp_control_inst_vars_mono >> strip_tac >>
  `!pt. ~MEM (pt,x) later` by metis_tac[fmp_select_point_restores_once] >>
  `~MEM x bases` by metis_tac[fmp_select_point_restores_once] >>
  gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  Cases_on `MEM j prefix`
  >- (drule_all fmp_emit_restores_assign_origin >> strip_tac >>
      qpat_x_assum `j = mk_inst _ _ _ _` SUBST_ALL_TAC >>
      qpat_x_assum `MEM x (mk_inst _ _ _ _).inst_outputs \/ _` mp_tac >>
      PURE_REWRITE_TAC
        [mk_inst_def, instruction_accessors, instruction_accfupds, combinTheory.K_THM,
         MEM, operand_11, OR_CLAUSES] >>
      disch_then (DISJ_CASES_THEN SUBST_ALL_TAC) >> gvs[]) >>
  Cases_on `MEM j head`
  >- (`j = h` by (irule focus_c4_inst_protected >> metis_tac[]) >> simp[]) >>
  `MEM j tail` by gvs[MEM_APPEND] >>
  `MEM x s1.irs_used_vars` by metis_tac[] >>
  qpat_x_assum `!k s rs out left s'. _`
    (qspecl_then [`SUC k`, `s1`, `later`, `tail`, `left`, `s'`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (qspec_then `j` mp_tac) >> simp[]
QED

Theorem focus_c4_blocks_protected[local]:
  fmp_lower_blocks infos ctx runner s restores bs = SOME (FmpBlocksResult out left s') /\
  MEM x s.irs_used_vars /\ x <> runner /\ d.inst_opcode = ADD /\
  (!pt. ~MEM (pt,x) restores) /\
  (!i. MEM i (fn_insts_blocks bs) ==> pre_fmp_opcode i.inst_opcode /\
    (MEM x i.inst_outputs ==> i = d) /\
    (MEM (Var x) i.inst_operands ==> i.inst_opcode = CODECOPY)) ==>
  !j. MEM j (fn_insts_blocks out) /\ (MEM x j.inst_outputs \/ MEM (Var x) j.inst_operands) ==>
      MEM j (fn_insts_blocks bs)
Proof
  map_every qid_spec_tac [`s'`, `left`, `out`, `restores`, `s`] >>
  Induct_on `bs` >- simp[fmp_lower_blocks_def, fn_insts_blocks_def] >>
  simp[fmp_lower_blocks_def, AllCaseEqs(), fn_insts_blocks_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule (REWRITE_RULE [Once (GSYM AND_IMP_INTRO)] focus_c4_indexed_protected) >>
  disch_then (qspecl_then [`x`, `d`] assume_tac) >>
  drule fmp_control_indexed_vars_mono >> strip_tac >>
  drule fmp_lower_indexed_leftover >> strip_tac >>
  qpat_x_assum `!s rs out left s'. _`
    (qspecl_then [`s2`, `later`, `tail`, `left`, `s'`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  simp[NoAsms, fn_insts_blocks_def, MEM_APPEND] >> metis_tac[]
QED

Theorem focus_c4_lowered_inst_origin[local]:
  fmp_stage_lowered infos ctx runner f g /\ MEM j (fn_insts g) ==>
  MEM j (fn_insts_blocks f.fn_blocks) \/
  ?sp s1 info users oldpc suffix root newpc s2 plan blocks s3.
    ir_supply_covers_fn sp f /\ fresh_ir_var sp = (runner,s1) /\
    split_fmp_entry f = SOME (FmpEntryLayout users oldpc suffix) /\
    fmp_make_root_layout ctx f info runner s1 =
      SOME (FmpRootLayout (LENGTH users) root newpc s2) /\
    analyze_fmp_reclaims infos ctx f = SOME plan /\
    fmp_lower_blocks infos ctx runner s2 (fmp_plan_to_alist f plan) f.fn_blocks =
      SOME (FmpBlocksResult blocks [] s3) /\
    (MEM j (fn_insts_blocks blocks) \/
     MEM j (OPTION_TO_LIST root) \/ MEM j (OPTION_TO_LIST newpc))
Proof
  simp[fmp_stage_lowered_def, fmp_lower_function_with_info_def, AllCaseEqs()] >>
  strip_tac >> gvs[fn_insts_def] >>
  drule fmp_checked_seal_some >> strip_tac >> gvs[fmp_seal_def, fn_insts_def] >>
  Cases_on `root_layout` >> gvs[] >>
  `?users oldpc suffix. split_fmp_entry f = SOME (FmpEntryLayout users oldpc suffix)` by
    (qpat_assum `fmp_make_root_layout _ _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[fmp_make_root_layout_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all fmp_make_root_layout_prefix >> strip_tac >> gvs[] >>
  drule_all fmp_lower_blocks_checked_entry_prefix >> strip_tac >>
  `entry.bb_instructions = users ++ OPTION_TO_LIST oldpc ++ tail` by
    (Cases_on `oldpc` >> fs[callLayoutDefsTheory.OPTION_TO_LIST_def]) >>
  qpat_x_assum `blocks = entry::rest` SUBST_ALL_TAC >>
  rename1 `fresh_ir_var sp = (runner,s1)` >>
  rename1 `fmp_make_root_layout ctx f info runner s1 =
      SOME (FmpRootLayout (LENGTH users) root newpc s2)` >>
  rename1 `fmp_lower_blocks infos ctx runner s2 (fmp_plan_to_alist f plan)
      f.fn_blocks = SOME (FmpBlocksResult (entry::rest) [] s3)` >>
  drule_all (SRULE [fn_insts_def] fmp_install_root_instruction_origin) >>
  disch_then assume_tac >> disj2_tac >>
  qexistsl [`sp`, `s1`, `info`, `root`, `newpc`, `s2`, `entry::rest`, `s3`] >>
  asm_rewrite_tac[]
QED

Theorem focus_c4_protected_origin[local]:
  fmp_stage_lowered infos ctx runner f g /\
  pre_fmp_ops f /\ MEM d (fn_insts f) /\ MEM x d.inst_outputs /\ d.inst_opcode = ADD /\
  (!i. MEM i (fn_insts f) /\ MEM x i.inst_outputs ==> i = d) /\
  (!i. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands ==> i.inst_opcode = CODECOPY) /\
  MEM j (fn_insts g) /\ (MEM x j.inst_outputs \/ MEM (Var x) j.inst_operands) ==>
  MEM j (fn_insts f)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all focus_c4_lowered_inst_origin >>
  disch_then (DISJ_CASES_THEN2 assume_tac
    (qx_choosel_then [`sp`, `s1`, `info`, `users`, `oldpc`, `suffix`,
       `root`, `newpc`, `s2`, `plan`, `blocks`, `s3`]
       (map_every assume_tac o CONJUNCTS)))
  >- simp[fn_insts_def] >>
  RULE_ASSUM_TAC (REWRITE_RULE [fn_insts_def]) >>
  PURE_REWRITE_TAC[fn_insts_def] >>
  `MEM x (fn_ir_vars f)` by
    (fs[fn_ir_vars_member, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `MEM x sp.irs_used_vars` by
    (fs[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM] >> metis_tac[]) >>
  drule fresh_ir_var_contract >> strip_tac >>
  drule fmp_make_root_layout_used_vars >> strip_tac >>
  `x <> runner` by metis_tac[] >>
  `!point. ~MEM (point,x) (fmp_plan_to_alist f plan)` by
    (rpt strip_tac >>
     `FLOOKUP plan point = SOME x` by metis_tac[MEM_fmp_plan_to_alist] >>
     drule_all analyze_fmp_reclaims_output >> strip_tac >>
     fs[fn_insts_def] >>
     `inst = d` by metis_tac[] >> gvs[]) >>
  `!j. MEM j (fn_insts_blocks blocks) /\
       (MEM x j.inst_outputs \/ MEM (Var x) j.inst_operands) ==>
       MEM j (fn_insts_blocks f.fn_blocks)` by
    (drule (REWRITE_RULE [Once (GSYM AND_IMP_INTRO)] focus_c4_blocks_protected) >>
     disch_then (qspecl_then [`x`, `d`] mp_tac) >>
     fs[pre_fmp_ops_def, fn_insts_def, EVERY_MEM] >> metis_tac[]) >>
  `!i. MEM i (OPTION_TO_LIST oldpc) ==>
       MEM i (fn_insts_blocks f.fn_blocks) /\ i.inst_opcode = RETPC_PARAM` by
    (qpat_assum `split_fmp_entry f = _` (fn layout =>
       POP_ASSUM_LIST (K ALL_TAC) >> assume_tac layout) >>
     drule split_fmp_entry_reconstruct >> strip_tac >>
     Cases_on `oldpc` >>
     fs[callLayoutDefsTheory.OPTION_TO_LIST_def, fn_insts_blocks_MEM] >>
     metis_tac[MEM, MEM_APPEND, split_fmp_entry_retpc_opcode]) >>
  `!i. MEM i (OPTION_TO_LIST oldpc) ==>
       ~MEM x i.inst_outputs /\ ~MEM (Var x) i.inst_operands` by
    (qx_gen_tac `old` >> strip_tac >>
     qpat_assum `!i. MEM i (OPTION_TO_LIST oldpc) ==> _` drule >> strip_tac >>
     conj_tac >> strip_tac
     >- (`old = d` by metis_tac[] >> gvs[]) >>
     `old.inst_opcode = CODECOPY` by metis_tac[] >> gvs[]) >>
  drule_all fmp_make_root_layout_opaque_shape >> strip_tac >>
  drule fmp_make_root_layout_runner_outputs >> strip_tac >>
  qpat_x_assum `MEM j (fn_insts_blocks blocks) \/ _` strip_assume_tac
  >- (fs[] >> metis_tac[]) >>
  (Cases_on `MEM (Var x) j.inst_operands`
   >- metis_tac[fmp_make_root_layout_operand_origin] >>
   metis_tac[MEM, fmp_optional_outputs_origin])
QED

(* Two adjacent kept instructions remain adjacent: neither is a reclaim
   point, and root installation cannot split this pair. *)

Theorem focus_c4_code_end_adjacent[local]:
  fmp_stage_lowered infos ctx runner f g /\
  (fn_is_context_entry ctx f ==> entry_fn_no_params f) /\
  lookup_block lbl f.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++ d::j::post /\
  d.inst_opcode = ADD /\ j.inst_opcode = CODECOPY ==>
  ?bg a b. lookup_block lbl g.fn_blocks = SOME bg /\
           bg.bb_instructions = a ++ d::j::b
Proof
  strip_tac >>
  qabbrev_tac `p = LENGTH pre` >>
  `SUC p < LENGTH bb.bb_instructions /\ p < LENGTH bb.bb_instructions /\
   EL p bb.bb_instructions = d /\ EL (SUC p) bb.bb_instructions = j` by
    (simp[Abbr `p`, EL_APPEND_EQN] >> decide_tac) >>
  `!k. k = p \/ k = SUC p ==>
    (EL k bb.bb_instructions).inst_opcode = ADD \/
    (EL k bb.bb_instructions).inst_opcode = CODECOPY` by
    (rpt strip_tac >> gvs[]) >>
  `!k. k = p \/ k = SUC p ==> (lbl,k) NOTIN FDOM (fmp_stage_plan infos ctx f)` by
    (rpt strip_tac >> drule_all fmp_stage_plan_point >> strip_tac >>
     drule fmp_reclaim_point_opcodes >> strip_tac >>
     qpat_assum `!k. k = p \/ k = SUC p ==> _` (qspec_then `k` mp_tac) >>
     impl_tac >- simp[] >> fs[]) >>
  `!rl rp. fmp_stage_root infos ctx f = SOME (rl,rp) /\ lbl = rl ==> rp <> SUC p` by
    (rpt strip_tac >>
     mp_tac (Q.INST [`idx` |-> `p`, `rp` |-> `SUC p`, `rl` |-> `lbl`,
                    `fn` |-> `f`, `fn'` |-> `g`]
       fmp_stage_root_crossing) >>
     impl_tac >- metis_tac[] >> fs[]) >>
  `fmp_stage_tidx (fmp_stage_plan infos ctx f) (fmp_stage_root infos ctx f)
      lbl bb.bb_instructions (SUC p) =
    SUC (fmp_stage_tidx (fmp_stage_plan infos ctx f) (fmp_stage_root infos ctx f)
      lbl bb.bb_instructions p)` by
    (irule fmp_stage_tidx_suc >> simp[] >> metis_tac[]) >>
  map_every (fn (i,idx) =>
    mp_tac (Q.INST [`inst` |-> i, `idx` |-> idx, `fn` |-> `f`,
                    `fn'` |-> `g`] fmp_stage_kept_inst) >>
    impl_tac >- gvs[pre_fmp_opcode_def] >> strip_tac)
      [(`d`, `p`), (`j`, `SUC p`)] >>
  gvs[] >>
  qabbrev_tac `k = fmp_stage_tidx (fmp_stage_plan infos ctx f)
      (fmp_stage_root infos ctx f) lbl (pre ++ [d;j] ++ post) p` >>
  qexistsl [`TAKE k bb'.bb_instructions`, `DROP (SUC (SUC k)) bb'.bb_instructions`] >>
  qpat_x_assum `EL k bb'.bb_instructions = d` (SUBST1_TAC o SYM) >>
  qpat_x_assum `EL (SUC k) bb'.bb_instructions = j` (SUBST1_TAC o SYM) >>
  `k < LENGTH bb'.bb_instructions` by decide_tac >>
  `DROP k bb'.bb_instructions =
    EL k bb'.bb_instructions :: EL (SUC k) bb'.bb_instructions ::
      DROP (SUC (SUC k)) bb'.bb_instructions` by metis_tac[rich_listTheory.DROP_CONS_EL] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> metis_tac[TAKE_DROP]
QED

Theorem focus_c4_code_end_seed_origin[local]:
  fmp_stage_lowered infos ctx runner f g /\ pre_fmp_ops f /\
  MEM j (fn_insts g) /\ j.inst_opcode = ADD /\
  j.inst_operands = [op; Label "code_end"] ==>
  MEM j (fn_insts f)
Proof
  strip_tac >> drule_all focus_c4_lowered_inst_origin >>
  disch_then (DISJ_CASES_THEN2 assume_tac
    (qx_choosel_then [`sp`, `s1`, `info`, `users`, `oldpc`, `suffix`,
       `root`, `newpc`, `s2`, `plan`, `blocks`, `s3`]
       (map_every assume_tac o CONJUNCTS)))
  >- simp[fn_insts_def] >>
  drule_all fmp_make_root_layout_opaque_shape >> strip_tac >>
  `MEM j (fn_insts_blocks blocks)` by
    (qpat_x_assum `MEM j (fn_insts_blocks blocks) \/ _`
       (DISJ_CASES_THEN2 ACCEPT_TAC (DISJ_CASES_THEN assume_tac))
     >- (qpat_assum `!i. MEM i (OPTION_TO_LIST root) ==>
                         MEM i.inst_opcode [INITIAL_FMP; FMP_PARAM]`
          (qspec_then `j` mp_tac) >>
        (gvs[listTheory.MEM])) >>
     qpat_assum `!i. MEM i (OPTION_TO_LIST newpc) ==> i.inst_opcode = RETPC_PARAM`
       (qspec_then `j` mp_tac) >> gvs[]) >>
  qpat_x_assum `MEM j (fn_insts_blocks blocks)` mp_tac >>
  pure_rewrite_tac[fn_insts_blocks_MEM] >> strip_tac >>
  drule_all fmp_lower_blocks_origin >> strip_tac
  >- (rename1 `fmp_lower_inst _ _ _ _ src_inst = SOME _` >>
      `pre_fmp_opcode src_inst.inst_opcode` by
        (fs[pre_fmp_ops_def, fn_insts_def, fn_insts_blocks_MEM, EVERY_MEM] >>
         metis_tac[]) >>
      gvs[fmp_lower_inst_def, AllCaseEqs(), mk_inst_def, pre_fmp_opcode_def] >>
      metis_tac[fn_insts_def, fn_insts_blocks_MEM]) >>
  gvs[mk_inst_def]
QED

Theorem focus_c4_protected_uses_origin[local]:
  fmp_stage_lowered infos ctx runner f g /\ pre_fmp_ops f /\
  middle_code_end_lifetime f /\ code_end_var f x ==>
  !j. MEM j (fn_insts g) /\ (MEM x j.inst_outputs \/ MEM (Var x) j.inst_operands) ==>
      MEM j (fn_insts f)
Proof
  strip_tac >>
  gvs[middle_code_end_lifetime_def] >>
  first_x_assum drule >> strip_tac >>
  `!i. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands ==>
    i.inst_opcode = CODECOPY` by
    (simp[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  rpt strip_tac >> irule focus_c4_protected_origin >>
  metis_tac[MEM]
QED

Theorem focus_c4_code_end_var_backward[local]:
  !g x. code_end_var g x ==> !infos ctx runner f.
    fmp_stage_lowered infos ctx runner f g /\ pre_fmp_ops f /\
    middle_code_end_lifetime f ==> code_end_var f x
Proof
  Induct_on `code_end_var` >> rpt strip_tac
  >- metis_tac[focus_c4_code_end_seed_origin, code_end_var_rules] >>
  rename1 `inst.inst_operands = [Var y]` >>
  `code_end_var f y` by metis_tac[] >>
  `MEM (Var y) inst.inst_operands` by simp[MEM] >>
  `MEM inst (fn_insts f)` by metis_tac[focus_c4_protected_uses_origin] >>
  metis_tac[code_end_var_rules]
QED

Theorem focus_c4_lowered_lifetime[local]:
  fmp_stage_lowered infos ctx runner f g /\
  (fn_is_context_entry ctx f ==> entry_fn_no_params f) /\
  wf_function f /\ fn_inst_ids_distinct g /\ pre_fmp_ops f /\
  middle_code_end_lifetime f ==> middle_code_end_lifetime g
Proof
  strip_tac >> simp[middle_code_end_lifetime_def] >> gen_tac >> strip_tac >>
  `code_end_var f x` by metis_tac[focus_c4_code_end_var_backward] >>
  `!j. MEM j (fn_insts g) /\ (MEM x j.inst_outputs \/ MEM (Var x) j.inst_operands) ==>
      MEM j (fn_insts f)` by metis_tac[focus_c4_protected_uses_origin] >>
  fs[middle_code_end_lifetime_def] >>
  first_x_assum drule >> strip_tac >>
  qexistsl [`d`, `op`] >> simp[] >> rpt conj_tac
  >- (qpat_assum `MEM d (fn_insts f)`
         (mp_tac o REWRITE_RULE [fn_insts_def, fn_insts_blocks_MEM]) >>
      strip_tac >> rename1 `MEM d b.bb_instructions` >>
      `lookup_block b.bb_label f.fn_blocks = SOME b` by metis_tac[wf_lookup_block] >>
      `?i. i < LENGTH b.bb_instructions /\ d = EL i b.bb_instructions` by
        metis_tac[MEM_EL] >>
      `pre_fmp_opcode d.inst_opcode /\ ~MEM d.inst_opcode [DALLOCA; INVOKE; RETPC_PARAM]` by
        simp[pre_fmp_opcode_def] >>
      drule_all fmp_stage_kept_inst >> strip_tac >>
      simp[fn_insts_def, fn_insts_blocks_MEM] >>
      metis_tac[EL_MEM, lookup_block_MEM]) >>
  rpt gen_tac >> strip_tac >>
  `MEM j (fn_insts g)` by (simp[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `MEM j (fn_insts f)` by metis_tac[] >>
  qpat_x_assum `MEM j (fn_insts f)`
    (qx_choose_then `src` strip_assume_tac o REWRITE_RULE [fn_insts_def, fn_insts_blocks_MEM]) >>
  `lookup_block src.bb_label f.fn_blocks = SOME src` by metis_tac[wf_lookup_block] >>
  qpat_assum `!bb j. _ ==> j.inst_opcode = CODECOPY /\ _` (qspecl_then [`src`, `j`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `src.bb_instructions = _`
    (assume_tac o REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  drule_all focus_c4_code_end_adjacent >> strip_tac >>
  `MEM bg g.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `MEM j bg.bb_instructions` by simp[] >>
  `bb = bg` by metis_tac[inst_in_unique_block] >>
  fs[APPEND] >> metis_tac[]
QED

Theorem focus_c4_actual_lowered[local]:
  fn_pass_step rpolicy (CFP_Simple VP_FmpLowering) observed sp fn out ==>
  ?infos runner. fmp_stage_lowered infos observed.cu_context runner fn out.fpo_function
Proof
  strip_tac >> drule fmp_fn_pass_step_result >> strip_tac >>
  `ir_supply_covers_fn sp fn` by
    (irule ir_supply_covers_unit_member >> qexists `observed` >>
     gvs[fn_pass_step_def] >> metis_tac[lookup_unique_function_member]) >>
  gvs[fmp_lower_function_def, AllCaseEqs()] >>
  simp[fmp_stage_lowered_def] >> metis_tac[]
QED

Theorem focus_fmp_stage_lifetime[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering) view C C' /\
  o1_ctx_shape C /\ o1_ctx_shape C' /\ EVERY (o1_fn_row 3) C.ctx_functions /\
  EVERY middle_code_end_lifetime C.ctx_functions ==>
  EVERY middle_code_end_lifetime C'.ctx_functions
Proof
  simp[ctx_pass_stage_def, EVERY_MEM] >> rpt strip_tac >>
  drule_all LIST_REL_MEM_IMP_R >> strip_tac >>
  pop_assum (strip_assume_tac o BETA_RULE) >>
  drule focus_c4_actual_lowered >> strip_tac >>
  rename1 `fmp_stage_lowered infos observed.cu_context runner src out.fpo_function` >>
  irule focus_c4_lowered_lifetime >> conj_tac
  >- (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, wf_function_def] >> metis_tac[]) >>
  qexistsl [`observed.cu_context`, `src`, `infos`, `runner`] >>
  gvs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, o1_fn_row_def,
      fmpWfDefsTheory.fn_is_context_entry_def] >> metis_tac[]
QED

Theorem focus_opt_c4_protected_lifetime[local]:
  (!k. k < 9 ==> ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
    (stage k) (stage (SUC k))) /\
  (!k. k <= 9 ==> o1_ctx_shape (stage k) /\ EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  (!f i. MEM f (stage 1).ctx_functions /\ MEM i (fn_insts f) ==>
    ~MEM (Label "code_end") i.inst_operands) ==>
  EVERY middle_code_end_lifetime (stage 4).ctx_functions
Proof
  strip_tac >>
  `ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload)
    (o1_walk_view rpolicy 1) (stage 1) (stage 2) /\
   ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) (stage 2) (stage 3) /\
   ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
    (o1_walk_view rpolicy 3) (stage 3) (stage 4)` by
    (qpat_assum `!k. k < 9 ==> _` (fn th =>
       map_every (fn q => qspec_then q mp_tac th) [`1`, `2`, `3`]) >>
     simp[NoAsms, venomPassScheduleTheory.o1_fn_passes_def, arithmeticTheory.ADD1] >>
     metis_tac[]) >>
  drule_all (REWRITE_RULE [GSYM middle_code_end_lifetime_def]
    lower_dload_stage_protected_lifetime) >> strip_tac >>
  drule_all (REWRITE_RULE [GSYM middle_code_end_lifetime_def]
    concretize_stage_protected_lifetime) >> strip_tac >>
  irule focus_fmp_stage_lifetime >> simp[] >>
  qexistsl [`stage 3`, `rpolicy`, `o1_walk_view rpolicy 3`] >>
  qpat_assum `!k. k <= 9 ==> _` (qspec_then `3` mp_tac) >>
  gvs[EVERY_MEM]
QED

Theorem focus_history_observation_agreement[local]:
  !C7 C8 sf tf bb bt ps xs ys be q inst k later (fuel:num) N e vals tail u t obs keys slots a.
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  dft_fn_rel sf tf /\ MEM bb sf.fn_blocks /\
  lookup_block bb.bb_label sf.fn_blocks = SOME bb /\
  lookup_block bb.bb_label tf.fn_blocks = SOME bt /\
  bb.bb_instructions = ps ++ xs /\ bt.bb_instructions = ps ++ ys /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs /\
  EVERY inst_shape_ok bb.bb_instructions /\
  dft_remaining_inv sf bb xs be /\ be.vs_inst_idx = LENGTH ps /\
  q < LENGTH xs /\ EL q xs = inst /\ inv_memory_observation inst.inst_opcode /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
  ys = TAKE k ys ++ inst::later /\
  EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k ys) /\
  FOLDR (dft_exec_cons (fuel-e) C7) OK (TAKE q xs)
    (be with vs_gas_readings := vals ++ tail) = OK u /\
  FOLDR (dft_exec_cons (N-e) C8) OK (TAKE k ys) be = OK t /\
  ALL_DISTINCT (MAP FST obs) /\ ALL_DISTINCT keys /\
  LIST_REL (\key slot. slot = ALOOKUP obs key) keys slots /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) slots vals /\
  trace_gas (trace_block a e (fuel-e) C7 sf
    (bb with bb_instructions := TAKE (LENGTH ps + q) bb.bb_instructions)
    (be with vs_gas_readings := vals ++ tail)) = ZIP (keys,vals) /\
  EVERY (\kw. MEM kw obs)
    (trace_gas (trace_block a e (N-e) C8 tf
      (bt with bb_instructions := TAKE (LENGTH ps + LENGTH (TAKE k ys)) bt.bb_instructions) be)) ==>
  (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op t) /\
  u.vs_initial_fmp = t.vs_initial_fmp
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH (TAKE q xs) = q` by simp[LENGTH_TAKE] >>
  `xs = TAKE q xs ++ inst::DROP (SUC q) xs` by
    metis_tac[TAKE_DROP, DROP_CONS_EL] >>
  drule_all dftPacketCommonOracleTheory.dft_packet_common_oracle >> strip_tac >>
  irule dftPacketObservationSuccessTheory.dft_packet_native_observation_success >>
  rpt (first_assum (irule_at Any)) >>
  qexistsl [`inst`, `DROP (SUC q) xs`, `later`] >>
  qpat_assum `xs = TAKE q xs ++ _` (fn sx =>
    qpat_assum `ys = TAKE k ys ++ _` (fn sy =>
      pure_rewrite_tac [GSYM sx, GSYM sy])) >>
  simp[] >>
  qpat_x_assum `trace_agrees _ (trace_block _ _ (fuel-e) _ _ _ _)` mp_tac >>
  simp[AC ADD_ASSOC ADD_COMM]
QED

Theorem focus_history_fold_continuation[local]:
  !pre s k u.
    EVERY (\i. ~is_terminator i.inst_opcode) pre /\
    FOLDR (dftIndexedExec$dft_exec_cons f C) OK pre s = OK u ==>
    FOLDR (dftIndexedExec$dft_exec_cons f C) k pre s = k u
Proof
  Induct >> simp[dftIndexedExecTheory.dft_exec_cons_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `step_inst f C h s` >>
  gvs[] >> first_x_assum irule >> simp[]
QED

(* A row scan checks each direct visit and its complete child trace at the
   state computed by the native instruction prefix. *)
Theorem focus_history_row_scan[local]:
  !todo pre s.
    DROP start.vs_inst_idx bb.bb_instructions = pre ++ todo /\
    s.vs_inst_idx = start.vs_inst_idx + LENGTH pre /\
    EVERY (\i. ~is_terminator i.inst_opcode) pre /\
    FOLDR (dftIndexedExec$dft_exec_cons fuel C) OK pre start = OK s /\
    (!k t i. k < LENGTH (DROP start.vs_inst_idx bb.bb_instructions) /\
      i = EL k (DROP start.vs_inst_idx bb.bb_instructions) /\
      t.vs_inst_idx = start.vs_inst_idx + k /\
      EVERY (\i. ~is_terminator i.inst_opcode)
        (TAKE k (DROP start.vs_inst_idx bb.bb_instructions)) /\
      FOLDR (dftIndexedExec$dft_exec_cons fuel C) OK
        (TAKE k (DROP start.vs_inst_idx bb.bb_instructions)) start = OK t ==>
      P ((a,e,i.inst_id),tf,i,t) /\ EVERY P (trace_step a e fuel C tf i t)) ==>
    EVERY P (trace_block a e fuel C tf bb s)
Proof
  Induct
  >- (rpt strip_tac >>
      `LENGTH bb.bb_instructions <= s.vs_inst_idx` by
        (qpat_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
         simp[LENGTH_DROP] >> decide_tac) >>
      simp[Once (cj 2 trace_defs), get_instruction_def]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `DROP start.vs_inst_idx bb.bb_instructions = pre ++ head::todo` >>
  `LENGTH pre < LENGTH bb.bb_instructions - start.vs_inst_idx` by
    (qpat_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[LENGTH_DROP]) >>
  `get_instruction bb s.vs_inst_idx = SOME head` by
    (`EL (LENGTH pre) (DROP start.vs_inst_idx bb.bb_instructions) = head` by
       simp[EL_APPEND] >>
     `LENGTH pre + start.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >>
     qpat_x_assum `EL (LENGTH pre) (DROP _ _) = head` mp_tac >>
     simp[listTheory.EL_DROP, get_instruction_def]) >>
  drule_then assume_tac trace_block_visit >>
  simp[EVERY_APPEND] >>
  `P ((a,e,head.inst_id),tf,head,s) /\ EVERY P (trace_step a e fuel C tf head s)` by
    (first_x_assum (qspecl_then [`LENGTH pre`,`s`,`head`] mp_tac) >>
     simp[EL_APPEND, TAKE_LENGTH_APPEND]) >>
  simp[] >> Cases_on `step_inst fuel C head s` >> simp[] >>
  Cases_on `is_terminator head.inst_opcode` >> simp[] >>
  rename1 `step_inst _ _ _ _ = OK post` >>
  first_x_assum (qspecl_then [`pre ++ [head]`,`post with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
  simp[FOLDR_APPEND, EVERY_APPEND, APPEND_ASSOC] >>
  drule_all_then (qspec_then `dftIndexedExec$dft_exec_cons fuel C head OK` SUBST1_TAC)
    focus_history_fold_continuation >>
  simp[dftIndexedExecTheory.dft_exec_cons_def]
QED

Theorem focus_history_call_anchor[local]:
  bt.bb_instructions = ps ++ ys /\
  ALL_DISTINCT (MAP (\v. v.inst_id) bt.bb_instructions) /\
  k < LENGTH ys /\ i = EL k ys /\ i.inst_id = c.inst_id /\
  LENGTH ps <= b0.vs_inst_idx /\ get_instruction bt b0.vs_inst_idx = SOME c /\
  FOLDR (dftIndexedExec$dft_exec_cons f C) OK (TAKE (b0.vs_inst_idx - LENGTH ps) ys) be = OK b0 /\
  FOLDR (dftIndexedExec$dft_exec_cons f C) OK (TAKE k ys) be = OK t ==>
  c = i /\ b0 = t
Proof
  rpt strip_tac >> gvs[get_instruction_def, AllCaseEqs()] >>
  `LENGTH ps + k < LENGTH (ps ++ ys)` by simp[] >>
  `EL (LENGTH ps + k) (ps ++ ys) = EL k ys` by simp[EL_APPEND] >>
  `EL b0.vs_inst_idx (MAP (\v. v.inst_id) (ps ++ ys)) =
   EL (LENGTH ps + k) (MAP (\v. v.inst_id) (ps ++ ys))` by simp[EL_MAP] >>
  `b0.vs_inst_idx = LENGTH ps + k` by (gvs[ALL_DISTINCT_EL_IMP, LENGTH_MAP]) >>
  gvs[]
QED

Theorem focus_history_closed_target_data[local]:
  !a e bb bt ps xs ys rho hin h0 be hbe count front brest.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),count,front,T,brest) ==>
  lookup_block hin.vs_current_bb tf.fn_blocks = SOME bt /\
  bt.bb_label = hin.vs_current_bb /\
  bt.bb_instructions = ps ++ ys /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bt.bb_instructions) /\
  is_terminator (LAST bt.bb_instructions).inst_opcode /\
  LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
    from_block [EL q xs] y) rho ys /\
  (!q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\ MEM q (TAKE count rho) ==>
    ?h b0 done child ir out post.
      FLOOKUP calls (a,e,(EL q xs).inst_id) = SOME (q,h,b0,done,child,SOME (ir,out,post))) /\
  FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK ys be = front
Proof
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  qpat_assum `!a sf tf inc entry order res nrest. _ ==> MEM sf _ /\ _`
    (fn th => qpat_assum `FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`
      (strip_assume_tac o MATCH_MP th)) >>
  qpat_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
     FLOOKUP blocks (a,e) = _ ==> ?sf tf inc entry order res nrest sp. _`
    (fn th => qpat_assum `FLOOKUP blocks (a,e) = SOME (_,_,_,_,_,_,_,_,SOME (be,hbe),_,_,T,_)`
      (strip_assume_tac o MATCH_MP th)) >>
  qpat_assum `!a e bb bt ps xs ys rho in_state h0 be hbe count front closed brest.
      FLOOKUP blocks (a,e) = _ ==> !q. _`
    (fn th => qpat_assum `FLOOKUP blocks (a,e) = SOME (_,_,_,_,_,_,_,_,SOME (be,hbe),_,_,T,_)`
      (assume_tac o MATCH_MP th)) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest)`,
     `FLOOKUP acts a = SOME _`, `dft_fn_rel sf tf`,
     `lookup_block bb.bb_label _ = SOME bb`,
     `lookup_block bb.bb_label _ = SOME bt`,
     `lookup_block hin.vs_current_bb _ = SOME bb`,
     `bt.bb_label = bb.bb_label`, `bt.bb_instructions = ps ++ ys`,
     `LIST_REL _ _ ys`, `case SOME (be,hbe) of NONE => _ | SOME v => _`,
     `!q. _ ==> ?h b0 done child ir out post. FLOOKUP calls (a,e,_) = _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[] >>
  `bb.bb_label = hin.vs_current_bb` by
    metis_tac[venomExecPropsTheory.lookup_block_label] >>
  drule_all dftRunRelTheory.dft_fn_rel_lookup_order >>
  strip_tac >>
  `MEM bb sf.fn_blocks` by metis_tac[venomExecPropsTheory.FIND_MEM,lookup_block_def] >>
  `wf_function sf` by fs[dftRunRelTheory.dft_fn_rel_def] >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[dftWfTheory.wf_fn_block_inst_ids_distinct] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bt.bb_instructions)` by
    metis_tac[dftSsaPreserveTheory.dft_block_rel_ids_distinct] >>
  `is_terminator (LAST bt.bb_instructions).inst_opcode` by
    metis_tac[dftRunRelTheory.dft_block_rel_last,bb_well_formed_def] >>
  `lookup_block hin.vs_current_bb tf.fn_blocks = SOME bt` by metis_tac[] >>
  qpat_assum `!F. N <= F ==> FOLDR _ _ _ _ = front` (qspec_then `N` mp_tac) >>
  gvs[]
QED

Theorem focus_history_returned_call_trace[local]:
  !a e tf bb bt ps xs ys rho hin h0 be hbe ct front br q h b0 done child ir out post k t i.
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP blocks (a,e) =
    SOME (bb,bt,ps,xs,ys,rho,hin,h0,SOME (be,hbe),ct,front,T,br) /\
  bt.bb_instructions = ps ++ ys /\
  ALL_DISTINCT (MAP (\v. v.inst_id) bt.bb_instructions) /\
  k < LENGTH ys /\ i = EL k ys /\
  FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK (TAKE k ys) be = OK t /\
  FLOOKUP calls (a,e,i.inst_id) = SOME (q,h,b0,done,child,SOME (ir,out,post)) ==>
  ?csf ctf order child_rest.
    FLOOKUP acts ((e,i.inst_id)::a) = SOME (csf,ctf,e,child,order,SOME (IntRet ir out),SOME child_rest) /\
    trace_step a e (N-e) C8 tf i t = trace_blocks ((e,i.inst_id)::a) e (N-e) C8 ctf child
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `FLOOKUP blocks (a,e) = SOME _` (mk_asm "closed row") >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE[dft_focus_packet_rel_def]) >>
  qpat_assum `!a e cid q h b0 done_at_call child_entry ret. FLOOKUP calls (a,e,cid) = _ ==> _`
    (fn th => qpat_assum `FLOOKUP calls (a,e,i.inst_id) = SOME _`
      (strip_assume_tac o MATCH_MP th)) >>
  asm "closed row" mp_tac >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`FLOOKUP blocks (a,e) = SOME _`, `bt.bb_instructions = ps ++ ys`,
     `ALL_DISTINCT (MAP _ bt.bb_instructions)`, `k < LENGTH ys`, `i = EL k ys`,
     `FOLDR _ _ (TAKE k ys) be = OK t`, `_.inst_id = i.inst_id`, `_.inst_opcode = INVOKE`,
     `LENGTH _ <= b0.vs_inst_idx`, `get_instruction _ b0.vs_inst_idx = SOME _`,
     `!F. N <= F ==> FOLDR _ _ _ _ = OK b0`,
     `FLOOKUP acts ((e,i.inst_id)::a) = SOME _`, `decode_invoke _ = SOME _`,
     `lookup_function _ C8.ctx_functions = SOME _`, `eval_operands _ b0 = SOME _`,
     `setup_callee _ _ b0 = SOME child`,
     `case SOME (ir,out,post) of NONE => _ | SOME v => _`,
     `!a sf tf inc entry order res nrest.
        FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[] >>
  `c = EL k ys /\ b0 = t` by
    (irule focus_history_call_anchor >>
     rpt (first_assum (irule_at Any)) >> simp[]) >>
  gvs[] >>
  rename1 `FLOOKUP acts ((e,(EL k ys).inst_id)::a) = SOME (csf,ctf,e,child,order,SOME _,cr)` >>
  `cr <> NONE` by
    (qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
       (fn th => qpat_assum `FLOOKUP acts ((e,(EL k ys).inst_id)::a) = SOME _`
         (mp_tac o MATCH_MP th)) >> simp[]) >>
  Cases_on `cr` >> gvs[] >>
  rpt (first_assum (irule_at Any)) >>
  irule trace_step_invoke >> rpt (first_assum (irule_at Any))
QED

Theorem focus_history_closed_row_child[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,row_order,hin,h0,SOME (be,hbe),ct,front,T,br) /\
  bt.bb_instructions = ps ++ ys /\ ALL_DISTINCT (MAP (\v. v.inst_id) bt.bb_instructions) /\
  LIST_REL (\q y. q < LENGTH xs /\ y.inst_id = (EL q xs).inst_id /\
    from_block [EL q xs] y) row_order ys /\
  (!q. q < LENGTH xs ==> MEM q (TAKE ct row_order)) /\
  (!q. q < LENGTH xs /\ (EL q xs).inst_opcode = INVOKE /\ MEM q (TAKE ct row_order) ==>
    ?h b0 done child ir out post.
      FLOOKUP calls (a,e,(EL q xs).inst_id) = SOME (q,h,b0,done,child,SOME (ir,out,post))) /\
  k < LENGTH ys /\ i = EL k ys /\ i.inst_opcode = INVOKE /\
  FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK (TAKE k ys) be = OK t ==>
  ?csf ctf child ord ir out child_rest.
    FLOOKUP acts ((e,i.inst_id)::a) = SOME (csf,ctf,e,child,ord,SOME (IntRet ir out),SOME child_rest) /\
    trace_step a e (N-e) C8 tf i t = trace_blocks ((e,i.inst_id)::a) e (N-e) C8 ctf child
Proof
  strip_tac >>
  qpat_assum `LIST_REL _ row_order ys` (mp_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
  strip_tac >>
  qpat_assum `!n. n < LENGTH row_order ==> _` (qspec_then `k` mp_tac) >>
  impl_tac >- simp[] >> disch_then (strip_assume_tac o BETA_RULE) >>
  `EL k row_order < LENGTH xs /\ (EL (EL k row_order) xs).inst_opcode = INVOKE` by
    (qpat_x_assum `from_block [_] _` mp_tac >> simp[NoAsms,dftStructuralTheory.from_block_def] >>
     strip_tac >> gvs[] >>
     qmatch_asmsub_abbrev_tac `is_flippable j.inst_opcode` >>
     namedCases_on `j.inst_operands` ["", "op1 rest_ops"] >> gvs[dftDefsTheory.flip_operands_def] >>
     namedCases_on `rest_ops` ["", "op2 rest_ops'"] >> gvs[dftDefsTheory.flip_operands_def] >>
     namedCases_on `rest_ops'` ["", "op3 rest_ops''"] >> gvs[dftDefsTheory.flip_operands_def] >>
     Cases_on `j.inst_opcode` >>
     gvs[dftDefsTheory.is_flippable_def, venomEffectsTheory.is_commutative_def,
         passSharedDefsTheory.is_comparator_def, passSharedDefsTheory.flip_comparison_opcode_def]) >>
  `MEM (EL k row_order) (TAKE ct row_order)` by simp[] >>
  qpat_assum `!q. _ ==> ?h b0 done child ir out post. FLOOKUP calls _ = _`
    (drule_all_then strip_assume_tac) >>
  `FLOOKUP calls (a,e,i.inst_id) = SOME (EL k row_order,h,b0,done,child,SOME (ir,out,post))` by simp[] >>
  drule_all_then strip_assume_tac focus_history_returned_call_trace >>
  metis_tac[]
QED

Theorem focus_history_closed_trace_row[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,row_order,hin,h0,SOME (be,hbe),ct,front,T,br) /\
  ys <> [] /\ ct = LENGTH ys /\
  EVERY (\i. is_pseudo i.inst_opcode) ps /\ EVERY (\i. ~is_pseudo i.inst_opcode) ys /\
  eval_phis hin bt.bb_instructions = OK sp /\
  FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK
    (DROP (phi_prefix_length bt.bb_instructions) ps)
    (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK be /\
  (!q. q < LENGTH xs ==> MEM q (TAKE ct row_order)) /\
  (!i t. lookup_block t.vs_current_bb tf.fn_blocks = SOME bt /\
    get_instruction bt t.vs_inst_idx = SOME i /\
    (LENGTH ps <= t.vs_inst_idx ==> t.vs_inst_idx - LENGTH ps < LENGTH ys /\
       t.vs_inst_idx - LENGTH ps < ct) ==> P ((a,e,i.inst_id),tf,i,t)) /\
  (!cid csf ctf child ord ir out child_rest.
    FLOOKUP acts ((e,cid)::a) = SOME (csf,ctf,e,child,ord,SOME (IntRet ir out),SOME child_rest) ==>
    EVERY P (trace_blocks ((e,cid)::a) e (N-e) C8 ctf child)) ==>
  lookup_block hin.vs_current_bb tf.fn_blocks = SOME bt /\
  exec_block (N-e) C8 bt (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = front /\
  EVERY P (trace_block a e (N-e) C8 tf bt (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions))
Proof
  strip_tac >> drule_all_then strip_assume_tac focus_history_closed_target_data >>
  qabbrev_tac `bphi = phi_prefix_length bt.bb_instructions` >>
  qabbrev_tac `start = sp with vs_inst_idx := bphi` >>
  qabbrev_tac `prefix = DROP bphi ps` >>
  `EVERY (\i. i.inst_opcode <> PHI) ys` by
    (qpat_x_assum `EVERY (\i. ~is_pseudo i.inst_opcode) ys` mp_tac >>
     simp[EVERY_MEM] >> metis_tac[is_pseudo_def]) >>
  `bphi <= LENGTH ps` by
    simp[Abbr `bphi`, dftIndexedExecTheory.dft_phi_prefix_append,
         venomExecProofsTheory.phi_prefix_length_le] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) prefix` by
    (simp[Abbr `prefix`, EVERY_MEM] >> rpt strip_tac >>
     `MEM i ps` by (drule rich_listTheory.MEM_DROP_IMP >> simp[]) >>
     `is_pseudo i.inst_opcode` by
       (qpat_assum `EVERY (\i. is_pseudo i.inst_opcode) ps`
          (mp_tac o REWRITE_RULE[EVERY_MEM]) >> simp[]) >>
     Cases_on `i.inst_opcode` >> gvs[is_pseudo_def,is_terminator_def]) >>
  `start.vs_inst_idx = bphi /\ start.vs_current_bb = hin.vs_current_bb` by
    (drule_then assume_tac venomExecProofsTheory.eval_phis_preserves_current_bb >>
     simp[Abbr `start`]) >>
  `LENGTH prefix = LENGTH ps - bphi /\ DROP start.vs_inst_idx bt.bb_instructions = prefix ++ ys` by
    simp[Abbr `prefix`, LENGTH_DROP, DROP_APPEND1] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (`is_terminator (LAST (prefix ++ ys)).inst_opcode` by
        (qpat_x_assum `is_terminator (LAST bt.bb_instructions).inst_opcode` mp_tac >>
         simp[LAST_APPEND_NOT_NIL]) >>
      `prefix ++ ys <> []` by simp[] >>
      `exec_block (N-e) C8 bt start =
       FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK (prefix ++ ys) start` by
        (irule dftPacketClosedRowNativeTheory.native_exec_block_terminated_fold >> simp[]) >>
      simp[FOLDR_APPEND] >>
      drule_all_then (qspec_then `FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK ys` SUBST1_TAC)
        focus_history_fold_continuation >> simp[]) >>
  irule focus_history_row_scan >>
  qexistsl [`[]`,`start`,`prefix ++ ys`] >> reverse conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> rename1 `P ((a,e,i.inst_id),tf,i,t) /\ _` >>
  `lookup_block t.vs_current_bb tf.fn_blocks = SOME bt` by
    (drule_all_then strip_assume_tac dftAvailabilityTheory.dft_prefix_frame >> simp[]) >>
  `get_instruction bt t.vs_inst_idx = SOME i` by
    (`k + start.vs_inst_idx < LENGTH bt.bb_instructions` by gvs[LENGTH_DROP] >>
     qspecl_then [`k`,`start.vs_inst_idx`,`bt.bb_instructions`] mp_tac listTheory.EL_DROP >>
     gvs[get_instruction_def,AC ADD_ASSOC ADD_COMM]) >>
  `k < LENGTH prefix + LENGTH ys /\ i = EL k (prefix ++ ys) /\
   t.vs_inst_idx = bphi + k` by gvs[] >>
  conj_tac
  >- (first_x_assum irule >> simp[]) >>
  reverse (Cases_on `i.inst_opcode = INVOKE`) >- simp[trace_step_noninvoke] >>
  `LENGTH prefix <= k` by
    (spose_not_then assume_tac >>
     `MEM i prefix` by gvs[EL_APPEND,EL_MEM] >>
     `MEM i ps` by (qpat_assum `MEM i prefix` mp_tac >>
       simp[Abbr `prefix`,NoAsms] >> disch_then (mp_tac o MATCH_MP rich_listTheory.MEM_DROP_IMP) >> simp[]) >>
     qpat_assum `EVERY (\i. is_pseudo i.inst_opcode) ps`
       (qspec_then `i` mp_tac o REWRITE_RULE[EVERY_MEM]) >> simp[is_pseudo_def]) >>
  qabbrev_tac `bk = k - LENGTH prefix` >>
  `bk < LENGTH ys /\ i = EL bk ys` by simp[Abbr `bk`,EL_APPEND] >>
  `FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK (TAKE bk ys) be = OK t` by
    (qpat_x_assum `FOLDR _ OK (TAKE k _) start = OK t` mp_tac >>
     simp[rich_listTheory.TAKE_APPEND2,FOLDR_APPEND] >>
     drule_all_then (qspec_then `FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK (TAKE bk ys)` SUBST1_TAC)
       focus_history_fold_continuation >> simp[Abbr `bk`]) >>
  drule_all_then strip_assume_tac focus_history_closed_row_child >>
  first_x_assum (qspec_then `tf` strip_assume_tac) >>
  qpat_assum `trace_step _ _ _ _ _ _ _ = _` SUBST1_TAC >>
  first_x_assum irule >> rpt (first_assum (irule_at Any))
QED

Theorem focus_history_activation_nonempty[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==> 0 < LENGTH order
Proof
  strip_tac >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE[dft_focus_packet_rel_def]) >>
  qpat_assum `!a sf tf inc entry order res nrest. FLOOKUP acts a = _ ==> _`
    (fn th => qpat_assum `FLOOKUP acts a = SOME _` (mp_tac o MATCH_MP th)) >>
  simp[LENGTH_NON_NIL]
QED

Theorem focus_history_closed_trace_suffix[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused ==>
  !fuel a clk sf tf inc entry order ir out rest r hin.
    FLOOKUP acts a = SOME (sf,tf,inc,entry,order,SOME (IntRet ir out),SOME rest) /\
    r < LENGTH order /\ clk = inc + r /\ fuel = N - clk ==>
    ((r = 0 /\ hin = entry) \/
     (?bb bt ps xs ys rho h0 body count front closed brest.
       FLOOKUP blocks (a,EL r order) =
         SOME (bb,bt,ps,xs,ys,rho,hin,h0,body,count,front,closed,brest))) ==>
    EVERY (\((a',e',id),f,i,s).
      ?sf' inc' entry' order' res' nrest' bb bt ps xs ys rho input h0 body_entry count front closed brest.
        FLOOKUP acts a' = SOME (sf',f,inc',entry',order',res',nrest') /\
        FLOOKUP blocks (a',e') =
          SOME (bb,bt,ps,xs,ys,rho,input,h0,body_entry,count,front,closed,brest) /\
        id = i.inst_id /\ lookup_block s.vs_current_bb f.fn_blocks = SOME bt /\
        get_instruction bt s.vs_inst_idx = SOME i /\
        (LENGTH ps <= s.vs_inst_idx ==> IS_SOME body_entry /\
          s.vs_inst_idx - LENGTH ps < LENGTH ys /\ s.vs_inst_idx - LENGTH ps < count))
      (trace_blocks a clk fuel C8 tf hin)
Proof
  strip_tac >> qmatch_goalsub_abbrev_tac `EVERY P _` >>
  completeInduct_on `fuel` >> rpt gen_tac >>
  disch_then strip_assume_tac >> disch_tac >>
  drule_all_then strip_assume_tac dft_packet_closed_suffix_row >>
  rename1 `FLOOKUP blocks (a,e) = SOME (bb,bt,ps,xs,ys,rho0,input,h0,SOME (be,hbe),count0,front,T,SOME brest)` >>
  `hin = input` by
    (qpat_x_assum `r = 0 /\ hin = entry \/ _` strip_assume_tac >> gvs[]) >>
  qpat_x_assum `hin = input` SUBST_ALL_TAC >>
  `fuel = SUC (N-e) /\ SUC clk = e` by decide_tac >>
  `!i t. lookup_block t.vs_current_bb tf.fn_blocks = SOME bt /\
    get_instruction bt t.vs_inst_idx = SOME i /\
    (LENGTH ps <= t.vs_inst_idx ==> t.vs_inst_idx - LENGTH ps < LENGTH ys /\
      t.vs_inst_idx - LENGTH ps < count0) ==> P ((a,e,i.inst_id),tf,i,t)` by
    (rpt gen_tac >> strip_tac >> simp[Abbr `P`] >>
     rpt (first_assum (irule_at Any)) >> simp[]) >>
  `!cid csf ctf child ord cir cout child_rest.
    FLOOKUP acts ((e,cid)::a) = SOME (csf,ctf,e,child,ord,SOME (IntRet cir cout),SOME child_rest) ==>
    EVERY P (trace_blocks ((e,cid)::a) e (N-e) C8 ctf child)` by
    (rpt gen_tac >> strip_tac >>
     `0 < LENGTH ord` by (drule_all focus_history_activation_nonempty >> simp[]) >>
     qpat_assum `!m. m < fuel ==> _` (qspec_then `N-e` mp_tac) >>
     impl_tac >- decide_tac >>
     disch_then irule >> rpt (first_assum (irule_at Any)) >> simp[]) >>
  `ys <> []` by
    (strip_tac >> qpat_x_assum `LENGTH ys = LENGTH xs` mp_tac >> simp[EQ_SYM_EQ, LENGTH_NIL]) >>
  `eval_phis input bt.bb_instructions = OK sp` by simp[] >>
  `FOLDR (dftIndexedExec$dft_exec_cons (N-e) C8) OK
     (DROP (phi_prefix_length bt.bb_instructions) ps)
     (sp with vs_inst_idx := phi_prefix_length bt.bb_instructions) = OK be` by
    (qpat_assum `bt.bb_instructions = ps ++ ys` SUBST1_TAC >>
     qpat_assum `!f. FOLDR _ _ _ _ = _` (qspec_then `N` ACCEPT_TAC)) >>
  drule_all_then strip_assume_tac focus_history_closed_trace_row >>
  qpat_assum `fuel = SUC (N-e)` SUBST1_TAC >>
  drule_all_then (fn th => once_rewrite_tac[th]) trace_blocks_enter >>
  qpat_assum `SUC clk = e` SUBST1_TAC >>
  qpat_assum `exec_block (N-e) C8 bt _ = front` SUBST1_TAC >>
  rewrite_tac[EVERY_APPEND] >> conj_tac >- first_assum ACCEPT_TAC >>
  Cases_on `SUC r = LENGTH order`
  >- (qpat_assum `SUC r = LENGTH order ==> _` (drule_then strip_assume_tac) >>
      qpat_assum `front = IntRet _ _` SUBST1_TAC >> simp[]) >>
  `SUC r < LENGTH order` by decide_tac >>
  qpat_assum `SUC r < LENGTH order ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `front = OK post` SUBST1_TAC >>
  qpat_assum `~post.vs_halted` (fn th => simp[NoAsms,th]) >>
  qpat_assum `!m. m < fuel ==> _` (qspec_then `N-e` mp_tac) >>
  impl_tac >- decide_tac >> disch_then irule >>
  qpat_assum `FLOOKUP acts a = SOME _` (irule_at Any) >>
  qpat_assum `SUC r < LENGTH order` (irule_at Any) >>
  simp[] >> rpt (first_assum (irule_at Any))
QED

Theorem focus_history_returned_row_coverage[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d q8 raw_slots sites unused /\
  FLOOKUP acts a = SOME (sf,tf,inc,ent,order,SOME (IntRet ir out),SOME rest) /\
  MEM ((a',e',id),f,i,s) (trace_blocks a inc (N-inc) C8 tf ent) ==>
  ?sf' inc' entry' order' res' nrest' bb bt ps xs ys rho input h0 body_entry count front closed brest.
    FLOOKUP acts a' = SOME (sf',f,inc',entry',order',res',nrest') /\
    FLOOKUP blocks (a',e') =
      SOME (bb,bt,ps,xs,ys,rho,input,h0,body_entry,count,front,closed,brest) /\
    id = i.inst_id /\ lookup_block s.vs_current_bb f.fn_blocks = SOME bt /\
    get_instruction bt s.vs_inst_idx = SOME i /\
    (LENGTH ps <= s.vs_inst_idx ==> IS_SOME body_entry /\
      s.vs_inst_idx - LENGTH ps < LENGTH ys /\ s.vs_inst_idx - LENGTH ps < count)
Proof
  strip_tac >> drule_all_then assume_tac focus_history_activation_nonempty >>
  drule_then (drule_at (Pat `MEM _ _`) o REWRITE_RULE[EVERY_MEM])
    focus_history_closed_trace_suffix >>
  simp[] >> disch_then irule >> rpt (first_assum (irule_at Any)) >> simp[]
QED

Theorem focus_history_native_ordinary[local]:
  wf_function fn /\
  h < LENGTH (trace_blocks [] 0 N C tf entry) /\
  EL h (trace_blocks [] 0 N C tf entry) = ((a,e,i.inst_id),fn,i,s) /\
  joint_transition C (JointConfig stk PG G tn fn i s oms om hs hist)
    (SOME (OriginOrdinary fuel post)) next ==>
  ?i' stk' PG' G' tn' oms' om' hs' hist'.
    SUC h < LENGTH (trace_blocks [] 0 N C tf entry) /\
    EL (SUC h) (trace_blocks [] 0 N C tf entry) =
      ((a,e,i'.inst_id),fn,i',post with vs_inst_idx := SUC s.vs_inst_idx) /\
    next = JointConfig stk' PG' G' tn' fn i'
      (post with vs_inst_idx := SUC s.vs_inst_idx) oms' om' hs' hist'
Proof
  strip_tac >>
  drule_all_then strip_assume_tac dftPacketNativeContinuationTheory.native_trace_blocks_continuation >>
  qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
  simp[joint_transition_ordinary] >> strip_tac >>
  `post.vs_current_bb = s.vs_current_bb` by
    (`step_inst_base i s = OK post` by metis_tac[step_inst_non_invoke] >>
     drule_all_then strip_assume_tac venomInstProofs1Theory.step_inst_base_preserves_all >>
     first_assum ACCEPT_TAC) >>
  `step_inst (N-e) C i s = OK post` by metis_tac[ptrSafeRunTheory.step_inst_non_invoke_fuel] >>
  `ALL_DISTINCT (fn_labels fn)` by fs[wf_function_def] >>
  drule_all_then strip_assume_tac dftGasToListReachBoundaryTheory.active_inst_lookup_distinct >>
  gvs[] >>
  rename1 `get_instruction bt (SUC s.vs_inst_idx) = SOME i'` >>
  `?suffix. DROP h (trace_blocks [] 0 N C tf entry) =
    ((a,e,i.inst_id),fn,i,s)::
    ((a,e,i'.inst_id),fn,i',post with vs_inst_idx := SUC s.vs_inst_idx)::suffix` by
    (simp[Once trace_defs,trace_step_noninvoke] >> simp[Once trace_defs]) >>
  `1 + h < LENGTH (trace_blocks [] 0 N C tf entry)` by
    (qpat_assum `DROP h _ = _::_::_` (mp_tac o AP_TERM ``LENGTH : list_visit list -> num``) >>
     simp[LENGTH_DROP]) >>
  drule_then (ASSUME_TAC o GSYM) EL_DROP >>
  qpat_assum `DROP h _ = _::_::_` (fn th =>
    qpat_x_assum `_ = EL 1 (DROP h _)` (mp_tac o REWRITE_RULE[th])) >>
  simp[ADD1] >> metis_tac[]
QED

(* A return in the current activation cannot occur within its child trace. *)
Theorem focus_history_native_row_return[local]:
  !xs s.
    DROP s.vs_inst_idx bb.bb_instructions = xs /\
    MEM ((a,d,id),fn,i,t) (trace_block a d fuel C fn bb s) /\
    i.inst_opcode <> INVOKE /\ step_inst fuel C i t = IntRet ir out ==>
    LAST (trace_block a d fuel C fn bb s) = ((a,d,id),fn,i,t) /\
    exec_block fuel C bb s = IntRet ir out
Proof
  Induct
  >- (rpt strip_tac >>
      `LENGTH bb.bb_instructions <= s.vs_inst_idx` by
        gvs[GSYM LENGTH_NIL, LENGTH_DROP] >>
      fs[Once (cj 2 trace_defs), get_instruction_def]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `DROP s.vs_inst_idx bb.bb_instructions = head::xs` >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (qpat_assum `DROP _ _.bb_instructions = _::_`
       (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[NoAsms, LENGTH_DROP]) >>
  `get_instruction bb s.vs_inst_idx = SOME head /\
   DROP (SUC s.vs_inst_idx) bb.bb_instructions = xs` by
    (drule DROP_BY_DROP_SUC >> simp[get_instruction_def]) >>
  drule_then assume_tac trace_block_visit >>
  drule_then assume_tac fnBlockBodyHelpersTheory.exec_block_step >>
  qpat_x_assum `MEM _ (trace_block _ _ _ _ _ _ _)` mp_tac >>
  asm_rewrite_tac[MEM, MEM_APPEND, pairTheory.PAIR_EQ] >> strip_tac
  >- gvs[trace_step_noninvoke]
  >- (`MEM (a,d,id) (MAP FST (trace_step a d fuel C fn head s))` by
        (simp[MEM_MAP] >> metis_tac[pairTheory.FST]) >>
      metis_tac[dftGasFromListTraceNamesTheory.trace_step_not_root]) >>
  Cases_on `step_inst fuel C head s` >> gvs[] >>
  Cases_on `is_terminator head.inst_opcode` >> gvs[] >>
  rename1 `step_inst fuel C head s = OK post` >>
  qpat_x_assum `!s'. DROP _ _ = _ /\ MEM _ _ ==> _`
    (qspec_then `post with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> strip_tac >>
  `trace_block a d fuel C fn bb (post with vs_inst_idx := SUC s.vs_inst_idx) <> []` by
    metis_tac[MEM] >>
  simp[LAST_CONS_cond, LAST_APPEND_NOT_NIL]
QED

Theorem focus_history_native_return_endpoint[local]:
  !f a D C fn ent d id i t ir out.
    MEM ((a,d,id),fn,i,t) (trace_blocks a D f C fn ent) /\
    i.inst_opcode <> INVOKE /\ step_inst (D+f-d) C i t = IntRet ir out ==>
    LAST (trace_blocks a D f C fn ent) = ((a,d,id),fn,i,t) /\
    run_blocks f C fn ent = IntRet ir out
Proof
  Induct >- simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `lookup_block ent.vs_current_bb fn.fn_blocks`
  >- fs[Once (cj 3 trace_defs)] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `eval_phis ent bb.bb_instructions` >>
  TRY (qpat_x_assum `MEM _ (trace_blocks _ _ _ _ _ _)` mp_tac >>
       simp[Once (cj 3 trace_defs)] >> NO_TAC) >>
  drule_all_then assume_tac trace_blocks_enter >>
  drule_all_then assume_tac frameGasEventsTheory.run_blocks_at >>
  rename1 `trace_blocks a D (SUC f) C fn ent` >>
  rename1 `eval_phis _ _ = OK sp` >>
  qabbrev_tac `u = sp with vs_inst_idx := phi_prefix_length bb.bb_instructions` >>
  qpat_x_assum `MEM _ (trace_blocks _ _ _ _ _ _)` mp_tac >>
  asm_rewrite_tac[MEM_APPEND] >> strip_tac
  >- (`d = SUC D` by
        (drule_then mp_tac dftGasFromListTraceNamesTheory.trace_block_region >>
         simp[dftGasFromListTraceNamesTheory.block_region_def] >>
         metis_tac[dftGasFromListTraceNamesTheory.frame_not_below_self,
                   dftGasFromListTraceNamesTheory.frame_below_def]) >>
      `D + SUC f - d = f` by decide_tac >>
      gvs[] >>
      `LAST (trace_block a (SUC D) f C fn bb u) = ((a,SUC D,id),fn,i,t) /\
       exec_block f C bb u = IntRet ir out` by
        metis_tac[focus_history_native_row_return] >> simp[]) >>
  Cases_on `exec_block f C bb u` >> gvs[] >>
  rename1 `exec_block f C bb u = OK post` >>
  Cases_on `post.vs_halted` >> gvs[] >>
  `step_inst (SUC D + f - d) C i t = IntRet ir out` by
    (`SUC D + f - d = D + SUC f - d` by decide_tac >> simp[]) >>
  first_x_assum drule_all >> strip_tac >>
  `trace_blocks a (SUC D) f C fn post <> []` by metis_tac[MEM] >>
  simp[LAST_APPEND_NOT_NIL]
QED

(* The native residual consists of the rest of this block and, if that block
   branches successfully, the subsequent blocks of the same activation. *)
Theorem focus_history_residual_entry[local]:
  wf_function fn /\ enters_block fn ent s /\ active_inst fn i s ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME i /\
    trace_blocks a d (SUC n) C fn ent =
      trace_block a (SUC d) n C fn bb s ++
      (case exec_block n C bb s of
        OK t => if t.vs_halted then [] else trace_blocks a (SUC d) n C fn t
      | _ => [])
Proof
  rw[enters_block_def] >>
  `s_phi.vs_current_bb = ent.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  `ALL_DISTINCT (fn_labels fn)` by fs[wf_function_def] >>
  drule_all_then strip_assume_tac dftGasToListReachBoundaryTheory.active_inst_lookup_distinct >>
  gvs[] >> metis_tac[trace_blocks_enter]
QED

Theorem focus_history_residual_ordinary[local]:
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  step_inst n C i s = OK t /\ u = (t with vs_inst_idx := SUC s.vs_inst_idx) ==>
  trace_block a d n C fn bb s = ((a,d,i.inst_id),fn,i,s)::trace_block a d n C fn bb u /\
  exec_block n C bb s = exec_block n C bb u
Proof
  strip_tac >> simp[Once trace_defs, trace_step_noninvoke] >>
  metis_tac[blockSimHelpersTheory.exec_block_step]
QED

Theorem focus_history_residual_branch[local]:
  get_instruction bb s.vs_inst_idx = SOME i /\
  is_terminator i.inst_opcode /\ step_inst n C i s = OK t /\ ~t.vs_halted ==>
  trace_block a d n C fn bb s = [((a,d,i.inst_id),fn,i,s)] /\
  exec_block n C bb s = OK t
Proof
  strip_tac >>
  `i.inst_opcode <> INVOKE` by (strip_tac >> fs[is_terminator_def]) >>
  simp[Once trace_defs, trace_step_noninvoke] >>
  drule_all blockSimHelpersTheory.exec_block_terminator >> simp[]
QED

Theorem focus_history_joint_large_index[local]:
  C.ctx_entry = SOME nm /\ lookup_function nm C.ctx_functions = SOME root_fn /\
  fn_entry_label root_fn = SOME lbl /\
  root_entry = (vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) /\
  o1_ctx_shape C /\ joint_trace vs0 C q0 evs qs q /\
  LENGTH evs + 1 < B /\
  (!fuel a D tf ent d id i s ir out.
    MEM ((a,d,id),tf,i,s) (trace_blocks a D fuel C tf ent) /\
    i.inst_opcode <> INVOKE /\ step_inst (D + fuel - d) C i s = IntRet ir out ==>
    run_blocks fuel C tf ent = IntRet ir out) ==>
  !h. h <= LENGTH evs ==>
    ?a d fn i s stk PG G tn oms om hs hist.
      h < LENGTH (trace_blocks [] 0 B C root_fn root_entry) /\
      EL h (trace_blocks [] 0 B C root_fn root_entry) = ((a,d,i.inst_id),fn,i,s) /\
      EL h (q0::qs) = JointConfig stk PG G tn fn i s oms om hs hist
Proof
  strip_tac >>
  `!fn. MEM fn C.ctx_functions ==> wf_function fn` by
    fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
  qabbrev_tac `whole = trace_blocks [] 0 B C root_fn root_entry` >>
  qabbrev_tac `residual = \a d fn bb s.
    trace_block a d (B-d) C fn bb s ++
    (case exec_block (B-d) C bb s of
       OK t => if t.vs_halted then [] else trace_blocks a d (B-d) C fn t
     | _ => [])` >>
  qabbrev_tac `aligned = \a D fn ent pre d i s past bb.
    D < d /\ MEM fn C.ctx_functions /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME i /\
    trace_blocks a D (B-D) C fn ent = past ++ residual a d fn bb s /\
    ?after. whole = pre ++ trace_blocks a D (B-D) C fn ent ++ after` >>
  qabbrev_tac `link_ok = \f (parent,past,d,bb,child).
    ?a D ent pre cf cs nm ops args.
      parent = (a,D,f.cf_fn,ent,pre) /\
      child = ((d,f.cf_inst.inst_id)::a,d,cf,cs,
        pre ++ past ++ [((a,d,f.cf_inst.inst_id),f.cf_fn,f.cf_inst,f.cf_state)]) /\
      aligned a D f.cf_fn ent pre d f.cf_inst f.cf_state past bb /\
      d <= SUC (LENGTH past + LENGTH pre) /\
      f.cf_inst.inst_opcode = INVOKE /\ decode_invoke f.cf_inst = SOME (nm,ops) /\
      lookup_function nm C.ctx_functions = SOME cf /\
      eval_operands ops f.cf_state = SOME args /\ setup_callee cf args f.cf_state = SOME cs` >>
  qabbrev_tac `aligned_at = \h v.
    ?a D fn ent pre d i s past bb stk PG G tn oms om hs hist links.
      v = JointConfig stk PG G tn fn i s oms om hs hist /\
      h = LENGTH pre + LENGTH past /\ d <= SUC h /\
      aligned a D fn ent pre d i s past bb /\ LIST_REL link_ok stk links /\
      (a,D,fn,ent,pre)::MAP (\(par,w,k,b,ch). par) links =
      MAP (\(par,w,k,b,ch). ch) links ++ [([],0,root_fn,root_entry,[])]` >>
  `!h. h <= LENGTH evs ==> aligned_at h (EL h (q0::qs))` by
    (Induct >- suspend "initial" >>
     rpt strip_tac >>
     `h < LENGTH evs` by decide_tac >>
     drule_all_then strip_assume_tac joint_trace_edge_at >>
     qpat_x_assum `h <= _ ==> _` mp_tac >> impl_tac >- decide_tac >>
     simp[Abbr `aligned_at`] >> strip_tac >>
     drule_then strip_assume_tac joint_transition_label_cases
     >- suspend "push"
     >- suspend "ordinary"
     >- suspend "branch"
     >> suspend "pop") >>
  rpt strip_tac >> first_x_assum drule >> simp[Abbr `aligned_at`] >>
  strip_tac >> suspend "indexed"
QED

Resume focus_history_joint_large_index[initial]:
  qpat_assum `joint_trace _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE[joint_trace_def]) >>
  disch_then (mp_tac o CONJUNCT1) >>
  simp[Once joint_initial_cases] >> rpt strip_tac >> gvs[] >>
  `MEM root_fn C.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  `wf_function root_fn` by simp[] >>
  `?bb. lookup_block s1.vs_current_bb root_fn.fn_blocks = SOME bb /\
        get_instruction bb s1.vs_inst_idx = SOME inst /\
        whole = residual [] 1 root_fn bb s1` by
    (simp[Abbr `whole`, Abbr `residual`] >>
     Cases_on `B` >> fs[] >>
     drule_all focus_history_residual_entry >>
     disch_then (qspecl_then [`n`,`0`,`[]`,`C`] mp_tac) >> simp[]) >>
  simp[Abbr `aligned_at`] >>
  qexistsl [`1`,`bb`] >>
  simp[Abbr `aligned`, Abbr `whole`]
QED
Resume focus_history_joint_large_index[push]:
  qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
  simp[joint_transition_call_iff] >> strip_tac >>
  rename1 `setup_callee cf args s = SOME cs` >>
  rename1 `enters_block cf cs cs1` >> rename1 `active_inst cf ci cs1` >>
  `MEM cf C.ctx_functions` by metis_tac[venomInstTheory.lookup_function_MEM] >>
  `wf_function cf` by simp[] >>
  `B - d = SUC (B - SUC d)` by decide_tac >>
  `?cb. lookup_block cs1.vs_current_bb cf.fn_blocks = SOME cb /\
        get_instruction cb cs1.vs_inst_idx = SOME ci /\
        trace_blocks ((d,i.inst_id)::a) d (B-d) C cf cs =
        residual ((d,i.inst_id)::a) (SUC d) cf cb cs1` by
    (drule_all focus_history_residual_entry >>
     disch_then (qspecl_then [`B - SUC d`,`d`,`(d,i.inst_id)::a`,`C`] mp_tac) >>
     simp[Abbr `residual`]) >>
  `?ca. whole = (pre ++ past ++ [((a,d,i.inst_id),fn,i,s)]) ++
                 trace_blocks ((d,i.inst_id)::a) d (B-d) C cf cs ++ ca` by
    (qpat_x_assum `aligned _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Abbr `aligned`] >> strip_tac >>
     qpat_x_assum `B - d = SUC _` kall_tac >>
     simp[Abbr `residual`, Once trace_defs] >>
     simp[Once trace_defs, APPEND_ASSOC] >>
     qpat_assum `trace_blocks (_::a) d _ C cf cs = _`
       (fn th => rewrite_tac[GSYM (BETA_RULE th)]) >> simp[]) >>
  qabbrev_tac `child_pre = pre ++ past ++ [((a,d,i.inst_id),fn,i,s)]` >>
  qabbrev_tac `child = ((d,i.inst_id)::a,d,cf,cs,child_pre)` >>
  qabbrev_tac `link = ((a,D,fn,ent,pre),past,d,bb,child)` >>
  `link_ok <|cf_fn := fn; cf_inst := i; cf_state := s; cf_params := PG;
             cf_prov := G; cf_tvar := tn.t_var|> link` by
    (simp[Abbr `link_ok`, Abbr `link`, Abbr `child`, Abbr `child_pre`] >>
     qexistsl [`nm'`,`ops`,`args`] >> simp[]) >>
  simp[] >>
  qexistsl [`(d,i.inst_id)::a`,`d`,`cs`,`child_pre`,`SUC d`,`[]`,`cb`,`link::links`] >>
  simp[Abbr `aligned`, Abbr `link`, Abbr `child`] >>
  simp[Abbr `child_pre`, APPEND_ASSOC] >> (metis_tac[])
QED
Resume focus_history_joint_large_index[ordinary]:
  qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
  simp[joint_transition_ordinary] >> strip_tac >>
  rename1 `active_inst fn ni (post with vs_inst_idx := SUC s.vs_inst_idx)` >>
  qabbrev_tac `u = post with vs_inst_idx := SUC s.vs_inst_idx` >>
  `step_inst (B-d) C i s = OK post` by metis_tac[ptrSafeRunTheory.step_inst_non_invoke_fuel] >>
  `u.vs_current_bb = s.vs_current_bb` by
    (`step_inst_base i s = OK post` by metis_tac[step_inst_non_invoke] >>
     drule_all_then strip_assume_tac venomInstProofs1Theory.step_inst_base_preserves_all >>
     simp[Abbr `u`]) >>
  `aligned a D fn ent pre d ni u (past ++ [((a,d,i.inst_id),fn,i,s)]) bb` by
    (qpat_x_assum `aligned _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Abbr `aligned`] >> strip_tac >>
     `ALL_DISTINCT (fn_labels fn)` by fs[wf_function_def] >>
     `get_instruction bb u.vs_inst_idx = SOME ni` by
       metis_tac[dftGasToListReachBoundaryTheory.active_inst_lookup_distinct, optionTheory.SOME_11] >>
     `residual a d fn bb s = [((a,d,i.inst_id),fn,i,s)] ++ residual a d fn bb u` by
       (`exec_block (B-d) C bb s = exec_block (B-d) C bb u` by
          (simp[Abbr `u`] >> irule blockSimHelpersTheory.exec_block_step >> metis_tac[]) >>
        simp[Abbr `residual`, SimpLHS, Once trace_defs, trace_step_noninvoke, Abbr `u`] >> simp[]) >>
     simp[APPEND_ASSOC]) >>
  simp[] >>
  qexistsl [`a`,`D`,`ent`,`pre`,`d`,`past ++ [((a,d,i.inst_id),fn,i,s)]`,`bb`,`links`] >>
  simp[] >> decide_tac
QED
Resume focus_history_joint_large_index[branch]:
  qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
  simp[joint_transition_block_iff] >> strip_tac >>
  rename1 `enters_block fn post u` >> rename1 `active_inst fn ni u` >>
  `i.inst_opcode <> INVOKE` by (strip_tac >> fs[is_terminator_def]) >>
  `step_inst (B-d) C i s = OK post` by metis_tac[ptrSafeRunTheory.step_inst_non_invoke_fuel] >>
  `?nb. aligned a D fn ent pre (SUC d) ni u (past ++ [((a,d,i.inst_id),fn,i,s)]) nb` by
    (qpat_x_assum `aligned _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Abbr `aligned`] >> strip_tac >>
     `wf_function fn` by simp[] >>
     `?nb. lookup_block u.vs_current_bb fn.fn_blocks = SOME nb /\
           get_instruction nb u.vs_inst_idx = SOME ni /\
           trace_blocks a d (B-d) C fn post = residual a (SUC d) fn nb u` by
       (`B - d = SUC (B - SUC d)` by decide_tac >>
        drule_all focus_history_residual_entry >>
        disch_then (qspecl_then [`B - SUC d`,`d`,`a`,`C`] mp_tac) >>
        simp[Abbr `residual`]) >>
     `residual a d fn bb s = [((a,d,i.inst_id),fn,i,s)] ++ residual a (SUC d) fn nb u` by
       (qpat_x_assum `step_inst fuel C i s = OK post` kall_tac >>
        drule_all focus_history_residual_branch >>
        simp[Abbr `residual`] >> strip_tac >> simp[]) >>
     qexists `nb` >> simp[APPEND_ASSOC]) >>
  simp[] >>
  qexistsl [`a`,`D`,`ent`,`pre`,`SUC d`,`past ++ [((a,d,i.inst_id),fn,i,s)]`,`nb`,`links`] >>
  simp[] >> decide_tac
QED
Resume focus_history_joint_large_index[pop]:
  qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
  simp[joint_transition_return] >> strip_tac >>
  qpat_x_assum `EL h (q0::qs) = JointConfig _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[] >> strip_tac >>
  Cases_on `links` >> gvs[] >>
  rename1 `link_ok f link` >> PairCases_on `link` >>
  qpat_x_assum `link_ok _ _` mp_tac >> simp[Abbr `link_ok`] >> strip_tac >>
  gvs[] >>
  `i.inst_opcode <> INVOKE` by metis_tac[fnBlockBodyStepsTheory.step_inst_invoke_not_intret] >>
  `step_inst (B-d) C i s = IntRet ret send` by
    metis_tac[ptrSafeRunTheory.step_inst_non_invoke_fuel] >>
  rename1 `aligned pa PD f.cf_fn pent ppre D f.cf_inst f.cf_state ppast pb` >>
  qabbrev_tac `child_path = (D,f.cf_inst.inst_id)::pa` >>
  qabbrev_tac `child = trace_blocks child_path D (B-D) C fn ent` >>
  `child = past ++ [((child_path,d,i.inst_id),fn,i,s)]` by
    (qpat_x_assum `aligned child_path _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Abbr `aligned`] >> strip_tac >>
     `exec_block (B-d) C bb s = IntRet ret send` by
       (drule_all fnBlockBodyHelpersTheory.exec_block_step >> simp[]) >>
     simp[Abbr `child`, Abbr `residual`] >>
     simp[Once trace_defs, trace_step_noninvoke]) >>
  `D + (B-D) = B` by decide_tac >>
  `run_blocks (B-D) C fn ent = IntRet ret send` by
    (`MEM ((child_path,d,i.inst_id),fn,i,s) (trace_blocks child_path D (B-D) C fn ent)` by
       (qpat_x_assum `child = _` mp_tac >> simp[Abbr `child`, MEM_APPEND] >> metis_tac[]) >>
     qpat_x_assum `!fuel a D tf ent d id i s ir out. _ ==> _` irule >>
     goal_assum $ drule_at Any >> simp[]) >>
  qabbrev_tac `u = post with vs_inst_idx := SUC f.cf_state.vs_inst_idx` >>
  qabbrev_tac `call_visit = ((pa,D,f.cf_inst.inst_id),f.cf_fn,f.cf_inst,f.cf_state)` >>
  `aligned pa PD f.cf_fn pent ppre D inst' u (ppast ++ [call_visit] ++ child) pb` by
    (qpat_x_assum `aligned pa _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Abbr `aligned`] >> strip_tac >>
     `u.vs_current_bb = f.cf_state.vs_current_bb` by
       (drule_then (strip_assume_tac o CONJUNCT1) dftGasInvSSAProbeTheory.inv_bind_outputs_frame >>
        simp[Abbr `u`, adopt_return_fmp_def, merge_callee_state_def, AllCaseEqs()] >>
        Cases_on `ret.iret_adopt_fmp` >> simp[]) >>
     `ALL_DISTINCT (fn_labels f.cf_fn)` by fs[wf_function_def] >>
     `get_instruction pb u.vs_inst_idx = SOME inst'` by
       metis_tac[dftGasToListReachBoundaryTheory.active_inst_lookup_distinct, optionTheory.SOME_11] >>
     `trace_block pa D (B-D) C f.cf_fn pb f.cf_state =
         [call_visit] ++ child ++ trace_block pa D (B-D) C f.cf_fn pb u` by
       (simp[Abbr `call_visit`, Abbr `child`, Abbr `child_path`, Abbr `u`, IgnAsm `child = _`] >>
        drule_all dftPacketReturnNativeTheory.dft_packet_native_return_concat >> simp[]) >>
     `exec_block (B-D) C pb f.cf_state = exec_block (B-D) C pb u` by
       (`step_inst (B-D) C f.cf_inst f.cf_state = OK post` by
          simp[Once venomExecSemanticsTheory.step_inst_def] >>
        simp[Abbr `u`] >> irule blockSimHelpersTheory.exec_block_step >>
        simp[is_terminator_def] >> metis_tac[]) >>
     simp[Abbr `residual`, APPEND_ASSOC]) >>
  qexistsl [`pa`,`PD`,`pent`,`ppre`,`D`,`ppast ++ [call_visit] ++ child`,`pb`,`t`] >>
  simp[] >> decide_tac
QED
Resume focus_history_joint_large_index[indexed]:
  qpat_x_assum `aligned _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[Abbr `aligned`] >> strip_tac >>
  `?suffix. residual a d fn bb s = ((a,d,i.inst_id),fn,i,s)::suffix` by
    (simp[Abbr `residual`, Once trace_defs] >> metis_tac[]) >>
  `?suffix. whole = (pre ++ past) ++ ((a,d,i.inst_id),fn,i,s)::suffix` by
    (simp[APPEND_ASSOC] >> metis_tac[]) >>
  qexistsl [`a`,`d`] >>
  qpat_x_assum `whole = (pre ++ past) ++ _` SUBST1_TAC >>
  simp[EL_APPEND, LENGTH_APPEND] >> decide_tac
QED
Finalise focus_history_joint_large_index
