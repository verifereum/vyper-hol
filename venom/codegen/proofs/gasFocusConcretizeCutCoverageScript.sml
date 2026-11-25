Theory gasFocusConcretizeCutCoverage
Ancestors
  concretizePtrStagePairedBridge concretizePtrStagePlacements
  concretizePtrImportOrigins concretizePtrPairedFields
  concretizeStageShape concretizeStepStructure
  o1PassContract venomWf venomInst unitShapeDefs concretizeMemLocDefs
  venomPassDispatcher
  gasFocusConcretizeEndpointCut gasFocusChronologicalCut
  concretizePtrContextRoot gasFocusConcretizeForwardWindow gasFocusConcretizeControlExtension
  concretizePtrObservationInterface gasFocusConcretizeTaggedSupport
  concretizePtrOpaqueRetpc concretizePtrPlacementBounds memLocDefs contextCodegenRel
  concretizePtrPairedPrefix concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrChronologicalHistory concretizeLayoutCutSafe
  concretizePtrHistoricalWriteExclusion concretizePtrOperationalOpcodes
  gasFocusConcretizeHistoricalCut concretizePtrParamSupport concretizePtrPrefixLedger
  gasFocusConcretizeWriterSeed gasFocusConcretizeOwnedSeed concretizePtrOwnedActualInitializer
  rich_list
  concretizePtrExactWriteTransport concretizePtrStageReserved concretizePtrStageBounds
  concretizePtrDallocaActualWrites concretizePtrValueTransport concretizePtrRequestHistory
  concretizePtrChronologicalDemand concretizePtrOwnershipErasure
  concretizePtrComparisonTransport concretizePtrWriteClassification ptrDiscipline
  concretizePtrOwnerPath concretizePtrAllocationOwnership
  concretizeLayoutAccessGeometry frameAllocationOwnership ptrDisciplineEmptyTaint
  concretizePtrRevertHistory concretizePtrActualWrites concretizePtrActualByteFrame
  concretizePtrEventEmbedding concretizePtrActiveWriteOwner concretizePtrSourceOwnership
  concretizePtrActivationBirths concretizePtrActivationChronology concretizePtrBytes
  concretizePtrTokenInterval concretizePtrHistoricalPlacement
  concretizeAnalysisSafeKill concretizeAnalysisSuccessfulWrites
  concretizeAnalysisTemporalDemand concretizePtrReadCoverage
  concretizePtrOwnerConflict concretizePtrHistoryCfg concretizeStageLookup fmpLowerProps
  concretizePtrAllocationSize concretizePtrExecutedCoverage staticLayoutAllocatorProofs
  concretizePtrCallSeparation concretizePtrTaggedCallLiveness concretizePtrLayoutOutput
  concretizePtrRetrospectiveLocal concretizePtrStackImports
  concretizePtrTaggedOrigins concretizePtrProductionCoverage
  concretizeAnalysisScanCoverage concretizeAnalysisBoundary concretizeAnalysisWriteSafety
  basePtrDefs staticLayoutDefs
  concretizePtrDallocaChronoJoint frameJointTrace frameJointTransition
  concretizePtrLifetime frameOriginHistory frameOriginReachable
  codegenRel unitTransformDefs
  o1LowerDloadPtrDiscipline o1SafeUpto list finite_map arithmetic words pred_set
  concretizePtrPairedPrefixProbe concretizePtrDeletedGapHistory
  gasFocusConcretizeCutAffine gasFocusConcretizeCutAlloca
  gasFocusConcretizeCutAssertion gasFocusConcretizeCutBindings
  gasFocusConcretizeCutBufferCopy gasFocusConcretizeCutCall
  gasFocusConcretizeCutComparison gasFocusConcretizeCutCreation
  gasFocusConcretizeCutDelegate gasFocusConcretizeCutEnvironment
  gasFocusConcretizeCutExtcodecopy gasFocusConcretizeCutFmpOps
  gasFocusConcretizeCutGas gasFocusConcretizeCutHashLog
  gasFocusConcretizeCutLoad gasFocusConcretizeCutMcopy
  gasFocusConcretizeCutRetAttach gasFocusConcretizeCutRetExecution
  gasFocusConcretizeCutRetRestore gasFocusConcretizeCutScalar
  gasFocusConcretizeCutStorage gasFocusConcretizeCutStore
  gasFocusConcretizeStaticFields gasFocusConcretizeHistoryFmp
  concretizePtrCurrentRangeTransport concretizePtrForwardingTransport
  concretizePtrCoverageStaticMemReachability
  ctxLookupAgree[qualified] lowerDloadDefs[qualified]
  frameRawProjection unitMemInv
  venomExecSemantics gasFocusConcretizeCutActualWrite
  concretizePtrHistoryCoverage[qualified,ignore_grammar]

(* The pairing is determined by the stage's static layout equations. No
   execution, including one outside the cut, is needed to construct it. *)
Theorem concretize_cut_paired_row[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  ptr_stage_placements C' positions /\ i < LENGTH C.ctx_functions /\
  R (EL i C.ctx_functions) (EL i C'.ctx_functions) ==>
  ?p. ptr_paired_code R (K p) positions (EL i C.ctx_functions) (EL i C'.ctx_functions) /\
    (!inst. MEM inst (fn_insts (EL i C.ctx_functions)) /\ inst.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP p (Allocation inst.inst_id)))
Proof
  strip_tac >> gvs[ctx_pass_stage_def, LIST_REL_EL_EQN] >>
  qpat_x_assum `!n. n < _ ==> ?observed s out. _`
    (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
  `MEM (EL i C.ctx_functions) C.ctx_functions /\
   MEM (EL i C'.ctx_functions) C'.ctx_functions` by metis_tac[EL_MEM] >>
  `(EL i C.ctx_functions).fn_eom = NONE` by fs[EVERY_MEM] >>
  gvs[fn_pass_step_def, execute_configured_fn_pass_concretize, AllCaseEqs()] >>
  drule_all concretize_function_fresh_positions >> strip_tac >>
  `!bb inst. MEM bb (EL i C.ctx_functions).fn_blocks /\
     MEM inst bb.bb_instructions /\ inst.inst_opcode = ALLOCA ==>
     FLOOKUP layout.cl_positions (Allocation inst.inst_id) =
       OPTION_MAP FST (FLOOKUP positions (Allocation inst.inst_id))` by
    (rpt gen_tac >> strip_tac >> irule ptr_layout_stage_lookup >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  qexists_tac `layout.cl_positions` >>
  simp[ptr_paired_code_def, apply_context_concretize_layout_def,
       apply_concretize_layout_def] >>
  conj_tac >-
    (mp_tac (Q.SPECL [`layout.cl_positions`,`EL i C.ctx_functions`]
       (GEN_ALL concretize_positions_entry_label)) >>
     simp[fn_entry_label_def, entry_block_def]) >>
  metis_tac[]
QED

Theorem concretize_cut_stage_pairing[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_ptr_safe_upto D lo n C vs /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions ==>
  ?R lp positions.
    ptr_stage_placements C' positions /\
    LIST_REL (ptr_paired_code R lp positions) C.ctx_functions C'.ctx_functions /\
    EVERY (\f. fn_inst_wf f /\ retpc_shape_ok f /\ opaque_use_ok f /\
      first_block_no_phi f /\ EVERY bb_well_formed f.fn_blocks /\
      ALL_DISTINCT (fn_labels f) /\
      (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
        IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions /\
    EVERY (\g. ALL_DISTINCT (fn_labels g)) C'.ctx_functions /\
    (!f g. ptr_paired_code R lp positions f g ==> g.fn_name = f.fn_name)
Proof
  strip_tac >> fs[o1_ptr_safe_upto_def] >>
  drule_all ptr_stage_placements_exists >> strip_tac >>
  drule ptr_stage_names >> simp[ctx_fn_names_def] >> strip_tac >>
  `LENGTH C.ctx_functions = LENGTH C'.ctx_functions` by metis_tac[LENGTH_MAP] >>
  `!i. i < LENGTH C.ctx_functions ==>
       (EL i C'.ctx_functions).fn_name = (EL i C.ctx_functions).fn_name` by
    (rpt strip_tac >>
     qpat_assum `MAP _ C.ctx_functions = MAP _ C'.ctx_functions`
       (mp_tac o AP_TERM (Term `EL i : string list -> string`)) >>
     simp[EL_MAP]) >>
  `ALL_DISTINCT C.ctx_functions` by
    (fs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def,
        ctx_fn_names_def] >> metis_tac[ALL_DISTINCT_MAP]) >>
  qabbrev_tac `R = \f g. ?i. i < LENGTH C.ctx_functions /\
    f = EL i C.ctx_functions /\ g = EL i C'.ctx_functions` >>
  `!f. MEM f C.ctx_functions ==> ?p.
     (!g. R f g ==> ptr_paired_code R (K p) positions f g) /\
     (!inst. MEM inst (fn_insts f) /\ inst.inst_opcode = ALLOCA ==>
       IS_SOME (FLOOKUP p (Allocation inst.inst_id)))` by
    (rpt strip_tac >>
     qpat_x_assum `MEM f C.ctx_functions`
       (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
     rename1 `j < LENGTH C.ctx_functions` >>
     qpat_x_assum `f = EL j C.ctx_functions` SUBST_ALL_TAC >>
     `R (EL j C.ctx_functions) (EL j C'.ctx_functions)` by
       (simp[Abbr `R`] >> metis_tac[]) >>
     drule_all concretize_cut_paired_row >> strip_tac >>
     qexists_tac `p` >> simp[] >> rpt strip_tac >>
     `g = EL j C'.ctx_functions` by (fs[Abbr `R`] >> metis_tac[ALL_DISTINCT_EL_IMP]) >>
     simp[]) >>
  qpat_x_assum `!f. MEM f _ ==> ?p. _`
    (qx_choose_then `lp` assume_tac o
     SIMP_RULE bool_ss [cardinalityCoreTheory.RIGHT_IMP_EXISTS_THM, SKOLEM_THM]) >>
  `!f. MEM f C.ctx_functions ==>
     (!g. R f g ==> ptr_paired_code R lp positions f g) /\
     (!inst. MEM inst (fn_insts f) /\ inst.inst_opcode = ALLOCA ==>
       IS_SOME (FLOOKUP (lp f) (Allocation inst.inst_id)))` by
    (rpt gen_tac >> disch_tac >>
     qpat_x_assum `!f. MEM f _ ==> _` (drule_then mp_tac) >>
     pure_rewrite_tac[ptr_paired_code_def, combinTheory.K_THM] >> simp[]) >>
  `LIST_REL (ptr_paired_code R lp positions) C.ctx_functions C'.ctx_functions` by
    (simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
     `R (EL n' C.ctx_functions) (EL n' C'.ctx_functions)` by
       (simp[Abbr `R`] >> metis_tac[]) >> metis_tac[EL_MEM]) >>
  qexistsl [`R`,`lp`,`positions`] >> simp[] >>
  conj_tac
  >- (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def,
         wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  conj_tac
  >- (fs[LIST_REL_EL_EQN, EVERY_EL, ptr_paired_code_def,
         o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >>
      rpt strip_tac >>
      qpat_x_assum `!i. _ ==> _ /\ _` (drule_then strip_assume_tac) >>
      fs[fn_labels_def] >> metis_tac[concretize_positions_labels, fn_labels_def, EL_MEM]) >>
  simp[ptr_paired_code_def, Abbr `R`] >> metis_tac[]
QED

(* At a fixed untainted byte, use the actual last writer, not a maximum
   output range; the retained target suffix cannot write it. *)
Theorem ptr_paired_fixed_read_recovery_upto:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\
  code_layout_valid vs /\ EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  alloca_frontier_upto n C vs /\ fixed_region_reserved lo C /\
  ptr_discipline_upto lo n C vs /\ gas_cut n vs at.po_state /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  (x < lo \/ dyn_floor C vs <= x) /\ x NOTIN endpoint.po_taint.t_mem /\
  ~in_revert_forward endpoint.po_fn endpoint.po_state /\
  endpoint.po_inst.inst_opcode <> ASSIGN ==>
  read_byte x endpoint.po_state.vs_memory = read_byte x at.po_state.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ptr_paired_endpoint_cut_safety >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_structural_trace_target >> strip_tac >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  drule_all ptr_chrono_ordinary_non_revert >> strip_tac >>
  `LENGTH ht = SUC (LENGTH done)` by fs[ptr_event_embedding_def] >>
  `!q. q < LENGTH done ==> SUC (EL q done) < LENGTH h /\
    ~in_revert_forward (EL (EL q done) h).po_fn
      (EL (EL q done) h).po_state` by
    (rpt strip_tac >>
     qpat_assum `ptr_event_embedding _ _ _` mp_tac >>
     pure_rewrite_tac[ptr_event_embedding_def] >> strip_tac >>
     `EL q done < LENGTH h - 1` by
       (first_x_assum (qspecl_then [`q`,`LENGTH done`] mp_tac) >>
        simp[EL_APPEND_EQN]) >>
     fs[EVERY_EL] >>
     `EL q done < LENGTH h` by decide_tac >> metis_tac[]) >>
  `!q. q < LENGTH done /\
    x NOTIN range_bytes (step_writes (EL (EL q done) h).po_inst
      (EL (EL q done) h).po_state (EL (SUC (EL q done)) h).po_state) ==>
    x NOTIN range_bytes (step_writes (EL q ht).po_inst
      (EL q ht).po_state (EL (SUC q) ht).po_state)` by
    (rpt strip_tac >> drule_all ptr_paired_fixed_actual_write_reflection_upto >>
     metis_tac[]) >>
  drule_all ptr_chrono_last_actual_or_none >> strip_tac
  >- (`read_byte x endpoint.po_state.vs_memory = read_byte x vs.vs_memory` by
        (irule ptr_chrono_history_no_actual_write_byte >> simp[] >> metis_tac[]) >>
      `read_byte x at.po_state.vs_memory = read_byte x vs.vs_memory` by
        (irule ptr_chrono_history_no_actual_write_byte >>
         qexistsl [`C'`,`ht`] >> simp[] >>
         rpt strip_tac >> `k < LENGTH done` by decide_tac >> metis_tac[]) >>
      metis_tac[]) >>
  suspend "writer"
QED

Resume ptr_paired_fixed_read_recovery_upto[writer]:
  drule ptr_structural_trace_actual_writer_retained >>
  disch_then (qspecl_then [`w`,`x`] mp_tac) >> simp[] >> strip_tac >>
  `(EL w h).po_inst.inst_opcode <> DRET` by
    (`w < LENGTH h` by decide_tac >>
     `ptr_observation_reachable vs C (EL w h)` by
       (qpat_assum `ptr_chrono_history vs C h endpoint`
          (mp_then Any mp_tac ptr_chrono_history_reachable) >> simp[EVERY_EL]) >>
     fs[ptr_observation_reachable_def] >>
     drule ptr_frame_operand_instructions >> strip_tac >>
     drule ptr_frame_context_membership >> strip_tac >>
     drule ptr_discipline_upto_fn_ptr_ok >> strip_tac >>
     fs[EVERY_MEM, fn_ptr_ok_def] >> metis_tac[]) >>
  `~is_terminator (EL w h).po_inst.inst_opcode /\
   (EL w h).po_inst.inst_opcode <> INVOKE` by
    (qpat_assum `(EL w h).po_inst.inst_opcode <> DRET` mp_tac >>
     Cases_on `(EL w h).po_inst.inst_opcode` >>
     simp[is_terminator_def] >>
     qpat_x_assum `x IN range_bytes _` mp_tac >>
     qpat_assum `(EL w h).po_inst.inst_opcode = _`
       (fn th => simp_tac (srw_ss())
         [th,step_writes_def,source_memory_write_ranges_def,range_bytes_def]) >>
     qpat_x_assum `DRET <> DRET` mp_tac >> simp[]) >>
  `read_byte x (EL (SUC w) h).po_state.vs_memory =
   read_byte x (EL (SUC q) ht).po_state.vs_memory` by
    (qpat_x_assum `EL q done = w` (SUBST_ALL_TAC o SYM) >>
     drule_all ptr_cut_paired_write_ledger_identity >>
     simp[ptr_ledger_write_pair_def, ptr_bytes_agree_def] >> strip_tac >>
     qpat_x_assum `!i. _ ==> read_byte i _ = _` (qspec_then `x` mp_tac) >> simp[]) >>
  suspend "frame"
QED

Resume ptr_paired_fixed_read_recovery_upto[frame]:
  `!j. q < j /\ j < LENGTH done ==> w < EL j done` by
    (qpat_assum `ptr_event_embedding _ _ _` mp_tac >>
     pure_rewrite_tac[ptr_event_embedding_def] >> strip_tac >>
     rpt strip_tac >> first_x_assum (qspecl_then [`q`,`j`] mp_tac) >>
     simp[EL_APPEND_EQN]) >>
  `!j. SUC q <= j /\ j < LENGTH ht-1 ==>
    x NOTIN range_bytes (step_writes (EL j ht).po_inst
      (EL j ht).po_state (EL (SUC j) ht).po_state)` by
    (rpt gen_tac >> strip_tac >>
     `j < LENGTH done /\ w < EL j done` by
       (conj_tac >- decide_tac >> first_x_assum irule >> decide_tac) >>
     metis_tac[]) >>
  `EL (LENGTH h-1) h = endpoint /\ LENGTH h-1 < LENGTH h` by
    (qpat_assum `ptr_chrono_history vs C h endpoint`
       (mp_tac o MATCH_MP ptr_chrono_history_end) >>
     strip_tac >> Cases_on `h` >> gvs[LAST_EL]) >>
  `EL (LENGTH ht-1) ht = at /\ LENGTH ht-1 < LENGTH ht` by
    (qpat_assum `ptr_chrono_history vs C' ht at`
       (mp_tac o MATCH_MP ptr_chrono_history_end) >>
     strip_tac >> Cases_on `ht` >> gvs[LAST_EL]) >>
  `read_byte x endpoint.po_state.vs_memory =
    read_byte x (EL (SUC w) h).po_state.vs_memory` by
    (`read_byte x (EL (LENGTH h-1) h).po_state.vs_memory =
      read_byte x (EL (SUC w) h).po_state.vs_memory` suffices_by simp[] >>
     irule ptr_chrono_history_actual_interval_byte_frame >>
     conj_tac >- (rpt strip_tac >>
       qpat_x_assum `!n. w < n /\ SUC n < LENGTH h ==> _`
         (qspec_then `k` mp_tac) >> simp[] >> decide_tac) >>
     simp[] >> metis_tac[]) >>
  `read_byte x at.po_state.vs_memory =
    read_byte x (EL (SUC q) ht).po_state.vs_memory` by
    (`read_byte x (EL (LENGTH ht-1) ht).po_state.vs_memory =
      read_byte x (EL (SUC q) ht).po_state.vs_memory` suffices_by simp[] >>
     irule ptr_chrono_history_actual_interval_byte_frame >>
     conj_tac >- simp[] >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Finalise ptr_paired_fixed_read_recovery_upto

(* The allocation whose byte is read stays active from the actual source
   initializer through the endpoint, possibly in a suspended caller. *)
(* An active owner cannot be killed by a chronological edge that misses
   its protected byte. Only this edge's access fact is needed. *)
Theorem ptr_cut_active_owner_no_kill[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\
  o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  ptr_chrono_history vs C h endpoint /\ SUC k < LENGTH h /\ a = EL k h /\
  o1_walk_view rpolicy 2 C' a.po_fn observed /\ access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
  ~in_revert_forward a.po_fn a.po_state /\ FLOOKUP a.po_state.vs_allocas aid = SOME (b,sz) /\
  b <= x /\ x < b + sz /\ x NOTIN range_bytes (step_writes a.po_inst a.po_state (EL (SUC k) h).po_state) ==>
  ~ptr_ml_can_kill (Allocation aid)
    (bp_analyze_fuel (concretize_memloc_fuel a.po_fn) (cfg_analyze a.po_fn) a.po_fn)
    (\p. if context_alloca_size a.po_fn (imported_mems_used observed.cu_context a.po_fn) p = 0
          then NONE else SOME (context_alloca_size a.po_fn (imported_mems_used observed.cu_context a.po_fn) p))
    a.po_inst
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> strip_tac >>
  `k < LENGTH h` by decide_tac >>
  `ptr_chrono_history vs C (TAKE (SUC k) h) a` by
    (simp[] >> drule ptr_chrono_history_prefix >> simp[]) >>
  qpat_assum `ptr_chrono_history vs C (TAKE _ _) a`
    (mp_then Any strip_assume_tac ptr_dalloca_chrono_joint_lift) >>
  rename1 `a = ptr_dalloca_joint_observe q` >>
  drule joint_trace_reachable >> strip_tac >>
  `?oms om hs hist. joint_origin_history vs C a.po_stack a.po_params a.po_prov
    a.po_taint a.po_fn a.po_inst a.po_state oms om hs hist` by
    (qpat_x_assum `a = EL k h` kall_tac >> Cases_on `q` >>
     gvs[joint_config_reachable_def, ptr_dalloca_joint_observe_def, ptr_observe_def] >>
     goal_assum (drule_at Any)) >>
  `MEM a.po_fn C.ctx_functions` by
    (drule joint_origin_history_erasure >> strip_tac >>
     drule origin_frame_erasure >> strip_tac >> drule ptr_frame_context_membership >> simp[]) >>
  `all_reachable a.po_fn /\ EVERY fn_defs_reach_uses C.ctx_functions` by
    fs[EVERY_MEM] >>
  `?n ops v. inst_write_size a.po_inst = SOME n /\ mem_write_ops a.po_inst = SOME ops /\
    ops.iao_ofst = Var v` by
    (qpat_x_assum `ptr_ml_can_kill _ _ _ _` mp_tac >>
     Cases_on `mem_write_ops a.po_inst` >>
     simp[ptr_ml_can_kill_def, inst_write_op_def, find_base_allocas_opt_def] >>
     rename1 `mem_write_ops a.po_inst = SOME ops` >>
     Cases_on `ops.iao_ofst` >> simp[find_base_allocas_def]) >>
  drule write_ops_operand >> strip_tac >>
  `ptr_chrono_step C a (EL (SUC k) h)` by
    (qpat_assum `a = EL k h` SUBST1_TAC >>
     qpat_assum `ptr_chrono_history vs C h endpoint`
       (mp_then Any (qspec_then `k` mp_tac) ptr_chrono_history_adjacent) >> simp[]) >>
  drule_all ptr_chrono_ordinary_step_success >> strip_tac >>
  `x NOTIN range_bytes (step_writes a.po_inst a.po_state s')` by
    metis_tac[literal_write_step_ranges] >>
  `MEM (Var v) a.po_inst.inst_operands` by
    (qpat_assum `ops.iao_ofst = Var v` (SUBST1_TAC o SYM) >>
     qpat_assum `MEM ops.iao_ofst a.po_inst.inst_operands` ACCEPT_TAC) >>
  qmatch_asmsub_abbrev_tac `ptr_ml_can_kill (Allocation aid) bp sizes a.po_inst` >>
  `bp = bp_analyze_fuel (concretize_memloc_fuel a.po_fn) (cfg_analyze a.po_fn) a.po_fn` by
    simp[Abbr `bp`] >>
  `sizes = (\p. if context_alloca_size a.po_fn (imported_mems_used observed.cu_context a.po_fn) p = 0
         then NONE else SOME (context_alloca_size a.po_fn (imported_mems_used observed.cu_context a.po_fn) p))` by
    simp[Abbr `sizes`] >>
  drule_all concretize_protected_cached_byte_no_kill_static >> simp[]
QED

Theorem ptr_cut_owner_interval_no_kill[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\
  o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  EVERY ssa_form C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  ptr_discipline_upto lo n C vs /\ gas_cut n vs endpoint.po_state /\
  ptr_chrono_history vs C h endpoint /\ i <= j /\ j < LENGTH h /\
  (ptr_owner_view d (EL i h)).cf_fn = fn /\
  o1_walk_view rpolicy 2 C' fn observed /\ b <= x /\ x < b + sz /\
  (!k. i <= k /\ k <= j ==> d <= LENGTH (EL k h).po_stack /\
    FLOOKUP (ptr_owner_view d (EL k h)).cf_state.vs_allocas aid = SOME (b,sz)) /\
  (!k. i <= k /\ k < j ==> ~in_revert_forward (EL k h).po_fn (EL k h).po_state /\
    x NOTIN range_bytes (step_writes (EL k h).po_inst (EL k h).po_state (EL (SUC k) h).po_state)) ==>
  !k. i <= k /\ k < j ==>
    ~ptr_ml_can_kill (Allocation aid)
      (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn)
      (\p. if context_alloca_size fn (imported_mems_used observed.cu_context fn) p = 0
            then NONE else SOME (context_alloca_size fn (imported_mems_used observed.cu_context fn) p))
      (ptr_owner_view d (EL k h)).cf_inst
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> gen_tac >> strip_tac >>
  `k < LENGTH h /\ SUC k < LENGTH h /\ k <= j` by decide_tac >>
  `d <= LENGTH (EL k h).po_stack /\
    FLOOKUP (ptr_owner_view d (EL k h)).cf_state.vs_allocas aid = SOME (b,sz)` by simp[] >>
  `ptr_observation_reachable vs C (EL k h)` by
    (drule ptr_chrono_history_reachable >> simp[EVERY_EL]) >>
  Cases_on `d < LENGTH (EL k h).po_stack`
  >- (drule_all ptr_owner_view_active >> strip_tac >>
      simp[ptr_ml_can_kill_def, inst_write_size_def, memLocDefsTheory.mem_write_ops_def]) >>
  `d = LENGTH (EL k h).po_stack` by decide_tac >>
  `(ptr_owner_view d (EL k h)).cf_fn = fn` by
    (`(ptr_owner_view d (EL i h)).cf_fn = (ptr_owner_view d (EL k h)).cf_fn`
       suffices_by metis_tac[] >>
     irule ptr_owner_view_interval_function >> simp[] >>
     qexistsl [`C`,`endpoint`,`vs`] >> simp[] >> rpt strip_tac >>
     `k' <= j` by decide_tac >> simp[]) >>
  `(EL k h).po_fn = fn /\
    FLOOKUP (EL k h).po_state.vs_allocas aid = SOME (b,sz)` by
    ((qpat_assum `d = LENGTH (EL k h).po_stack` (fn eq =>
       qpat_assum `(ptr_owner_view d (EL k h)).cf_fn = fn` mp_tac >>
       qpat_assum `FLOOKUP (ptr_owner_view d (EL k h)).cf_state.vs_allocas aid = _` mp_tac >>
       simp[eq,ptr_owner_view_def])) >> (gvs[ptr_owner_view_def])) >>
  `gas_cut n vs (EL k h).po_state` by
    (`EVERY (\a. gas_cut n vs a.po_state) h` by
       (irule ptr_chrono_history_cut >> metis_tac[]) >> fs[EVERY_EL]) >>
  drule ptr_discipline_upto_fn_ptr_ok >> strip_tac >>
  `access_ok lo (EL k h).po_prov (EL k h).po_fn (EL k h).po_inst (EL k h).po_state` by
    (qpat_assum `ptr_observation_reachable vs C (EL k h)`
       (strip_assume_tac o REWRITE_RULE [ptr_observation_reachable_def]) >>
     first_x_assum drule_all >> simp[]) >>
  simp[ptr_owner_view_def] >> metis_tac[ptr_cut_active_owner_no_kill]
QED

(* Read the concrete layout from the stage row of a live allocation owner.
   This needs only reachability of the sampled observation, not global safety. *)
Theorem ptr_cut_owner_layout_row[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  ptr_observation_reachable vs C A /\ d <= LENGTH A.po_stack /\
  fn = (ptr_owner_view d A).cf_fn /\
  FLOOKUP (ptr_owner_view d A).cf_state.vs_allocas aid = SOME (b,sz) /\
  ptr_stage_placements C' positions /\
  FLOOKUP positions (Allocation aid) = SOME (p,sz) /\
  lookup_function fn.fn_name C.ctx_functions = SOME fn /\
  lookup_function fn.fn_name C'.ctx_functions = SOME out.fpo_function /\
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
  ctx_fn_names observed.cu_context = ctx_fn_names C /\ o1_walk_view rpolicy 2 C' fn observed ==>
  fn.fn_eom = NONE /\ MEM (Allocation aid,p,sz) out.fpo_function.fn_mems_used /\
  ?reserved items.
    concretize_function_fuel_in_context (concretize_memloc_fuel fn)
      observed.cu_context reserved fn = SOME out.fpo_function /\
    static_alloca_items fn = SOME items /\ MEM (Allocation aid,sz) items /\
    (!c q size. MEM (c,q,size) (imported_mems_used observed.cu_context fn) ==>
      ~MEM c (MAP (\i. Allocation i.inst_id)
        (FILTER (\i. is_alloca_op i.inst_opcode) (fn_insts fn))))
Proof
  strip_tac >>
  `MEM fn C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `fn.fn_eom = NONE /\ fn_inst_ids_distinct fn` by
    (fs[EVERY_MEM, o1_ctx_shape_def, o1_fn_shape_def, ctx_wf_def, wf_function_def] >> metis_tac[]) >>
  qpat_x_assum `ptr_observation_reachable _ _ _`
    (strip_assume_tac o REWRITE_RULE [ptr_observation_reachable_def]) >>
  drule_all ptr_frame_table_source_static >> strip_tac >>
  drule_all ptr_frame_sizes_static >> strip_tac >>
  `ptr_table_source fn (ptr_owner_view d A).cf_state /\
   alloca_sizes_match fn (ptr_owner_view d A).cf_state` by
    (Cases_on `d = LENGTH A.po_stack`
     >- (fs[ptr_owner_view_def] >> metis_tac[]) >>
     `MEM (ptr_owner_view d A) A.po_stack` by
       (simp[ptr_owner_view_def] >> irule EL_MEM >> decide_tac) >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  `?i. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\ i.inst_id = aid` by
    metis_tac[ptr_table_source_def] >>
  `sz = get_alloca_size fn (Allocation aid)` by metis_tac[concretizeMemLocTransitionProofsTheory.alloca_sizes_match_def] >>
  `?reserved. concretize_function_fuel_in_context (concretize_memloc_fuel fn)
       observed.cu_context reserved fn = SOME out.fpo_function` by
    (qpat_x_assum `fn_pass_step _ _ _ _ _ _` mp_tac >>
     simp[fn_pass_step_def, execute_configured_fn_pass_concretize, AllCaseEqs()] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  drule_all ptr_concretize_static_items >> strip_tac >>
  `MEM (Allocation aid,sz) items` by
    (drule_all static_alloca_items_ALLOCA_exact >> strip_tac >>
     rename1 `i.inst_operands = [Lit amount]` >>
     `sz = w2n amount` by metis_tac[ptr_alloca_inst_size] >>
     drule static_alloca_items_MEM >>
     disch_then (qspec_then `(Allocation aid,sz)` mp_tac) >> simp[] >> metis_tac[]) >>
  `MEM (Allocation aid,p,sz) out.fpo_function.fn_mems_used` by
    (drule_all ptr_step_alloca_mems >> strip_tac >>
     `MEM out.fpo_function C'.ctx_functions` by metis_tac[lookup_function_MEM] >>
     fs[ptr_stage_placements_def] >> metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`reserved`,`items`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  pure_rewrite_tac[MEM_MAP, MEM_FILTER] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  strip_tac >> rename1 `is_alloca_op z.inst_opcode` >>
  `z.inst_opcode = ALLOCA` by
    (qpat_x_assum `is_alloca_op z.inst_opcode` mp_tac >>
     Cases_on `z.inst_opcode` >> simp[is_alloca_op_def]) >>
  drule_all ptr_stage_local_not_imported >>
  simp[MEM_MAP] >>
  qpat_assum `MEM (_,_,_) (imported_mems_used _ _)` (fn th =>
    rename1 `MEM (c,q,nbytes) (imported_mems_used _ _)`) >>
  qexists_tac `(c,q,nbytes)` >> simp[] >> metis_tac[]
QED

(* A clean demanded source byte cannot come from the fresh or initial
   boundary: it has an actual writer within the retained owner's lifetime. *)
Theorem focus_cut_owned_writer_path:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  i < LENGTH h /\ qi <= LENGTH done /\
  (qi = 0 \/ EL (qi-1) done < i) /\ i <= EL qi (done ++ [LENGTH h-1]) /\
  EL i H = (tsi,ri,bi,PTi,TGi,si,ei) /\
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
  ~in_revert_forward (EL i h).po_fn (EL i h).po_state /\
  (EL i h).po_inst.inst_opcode <> ASSIGN /\
  d <= LENGTH (EL i h).po_stack /\ EL (LENGTH (EL i h).po_stack - d) tsi = token /\
  FLOOKUP TGi v = SOME (token,aid) /\ MEM (Var v) (EL i h).po_inst.inst_operands /\
  (inst_read_op (EL i h).po_inst = SOME (Var v) \/ (EL i h).po_inst.inst_opcode = INVOKE) /\
  FLOOKUP (ptr_owner_view d (EL i h)).cf_state.vs_allocas aid = SOME (b,sz) /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
  b <= x /\ x < b + sz /\ lo <= x /\ x < dyn_floor C vs /\
  x NOTIN (EL i h).po_taint.t_mem ==>
  ?w q reloc.
    q < qi /\ q < LENGTH done /\ EL q done = w /\ w < i /\
    MEM (w,q,reloc) ws /\ reloc x = pa + (x-b) /\
    ptr_ledger_write_pair C C' reloc (EL w h) (EL (SUC w) h)
      (EL q ht) (EL (SUC q) ht) /\
    x IN range_bytes (step_writes (EL w h).po_inst
      (EL w h).po_state (EL (SUC w) h).po_state) /\
    x NOTIN (EL (SUC w) h).po_taint.t_mem /\
    (!k. w <= k /\ k <= i ==> d <= LENGTH (EL k h).po_stack /\
      FLOOKUP (ptr_owner_view d (EL k h)).cf_state.vs_allocas aid = SOME (b,sz)) /\
    (!k. SUC w <= k /\ k < i ==>
      x NOTIN range_bytes (step_writes (EL k h).po_inst
        (EL k h).po_state (EL (SUC k) h).po_state)) /\
    (!k. SUC q <= k /\ k < qi ==>
      pa + (x-b) NOTIN range_bytes (step_writes (EL k ht).po_inst
        (EL k ht).po_state (EL (SUC k) ht).po_state))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ptr_paired_endpoint_cut_safety >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  `ptr_chrono_history vs C (TAKE (SUC i) h) (EL i h)` by
    (drule ptr_chrono_history_prefix >> simp[]) >>
  `ptr_source_ownership vs C (TAKE (SUC i) h) (EL i h) tsi ri bi PTi TGi si` by
    (drule ptr_structural_transcript_ownership >>
     disch_then (qspec_then `i` mp_tac) >> simp[ptr_snapshot_ownership_def]) >>
  `vs.vs_allocas = FEMPTY` by fs[o1_initial_state_ok_def] >>
  `LENGTH (TAKE (SUC i) h) = SUC i` by simp[LENGTH_TAKE] >>
  drule_all (Q.INST [`h` |-> `TAKE (SUC i) h`]
    (SPEC_ALL ptr_endpoint_owned_actual_initializer)) >>
  disch_then (qx_choose_then `w` (map_every assume_tac o CONJUNCTS)) >>
  `w < i /\ SUC w <= i /\ SUC w < LENGTH h` by decide_tac >>
  `x IN range_bytes (step_writes (EL w h).po_inst
      (EL w h).po_state (EL (SUC w) h).po_state) /\
   x NOTIN (EL (SUC w) h).po_taint.t_mem` by fs[EL_TAKE] >>
  `!k. SUC w <= k /\ k < i ==> x NOTIN range_bytes
    (step_writes (EL k h).po_inst (EL k h).po_state (EL (SUC k) h).po_state)` by
    ((gen_tac >> strip_tac >>
     `w < k /\ SUC k < SUC i /\ k < SUC i` by decide_tac >>
     qpat_assum `!k. w < k /\ SUC k < LENGTH (TAKE _ _) ==> _`
       (qspec_then `k` mp_tac) >> simp[EL_TAKE] >> (gvs[EL_TAKE]))) >>
  `!k. w <= k /\ k <= i ==> d <= LENGTH (EL k h).po_stack /\
      FLOOKUP (ptr_owner_view d (EL k h)).cf_state.vs_allocas aid = SOME (b,sz)` by
    (gen_tac >> strip_tac >> `k < SUC i` by decide_tac >>
     qpat_assum `!k. w <= k /\ k < LENGTH (TAKE _ _) ==> _`
       (qspec_then `k` mp_tac) >> gvs[listTheory.EL_TAKE]) >>
  drule_all (Q.INST [`h` |-> `TAKE (SUC i) h`]
    (SPEC_ALL ptr_chrono_ordinary_non_revert)) >>
  disch_then (mp_tac o REWRITE_RULE [EVERY_EL]) >>
  strip_tac >>
  `!k. k <= i ==> ~in_revert_forward (EL k h).po_fn (EL k h).po_state` by
    (gen_tac >> strip_tac >> `k < SUC i` by decide_tac >>
     qpat_assum `!k. k < LENGTH (TAKE _ _) ==> _`
       (qspec_then `k` mp_tac) >> gvs[listTheory.EL_TAKE]) >>
  `w < LENGTH h` by decide_tac >>
  `d <= LENGTH (EL w h).po_stack /\
   FLOOKUP (ptr_owner_view d (EL w h)).cf_state.vs_allocas aid = SOME (b,sz)` by simp[] >>
  `~in_revert_forward (EL w h).po_fn (EL w h).po_state` by simp[] >>
  drule ptr_paired_prefix_memory >> strip_tac >>
  drule ptr_paired_memory_placements >> strip_tac >>
  qabbrev_tac `writer = EL w H` >> PairCases_on `writer` >>
  `!mems. ml_used_gen (Allocation aid)
    (bp_analyze_fuel (concretize_memloc_fuel (ptr_owner_view d (EL w h)).cf_fn)
      (cfg_analyze (ptr_owner_view d (EL w h)).cf_fn) (ptr_owner_view d (EL w h)).cf_fn)
    mems (ptr_owner_view d (EL w h)).cf_inst` by
    (gen_tac >> irule ptr_cut_actual_writer_seed >>
     (metis_tac[])) >>
  drule ptr_discipline_upto_fn_ptr_ok >> strip_tac >>
  `EVERY wf_function C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions` by
    (qpat_assum `o1_ctx_shape C` mp_tac >>
     simp[NoAsms, o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
     disch_then (mp_tac o cj 3) >> metis_tac[]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (qpat_assum `EVERY fn_inst_wf C.ctx_functions` mp_tac >>
     simp[NoAsms, EVERY_MEM, ptr_fn_inst_wf_flat]) >>
  `!mems. ml_read_gen (Allocation aid)
    (bp_analyze_fuel (concretize_memloc_fuel (ptr_owner_view d (EL i h)).cf_fn)
      (cfg_analyze (ptr_owner_view d (EL i h)).cf_fn) (ptr_owner_view d (EL i h)).cf_fn)
    mems (ptr_owner_view d (EL i h)).cf_inst` by
    (gen_tac >> irule ptr_source_owned_read_seed >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  suspend "interval"
QED

Resume focus_cut_owned_writer_path[interval]:
  `(ptr_owner_view d (EL w h)).cf_fn = (ptr_owner_view d (EL i h)).cf_fn` by
    (irule ptr_owner_view_interval_function >> simp[] >>
     qexistsl [`C`,`endpoint`,`vs`] >> simp[]) >>
  drule ptr_structural_trace_actual_writer_retained >>
  disch_then (qspecl_then [`w`,`x`] mp_tac) >> simp[] >> strip_tac >>
  `!j. j < LENGTH h ==> ptr_observation_reachable vs C (EL j h) /\
    gas_cut n vs (EL j h).po_state` by
    (qpat_assum `ptr_chrono_history vs C h endpoint`
       (mp_then Any strip_assume_tac ptr_chrono_history_reachable) >>
     `EVERY (\a. gas_cut n vs a.po_state) h` by
       (irule ptr_chrono_history_cut >> metis_tac[]) >>
     fs[EVERY_EL]) >>
  `(EL w h).po_inst.inst_opcode <> DRET /\
   dyn_floor C (EL w h).po_state = dyn_floor C vs` by
    (qpat_assum `!j. j < LENGTH h ==> _` (qspec_then `w` mp_tac) >>
     (impl_tac >- simp[]) >>
     pure_rewrite_tac[ptr_observation_reachable_def] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `frame_reachable vs C (EL w h).po_stack _ _ _ _ _ _`
       (fn th => map_every (assume_tac o cj 1 o (fn lem => MATCH_MP lem th))
         [ptr_frame_operand_instructions, ptr_frame_context_membership,
          frame_reachable_initial_fmp]) >>
     simp[dyn_floor_def] >> fs[EVERY_MEM, fn_ptr_ok_def] >> metis_tac[]) >>
  `~is_terminator (EL w h).po_inst.inst_opcode /\
   (EL w h).po_inst.inst_opcode <> INVOKE` by
    (qpat_assum `(EL w h).po_inst.inst_opcode <> DRET` mp_tac >>
     Cases_on `(EL w h).po_inst.inst_opcode` >>
     simp[is_terminator_def] >>
     qpat_x_assum `x IN range_bytes _` mp_tac >>
     qpat_assum `(EL w h).po_inst.inst_opcode = _`
       (fn th => simp_tac (srw_ss())
         [th,step_writes_def,source_memory_write_ranges_def,range_bytes_def]) >>
     qpat_x_assum `DRET <> DRET` mp_tac >> simp[]) >>
  drule ptr_paired_prefix_writes >> strip_tac >>
  `?rho. MEM (w,q,rho) ws` by
    (qpat_assum `ptr_paired_writes _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ptr_paired_writes_def] >> strip_tac >>
     first_x_assum (qspec_then `q` mp_tac) >> simp[] >> metis_tac[NOT_IN_EMPTY]) >>
  drule_all ptr_paired_write_event >> simp[ptr_paired_write_def] >> strip_tac >>
  suspend "post_write"
QED

Resume focus_cut_owned_writer_path[post_write]:
  rename1 `ptr_ledger_write_pair C C' reloc _ _ _ _` >>
  drule ptr_structural_transcript_ownership >>
  disch_then (qspec_then `SUC w` mp_tac) >> simp[] >>
  qabbrev_tac `snap = EL (SUC w) H` >> PairCases_on `snap` >>
  simp[ptr_snapshot_ownership_def] >> strip_tac >>
  drule ptr_source_ownership_caches >> strip_tac >>
  drule_all ptr_source_birth_caches_slices >> strip_tac >>
  drule ptr_source_birth_caches_activations >> strip_tac >>
  drule ptr_source_activations_length >> strip_tac >>
  `ptr_active_alloc_geometry ((EL (SUC w) h).po_state ::
    MAP (\f. f.cf_state) (EL (SUC w) h).po_stack)` by
    (`ptr_observation_reachable vs C (EL (SUC w) h)` by metis_tac[] >>
     fs[ptr_observation_reachable_def] >> metis_tac[ptr_frame_alloc_geometry]) >>
  `d <= LENGTH (EL (SUC w) h).po_stack /\
   FLOOKUP (ptr_owner_view d (EL (SUC w) h)).cf_state.vs_allocas aid = SOME (b,sz)` by simp[] >>
  `reloc x = pa + (x-b)` by
    (drule_at (Pat `ptr_paired_write_owner _ _ _ _ _ _`)
       ptr_paired_write_owner_relocation >>
     disch_then (irule_at (Pat `reloc _ = _`)) >> simp[] >>
     goal_assum (drule_at (Pat `ptr_birth_slices _ _ _`)) >>
     qexists `sz` >> qexistsl [`d`,`aid`] >> simp[]) >>
  drule ptr_structural_trace_target >> strip_tac >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  `LENGTH ht = SUC (LENGTH done) /\
   !j k. j < k /\ k <= LENGTH done ==>
     EL j (done ++ [LENGTH h-1]) < EL k (done ++ [LENGTH h-1])` by
    gvs[ptr_event_embedding_def] >>
  `q < qi` by
    (spose_not_then assume_tac >>
     `qi <= q /\ qi < LENGTH done` by decide_tac >>
     Cases_on `qi = q` >- gvs[EL_APPEND_EQN] >>
     `qi < q /\ q <= LENGTH done` by decide_tac >>
     `i <= EL qi done` by gvs[EL_APPEND_EQN] >>
     `EL qi done < w` by
       (qpat_assum `!j k. j < k /\ k <= LENGTH done ==> _`
          (qspecl_then [`qi`,`q`] mp_tac) >> gvs[EL_APPEND_EQN]) >>
     decide_tac) >>
  `!j. j < qi ==> EL j done < i` by
    (gen_tac >> strip_tac >> `0 < qi /\ j <= qi-1 /\ qi-1 < LENGTH done` by decide_tac >>
     Cases_on `j = qi-1` >- gvs[] >>
     `j < qi-1 /\ j < LENGTH done /\ qi-1 <= LENGTH done` by decide_tac >>
     `EL j done < EL (qi-1) done` by
       (map_every (fn bound => qpat_assum bound mp_tac)
          [`j < qi-1`, `qi-1 <= LENGTH done`, `j < LENGTH done`,
           `qi-1 < LENGTH done`] >>
        qpat_assum `!j k. j < k /\ k <= LENGTH done ==> _`
          (qspecl_then [`j`,`qi-1`] mp_tac) >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[EL_APPEND_EQN]) >>
     `EL (qi-1) done < i` by gvs[] >> decide_tac) >>
  `!j. SUC q <= j /\ j < qi ==>
    pa + (x-b) NOTIN range_bytes (step_writes (EL j ht).po_inst
      (EL j ht).po_state (EL (SUC j) ht).po_state)` by
    (qx_gen_tac `j` >> strip_tac >>
     `j < LENGTH done /\ j <= LENGTH done /\ q < j` by decide_tac >>
     `w < EL j done` by
       (qpat_assum `!j k. j < k /\ k <= LENGTH done ==> _`
          (qspecl_then [`q`,`j`] mp_tac) >> gvs[EL_APPEND_EQN]) >>
     `EL j done < i` by simp[] >>
     `SUC w <= EL j done /\ SUC (EL j done) < LENGTH h /\ EL j done < LENGTH h` by decide_tac >>
     `x NOTIN range_bytes (step_writes (EL (EL j done) h).po_inst
       (EL (EL j done) h).po_state (EL (SUC (EL j done)) h).po_state)` by simp[] >>
     `EL j done <= i` by decide_tac >>
     `~in_revert_forward (EL (EL j done) h).po_fn (EL (EL j done) h).po_state` by simp[] >>
     strip_tac >>
     drule_all ptr_paired_actual_write_origin_upto >>
     disch_then (DISJ_CASES_THEN2 (map_every assume_tac o CONJUNCTS) strip_assume_tac)
     >- (`x-b < sz` by decide_tac >>
         `lo <= pa + (x-b)` by
           (irule ptr_stage_placements_reserved_prefix >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
         `pa + sz <= eom` by
           (irule ptr_stage_placements_endpoint_bound >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
         `pa + sz < dimword (:256)` by
           (drule_all concretizePtrPlacementBoundsTheory.ptr_stage_placements_strict_bound >> simp[]) >>
         Cases_on `ctx_has_dalloca C` >> fs[dyn_floor_def] >> decide_tac) >>
     `w <= i /\ w <= EL j done` by decide_tac >>
     `!k. w <= k /\ k <= i ==> d <= LENGTH (EL k h).po_stack` by simp[] >>
     `EL (LENGTH (EL (EL j done) h).po_stack - d) tsj = token` by
       (drule_all (Q.INST [`i` |-> `w`, `j` |-> `i`]
          (SPEC_ALL ptr_transcript_bottom_token_interval)) >>
        simp[]) >>
     `d <= LENGTH (EL (EL j done) h).po_stack /\
      FLOOKUP (ptr_owner_view d (EL (EL j done) h)).cf_state.vs_allocas aid = SOME (b,sz)` by simp[] >>
     `ptr_source_ownership vs C (TAKE (SUC (EL j done)) h) (EL (EL j done) h) tsj rj bj PTj TGj sj` by
       (drule ptr_structural_transcript_ownership >>
        disch_then (qspec_then `EL j done` mp_tac) >> simp[ptr_snapshot_ownership_def]) >>
     `ptr_birth_slices (EL (EL j done) h) tsj bj` by
       (irule ptr_source_birth_caches_slices >>
        map_every qexists [`C`,`TAKE (SUC (EL j done)) h`,`rj`,`vs`] >>
        irule ptr_source_ownership_caches >> goal_assum (drule_at Any)) >>
     `FLOOKUP bj (token,aid) = SOME (b,sz)` by
       (qpat_assum `ptr_birth_slices (EL (EL j done) h) tsj bj` mp_tac >>
        pure_rewrite_tac[ptr_birth_slices_def] >>
        disch_then (qspecl_then [`d`,`aid`] mp_tac) >> simp[]) >>
     `FLOOKUP bj (tok,bid) = SOME (db,sb)` by
       (`ptr_ledger_erases (dyn_floor C vs) bj TGj (EL (EL j done) h).po_prov` by
          (irule (cj 2 ptr_source_ownership_erases_upto) >>
           simp[] >> metis_tac[]) >>
        pop_assum (mp_tac o REWRITE_RULE [ptr_ledger_erases_def]) >>
        disch_then (CONJUNCTS_THEN2 (qspec_then `dv` mp_tac) kall_tac) >>
        simp[ptr_owner_erases_def, EQ_SYM_EQ]) >>
     Cases_on `tok = token /\ bid = aid`
     >- (`db = b /\ pb = pa` by gvs[] >>
         `db + (pa + (x-b) - pb) = x` by decide_tac >> fs[]) >>
     `?e owner output.
       e <= LENGTH (EL (EL j done) h).po_stack /\
       EL (LENGTH (EL (EL j done) h).po_stack - e) tsj = tok /\
       FLOOKUP rj tok = SOME owner /\
       owner = (ptr_owner_view e (EL (EL j done) h)).cf_fn /\
       FLOOKUP (ptr_owner_view e (EL (EL j done) h)).cf_state.vs_allocas bid = SOME (db,sb) /\
       lookup_function owner.fn_name C'.ctx_functions = SOME output /\
       MEM (Allocation bid,pb,sb) output.fn_mems_used` by
       (`EL j done <= EL j done` by simp[] >>
        drule_all (Q.INST [`i` |-> `EL j done`, `j` |-> `EL j done`]
          (SPEC_ALL ptr_transcript_historical_placement_upto)) >>
        simp[] >> metis_tac[]) >>
     qabbrev_tac `t = EL j done` >> qabbrev_tac `r = i` >>
     qabbrev_tac `fn = (ptr_owner_view d (EL t h)).cf_fn` >>
     `MEM fn C.ctx_functions` by
       (`ptr_observation_reachable vs C (EL t h)` by metis_tac[] >>
        qpat_x_assum `ptr_observation_reachable vs C (EL t h)`
          (strip_assume_tac o REWRITE_RULE [ptr_observation_reachable_def]) >>
        drule ptr_frame_context_membership >> strip_tac >>
        Cases_on `d = LENGTH (EL t h).po_stack` >>
        simp[Abbr `fn`, ptr_owner_view_def] >>
        `LENGTH (EL t h).po_stack - (d+1) < LENGTH (EL t h).po_stack` by
          (irule arithmeticTheory.SUB_LESS >> simp[arithmeticTheory.ADD1, arithmeticTheory.LESS_EQ]) >>
        qpat_assum `EVERY (\f. MEM f.cf_fn C.ctx_functions) (EL t h).po_stack`
          (mp_tac o REWRITE_RULE [EVERY_EL]) >>
        disch_then (qspec_then `LENGTH (EL t h).po_stack - (d+1)` mp_tac) >> simp[]) >>
     `lookup_function fn.fn_name C.ctx_functions = SOME fn` by
       ((irule fmp_lookup_function_self >>
        simp[] >>
        qpat_assum `o1_ctx_shape C` mp_tac >>
        simp[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def] >> (gvs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def, fmp_lookup_function_self]))) >>
     drule_all ctx_pass_stage_lookup >> strip_tac >>
     rename1 `o1_walk_view rpolicy 2 C' fn observed` >>
     `wf_function fn /\ all_reachable fn` by fs[EVERY_MEM] >>
     `ptr_history_cfg_ok fn (cfg_analyze fn)` by simp[ptr_history_cfg_analyze_ok] >>
     `(ptr_owner_view d (EL t h)).cf_fn = (ptr_owner_view d (EL r h)).cf_fn` by
       (irule ptr_owner_view_interval_function >> simp[] >>
        qexistsl [`C`,`endpoint`,`vs`] >> simp[]) >>
     `(ptr_owner_view d (EL w h)).cf_fn = fn /\
      (ptr_owner_view d (EL i h)).cf_fn = fn` by
       (qpat_assum `(ptr_owner_view d (EL t h)).cf_fn = _` mp_tac >>
        simp[Abbr `fn`, EQ_SYM_EQ]) >>
     qabbrev_tac `bp = bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn` >>
     qabbrev_tac `mems = \nm. incr_ssort alloc_to (MAP FST (callee_mems_used observed.cu_context nm))` >>
     qabbrev_tac `sizes = \p. if context_alloca_size fn (imported_mems_used observed.cu_context fn) p = 0
          then NONE else SOME (context_alloca_size fn (imported_mems_used observed.cu_context fn) p)` >>
     `!k. t <= k /\ k < r ==>
        ~ptr_ml_can_kill (Allocation aid) bp sizes (ptr_owner_view d (EL k h)).cf_inst` by
       (`!k. t <= k /\ k <= r ==> d <= LENGTH (EL k h).po_stack /\
            FLOOKUP (ptr_owner_view d (EL k h)).cf_state.vs_allocas aid = SOME (b,sz)` by
          (rpt strip_tac >>
           `w <= k /\ k < LENGTH h` by
             (map_every (fn bound => qpat_assum bound mp_tac)
                [`w < t`, `t <= k`, `k <= r`, `r < LENGTH h`] >>
              POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
           simp[]) >>
        `!k. t <= k /\ k < r ==> ~in_revert_forward (EL k h).po_fn (EL k h).po_state /\
            x NOTIN range_bytes (step_writes (EL k h).po_inst (EL k h).po_state (EL (SUC k) h).po_state)` by
          (gen_tac >> strip_tac >>
           `SUC w <= k /\ k <= r` by
             (map_every (fn bound => qpat_assum bound mp_tac)
                [`w < t`, `t <= k`, `k < r`] >>
              POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
           simp[]) >>
        mp_tac (Q.INST [`i` |-> `t`, `j` |-> `r`, `aid` |-> `aid`, `d` |-> `d`,
                        `fn` |-> `fn`, `x` |-> `x`, `n` |-> `n`]
                 (SPEC_ALL ptr_cut_owner_interval_no_kill)) >>
        simp[Abbr `bp`, Abbr `sizes`] >> metis_tac[]) >>
     `ml_used_gen (Allocation aid) bp mems (ptr_owner_view d (EL w h)).cf_inst /\
      ml_read_gen (Allocation aid) bp mems (ptr_owner_view d (EL r h)).cf_inst` by
       (simp[Abbr `bp`] >> metis_tac[]) >>
     `?xs. FLOOKUP (context_mem_livesets (concretize_memloc_fuel fn)
             observed.cu_context fn bp (cfg_analyze fn)) (Allocation aid) = SOME xs /\
           MEM ((ptr_owner_view d (EL t h)).cf_state.vs_current_bb,
                (ptr_owner_view d (EL t h)).cf_state.vs_inst_idx) xs` by
       (irule ptr_owner_context_liveset >>
        simp[Abbr `bp`] >>
        conj_tac
        >- (qexistsl [`r`,`w`] >> simp[]) >>
        qexistsl [`C`,`endpoint`,`vs`] >> simp[]) >>
     `0 < sz /\ 0 < sb /\ pa <= pa+(x-b) /\ pa+(x-b) < pa+sz` by
       (map_every (fn bound => qpat_assum bound mp_tac)
          [`b <= x`, `x < b + sz`, `pb <= pa + (x-b)`, `pa + (x-b) < pb + sb`] >>
        POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     `ptr_observation_reachable vs C (EL t h)` by simp[] >>
     `lookup_function fn.fn_name C'.ctx_functions = SOME out.fpo_function` by simp[] >>
     `fn = (ptr_owner_view d (EL t h)).cf_fn` by simp[Abbr `fn`] >>
     drule_all (Q.INST [`A` |-> `EL t h`,`d` |-> `d`,`aid` |-> `aid`,
                        `fn` |-> `fn`,`p` |-> `pa`] (SPEC_ALL ptr_cut_owner_layout_row)) >>
     strip_tac >>
     rename1 `static_alloca_items fn = SOME itemsA` >>
     `MEM owner C.ctx_functions` by
       (qpat_assum `ptr_observation_reachable vs C (EL t h)`
          (mp_tac o REWRITE_RULE [ptr_observation_reachable_def]) >>
        disch_then (strip_assume_tac o MATCH_MP ptr_frame_context_membership) >>
        qpat_assum `owner = (ptr_owner_view e (EL t h)).cf_fn` SUBST1_TAC >>
        Cases_on `e = LENGTH (EL t h).po_stack` >> simp[ptr_owner_view_def] >>
        `LENGTH (EL t h).po_stack - (e+1) < LENGTH (EL t h).po_stack` by
          (irule arithmeticTheory.SUB_LESS >> simp[arithmeticTheory.ADD1, arithmeticTheory.LESS_EQ]) >>
        qpat_assum `EVERY (\f. MEM f.cf_fn C.ctx_functions) (EL t h).po_stack`
          (mp_tac o REWRITE_RULE [EVERY_EL]) >>
        disch_then (qspec_then `LENGTH (EL t h).po_stack - (e+1)` mp_tac) >> simp[]) >>
     `lookup_function owner.fn_name C.ctx_functions = SOME owner` by
       (irule fmp_lookup_function_self >>
        metis_tac[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def]) >>
     drule_all (Q.INST [`fn` |-> `owner`, `name` |-> `owner.fn_name`]
         (SPEC_ALL ctx_pass_stage_lookup)) >> strip_tac >>
     rename1 `o1_walk_view rpolicy 2 C' owner observedB` >>
     rename1 `fn_pass_step rpolicy _ observedB supplyB owner outB` >>
     `lookup_function owner.fn_name C'.ctx_functions = SOME outB.fpo_function` by metis_tac[] >>
     drule_all (Q.INST [`A` |-> `EL t h`,`d` |-> `e`,`aid` |-> `bid`,
                        `fn` |-> `owner`,`p` |-> `pb`] (SPEC_ALL ptr_cut_owner_layout_row)) >>
     strip_tac >>
     rename1 `static_alloca_items owner = SOME itemsB` >>
     `fn_ptr_ok P fn /\ fn_ptr_ok P owner /\ wf_function owner /\
      all_reachable owner /\ ssa_form owner /\ fn_inst_wf owner /\ EVERY inst_wf (fn_insts owner)` by
       (rpt (conj_tac >-
          (irule (iffLR EVERY_MEM) >> qexists `C.ctx_functions` >>
           conj_tac >> first_assum ACCEPT_TAC)) >>
        qpat_assum `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions`
          (qspec_then `owner` mp_tac o ONCE_REWRITE_RULE [EVERY_MEM]) >>
        BETA_TAC >> (impl_tac >- first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
     `ptr_history_cfg_ok owner (cfg_analyze owner)` by simp[ptr_history_cfg_analyze_ok] >>
     `reserved_intervals_disjoint (pa,sz) (pb,sb)` by
       (Cases_on `e = d`
        >- (`tok = token /\ owner = fn /\ bid <> aid` by metis_tac[] >>
            `outB.fpo_function = out.fpo_function /\ itemsB = itemsA` by
              metis_tac[optionTheory.SOME_11] >>
            `MEM (Allocation bid,sb) itemsA /\
             MEM (Allocation bid,pb,sb) out.fpo_function.fn_mems_used /\
             fn_inst_wf fn /\ ssa_form fn /\ EVERY inst_wf (fn_insts fn)` by metis_tac[] >>
            `?ys. FLOOKUP (context_mem_livesets (concretize_memloc_fuel fn)
                  observed.cu_context fn bp (cfg_analyze fn)) (Allocation bid) = SOME ys /\
              MEM ((ptr_owner_view d (EL t h)).cf_state.vs_current_bb,
                   (ptr_owner_view d (EL t h)).cf_state.vs_inst_idx) ys` by
              (Cases_on `d = LENGTH (EL t h).po_stack`
               >- (`fn = (EL t h).po_fn /\ tok = HD tsj` by
                      (conj_tac
                       >- (qpat_assum `fn = (ptr_owner_view d (EL t h)).cf_fn`
                             (fn th => once_rewrite_tac[th]) >>
                           qpat_assum `d = LENGTH (EL t h).po_stack`
                             (fn th => simp[NoAsms, th, ptr_owner_view_def])) >>
                       `LENGTH tsj = SUC (LENGTH (EL t h).po_stack)` by
                         (qpat_assum `ptr_source_ownership _ _ _ (EL t h) tsj _ _ _ _ _`
                            (mp_tac o MATCH_MP ptr_source_ownership_caches) >>
                          disch_then (mp_tac o MATCH_MP ptr_source_birth_caches_activations) >>
                          disch_then (ACCEPT_TAC o MATCH_MP ptr_source_activations_length)) >>
                       qpat_assum `d = LENGTH (EL t h).po_stack` (fn hd =>
                         qpat_assum `EL (LENGTH (EL t h).po_stack - d) tsj = token`
                           (mp_tac o SIMP_RULE (srw_ss()) [hd])) >>
                       qpat_x_assum `LENGTH tsj = SUC _` mp_tac >>
                       Cases_on `tsj` >> simp[NoAsms] >> metis_tac[]) >>
                   `dv IN pointer_derived_vars fn (ptr_bp_alloc_roots fn bid)` by
                     (irule (INST_TYPE [alpha |-> ``:num``] ptr_tag_roots_local_wf) >> simp[] >>
                      goal_assum (drule_at (Pat `FLOOKUP TGj dv = SOME (_,_)`)) >>
                      qexists `PTj` >> conj_tac
                      >- (rpt strip_tac >> spose_not_then strip_assume_tac >>
                          `MEM (SOME (tok,bid)) PTj` by
                            (qpat_assum `EL (w2n _) PTj = SOME (tok,bid)`
                               (fn th => once_rewrite_tac[GSYM th]) >>
                             irule EL_MEM >> first_assum ACCEPT_TAC) >>
                          drule_all ptr_source_params_fresh_current >> simp[]) >>
                      drule_all ptr_source_tag_roots_current >>
                      disch_then (qspec_then `(tok,bid)` mp_tac) >> simp[]) >>
                   `!i. MEM i (fn_insts fn) ==>
                     MEM i (bp_scan_insts fn (cfg_analyze fn).cfg_dfs_pre)` by
                     metis_tac[bp_scan_production_complete] >>
                   `?off. MEM (Ptr (Allocation bid) off)
                     (bp_get_ptrs (bp_analyze_fuel (concretize_memloc_fuel fn)
                       (cfg_analyze fn) fn) dv)` by
                     (irule ptr_bp_production_coverage >> metis_tac[]) >>
                   `MEM (Allocation bid) (find_base_allocas_opt bp (inst_write_op (EL t h).po_inst))` by
                     (simp[Abbr `bp`, find_base_allocas_opt_def, GSYM bp_bases_find_base_allocas,
                           bp_bases_def, MEM_MAP] >> metis_tac[ptr_base_def]) >>
                   `active_inst fn (EL t h).po_inst (EL t h).po_state` by
                     (qpat_assum `ptr_observation_reachable vs C (EL t h)`
                        (mp_then Any mp_tac (cj 1 ptr_owner_view_active)) >>
                      disch_then (qspec_then `LENGTH (EL t h).po_stack` mp_tac) >>
                      qpat_assum `fn = (EL t h).po_fn`
                        (fn th => simp[NoAsms, th, ptr_owner_view_def])) >>
                   qpat_assum `d = LENGTH (EL t h).po_stack`
                     (fn th => simp[NoAsms, th, ptr_owner_view_def]) >>
                   irule ptr_active_write_liveset >> metis_tac[]) >>
               `LENGTH (EL t h).po_stack - (d+1) < LENGTH (EL t h).po_stack /\
                SUC (LENGTH (EL t h).po_stack - (d+1)) = LENGTH (EL t h).po_stack - d` by
                 (qpat_assum `d <= LENGTH (EL t h).po_stack` mp_tac >>
                  qpat_assum `d <> LENGTH (EL t h).po_stack` mp_tac >>
                  POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
               `EL (SUC (LENGTH (EL t h).po_stack - (d+1))) tsj = tok /\
                fn = (EL (LENGTH (EL t h).po_stack - (d+1)) (EL t h).po_stack).cf_fn` by
                 (conj_tac
                  >- (qpat_assum `SUC _ = LENGTH (EL t h).po_stack - d`
                        (fn th => once_rewrite_tac[th]) >>
                      qpat_assum `EL (LENGTH (EL t h).po_stack - e) tsj = tok` mp_tac >>
                      qpat_assum `e = d` (fn th => simp[NoAsms, th])) >>
                  qpat_assum `fn = (ptr_owner_view d (EL t h)).cf_fn` mp_tac >>
                  qpat_assum `d <> LENGTH (EL t h).po_stack`
                    (fn th => simp[NoAsms, th, ptr_owner_view_def])) >>
               drule_all ptr_source_tagged_owner_call_liveset >>
               disch_then (qspec_then `observed.cu_context` strip_assume_tac) >>
               qpat_assum `d <> LENGTH (EL t h).po_stack`
                 (fn th => simp[NoAsms, th, ptr_owner_view_def]) >>
               simp[Abbr `bp`] >> metis_tac[]) >>
            rename1 `FLOOKUP _ (Allocation bid) = SOME ys` >>
            qpat_x_assum `owner = fn` SUBST_ALL_TAC >>
            qpat_x_assum `Abbrev (bp = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
            irule ptr_output_local_local_separation >>
            conj_tac >- first_assum ACCEPT_TAC >>
            conj_tac >- first_assum ACCEPT_TAC >>
            qexistsl [`P`,`Allocation aid`,
              `((ptr_owner_view d (EL t h)).cf_state.vs_current_bb,
                (ptr_owner_view d (EL t h)).cf_state.vs_inst_idx)`,`Allocation bid`,
              `observed.cu_context`,`fn`,`out.fpo_function`,`concretize_memloc_fuel fn`,
              `itemsA`,`xs`,`ys`,`observed`,`out`,`reserved`,`rpolicy`,`s`] >>
            rpt conj_tac
            >- (qpat_assum `bid <> aid` mp_tac >> simp[NoAsms, EQ_SYM]) >>
            asm_rewrite_tac[]) >>
        Cases_on `d < e`
        >- (`d < LENGTH (EL t h).po_stack /\
             LENGTH (EL t h).po_stack-d-1 < LENGTH (EL t h).po_stack /\
             LENGTH (EL t h).po_stack-e <= LENGTH (EL t h).po_stack-d-1` by
              (qpat_assum `d < e` mp_tac >>
               qpat_assum `e <= LENGTH (EL t h).po_stack` mp_tac >>
               POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
            `(ptr_owner_view d (EL t h)) =
             EL (LENGTH (EL t h).po_stack-d-1) (EL t h).po_stack` by
              (qpat_assum `d < LENGTH (EL t h).po_stack` mp_tac >>
               simp[NoAsms, ptr_owner_view_def]) >>
            `EL (LENGTH (EL t h).po_stack-e)
               (((EL t h).po_fn,(EL t h).po_state)::MAP (\f. (f.cf_fn,f.cf_state)) (EL t h).po_stack) =
             (owner,(ptr_owner_view e (EL t h)).cf_state)` by
              (qpat_assum `owner = (ptr_owner_view e (EL t h)).cf_fn`
                 (fn th => rewrite_tac[th]) >>
               qpat_assum `e <= LENGTH (EL t h).po_stack` mp_tac >>
               POP_ASSUM_LIST (K ALL_TAC) >>
               Cases_on `LENGTH (EL t h).po_stack-e` >> strip_tac
               >- (`e = LENGTH (EL t h).po_stack` by decide_tac >> simp[]) >>
               rename1 `LENGTH (EL t h).po_stack-e = SUC k` >>
               `e <> LENGTH (EL t h).po_stack /\
                LENGTH (EL t h).po_stack-e-1 = k /\ k < LENGTH (EL t h).po_stack` by decide_tac >>
               simp[ptr_owner_view_def, EL_MAP]) >>
            `fn = (EL (LENGTH (EL t h).po_stack-d-1) (EL t h).po_stack).cf_fn` by
              (qpat_assum `ptr_owner_view d (EL t h) = _`
                 (fn th => pure_rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
            `((ptr_owner_view d (EL t h)).cf_state.vs_current_bb,
              (ptr_owner_view d (EL t h)).cf_state.vs_inst_idx) =
             ((EL (LENGTH (EL t h).po_stack-d-1) (EL t h).po_stack).cf_state.vs_current_bb,
              (EL (LENGTH (EL t h).po_stack-d-1) (EL t h).po_stack).cf_state.vs_inst_idx)` by
              (qpat_assum `ptr_owner_view d (EL t h) = _`
                 (fn th => pure_rewrite_tac[GSYM th]) >> REFL_TAC) >>
            `?pc. MEM (Allocation bid,pc,sb) (imported_mems_used observed.cu_context fn) /\
              reserved_intervals_disjoint (pa,sz) (pc,sb)` by
              (qpat_assum `Abbrev (bp = _)`
                 (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
               irule ptr_output_suspended_descendant_separation_static >>
               rpt (conj_tac >- first_assum ACCEPT_TAC) >>
               conj_tac >- (qexists `P` >> first_assum ACCEPT_TAC) >>
               rpt (conj_tac >- first_assum ACCEPT_TAC) >>
               qexistsl [`C`,`C'`,`Allocation aid`,
                 `((ptr_owner_view d (EL t h)).cf_state.vs_current_bb,
                   (ptr_owner_view d (EL t h)).cf_state.vs_inst_idx)`,
                 `db`,`owner`,`(ptr_owner_view e (EL t h)).cf_state`,`endpoint`,
                 `out.fpo_function`,`h`,`itemsA`,`LENGTH (EL t h).po_stack-e`,`xs`,
                 `LENGTH (EL t h).po_stack-d-1`,`names`,`out`,`reserved`,`rpolicy`,`s`,
                 `(EL t h).po_stack`,`t`,`vs`] >>
               rpt conj_tac >> pure_rewrite_tac[REFL_CLAUSE] >>
               first_assum ACCEPT_TAC) >>
            `MEM (Allocation bid,pc,sb) out.fpo_function.fn_mems_used` by
              (irule ptr_stage_import_retained >>
               goal_assum (drule_at (Pat `fn_pass_step _ _ observed s fn out`)) >>
               qexistsl [`C`,`C'`,`names`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
            `MEM out.fpo_function C'.ctx_functions` by
              (qpat_assum `lookup_function fn.fn_name C'.ctx_functions = SOME out.fpo_function`
                 (mp_tac o MATCH_MP lookup_function_MEM) >> simp[NoAsms]) >>
            `FLOOKUP positions (Allocation bid) = SOME (pc,sb)` by
              (qpat_assum `ptr_stage_placements C' positions`
                 (mp_tac o REWRITE_RULE [ptr_stage_placements_def]) >>
               disch_then (qspecl_then [`Allocation bid`,`pc`,`sb`] (fn th => rewrite_tac[th])) >>
               qexists `out.fpo_function` >> conj_tac >> first_assum ACCEPT_TAC) >>
            `pc = pb` by
              (qpat_assum `FLOOKUP positions (Allocation bid) = SOME (pc,sb)` mp_tac >>
               qpat_assum `FLOOKUP positions (Allocation bid) = SOME (pb,sb)` mp_tac >>
               simp[NoAsms] >> metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ]) >>
            qpat_assum `pc = pb` (fn th => once_rewrite_tac[GSYM th]) >>
            first_assum ACCEPT_TAC) >>
        `e < LENGTH (EL t h).po_stack /\
         LENGTH (EL t h).po_stack-e-1 < LENGTH (EL t h).po_stack /\
         LENGTH (EL t h).po_stack-d <= LENGTH (EL t h).po_stack-e-1 /\
         SUC (LENGTH (EL t h).po_stack-e-1) = LENGTH (EL t h).po_stack-e` by
          (qpat_assum `~(d < e)` mp_tac >> qpat_assum `e <> d` mp_tac >>
           qpat_assum `d <= LENGTH (EL t h).po_stack` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
        `ptr_owner_view e (EL t h) =
         EL (LENGTH (EL t h).po_stack-e-1) (EL t h).po_stack` by
          (qpat_assum `e < LENGTH (EL t h).po_stack` mp_tac >>
           simp[NoAsms, ptr_owner_view_def]) >>
        `EL (LENGTH (EL t h).po_stack-d)
         (((EL t h).po_fn,(EL t h).po_state)::MAP (\f. (f.cf_fn,f.cf_state)) (EL t h).po_stack) =
         (fn,(ptr_owner_view d (EL t h)).cf_state)` by
          (qpat_assum `fn = (ptr_owner_view d (EL t h)).cf_fn`
             (fn th => rewrite_tac[th]) >>
           qpat_assum `d <= LENGTH (EL t h).po_stack` mp_tac >>
           POP_ASSUM_LIST (K ALL_TAC) >>
           Cases_on `LENGTH (EL t h).po_stack-d` >> strip_tac
           >- (`d = LENGTH (EL t h).po_stack` by decide_tac >> simp[]) >>
           rename1 `LENGTH (EL t h).po_stack-d = SUC k` >>
           `d <> LENGTH (EL t h).po_stack /\
            LENGTH (EL t h).po_stack-d-1 = k /\ k < LENGTH (EL t h).po_stack` by decide_tac >>
           simp[ptr_owner_view_def, EL_MAP]) >>
        `EL (SUC (LENGTH (EL t h).po_stack-e-1)) tsj = tok` by
          (qpat_assum `SUC _ = LENGTH (EL t h).po_stack-e`
             (fn th => once_rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
        `owner = (EL (LENGTH (EL t h).po_stack-e-1) (EL t h).po_stack).cf_fn` by
          (qpat_assum `ptr_owner_view e (EL t h) = _`
             (fn th => pure_rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
        `((ptr_owner_view e (EL t h)).cf_state.vs_current_bb,
          (ptr_owner_view e (EL t h)).cf_state.vs_inst_idx) =
         ((EL (LENGTH (EL t h).po_stack-e-1) (EL t h).po_stack).cf_state.vs_current_bb,
          (EL (LENGTH (EL t h).po_stack-e-1) (EL t h).po_stack).cf_state.vs_inst_idx)` by
          (qpat_assum `ptr_owner_view e (EL t h) = _`
             (fn th => pure_rewrite_tac[GSYM th]) >> REFL_TAC) >>
        `?pc. MEM (Allocation aid,pc,sz) (imported_mems_used observedB.cu_context owner) /\
          reserved_intervals_disjoint (pb,sb) (pc,sz)` by
          (irule ptr_output_tagged_ancestor_destination_separation_static >>
           rpt (conj_tac >- first_assum ACCEPT_TAC) >>
           conj_tac >- (qexists `P` >> first_assum ACCEPT_TAC) >>
           rpt (conj_tac >- first_assum ACCEPT_TAC) >>
           qexistsl [`C`,`C'`,`PTj`,`TGj`,
             `((ptr_owner_view e (EL t h)).cf_state.vs_current_bb,
               (ptr_owner_view e (EL t h)).cf_state.vs_inst_idx)`,
             `bid`,`bj`,`b`,`fn`,`(ptr_owner_view d (EL t h)).cf_state`,
             `endpoint`,`outB.fpo_function`,`h`,`itemsB`,`LENGTH (EL t h).po_stack-d`,
             `LENGTH (EL t h).po_stack-e-1`,`names`,`outB`,`tok`,`TAKE (SUC t) h`,
             `rj`,`reserved'`,`rpolicy`,`supplyB`,`sj`,`(EL t h).po_stack`,`t`,`tsj`,`dv`,`vs`] >>
           rpt conj_tac >> pure_rewrite_tac[REFL_CLAUSE] >>
           first_assum ACCEPT_TAC) >>
        `MEM (Allocation aid,pc,sz) outB.fpo_function.fn_mems_used` by
          (irule ptr_stage_import_retained >>
           goal_assum (drule_at (Pat `fn_pass_step _ _ observedB supplyB owner outB`)) >>
           qexistsl [`C`,`C'`,`names`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
        `MEM outB.fpo_function C'.ctx_functions` by
          (qpat_assum `lookup_function owner.fn_name C'.ctx_functions = SOME outB.fpo_function`
             (mp_tac o MATCH_MP lookup_function_MEM) >> simp[NoAsms]) >>
        `FLOOKUP positions (Allocation aid) = SOME (pc,sz)` by
          (qpat_assum `ptr_stage_placements C' positions`
             (mp_tac o REWRITE_RULE [ptr_stage_placements_def]) >>
           disch_then (qspecl_then [`Allocation aid`,`pc`,`sz`] (fn th => rewrite_tac[th])) >>
           qexists `outB.fpo_function` >> conj_tac >> first_assum ACCEPT_TAC) >>
        `pc = pa` by
          (qpat_assum `FLOOKUP positions (Allocation aid) = SOME (pc,sz)` mp_tac >>
           qpat_assum `FLOOKUP positions (Allocation aid) = SOME (pa,sz)` mp_tac >>
           simp[NoAsms] >> metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ]) >>
        qpat_assum `pc = pa` (fn th => once_rewrite_tac[GSYM th]) >>
        qpat_assum `reserved_intervals_disjoint (pb,sb) (pc,sz)` mp_tac >>
        simp[NoAsms, reserved_intervals_disjoint_def, DISJ_COMM]) >>
     qpat_x_assum `reserved_intervals_disjoint _ _`
       (mp_tac o REWRITE_RULE [reserved_intervals_disjoint_def]) >>
     qpat_assum `pa <= pa+(x-b)` mp_tac >>
     qpat_assum `pa+(x-b) < pa+sz` mp_tac >>
     qpat_assum `pb <= pa+(x-b)` mp_tac >>
     qpat_assum `pa+(x-b) < pb+sb` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  qexistsl [`q`,`reloc`] >> gvs[]
QED

Finalise focus_cut_owned_writer_path

Theorem ptr_paired_owned_read_recovery_upto:
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

(* The new committed sample is the old source endpoint; earlier samples
   keep both their source index and their forwarding exclusion. *)
(* Classify one positive range using the selector that produced it. *)
Theorem ptr_cut_range_geometry:
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  ((ranges = source_memory_read_ranges inst s /\ mops = mem_read_ops inst) \/
   (ranges = source_memory_write_ranges inst s /\ mops = mem_write_ops inst)) /\
  mops = SOME ops /\ MEM (w2n x,len) ranges /\ 0 < len /\
  ptr_ledger_erases dyn births TG G /\
  (!aid pa sz. FLOOKUP positions (Allocation aid) = SOME (pa,sz) ==>
     pa + sz < dimword (:256)) /\
  ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {} (SOME x) (SOME y) ==>
  (x = y /\ (w2n x + len <= lo \/ dyn <= w2n x) /\ op_prov TG ops.iao_ofst = NONE) \/
  (?v token aid b sz pa. ops.iao_ofst = Var v /\ FLOOKUP TG v = SOME (token,aid) /\
    FLOOKUP births (token,aid) = SOME (b,sz) /\
    FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
    b <= w2n x /\ w2n x + len <= b + sz /\ w2n y = pa + (w2n x - b))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `len = 0 \/ (w2n x + len <= lo /\ op_prov G ops.iao_ofst = NONE) \/
     (?v b sz. ops.iao_ofst = Var v /\ FLOOKUP G v = SOME (b,sz) /\
        b <= w2n x /\ w2n x + len <= b + sz)` by
    (drule_all ptr_access_range_classification >> simp[]) >>
  pop_assum strip_assume_tac >- fs[]
  >- (`op_prov TG ops.iao_ofst = NONE` by
        (Cases_on `ops.iao_ofst` >> gs[op_prov_def] >>
         rename1 `FLOOKUP G v = NONE` >>
         Cases_on `FLOOKUP TG v` >> simp[] >>
         fs[ptr_ledger_erases_def] >>
         qpat_x_assum `!v. ptr_owner_erases _ _ _ _` (qspec_then `v` mp_tac) >>
         simp[ptr_owner_erases_def, FLOOKUP_DEF] >> metis_tac[]) >>
      gvs[ptr_lookup_transport_def, ptr_value_transport_scalar_empty]) >>
  `ptr_owner_erases dyn births (FLOOKUP TG v) (SOME (b,sz))` by
    (fs[ptr_ledger_erases_def] >> metis_tac[]) >>
  Cases_on `FLOOKUP TG v`
  >- gvs[ptr_owner_erases_def, op_prov_def, ptr_lookup_transport_def,
         ptr_value_transport_scalar_empty] >>
  rename1 `FLOOKUP TG v = SOME tag` >> PairCases_on `tag` >>
  rename1 `FLOOKUP TG v = SOME (token,aid)` >>
  `FLOOKUP births (token,aid) = SOME (b,sz)` by fs[ptr_owner_erases_def] >>
  `?pa. FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
    y = x - n2w b + n2w pa` by
    gvs[ptr_lookup_transport_def, ptr_value_transport_def, op_prov_def] >>
  `pa + sz < dimword (:256)` by metis_tac[] >>
  `w2n y = pa + (w2n x - b)` by
    (irule ptr_closed_relocation_value >> simp[] >> qexists `sz` >> simp[] >> decide_tac) >>
  disj2_tac >> qexistsl [`v`,`token`,`aid`,`b`,`sz`,`pa`] >> simp[]
QED

(* Byte content at a read fetch does not depend on a successor step. *)
Theorem focus_cut_paired_read_bytes_ptr_safe:
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
    (SOME x) (SOME y) ==>
  !j. j < len /\ w2n x+j NOTIN a.po_taint.t_mem ==>
    read_byte (w2n x+j) a.po_state.vs_memory =
    read_byte (w2n y+j) at.po_state.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac >> strip_tac >>
  `ptr_discipline_upto lo n C vs /\ fixed_region_reserved lo C /\
    EVERY (\f. f.fn_eom = NONE) C.ctx_functions` by fs[o1_ptr_safe_upto_def] >>
  drule_all ptr_paired_endpoint_cut_safety >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
     metis_tac[ptr_fn_inst_wf_flat, EVERY_MEM]) >>
  drule_all ptr_source_ownership_erases_upto >> strip_tac >>
  `!aid pa sz. FLOOKUP positions (Allocation aid) = SOME (pa,sz) ==>
      pa + sz < dimword (:256)` by
    (rpt strip_tac >> drule_all ptr_stage_placements_strict_bound >> simp[]) >>
  `a.po_inst.inst_opcode <> ASSIGN` by gvs[mem_read_ops_def, AllCaseEqs()] >>
  `0 < len` by decide_tac >>
  Q.SUBGOAL_THEN
    `(x = y /\ (w2n x+len <= lo \/ dyn_floor C vs <= w2n x) /\
       op_prov TG ops.iao_ofst = NONE) \/
     (?v token aid b sz pa. ops.iao_ofst = Var v /\ FLOOKUP TG v = SOME (token,aid) /\
       FLOOKUP births (token,aid) = SOME (b,sz) /\
       FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
       b <= w2n x /\ w2n x+len <= b+sz /\ w2n y = pa + (w2n x-b))`
    (DISJ_CASES_THEN2 (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) assume_tac) strip_assume_tac)
  >- (irule ptr_cut_range_geometry >>
      qpat_assum `ptr_lookup_transport _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `access_ok _ _ _ _ _` (irule_at Any) >>
      qpat_assum `ptr_ledger_erases _ _ _ _` (irule_at Any) >> simp[] >> metis_tac[])
  >- (`w2n x+j < lo \/ dyn_floor C vs <= w2n x+j` by
        (qpat_x_assum `(_ + len <= lo \/ _) /\ _` strip_assume_tac >> decide_tac) >>
      drule ptr_paired_fixed_read_recovery_upto >> disch_then irule >> simp[] >>
      rpt conj_tac >> goal_assum (drule_at Any) >> simp[]) >>
  suspend "owned"
QED

Resume focus_cut_paired_read_bytes_ptr_safe[owned]:
  `ptr_observation_reachable vs C a` by simp[ptr_observation_reachable_def] >>
  `vs.vs_allocas = FEMPTY` by fs[o1_initial_state_ok_def] >>
  drule_all ptr_source_ownership_live_prov >> pure_rewrite_tac[MEM_EL] >>
  disch_then (qx_choose_then `k` strip_assume_tac) >>
  drule ptr_source_ownership_caches >> strip_tac >>
  drule ptr_source_birth_caches_slices >> strip_tac >>
  `LENGTH tokens = SUC (LENGTH a.po_stack)` by
    (drule ptr_source_birth_caches_activations >> strip_tac >>
     drule ptr_source_activations_length >> simp[]) >>
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
  drule ptr_paired_owned_read_recovery_upto >> disch_then irule >> simp[] >>
  rpt conj_tac >> goal_assum (drule_at Any) >> simp[]
  >> (metis_tac[])
QED

Finalise focus_cut_paired_read_bytes_ptr_safe

Theorem focus_cut_paired_read_bytes:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ EVERY all_reachable C.ctx_functions /\
  EVERY ssa_form C.ctx_functions /\ EVERY fn_defs_reach_uses C.ctx_functions /\
  o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  o1_safe_upto D lo n C vs /\ alloca_frontier_upto n C vs /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  max_live_eom C' = SOME eom /\ ptr_stage_placements C' positions /\
  (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  gas_cut n vs at.po_state /\ ~in_revert_forward a.po_fn a.po_state /\
  mem_read_ops a.po_inst = SOME ops /\
  eval_operand ops.iao_ofst a.po_state = SOME x /\
  eval_operand ops.iao_ofst at.po_state = SOME y /\
  MEM (w2n x,len) (source_memory_read_ranges a.po_inst a.po_state) /\
  ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {}
    (SOME x) (SOME y) ==>
  !j. j < len /\ w2n x+j NOTIN a.po_taint.t_mem ==>
    read_byte (w2n x+j) a.po_state.vs_memory =
    read_byte (w2n y+j) at.po_state.vs_memory
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  fs[o1_safe_upto_def] >>
  mp_tac focus_cut_paired_read_bytes_ptr_safe >> simp[]
QED

(* Positive read and write ranges at a kept fetch. The descriptor branch
   retains the actual evaluations and the current allocation owner. *)
Theorem focus_cut_paired_access_ranges:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_initial_state_ok vs /\
  vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  ptr_discipline_upto lo n C vs /\ EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  max_live_eom C' = SOME eom /\ ptr_stage_placements C' positions /\
  gas_cut n vs at.po_state /\ ~in_revert_forward a.po_fn a.po_state /\
  at.po_inst = a.po_inst /\
  ((mops = mem_read_ops a.po_inst /\
    rs = source_memory_read_ranges a.po_inst a.po_state /\
    rt = source_memory_read_ranges at.po_inst at.po_state) \/
   (mops = mem_write_ops a.po_inst /\
    rs = source_memory_write_ranges a.po_inst a.po_state /\
    rt = source_memory_write_ranges at.po_inst at.po_state)) /\
  MEM (off,len) rt /\ 0 < len ==>
  ?off_s. MEM (off_s,len) rs /\
    ((off = off_s /\ off_s + len <= lo /\
       (!ops. mops = SOME ops ==> op_prov a.po_prov ops.iao_ofst = NONE /\
                                  op_prov TG ops.iao_ofst = NONE)) \/
     (?ops x y. mops = SOME ops /\
       eval_operand ops.iao_ofst a.po_state = SOME x /\
       eval_operand ops.iao_ofst at.po_state = SOME y /\
       off_s = w2n x /\ off = w2n y /\
       ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {}
         (SOME x) (SOME y) /\
       ((x = y /\ op_prov TG ops.iao_ofst = NONE /\
           (w2n x + len <= lo \/ dyn_floor C vs <= w2n x)) \/
        (?v token aid b sz pa d owner output.
          ops.iao_ofst = Var v /\ FLOOKUP TG v = SOME (token,aid) /\
          FLOOKUP a.po_prov v = SOME (b,sz) /\
          EL (LENGTH h - 1) H = (tokens,registry,births,PT,TG,saved,entries) /\
          d <= LENGTH a.po_stack /\ EL (LENGTH a.po_stack - d) tokens = token /\
          FLOOKUP registry token = SOME owner /\ owner = (ptr_owner_view d a).cf_fn /\
          FLOOKUP (ptr_owner_view d a).cf_state.vs_allocas aid = SOME (b,sz) /\
          lookup_function owner.fn_name C'.ctx_functions = SOME output /\
          MEM (Allocation aid,pa,sz) output.fn_mems_used /\
          FLOOKUP births (token,aid) = SOME (b,sz) /\
          FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
          b <= w2n x /\ w2n x + len <= b + sz /\
          w2n y = pa + (w2n x - b) /\ pa + sz <= eom /\ w2n y + len <= eom))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ptr_paired_endpoint_cut_safety >> strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
      a.po_state at.po_state /\ a.po_state.vs_labels = at.po_state.vs_labels` by
    (fs[ptr_paired_sample_def] >> metis_tac[ptr_history_content_labels]) >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
     metis_tac[ptr_fn_inst_wf_flat, EVERY_MEM]) >>
  drule ptr_discipline_upto_fn_ptr_ok >> strip_tac >>
  drule_all ptr_frame_current_static >> strip_tac >>
  rename1 `ptr_static_support P a.po_fn a.po_prov` >>
  `FDOM a.po_prov SUBSET fn_pv P a.po_fn` by
    (fs[ptr_static_support_def, SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[optionTheory.NOT_NONE_SOME]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (drule concretizePtrChronologicalDemandTheory.ptr_frame_operand_instructions >> simp[]) >>
  `fn_ptr_ok P a.po_fn /\ inst_wf a.po_inst /\ opaque_use_ok a.po_fn /\
   label_positions_ok a.po_inst` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, inst_shape_ok_def, EVERY_MEM] >>
     metis_tac[]) >>
  drule_all ptr_source_ownership_erases_upto >> strip_tac >>
  Q.SUBGOAL_THEN
    `((rs = source_memory_read_ranges a.po_inst a.po_state /\ mops = mem_read_ops a.po_inst) \/
      (rs = source_memory_write_ranges a.po_inst a.po_state /\ mops = mem_write_ops a.po_inst))`
    assume_tac >- metis_tac[] >>
  Q.SUBGOAL_THEN
    `?off_s. MEM (off_s,len) rs /\
      ((off = off_s /\ ~(?ops. mops = SOME ops /\ op_prov a.po_prov ops.iao_ofst <> NONE)) \/
       (?ops x y. mops = SOME ops /\ eval_operand ops.iao_ofst a.po_state = SOME x /\
        eval_operand ops.iao_ofst at.po_state = SOME y /\ off_s = w2n x /\ off = w2n y /\
        ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {} (SOME x) (SOME y)))`
    (qx_choose_then `off_s` (CONJUNCTS_THEN2 assume_tac strip_assume_tac))
  >- (irule ptr_current_range_transport >>
      qpat_assum `ptr_mixed_vars _ _ _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `ptr_ledger_erases _ _ _ _` (irule_at Any) >> simp[] >> metis_tac[]) >>
  qexists `off_s` >> simp[]
  >- suspend "scalar" >>
  suspend "descriptor"
QED

Resume focus_cut_paired_access_ranges[scalar]:
  disj1_tac >> simp[] >>
  `off_s + len <= lo` by
    (drule_all ptr_access_range_classification >> simp[] >> strip_tac >>
     fs[op_prov_def] >> metis_tac[]) >>
  simp[] >> rpt strip_tac >>
  `op_prov a.po_prov ops.iao_ofst = NONE` by metis_tac[] >>
  drule ptr_owner_op_projection >> disch_then (qspec_then `ops.iao_ofst` mp_tac) >>
  Cases_on `op_prov TG ops.iao_ofst` >>
  simp[ptr_owner_erases_def, FLOOKUP_DEF]
QED

Resume focus_cut_paired_access_ranges[descriptor]:
  `!aid pa sz. FLOOKUP positions (Allocation aid) = SOME (pa,sz) ==>
      pa + sz < dimword (:256)` by
    (rpt strip_tac >> drule_all ptr_stage_placements_strict_bound >> simp[]) >>
  `MEM (w2n x,len) rs` by metis_tac[] >>
  drule_all ptr_cut_range_geometry >> strip_tac
  >- (disj2_tac >> disj1_tac >> gvs[])
  >- (disj2_tac >> disj1_tac >> gvs[]) >>
  suspend "owner"
QED

Resume focus_cut_paired_access_ranges[owner]:
  `FLOOKUP a.po_prov v = SOME (b,sz)` by
    (drule ptr_owner_op_projection >> disch_then (qspec_then `Var v` mp_tac) >>
     simp[ptr_owner_erases_def, op_prov_def]) >>
  drule ptr_structural_transcript_endpoint >> strip_tac >>
  `LENGTH h - 1 < LENGTH h` by decide_tac >>
  `H <> []` by (Cases_on `H` >> gvs[]) >>
  `EL (LENGTH h - 1) H = (tokens,registry,births,PT,TG,saved,entries)` by
    (drule (REWRITE_RULE [PRE_SUB1] LAST_EL) >> metis_tac[]) >>
  `EL (LENGTH h - 1) h = a` by
    (drule ptr_structural_trace_source >> strip_tac >>
     drule ptr_chrono_history_end >> strip_tac >>
     qpat_x_assum `LAST h = a` mp_tac >> simp[LAST_EL, PRE_SUB1]) >>
  `?d owner output p.
    d <= LENGTH a.po_stack /\ EL (LENGTH a.po_stack - d) tokens = token /\
    FLOOKUP registry token = SOME owner /\ owner = (ptr_owner_view d a).cf_fn /\
    FLOOKUP (ptr_owner_view d a).cf_state.vs_allocas aid = SOME (b,sz) /\
    lookup_function owner.fn_name C'.ctx_functions = SOME output /\
    MEM (Allocation aid,p,sz) output.fn_mems_used /\
    FLOOKUP positions (Allocation aid) = SOME (p,sz)` by
    ((drule_at (Pat `ptr_structural_transcript _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
       (Q.SPECL [`LENGTH (h:ptr_observation list) - 1`, `LENGTH (h:ptr_observation list) - 1`]
         (GENL [``i:num``,``j:num``] ptr_transcript_historical_placement_upto)) >>
     simp[] >> disch_then drule_all >> simp[] >> (metis_tac[]))) >>
  `pa + sz <= eom` by
    (irule ptr_stage_placements_endpoint_bound >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `w2n y + len <= eom` by decide_tac >>
  disj2_tac >> disj2_tac >> qexistsl [`v`,`aid`,`b`,`sz`,`pa`,`d`,`output`] >> gvs[]
QED

Finalise focus_cut_paired_access_ranges

(* A paired layout belongs to a fixed root and target context. Keep those
   parameters fixed when instantiating the general chronology induction. *)
Theorem concretize_cut_history_ind:
  (!name fn lbl inst s1.
      Ct.ctx_entry = SOME name /\ lookup_function name Ct.ctx_functions = SOME fn /\
      fn_entry_label fn = SOME lbl /\
      enters_block fn (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl;
        vs_inst_idx := 0|>) s1 /\ active_inst fn inst s1 ==>
      P [ptr_observe [] [] FEMPTY entry_taint fn inst s1]
        (ptr_observe [] [] FEMPTY entry_taint fn inst s1)) /\
  (!h a b. ptr_chrono_history vs Ct h a /\ P h a /\ ptr_chrono_step Ct a b ==>
      P (h ++ [b]) b) ==>
  !ht at. ptr_chrono_history vs Ct ht at ==> P ht at
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!v ctx ht at. ptr_chrono_history v ctx ht at ==>
      v = vs /\ ctx = Ct ==> P ht at` suffices_by
    (disch_then (qspecl_then [`vs`,`Ct`] mp_tac) >> simp[]) >>
  ho_match_mp_tac ptr_chrono_history_strongind >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem focus_concretize_cut_coverage_ptr_safe:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_initial_state_ok vs /\
  vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  o1_ptr_safe_upto D lo n C vs /\ alloca_frontier_upto n C vs /\
  EVERY ssa_form C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  max_live_eom C' = SOME eom /\
  (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) ==>
  ?R lp positions.
    ptr_stage_placements C' positions /\
    !ht at. ptr_chrono_history vs C' ht at ==> gas_cut n vs at.po_state ==>
      (?h a done tokens registry births PT TG saved entries H calls ws.
        ptr_paired_prefix R lp positions lo vs C C'
          h a ht at done tokens registry births PT TG saved entries H calls ws /\
        EVERY (\i. ~in_revert_forward (EL i h).po_fn (EL i h).po_state) done /\
        a.po_inst.inst_opcode <> NOP /\
        at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst) \/
      (?bb i j. lookup_block at.po_state.vs_current_bb at.po_fn.fn_blocks = SOME bb /\
        revert_forward_pair bb i j /\
        i < at.po_state.vs_inst_idx /\ at.po_state.vs_inst_idx <= j)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ptr_discipline_upto lo n C vs` by fs[o1_ptr_safe_upto_def] >>
  drule_all concretize_cut_stage_pairing >> strip_tac >>
  `C.ctx_entry = C'.ctx_entry /\ vs.vs_vars = FEMPTY` by
    fs[ctx_pass_stage_def, o1_initial_state_ok_def] >>
  `EVERY fn_inst_wf C.ctx_functions` by fs[EVERY_MEM] >>
  qexistsl [`R`, `lp`, `positions`] >> simp[] >>
  ho_match_mp_tac concretize_cut_history_ind >> conj_tac
  >- suspend "root" >>
  suspend "successor"
QED

Resume focus_concretize_cut_coverage_ptr_safe[root]:
  rpt gen_tac >> strip_tac >> disch_tac >> disj1_tac >>
  `ptr_chrono_history vs C'
     [ptr_observe [] [] FEMPTY entry_taint fn inst s1]
     (ptr_observe [] [] FEMPTY entry_taint fn inst s1)` by
    metis_tac[ptr_chrono_history_rules] >>
  `(ptr_observe [] [] FEMPTY entry_taint fn inst s1).po_stack = []` by
    simp[ptr_observe_def] >>
  `EVERY (\f. first_block_no_phi f /\ fn_inst_wf f /\
     EVERY bb_well_formed f.fn_blocks /\
     (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
       IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all ptr_paired_context_root >>
  disch_then (qspec_then `lo` strip_assume_tac) >>
  qpat_assum `ptr_paired_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (irule_at Any) >> simp[]
QED

Resume focus_concretize_cut_coverage_ptr_safe[successor]:
  rpt gen_tac >> strip_tac >> disch_tac >>
  rename1 `ptr_chrono_step C' at zt` >>
  `gas_cut n vs at.po_state` by
    (drule ptr_chrono_step_readings_le >> metis_tac[gas_cut_readings_mono]) >>
  qpat_x_assum `gas_cut _ _ _ ==> _ \/ _` mp_tac >>
  simp[] >> reverse strip_tac
  >- (disj2_tac >> irule ptr_focus_forward_window_successor >>
      rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]) >>
  Cases_on `in_revert_forward a.po_fn a.po_state`
      >- (disj2_tac >> irule ptr_focus_forward_window_successor >>
          rpt (goal_assum (drule_at Any)) >> simp[] >>
          (metis_tac[])) >>
      disj1_tac >>
      `(?P. EVERY (fn_ptr_ok P) C.ctx_functions)` by
        (drule ptr_discipline_upto_fn_ptr_ok >> metis_tac[]) >>
      drule_all ptr_paired_endpoint_cut_safety >> strip_tac >>
      `?delta z tokens' registry' births' PT' TG' saved' entries' snapshots calls' ws'.
        delta <> [] /\ LENGTH snapshots = LENGTH delta /\
        ptr_paired_prefix R lp positions lo vs C C'
          (h ++ delta) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
          tokens' registry' births' PT' TG' saved' entries'
          (H ++ snapshots) calls' ws' /\
        z.po_inst.inst_opcode <> NOP /\
        zt.po_inst = concretize_inst_with_positions (lp z.po_fn) z.po_inst`
        suffices_by
        (strip_tac >>
         `EVERY (\i. ~in_revert_forward (EL i (h ++ delta)).po_fn
          (EL i (h ++ delta)).po_state) (done ++ [LENGTH h - 1])` by
           (irule concretizePtrHistoryCoverageTheory.ptr_paired_history_safe_append >>
            rpt (goal_assum (drule_at Any)) >> simp[]) >>
         qpat_assum `ptr_paired_prefix _ _ _ _ _ _ _ (_ ++ _) _ _ _ _ _ _ _ _ _ _ _ _ _ _`
           (irule_at Any) >> simp[]) >>
      Cases_on `a.po_inst.inst_opcode = INVOKE`
      >- (`EVERY (\f. first_block_no_phi f /\ fn_inst_wf f /\ opaque_use_ok f /\
              EVERY bb_well_formed f.fn_blocks /\ ALL_DISTINCT (fn_labels f) /\
              (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
                IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions` by
            (fs[EVERY_MEM] >> metis_tac[]) >>
          irule ptr_focus_invoke_extension >> simp[] >> metis_tac[]) >>
      Cases_on `MEM a.po_inst.inst_opcode [JMP; JNZ; DJMP]`
      >- (`EVERY (\f. fn_inst_wf f /\ retpc_shape_ok f /\ opaque_use_ok f /\
              EVERY bb_well_formed f.fn_blocks /\ ALL_DISTINCT (fn_labels f) /\
              (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
                IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions` by
            (fs[EVERY_MEM] >> metis_tac[]) >>
          irule ptr_focus_jump_extension >> simp[] >> conj_tac
          >- (qexists `P` >> simp[]) >>
          goal_assum (drule_at (Pat `ptr_paired_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
          fs[MEM]) >>
  `?b ts reg B P0 T0 S0 E0 sample cs w.
      ptr_paired_prefix R lp positions lo vs C C'
        (h ++ [b]) b (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
        ts reg B P0 T0 S0 E0 (H ++ [sample]) cs w` suffices_by
    (strip_tac >>
     `fn_inst_wf b.po_fn` by
       (drule ptr_paired_prefix_transcript >> strip_tac >>
        drule ptr_structural_transcript_erasure >> strip_tac >>
        drule ptr_structural_trace_source >> strip_tac >>
        drule ptr_chrono_history_reachable >>
        simp[ptr_observation_reachable_def] >> strip_tac >>
        drule ptr_frame_context_membership >> strip_tac >>
        fs[EVERY_MEM]) >>
     drule_all ptr_paired_prefix_normalize >> strip_tac >>
     qexistsl_tac [`[b] ++ delta`, `ptr_gap_scan bb n' b`,
       `ts`, `reg`, `B`, `P0`, `T0`, `S0`, `E0`, `[sample] ++ snapshots`, `cs`, `w`] >>
     gvs[APPEND_ASSOC, ptr_gap_scan_fields]) >>
  `MEM a.po_fn C.ctx_functions` by
    (drule ptr_frame_context_membership >> simp[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (drule concretizePtrChronologicalDemandTheory.ptr_frame_operand_instructions >> simp[]) >>
  `~MEM a.po_inst.inst_opcode
      [MEMTOP; GETFMP; SETFMP; FMP_PARAM; DRET; RETFMP;
       PHI; NOP; RETURN; REVERT; STOP; SINK; SELFDESTRUCT; INVALID]` by
    (`~MEM a.po_inst.inst_opcode
        [MEMTOP; GETFMP; SETFMP; FMP_PARAM; DRET; RETFMP; NOP]` by
       (fs[EVERY_MEM, fn_ptr_ok_def, MEM] >> metis_tac[]) >>
     simp[MEM] >> rpt strip_tac >> gvs[] >>
     `at.po_inst = a.po_inst` by simp[concretize_positions_unchanged] >>
     qpat_x_assum `at.po_inst = concretize_inst_with_positions _ _` kall_tac >>
     qpat_x_assum `ptr_chrono_step C' at zt` mp_tac >>
     simp[Once ptr_chrono_step_cases, ptr_observe_def,
          ptr_observation_component_equality, is_terminator_def,
          step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()]) >>
  `EVERY (\f. f.fn_eom = NONE) C.ctx_functions` by fs[o1_ptr_safe_upto_def] >>
  suspend "ordinary"
QED

Resume focus_concretize_cut_coverage_ptr_safe[ordinary]:
  SUBGOAL_THEN ``?Q. EVERY (fn_ptr_ok Q) C.ctx_functions`` assume_tac
  >- (qexists `P` >> simp[]) >>
  Cases_on `MEM a.po_inst.inst_opcode [ASSIGN; PARAM; RETPC_PARAM]`
  >- (drule_all ptr_focus_binding_step >> strip_tac >> goal_assum (drule_at Any)) >>
  Cases_on `MEM a.po_inst.inst_opcode [ADD; SUB]`
  >- (drule_all ptr_focus_affine_step >> strip_tac >> goal_assum (drule_at Any)) >>
  Cases_on `MEM a.po_inst.inst_opcode [EQ; LT; GT]`
  >- (drule_all ptr_focus_comparison_step >> strip_tac >> goal_assum (drule_at Any)) >>
  Cases_on `MEM a.po_inst.inst_opcode
    [MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD; SLT; SGT;
     ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET; SHL; SHR; SAR]`
  >- (drule_all ptr_focus_scalar_step >> strip_tac >> goal_assum (drule_at Any)) >>
  Cases_on `MEM a.po_inst.inst_opcode [ASSERT; ASSERT_UNREACHABLE]`
  >- (drule_all ptr_focus_assertion_step >> strip_tac >> goal_assum (drule_at Any)) >>
  Cases_on `MEM a.po_inst.inst_opcode [CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID;
    COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE; CALLDATASIZE;
    RETURNDATASIZE; BLOBBASEFEE; CODESIZE; SELFBALANCE; BLOCKHASH; BLOBHASH;
    BALANCE; EXTCODESIZE; EXTCODEHASH; CALLDATALOAD; DLOAD]`
  >- (drule_all ptr_focus_environment_step >> strip_tac >> goal_assum (drule_at Any)) >>
  Cases_on `a.po_inst.inst_opcode = GAS`
  >- (drule_all ptr_focus_gas_step >> strip_tac >> goal_assum (drule_at Any)) >>
  Cases_on `MEM a.po_inst.inst_opcode [INITIAL_FMP; BUMP; DALLOCA]`
  >- (drule_all ptr_focus_fmp_op_step >> strip_tac >> goal_assum (drule_at Any)) >>
  Cases_on `a.po_inst.inst_opcode = ALLOCA`
  >- (drule_all ptr_focus_alloca_step >> strip_tac >> goal_assum (drule_at Any)) >>
  Cases_on `a.po_inst.inst_opcode = RET`
  >- (`EVERY (\f. retpc_shape_ok f /\
           (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
            IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions` by
        (fs[EVERY_MEM] >> metis_tac[]) >>
      `at.po_inst.inst_opcode = RET` by simp[concretize_positions_unchanged] >>
      drule_all ptr_focus_ret_execution >> strip_tac >>
      drule_all ptr_focus_ret_restore >> strip_tac >>
      drule_all ptr_focus_ret_attach >> strip_tac >> goal_assum (drule_at Any)) >>
  suspend "memory"
QED

Resume focus_concretize_cut_coverage_ptr_safe[memory]:
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    fs[EVERY_MEM, ptr_fn_inst_wf_flat] >>
  `ptr_source_ownership vs C h a tokens registry births PT TG saved` by
    (drule ptr_paired_prefix_transcript >> strip_tac >>
     drule ptr_structural_transcript_erasure >> strip_tac >>
     drule ptr_structural_trace_ownership >> simp[]) >>
  drule_all ptr_source_ownership_erases_upto >> strip_tac >>
  Cases_on `MEM a.po_inst.inst_opcode [MSTORE; MSTORE8; ISTORE]`
  >- (drule_all ptr_focus_store_step >> strip_tac >> goal_assum (drule_at Any)) >>
  Cases_on `MEM a.po_inst.inst_opcode [CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY]`
  >- (drule_all ptr_focus_buffer_copy_step >> strip_tac >> goal_assum (drule_at Any)) >>
  `dyn_floor C a.po_state = dyn_floor C vs` by
    (drule frame_reachable_initial_fmp >> simp[dyn_floor_def]) >>
  `!aid pa sz. FLOOKUP positions (Allocation aid) = SOME (pa,sz) ==>
      pa + sz < dimword (:256)` by
    (rpt strip_tac >> drule_all ptr_stage_placements_strict_bound >> simp[]) >>
  `!ops x y len.
    mem_write_ops a.po_inst = SOME ops /\
    eval_operand ops.iao_ofst a.po_state = SOME x /\
    eval_operand ops.iao_ofst at.po_state = SOME y /\
    MEM (w2n x,len) (source_memory_write_ranges a.po_inst a.po_state) /\
    ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {}
      (SOME x) (SOME y) /\ 0 < len ==>
    (x = y /\ (w2n x+len <= lo \/ dyn_floor C a.po_state <= w2n x)) \/
    (?token aid b sz pa. MEM token tokens /\
      FLOOKUP births (token,aid) = SOME (b,sz) /\
      FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
      b <= w2n x /\ w2n x+len <= b+sz /\ w2n y = pa + (w2n x-b))` by
    (rpt gen_tac >> strip_tac >>
     `(x = y /\ (w2n x+len <= lo \/ dyn_floor C vs <= w2n x) /\
       op_prov TG ops.iao_ofst = NONE) \/
      (?v token aid b sz pa. ops.iao_ofst = Var v /\ FLOOKUP TG v = SOME (token,aid) /\
        FLOOKUP births (token,aid) = SOME (b,sz) /\
        FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
        b <= w2n x /\ w2n x+len <= b+sz /\ w2n y = pa + (w2n x-b))` suffices_by
       (DISCH_THEN (DISJ_CASES_THEN2 assume_tac strip_assume_tac)
        >- (disj1_tac >> gvs[]) >>
        drule_all ptr_source_ownership_live_prov >> strip_tac >>
        disj2_tac >> qexistsl [`token`,`aid`,`b`,`sz`,`pa`] >> simp[]) >>
     irule ptr_cut_range_geometry >> metis_tac[]) >>
  Cases_on `a.po_inst.inst_opcode = EXTCODECOPY`
  >- (`EVERY (\f. fn_inst_wf f /\ opaque_use_ok f /\
          EVERY bb_well_formed f.fn_blocks /\ ALL_DISTINCT (fn_labels f) /\
          (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
            IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions` by
        (fs[EVERY_MEM] >> metis_tac[]) >>
      drule_all ptr_focus_extcodecopy_step >> strip_tac >> goal_assum (drule_at Any)) >>
  `a.po_inst.inst_opcode <> ASSIGN` by fs[MEM] >>
  `fixed_region_reserved lo C` by fs[o1_ptr_safe_upto_def] >>
  `vs.vs_allocas = FEMPTY` by fs[o1_initial_state_ok_def] >>
  `!ops x y len j.
    mem_read_ops a.po_inst = SOME ops /\ MEM ops.iao_ofst a.po_inst.inst_operands /\
    eval_operand ops.iao_ofst a.po_state = SOME x /\
    eval_operand ops.iao_ofst at.po_state = SOME y /\
    MEM (w2n x,len) (source_memory_read_ranges a.po_inst a.po_state) /\
    ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {}
      (SOME x) (SOME y) /\ j < len /\ w2n x+j NOTIN a.po_taint.t_mem ==>
    read_byte (w2n x+j) a.po_state.vs_memory =
    read_byte (w2n y+j) at.po_state.vs_memory` by
    (rpt gen_tac >> strip_tac >> drule_all focus_cut_paired_read_bytes_ptr_safe >> simp[]) >>
  Cases_on `MEM a.po_inst.inst_opcode [MLOAD; ILOAD]`
  >- (`opaque_use_ok a.po_fn` by (fs[EVERY_MEM] >> metis_tac[]) >>
      `EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands` by
        (irule ptr_nonopaque_instruction_operands >> fs[MEM]) >>
      `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
          a.po_state at.po_state /\ a.po_state.vs_labels = at.po_state.vs_labels` by
        (drule ptr_paired_prefix_endpoint >> strip_tac >>
         fs[ptr_paired_sample_def] >> metis_tac[ptr_history_content_labels]) >>
      `!op x y k. a.po_inst.inst_operands = [op] /\
         eval_operand op a.po_state = SOME x /\ eval_operand op at.po_state = SOME y /\
         k < 32 /\ w2n x+k NOTIN a.po_taint.t_mem ==>
         read_byte (w2n x+k) a.po_state.vs_memory =
         read_byte (w2n y+k) at.po_state.vs_memory` by
        (rpt gen_tac >> strip_tac >>
         `op_taint a.po_taint op = {}` by
           (qpat_assum `taint_ok _ _ _ _` (mp_tac o REWRITE_RULE [taint_ok_def]) >>
            fs[MEM] >> metis_tac[]) >>
         `ptr_lookup_transport births positions (op_prov TG op) {} (SOME x) (SOME y)` by
           (drule ptr_mixed_vars_eval >> disch_then (qspec_then `op` mp_tac) >> fs[]) >>
         first_x_assum irule >> simp[] >>
         fs[MEM] >> gvs[mem_read_ops_def, source_memory_read_ranges_def]) >>
      drule_all ptr_focus_load_step >> strip_tac >> goal_assum (drule_at Any)) >>
  `ptr_use_ok P (fn_pv P a.po_fn) a.po_inst /\ FDOM TG SUBSET fn_pv P a.po_fn` by
    (drule_all ptr_focus_source_tagged_support >> strip_tac >>
     conj_tac >- (fs[EVERY_MEM, fn_ptr_ok_def] >> metis_tac[]) >>
     fs[ptr_static_support_def, SUBSET_DEF, FLOOKUP_DEF, AllCaseEqs()] >> metis_tac[]) >>
  Cases_on `MEM a.po_inst.inst_opcode [SLOAD; TLOAD; SSTORE; TSTORE]`
  >- (drule_all ptr_focus_storage_step >> strip_tac >> goal_assum (drule_at Any)) >>
  `!ai. MEM ai (fn_insts a.po_fn) /\ ai.inst_opcode = ALLOCA ==>
          ?p. FLOOKUP (lp a.po_fn) (Allocation ai.inst_id) = SOME p` by
    (qpat_assum `EVERY (\f. fn_inst_wf f /\ retpc_shape_ok f /\ _) C.ctx_functions`
       (qspec_then `a.po_fn` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     simp[optionTheory.IS_SOME_EXISTS]) >>
  `!ops x y len.
    mem_read_ops a.po_inst = SOME ops /\ inst_read_op a.po_inst = SOME ops.iao_ofst /\
    MEM ops.iao_ofst a.po_inst.inst_operands /\
    eval_operand ops.iao_ofst a.po_state = SOME x /\
    eval_operand ops.iao_ofst at.po_state = SOME y /\
    MEM (w2n x,len) (source_memory_read_ranges a.po_inst a.po_state) /\
    ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {} (SOME x) (SOME y) ==>
    !j. j < len /\ w2n x+j NOTIN a.po_taint.t_mem ==>
    read_byte (w2n x+j) a.po_state.vs_memory =
    read_byte (w2n y+j) at.po_state.vs_memory` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >> qexists `len` >> simp[]) >>
  Cases_on `MEM a.po_inst.inst_opcode [SHA3; LOG]`
  >- (drule_all ptr_focus_hash_log_step >> strip_tac >> goal_assum (drule_at Any)) >>
  Cases_on `a.po_inst.inst_opcode = DELEGATECALL`
  >- (drule_all ptr_focus_delegate_step >> strip_tac >> goal_assum (drule_at Any)) >>
  `!ops x y len j.
    mem_read_ops a.po_inst = SOME ops /\
    eval_operand ops.iao_ofst a.po_state = SOME x /\
    eval_operand ops.iao_ofst at.po_state = SOME y /\
    MEM (w2n x,len) (source_memory_read_ranges a.po_inst a.po_state) /\
    ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {}
      (SOME x) (SOME y) /\ j < len /\ w2n x+j NOTIN a.po_taint.t_mem ==>
    read_byte (w2n x+j) a.po_state.vs_memory =
    read_byte (w2n y+j) at.po_state.vs_memory` by
    (rpt gen_tac >> strip_tac >>
     `MEM ops.iao_ofst a.po_inst.inst_operands` by
       metis_tac[lowerDloadDescriptorObservationTheory.ld_descriptor_offset_operand] >>
     qpat_assum `!ops x y len j. mem_read_ops _ = _ /\ MEM _ _ /\ _ ==> _` irule >>
     simp[] >> qexists `len` >> simp[]) >>
  Cases_on `MEM a.po_inst.inst_opcode [CREATE; CREATE2]`
  >- (drule_all ptr_focus_creation_step >> strip_tac >> goal_assum (drule_at Any)) >>
  Cases_on `MEM a.po_inst.inst_opcode [CALL; STATICCALL]`
  >- (`EVERY (\f. fn_inst_wf f /\ opaque_use_ok f /\ ssa_form f /\
          EVERY bb_well_formed f.fn_blocks /\ ALL_DISTINCT (fn_labels f) /\
          (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
            IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions` by
        (fs[EVERY_MEM] >> metis_tac[]) >>
      drule_all ptr_focus_call_step >> strip_tac >> goal_assum (drule_at Any)) >>
  Cases_on `a.po_inst.inst_opcode = MCOPY`
  >- (`active_inst a.po_fn a.po_inst a.po_state` by
        (drule ptr_owner_frame_active >> simp[]) >>
      `inst_wf a.po_inst /\ fn_ptr_ok P a.po_fn /\ opaque_use_ok a.po_fn /\
       EVERY bb_well_formed a.po_fn.fn_blocks /\ ALL_DISTINCT (fn_labels a.po_fn) /\
       (!ai. MEM ai (fn_insts a.po_fn) /\ ai.inst_opcode = ALLOCA ==>
             IS_SOME (FLOOKUP (lp a.po_fn) (Allocation ai.inst_id)))` by
        (fs[EVERY_MEM, optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
      `ALL_DISTINCT (fn_labels at.po_fn)` by
        (drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def] >>
         strip_tac >> drule ptr_frame_context_membership >> fs[EVERY_MEM]) >>
      `EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands` by
        (irule ptr_nonopaque_instruction_operands >> fs[MEM]) >>
      drule_all ptr_focus_source_tagged_support >> strip_tac >>
      `!dop sop nop r rt m j.
        a.po_inst.inst_operands = [dop;sop;nop] /\
        eval_operand sop a.po_state = SOME r /\ eval_operand sop at.po_state = SOME rt /\
        eval_operand nop a.po_state = SOME m /\
        MEM (w2n r,w2n m) (source_memory_read_ranges a.po_inst a.po_state) /\
        ptr_lookup_transport births positions (op_prov TG sop) {} (SOME r) (SOME rt) /\
        j < w2n m /\ w2n r+j NOTIN a.po_taint.t_mem ==>
        read_byte (w2n r+j) a.po_state.vs_memory = read_byte (w2n rt+j) at.po_state.vs_memory` by
        (rpt gen_tac >> strip_tac >> first_x_assum irule >>
         simp[] >> conj_tac >- (qexists `w2n m` >> simp[]) >>
         qexists `<|iao_ofst := sop; iao_size := SOME nop; iao_max_size := SOME nop|>` >>
         simp[mem_read_ops_def]) >>
      `ptr_ledger_erases (dyn_floor C a.po_state) births TG a.po_prov` by simp[] >>
      drule_all ptr_focus_mcopy_step >> strip_tac >> goal_assum (drule_at Any)) >>
  rpt (qpat_x_assum `~MEM a.po_inst.inst_opcode _` mp_tac) >>
  rpt (qpat_x_assum `a.po_inst.inst_opcode <> _` mp_tac) >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  Cases_on `a.po_inst.inst_opcode` >> simp[MEM]
QED

Finalise focus_concretize_cut_coverage_ptr_safe

(* Read/write ranges at the paired endpoint: unchanged scalars stay in
   their original region, and relocated ranges stay within their slot. *)
Theorem ptr_cut_paired_range_bound[local]:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\ inst_wf inst /\
  opaque_use_ok fn /\ label_positions_ok inst /\
  ptr_ledger_erases (dyn_floor C vs) births TG G /\ FDOM G SUBSET fn_pv P fn /\
  ptr_mixed_vars births positions TG tn fn ft src tgt /\
  src.vs_labels = tgt.vs_labels /\ taint_ok fn tn inst src /\
  access_ok lo G fn inst src /\ ~in_revert_forward fn src /\
  lo <= eom /\
  (!aid pa sz. FLOOKUP positions (Allocation aid) = SOME (pa,sz) ==>
     pa + sz < dimword (:256) /\ pa + sz <= eom) /\
  src.vs_initial_fmp = tgt.vs_initial_fmp /\ src.vs_fmp = tgt.vs_fmp /\
  raw_mem_ok C fn inst src /\
  src.vs_alloca_next + 32 * ctx_dload_count C <= dyn_floor C vs ==>
  !off len.
    MEM (off,len) (source_memory_read_ranges inst tgt ++
                    source_memory_write_ranges inst tgt) ==>
    len = 0 \/ off + len <= eom \/
    (w2n tgt.vs_initial_fmp <= off /\ off + len <= w2n tgt.vs_fmp)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac >> strip_tac >>
  Cases_on `len = 0` >- simp[] >>
  Q.SUBGOAL_THEN `?mops ranges_s ranges_t.
     ((mops = mem_read_ops inst /\
       ranges_s = source_memory_read_ranges inst src /\
       ranges_t = source_memory_read_ranges inst tgt) \/
      (mops = mem_write_ops inst /\
       ranges_s = source_memory_write_ranges inst src /\
       ranges_t = source_memory_write_ranges inst tgt)) /\
     MEM (off,len) ranges_t`
    (qx_choose_then `mops` (qx_choose_then `ranges_s`
      (qx_choose_then `ranges_t` (map_every assume_tac o CONJUNCTS))))
  >- metis_tac[MEM_APPEND] >>
  drule_all ptr_current_range_transport >>
  disch_then (qx_choose_then `off_s` strip_assume_tac)
  >- (Q.SUBGOAL_THEN
        `((ranges_s = source_memory_read_ranges inst src /\ mops = mem_read_ops inst) \/
          (ranges_s = source_memory_write_ranges inst src /\ mops = mem_write_ops inst))`
        assume_tac >- metis_tac[] >>
      drule_all ptr_access_range_classification >> simp[] >> strip_tac >- decide_tac >>
      fs[op_prov_def] >> metis_tac[]) >>
  Q.SUBGOAL_THEN
    `((ranges_s = source_memory_read_ranges inst src /\ mops = mem_read_ops inst) \/
      (ranges_s = source_memory_write_ranges inst src /\ mops = mem_write_ops inst))`
    assume_tac >- metis_tac[] >>
  `0 < len` by decide_tac >>
  `MEM (w2n x,len) ranges_s` by gvs[] >>
  `!aid pa sz. FLOOKUP positions (Allocation aid) = SOME (pa,sz) ==>
      pa + sz < dimword (:256)` by metis_tac[] >>
  drule_all ptr_cut_range_geometry >> strip_tac
  >- (qpat_x_assum `x = y` SUBST_ALL_TAC >> simp[] >> decide_tac)
  >- (qpat_x_assum `x = y` SUBST_ALL_TAC >>
      `inst_mem_below_frontiers inst src` by
        (fs[raw_mem_ok_def, inst_mem_ok_in_fn_def, in_revert_forward_def] >> metis_tac[]) >>
      `MEM (w2n y,len) (inst_mem_ranges inst src)` by
        (simp[inst_mem_ranges_def, MEM_APPEND] >> metis_tac[]) >>
      qpat_x_assum `inst_mem_below_frontiers _ _` mp_tac >>
      rewrite_tac[inst_mem_below_frontiers_def, EVERY_MEM] >>
      disch_then (qspec_then `(w2n y,len)` mp_tac) >>
      gvs[inst_mem_ranges_def]) >>
  `pa + sz <= eom` by metis_tac[] >> gvs[] >> decide_tac
QED

Theorem ptr_cut_paired_static_mem_cut_headroom[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_initial_state_ok vs /\
  vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  o1_ptr_safe_upto D lo n C vs /\
  mem_inv (\ctx fn inst s. gas_cut n vs s ==> dload_headroom_ok ctx fn inst s) C vs /\
  (!fn inst s. raw_reachable vs C fn inst s /\ gas_cut n vs s ==>
    raw_mem_ok C fn inst s /\ dload_offset_ok C fn inst s) /\ callee_first names C.ctx_functions /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  max_live_eom C' = SOME eom /\ ptr_stage_placements C' positions /\
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode <> NOP /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  gas_cut n vs at.po_state ==>
  static_mem_ok eom C' at.po_fn at.po_inst at.po_state
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ptr_discipline_upto lo n C vs /\ fixed_region_reserved lo C /\
   EVERY (\f. f.fn_eom = NONE) C.ctx_functions` by fs[o1_ptr_safe_upto_def] >>
  drule_all ptr_paired_endpoint_cut_safety >> strip_tac >>
  `raw_reachable vs C a.po_fn a.po_inst a.po_state` by
    (drule_all lowerDloadPtrRawReachableTheory.frame_reachable_raw >> simp[]) >>
  `raw_mem_ok C a.po_fn a.po_inst a.po_state` by metis_tac[] >>
  Q.SUBGOAL_THEN `?Q. EVERY (fn_ptr_ok Q) C.ctx_functions` assume_tac
  >- (qexists `P` >> simp[]) >>
  drule_all ptr_focus_paired_static_fields >> strip_tac >>
  simp[static_mem_ok_def] >>
  Cases_on `in_revert_forward a.po_fn a.po_state`
  >- (drule_all ptr_paired_prefix_forwarding_static >> simp[]) >>
  disj2_tac >>
  Cases_on `a.po_inst.inst_opcode = ALLOCA`
  >- (gvs[concretize_inst_with_positions_def, AllCaseEqs()] >>
      qpat_x_assum `_ = at.po_inst`
        (mp_tac o AP_TERM ``\i:instruction. i.inst_opcode``) >>
      simp[passSharedDefsTheory.mk_nop_inst_def, passSharedDefsTheory.mk_assign_inst_def] >> strip_tac >>
      simp[inst_mem_ranges_def, source_memory_read_ranges_def,
           source_memory_write_ranges_def]) >>
  suspend "kept_range"
QED

Resume ptr_cut_paired_static_mem_cut_headroom[kept_range]:
  `at.po_inst = a.po_inst` by metis_tac[concretize_positions_unchanged] >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
     a.po_state at.po_state /\ a.po_state.vs_labels = at.po_state.vs_labels /\
   a.po_state.vs_initial_fmp = at.po_state.vs_initial_fmp /\
   a.po_state.vs_fmp = at.po_state.vs_fmp` by
    (fs[ptr_paired_sample_def] >>
     drule ptr_history_content_control >>
     simp[concretizePtrTaintContentTheory.ptr_taint_control_def,
          ptr_core_shared_def, concretizePtrSharedFieldsTheory.ptr_shared_fields_def] >>
     metis_tac[ptr_history_content_labels]) >>
  `ptr_source_ownership vs C h a tokens registry births PT TG saved` by
    (drule ptr_paired_prefix_transcript >> strip_tac >>
     drule ptr_structural_transcript_erasure >> strip_tac >>
     drule ptr_structural_trace_ownership >> simp[]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >> metis_tac[ptr_fn_inst_wf_flat, EVERY_MEM]) >>
  drule_all ptr_frame_current_static >> strip_tac >>
  `FDOM a.po_prov SUBSET fn_pv P a.po_fn` by
    (fs[ptr_static_support_def, SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[optionTheory.NOT_NONE_SOME]) >>
  `active_inst a.po_fn a.po_inst a.po_state` by (drule ptr_owner_frame_active >> simp[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, unitLabelMapIdentityTheory.fn_insts_MEM] >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM, MEM_EL]) >>
  `fn_ptr_ok P a.po_fn /\ inst_wf a.po_inst /\ opaque_use_ok a.po_fn /\
   label_positions_ok a.po_inst` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, inst_shape_ok_def, EVERY_MEM] >>
     metis_tac[]) >>
  drule_all ptr_source_ownership_erases_upto >> strip_tac >>
  `lo <= eom` by (drule_all ptr_stage_fixed_region_bound >> simp[]) >>
  `a.po_state.vs_alloca_next + 32 * ctx_dload_count C <= dyn_floor C vs` by
    (`dload_headroom_ok C a.po_fn a.po_inst a.po_state` by
       (qpat_x_assum `mem_inv _ C vs` mp_tac >>
        rewrite_tac[mem_inv_raw_reachable] >>
        disch_then (mp_tac o CONJUNCT2) >>
        disch_then (qspecl_then [`a.po_fn`, `a.po_inst`, `a.po_state`] mp_tac) >>
        simp[]) >>
     drule ctxLookupAgreeTheory.raw_reachable_initial_fmp >>
     disch_then (fn initial_fmp =>
       qpat_x_assum `dload_headroom_ok C _ _ _`
         (mp_tac o REWRITE_RULE [lowerDloadDefsTheory.dload_headroom_ok_def,
           GSYM ctx_has_dalloca_def, initial_fmp])) >>
     Cases_on `ctx_has_dalloca C` >> simp[dyn_floor_def] >> decide_tac) >>
  `!aid pa sz. FLOOKUP positions (Allocation aid) = SOME (pa,sz) ==>
     pa + sz < dimword (:256) /\ pa + sz <= eom` by
    (rpt strip_tac >>
     drule_all ptr_stage_placements_strict_bound >>
     drule_all ptr_stage_placements_endpoint_bound >> simp[]) >>
  `concretize_inst_with_positions (lp a.po_fn) a.po_inst = a.po_inst` by
    metis_tac[concretize_positions_unchanged] >>
  qpat_assum `concretize_inst_with_positions _ a.po_inst = a.po_inst`
    (pure_once_rewrite_tac o single) >>
  rewrite_tac[inst_mem_ranges_def, EVERY_MEM] >>
  Cases >> disch_tac >>
  drule_all ptr_cut_paired_range_bound >> simp[arithmeticTheory.ADD_COMM]
QED

Finalise ptr_cut_paired_static_mem_cut_headroom

(* The final REVERT is exempt from the range check. The strict interior
   consists solely of ASSIGNs and hence has no memory ranges. *)
Theorem ptr_cut_window_static_mem[local]:
  ptr_chrono_history vs C h at /\
  EVERY (\g. ALL_DISTINCT (fn_labels g)) C.ctx_functions /\
  w2n at.po_state.vs_initial_fmp <= w2n at.po_state.vs_fmp /\
  lookup_block at.po_state.vs_current_bb at.po_fn.fn_blocks = SOME bb /\
  revert_forward_pair bb i j /\
  i < at.po_state.vs_inst_idx /\ at.po_state.vs_inst_idx <= j ==>
  static_mem_ok eom C at.po_fn at.po_inst at.po_state
Proof
  strip_tac >>
  drule ptr_chrono_history_reachable >>
  simp[ptr_observation_reachable_def] >> strip_tac >>
  drule ptr_frame_context_membership >> strip_tac >>
  `ALL_DISTINCT (fn_labels at.po_fn)` by fs[EVERY_MEM] >>
  drule ptr_owner_frame_active >> strip_tac >>
  drule_all lowerDloadPtrRawReachableTheory.active_inst_block_lookup >> strip_tac >>
  `get_instruction bb at.po_state.vs_inst_idx = SOME at.po_inst` by gvs[] >>
  `i <= at.po_state.vs_inst_idx` by decide_tac >>
  drule_all lowerDloadPtrForwardTheory.revert_forward_pair_interval_opcode >> strip_tac
  >- decide_tac
  >- simp[static_mem_ok_def, unitTransformDefsTheory.dalloca_no_wrap_def,
          inst_mem_ranges_def, source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  `bb' = bb` by metis_tac[optionTheory.SOME_11] >>
  gvs[static_mem_ok_def, unitTransformDefsTheory.dalloca_no_wrap_def,
      in_revert_forward_def, revert_forward_at_def] >>
  disj1_tac >> qexists `i` >> simp[]
QED

Theorem focus_concretize_cut_fields_cut_headroom:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_initial_state_ok vs /\
  vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  o1_ptr_safe_upto D lo n C vs /\
  mem_inv (\ctx fn inst s. gas_cut n vs s ==> dload_headroom_ok ctx fn inst s) C vs /\
  (!fn inst s. raw_reachable vs C fn inst s /\ gas_cut n vs s ==>
    raw_mem_ok C fn inst s /\ dload_offset_ok C fn inst s) /\
  alloca_frontier_upto n C vs /\
  EVERY ssa_form C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  max_live_eom C' = SOME eom /\
  (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) ==>
  mem_inv (\ctx fn inst s. gas_cut n vs s ==> static_mem_ok eom ctx fn inst s) C' vs /\
  ?R lp positions.
    ptr_stage_placements C' positions /\
    !ht at. ptr_chrono_history vs C' ht at /\ gas_cut n vs at.po_state ==>
      w2n at.po_state.vs_initial_fmp <= w2n at.po_state.vs_fmp /\
      dalloca_no_wrap at.po_inst at.po_state /\
      ((?h a done tokens registry births PT TG saved entries H calls ws.
        ptr_paired_prefix R lp positions lo vs C C'
          h a ht at done tokens registry births PT TG saved entries H calls ws /\
        EVERY (\i. ~in_revert_forward (EL i h).po_fn (EL i h).po_state) done /\
        a.po_inst.inst_opcode <> NOP /\
        at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
        frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
          a.po_fn a.po_inst a.po_state /\
        gas_cut n vs a.po_state /\
        access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
        taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
        allocas_from lo a.po_state /\
        (ctx_has_dalloca C ==> allocas_below_fmp a.po_state)) \/
       (?bb i j. lookup_block at.po_state.vs_current_bb at.po_fn.fn_blocks = SOME bb /\
        revert_forward_pair bb i j /\
        i < at.po_state.vs_inst_idx /\ at.po_state.vs_inst_idx <= j))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all focus_concretize_cut_coverage_ptr_safe >> strip_tac >>
  `ptr_discipline_upto lo n C vs` by fs[o1_ptr_safe_upto_def] >>
  drule ptr_discipline_upto_fn_ptr_ok >> strip_tac >>
  drule_all concretize_cut_stage_pairing >> strip_tac >>
  suspend "historical"
QED

Resume focus_concretize_cut_fields_cut_headroom[historical]:
  `!ht at. ptr_chrono_history vs C' ht at /\ gas_cut n vs at.po_state ==>
     static_mem_ok eom C' at.po_fn at.po_inst at.po_state \/
     ?bb i j. lookup_block at.po_state.vs_current_bb at.po_fn.fn_blocks = SOME bb /\
       revert_forward_pair bb i j /\
       i < at.po_state.vs_inst_idx /\ at.po_state.vs_inst_idx <= j` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!ht at. ptr_chrono_history _ _ ht at ==> _`
       (drule_then (drule_then strip_assume_tac))
     >- (disj1_tac >> drule_all ptr_cut_paired_static_mem_cut_headroom >> simp[]) >>
     disj2_tac >> metis_tac[]) >>
  `!ht at. ptr_chrono_history vs C' ht at /\ gas_cut n vs at.po_state ==>
     w2n at.po_state.vs_initial_fmp <= w2n at.po_state.vs_fmp` by
    (rpt gen_tac >> strip_tac >>
     drule ptr_focus_coverage_history_fmp >> disch_then irule >> simp[] >>
     qexists `n` >> simp[] >> rpt gen_tac >> strip_tac >>
     qpat_assum `!ht at. _ ==> static_mem_ok _ _ _ _ _ \/ _`
       (drule_all_then strip_assume_tac)
     >- (disj1_tac >> fs[static_mem_ok_def]) >> disj2_tac >> metis_tac[]) >>
  `!ht at. ptr_chrono_history vs C' ht at /\ gas_cut n vs at.po_state ==>
     static_mem_ok eom C' at.po_fn at.po_inst at.po_state` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!ht at. _ ==> _ <= _` (drule_all_then assume_tac) >>
     qpat_assum `!ht at. _ ==> static_mem_ok _ _ _ _ _ \/ _`
       (drule_all_then strip_assume_tac) >>
     drule_all ptr_cut_window_static_mem >> simp[]) >>
  conj_tac >- suspend "mem_inv" >>
  suspend "point"
QED

Resume focus_concretize_cut_fields_cut_headroom[mem_inv]:
  rewrite_tac[mem_inv_raw_reachable] >> conj_tac
  >- (qpat_x_assum `mem_inv (\ctx fn inst s. gas_cut n vs s ==> dload_headroom_ok ctx fn inst s) C vs` mp_tac >>
      rewrite_tac[mem_inv_raw_reachable] >> strip_tac >>
      `C'.ctx_entry = C.ctx_entry` by fs[ctx_pass_stage_def] >>
      simp[] >> drule_all o1PassLiftTheory.list_rel_lookup_function >>
      disch_then (qspec_then `name` mp_tac) >> simp[] >>
      Cases_on `lookup_function name C'.ctx_functions` >> simp[] >>
      strip_tac >> fs[ptr_paired_code_def] >> metis_tac[]) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  drule ptr_raw_reachable_frame >> strip_tac >>
  drule ptr_reachable_has_chrono_history >> strip_tac >>
  qpat_assum `!ht at. _ ==> static_mem_ok _ _ _ _ _`
    (drule_then mp_tac o REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  simp[ptr_observe_def]
QED

Resume focus_concretize_cut_fields_cut_headroom[point]:
  qexistsl [`R`, `lp`, `positions`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!ht at. _ ==> static_mem_ok _ _ _ _ _` (drule_all_then assume_tac) >>
  `w2n at.po_state.vs_initial_fmp <= w2n at.po_state.vs_fmp /\
   dalloca_no_wrap at.po_inst at.po_state` by fs[static_mem_ok_def] >> simp[] >>
  qpat_assum `!ht at. ptr_chrono_history _ _ ht at ==> _`
    (drule_then (drule_then strip_assume_tac))
  >- (disj1_tac >>
      drule_all ptr_paired_endpoint_cut_safety >> strip_tac >>
      qpat_assum `ptr_paired_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
        (irule_at Any) >> simp[]) >>
  disj2_tac >> metis_tac[]
QED

Finalise focus_concretize_cut_fields_cut_headroom

Theorem focus_concretize_cut_fields:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_initial_state_ok vs /\
  vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  o1_safe_upto D lo n C vs /\ alloca_frontier_upto n C vs /\
  EVERY ssa_form C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  max_live_eom C' = SOME eom /\
  (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) ==>
  mem_inv (\ctx fn inst s. gas_cut n vs s ==> static_mem_ok eom ctx fn inst s) C' vs /\
  ?R lp positions.
    ptr_stage_placements C' positions /\
    !ht at. ptr_chrono_history vs C' ht at /\ gas_cut n vs at.po_state ==>
      w2n at.po_state.vs_initial_fmp <= w2n at.po_state.vs_fmp /\
      dalloca_no_wrap at.po_inst at.po_state /\
      ((?h a done tokens registry births PT TG saved entries H calls ws.
        ptr_paired_prefix R lp positions lo vs C C'
          h a ht at done tokens registry births PT TG saved entries H calls ws /\
        EVERY (\i. ~in_revert_forward (EL i h).po_fn (EL i h).po_state) done /\
        a.po_inst.inst_opcode <> NOP /\
        at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
        frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
          a.po_fn a.po_inst a.po_state /\
        gas_cut n vs a.po_state /\
        access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
        taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
        allocas_from lo a.po_state /\
        (ctx_has_dalloca C ==> allocas_below_fmp a.po_state)) \/
       (?bb i j. lookup_block at.po_state.vs_current_bb at.po_fn.fn_blocks = SOME bb /\
        revert_forward_pair bb i j /\
        i < at.po_state.vs_inst_idx /\ at.po_state.vs_inst_idx <= j))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  fs[o1_safe_upto_def] >>
  `mem_inv (\ctx fn inst s. gas_cut n vs s ==> dload_headroom_ok ctx fn inst s) C vs` by fs[mem_inv_raw_reachable] >>
  mp_tac focus_concretize_cut_fields_cut_headroom >> simp[]
QED
