Theory gasFocusConcretizeCutCoverage
Ancestors
  concretizePtrStagePairedBridge concretizePtrStagePlacements
  concretizePtrImportOrigins concretizePtrPairedFields
  concretizeStageShape concretizeStepStructure
  o1PassContract venomWf venomInst unitShapeDefs concretizeMemLocDefs
  venomPassDispatcher
  gasFocusConcretizeEndpointCut gasFocusChronologicalCut
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

(* Source observations already traversed by a paired prefix are still in
   the cut: the remaining readings can only decrease along the history. *)
Theorem concretize_paired_history_safety[local]:
  ptr_paired_prefix R lp positions lo vs C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_discipline_upto lo n C vs /\ gas_cut n vs at.po_state ==>
  !obs. MEM obs h ==>
    access_ok lo obs.po_prov obs.po_fn obs.po_inst obs.po_state /\
    taint_ok obs.po_fn obs.po_taint obs.po_inst obs.po_state /\
    allocas_from lo obs.po_state /\
    (ctx_has_dalloca C ==> allocas_below_fmp obs.po_state)
Proof
  strip_tac >>
  drule_all ptr_paired_endpoint_cut_safety >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule_all ptr_chrono_history_cut >> simp[EVERY_MEM] >> strip_tac >>
  drule ptr_chrono_history_reachable >>
  simp[EVERY_MEM, ptr_observation_reachable_def] >> strip_tac >>
  rpt strip_tac >>
  qpat_assum `!b. MEM b h ==> gas_cut _ _ _` (drule_then assume_tac) >>
  qpat_assum `!x. MEM x h ==> frame_reachable _ _ _ _ _ _ _ _ _`
    (drule_then assume_tac) >>
  drule_all ptr_discipline_upto_at >> simp[]
QED

(* Project the actual paired event before querying safety at its source sample. *)
Theorem ptr_paired_historical_event_upto[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  o1_ctx_shape C /\ ptr_discipline_upto lo n C vs /\ gas_cut n vs at.po_state /\
  q < LENGTH done ==>
  ?tsj rj bj PTj TGj sj ej next.
    EL (EL q done) H = (tsj,rj,bj,PTj,TGj,sj,ej) /\
    next = EL (SUC (EL q done)) H /\
    SUC (EL q done) < LENGTH h /\ SUC q < LENGTH ht /\
    ptr_structural_transcript R vs C C' h endpoint ht at done tokens registry
      births PT TG saved entries H /\ ptr_stage_placements C' positions /\
    ptr_snapshot_step C (TAKE (SUC (EL q done)) h)
      (EL (EL q done) h) (EL (SUC (EL q done)) h)
      (tsj,rj,bj,PTj,TGj,sj,ej) next /\
    ptr_mixed_vars bj positions TGj (EL (EL q done) h).po_taint
      (EL (EL q done) h).po_fn (EL q ht).po_fn
      (EL (EL q done) h).po_state (EL q ht).po_state /\
    ptr_history_content (EL (EL q done) h).po_taint
      (EL (EL q done) h).po_state (EL q ht).po_state /\
    ptr_observation_reachable vs C (EL (EL q done) h) /\
    gas_cut n vs endpoint.po_state /\ gas_cut n vs (EL (EL q done) h).po_state /\
    access_ok lo (EL (EL q done) h).po_prov (EL (EL q done) h).po_fn
      (EL (EL q done) h).po_inst (EL (EL q done) h).po_state /\
    taint_ok (EL (EL q done) h).po_fn (EL (EL q done) h).po_taint
      (EL (EL q done) h).po_inst (EL (EL q done) h).po_state /\
    (EL q ht).po_inst = concretize_inst_with_positions
      (lp (EL (EL q done) h).po_fn) (EL (EL q done) h).po_inst
Proof
  strip_tac >>
  drule_all ptr_paired_endpoint_cut_safety >> strip_tac >>
  drule ptr_paired_prefix_memory >> strip_tac >>
  drule ptr_paired_memory_samples >> strip_tac >>
  `q < LENGTH ht` by fs[ptr_paired_samples_def, ptr_sample_list_def] >>
  drule_all ptr_paired_memory_alignment >> strip_tac >>
  drule ptr_paired_memory_transcript >> strip_tac >>
  drule ptr_paired_memory_placements >> strip_tac >>
  `SUC q < LENGTH ht` by fs[ptr_paired_samples_def, ptr_sample_list_def] >>
  `EL q (done ++ [LENGTH h - 1]) = EL q done` by simp[EL_APPEND_EQN] >>
  gvs[] >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_nop_interval >>
  disch_then (qspec_then `q` mp_tac) >> simp[] >> strip_tac >>
  `SUC (EL q done) < LENGTH h` by decide_tac >>
  drule ptr_structural_transcript_adjacent >>
  disch_then (qspec_then `EL q done` mp_tac) >> simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `ptr_snapshot_step C pre aa bb snapshot snapshot'` >>
  PairCases_on `snapshot` >> PairCases_on `snapshot'` >>
  gvs[ptr_snapshot_step_def] >>
  `ptr_mixed_vars snapshot2 positions snapshot4 aa.po_taint aa.po_fn
      (EL q ht).po_fn aa.po_state (EL q ht).po_state` by
    (qpat_assum `ptr_paired_samples _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ptr_paired_samples_def, ptr_sample_list_def] >> strip_tac >>
     qpat_x_assum `!j. j < LENGTH ht ==> _` (qspec_then `q` mp_tac) >>
     simp[ptr_paired_sample_def, Abbr `aa`]) >>
  `ptr_history_content aa.po_taint aa.po_state (EL q ht).po_state` by
    (drule ptr_paired_samples_history >>
     disch_then (qspec_then `q` mp_tac) >> simp[Abbr `aa`]) >>
  drule ptr_structural_trace_source >> strip_tac >>
  `EL q done < LENGTH h` by decide_tac >>
  `ptr_observation_reachable vs C aa` by
    (drule ptr_chrono_history_reachable >> simp[EVERY_EL, Abbr `aa`]) >>
  `gas_cut n vs aa.po_state` by
    (drule_all ptr_chrono_history_cut >> simp[EVERY_EL, Abbr `aa`]) >>
  `access_ok lo aa.po_prov aa.po_fn aa.po_inst aa.po_state /\
   taint_ok aa.po_fn aa.po_taint aa.po_inst aa.po_state` by
    (fs[ptr_observation_reachable_def] >> drule_all ptr_discipline_upto_at >> simp[]) >>
  `aa.po_inst.inst_id = (EL q ht).po_inst.inst_id` by
    (drule ptr_trace_departed_inst_ids >>
     disch_then (qspec_then `q` mp_tac) >> simp[Abbr `aa`]) >>
  `MEM aa.po_fn C.ctx_functions` by
    (fs[ptr_observation_reachable_def] >> drule ptr_frame_context_membership >> simp[]) >>
  `fn_inst_ids_distinct aa.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def,
        EVERY_MEM, wf_function_def] >> metis_tac[]) >>
  `(EL q ht).po_inst = concretize_inst_with_positions (lp aa.po_fn) aa.po_inst` by
    (irule ptr_departed_cursor_instruction >> simp[]) >>
  simp[ptr_snapshot_step_def]
QED

Theorem ptr_erased_tagged_domain[local]:
  ptr_ledger_erases dyn births TG G /\ ptr_static_support P fn G ==>
  !u. u IN FDOM TG ==> u IN fn_pv P fn
Proof
  simp[ptr_ledger_erases_def, ptr_static_support_def] >> rpt strip_tac >>
  `?tag. FLOOKUP TG u = SOME tag` by metis_tac[FLOOKUP_DEF] >>
  `?site. FLOOKUP births tag = SOME site` by metis_tac[FLOOKUP_DEF] >>
  qpat_x_assum `!v. ptr_owner_erases _ _ _ _` (qspec_then `u` mp_tac) >>
  simp[ptr_owner_erases_def] >> metis_tac[]
QED

(* Reflect a target write to the actual source byte, not to the maximum
   requested output range. The alternate arm records the relocated owner. *)
Theorem ptr_paired_actual_write_origin_upto[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\
  code_layout_valid vs /\ EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ptr_discipline_upto lo n C vs /\ gas_cut n vs at.po_state /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  q < LENGTH done /\
  ~in_revert_forward (EL (EL q done) h).po_fn (EL (EL q done) h).po_state /\
  x IN range_bytes (step_writes (EL q ht).po_inst
    (EL q ht).po_state (EL (SUC q) ht).po_state) ==>
  (x IN range_bytes (step_writes (EL (EL q done) h).po_inst
    (EL (EL q done) h).po_state (EL (SUC (EL q done)) h).po_state) /\
   (x < lo \/ dyn_floor C vs <= x)) \/
  (?tsj rj bj PTj TGj sj ej dv tok bid db sb pb.
    EL (EL q done) H = (tsj,rj,bj,PTj,TGj,sj,ej) /\
    inst_write_op (EL (EL q done) h).po_inst = SOME (Var dv) /\
    FLOOKUP TGj dv = SOME (tok,bid) /\
    FLOOKUP (EL (EL q done) h).po_prov dv = SOME (db,sb) /\
    FLOOKUP positions (Allocation bid) = SOME (pb,sb) /\
    pb <= x /\ x < pb+sb /\
    db+(x-pb) IN range_bytes (step_writes (EL (EL q done) h).po_inst
      (EL (EL q done) h).po_state (EL (SUC (EL q done)) h).po_state))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ptr_paired_historical_event_upto >> strip_tac >>
  `(EL q ht).po_inst = (EL (EL q done) h).po_inst` by
    (metis_tac[ptr_dalloca_written_instruction]) >>
  qpat_x_assum `(EL q ht).po_inst = concretize_inst_with_positions _ _` kall_tac >>
  `EL q done < LENGTH h` by decide_tac >>
  drule ptr_structural_transcript_ownership >>
  disch_then (qspec_then `EL q done` mp_tac) >>
  simp[ptr_snapshot_ownership_def] >> strip_tac >>
  `EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions` by
    (pure_once_rewrite_tac[EVERY_MEM] >> qx_gen_tac `f` >> strip_tac >>
     BETA_TAC >> irule ptr_fn_inst_wf_flat >>
     fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
     first_x_assum drule >> simp[]) >>
  drule_all ptr_source_ownership_erases_upto >> strip_tac >>
  drule ptr_discipline_upto_fn_ptr_ok >> strip_tac >>
  fs[ptr_observation_reachable_def] >>
  drule_all ptr_frame_current_static >> strip_tac >>
  drule ptr_frame_operand_instructions >> strip_tac >>
  qmatch_asmsub_abbrev_tac `ptr_mixed_vars bj positions TGj aa.po_taint
    aa.po_fn (EL q ht).po_fn aa.po_state (EL q ht).po_state` >>
  `fn_ptr_ok P aa.po_fn /\ opaque_use_ok aa.po_fn /\ label_positions_ok aa.po_inst` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM,
        inst_shape_ok_def] >> metis_tac[]) >>
  `aa.po_inst.inst_opcode <> DRET` by (fs[fn_ptr_ok_def, EVERY_MEM] >> metis_tac[]) >>
  `aa.po_state.vs_labels = (EL q ht).po_state.vs_labels` by
    (drule ptr_history_content_labels >> simp[]) >>
  `!u. u IN FDOM TGj ==> u IN fn_pv P aa.po_fn` by
    ((metis_tac[ptr_erased_tagged_domain])) >>
  `(EL (SUC (EL q done)) h).po_state.vs_returndata =
      (EL (SUC q) ht).po_state.vs_returndata` by
    (drule ptr_paired_prefix_samples >> strip_tac >>
     drule ptr_structural_transcript_erasure >> strip_tac >>
     drule_all ptr_paired_samples_post_returndata >> simp[]) >>
  gvs[] >> drule_all ptr_ordinary_write_operand_transport >>
  disch_then (qx_choose_then `ops` (qx_choose_then `sizeop`
    (qx_choose_then `dest` (qx_choose_then `z` (qx_choose_then `destt`
      (map_every assume_tac o CONJUNCTS)))))) >>
  unabbrev_all_tac >>
  `EL q done < LENGTH h` by decide_tac >>
  `MEM (EL (EL q done) h).po_inst.inst_opcode [CALL;STATICCALL;DELEGATECALL] ==>
     LENGTH (EL (SUC (EL q done)) h).po_state.vs_returndata =
     LENGTH (EL (SUC q) ht).po_state.vs_returndata` by simp[] >>
  `w2n destt <= x /\ x < w2n destt + w2n z` by
    (drule_all ptr_step_write_max_containment >> simp[]) >>
  drule_all ptr_historical_write_classification_upto >>
  disch_then (DISJ_CASES_THEN2 (MAP_EVERY assume_tac o CONJUNCTS) strip_assume_tac)
  >- (disj1_tac >>
      `destt = dest` by gvs[ptr_lookup_transport_some, ptr_value_transport_scalar_empty] >>
      conj_tac >- (drule_all ptr_write_transport_fixed_exact >> simp[]) >>
      qpat_x_assum `destt = dest` SUBST_ALL_TAC >> decide_tac) >>
  `FLOOKUP bj (token,bid) = SOME (db,sb)` by
    (fs[ptr_ledger_erases_def] >>
     qpat_x_assum `!v. ptr_owner_erases _ _ _ _` (qspec_then `dv` mp_tac) >>
     simp[ptr_owner_erases_def]) >>
  `op_prov TGj ops.iao_ofst = SOME (token,bid)` by simp[op_prov_def] >>
  `destt = dest - n2w db + n2w pb` by
    (gvs[ptr_lookup_transport_some, ptr_value_transport_def]) >>
  `w2n destt = pb + (w2n dest - db)` by
    (irule ptr_closed_relocation_value >> simp[] >>
     qexists `sb` >> simp[] >> decide_tac) >>
  `pb <= x /\ x < pb+sb /\ x-pb < sb /\ pb+(x-pb) = x` by decide_tac >>
  disj2_tac >> qexistsl [`dv`,`token`,`bid`,`db`,`sb`,`pb`] >>
  asm_rewrite_tac[inst_write_op_def] >>
  drule_all ptr_write_transport_owner_exact >>
  simp[]
QED

Theorem ptr_paired_fixed_actual_write_reflection_upto[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\
  code_layout_valid vs /\ EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  fixed_region_reserved lo C /\ ptr_discipline_upto lo n C vs /\ gas_cut n vs at.po_state /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  (x < lo \/ dyn_floor C vs <= x) /\ q < LENGTH done /\
  x IN range_bytes (step_writes (EL q ht).po_inst
    (EL q ht).po_state (EL (SUC q) ht).po_state) ==>
  x IN range_bytes (step_writes (EL (EL q done) h).po_inst
    (EL (EL q done) h).po_state (EL (SUC (EL q done)) h).po_state) \/
  in_revert_forward (EL (EL q done) h).po_fn
    (EL (EL q done) h).po_state
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `in_revert_forward (EL (EL q done) h).po_fn
    (EL (EL q done) h).po_state` >- simp[] >>
  simp[] >> drule_all ptr_paired_actual_write_origin_upto >>
  disch_then (DISJ_CASES_THEN2 (ACCEPT_TAC o CONJUNCT1) strip_assume_tac) >>
  drule ptr_paired_prefix_memory >> strip_tac >>
  drule ptr_paired_memory_placements >> strip_tac >>
  `x - pb < sb /\ pb + (x-pb) = x` by decide_tac >>
  Cases_on `x < lo`
  >- (`lo <= pb + (x-pb)` by
        (irule ptr_stage_placements_reserved_prefix >>
         rpt (goal_assum (drule_at Any)) >> simp[]) >>
      decide_tac) >>
  `dyn_floor C vs <= x` by metis_tac[] >>
  `pb + sb < dimword (:256)` by (drule_all concretizePtrPlacementBoundsTheory.ptr_stage_placements_strict_bound >> simp[]) >>
  `pb + sb <= eom` by
    (irule ptr_stage_placements_endpoint_bound >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  Cases_on `ctx_has_dalloca C` >> fs[dyn_floor_def] >> decide_tac
QED

Theorem ptr_cut_owner_allocas_from[local]:
  ptr_observation_reachable vs C obs /\ ptr_discipline_upto lo n C vs /\
  gas_cut n vs obs.po_state /\ d <= LENGTH obs.po_stack ==>
  allocas_from lo (ptr_owner_view d obs).cf_state
Proof
  strip_tac >> fs[ptr_observation_reachable_def] >>
  Cases_on `d = LENGTH obs.po_stack`
  >- (simp[ptr_owner_view_def] >> metis_tac[ptr_discipline_upto_at]) >>
  drule_all frame_reachable_saved_allocas_from >> strip_tac >>
  `LENGTH obs.po_stack - d - 1 < LENGTH obs.po_stack` by decide_tac >>
  fs[EVERY_EL, ptr_owner_view_def]
QED

(* With no DALLOCA it is enough to bound the active frontier: saved
   allocations lie below it, so the cut need not be queried at saved states. *)
Theorem ptr_cut_owner_below_floor[local]:
  ptr_observation_reachable vs C obs /\ ptr_discipline_upto lo n C vs /\
  gas_cut n vs obs.po_state /\ alloca_frontier_upto n C vs /\
  vs.vs_allocas = FEMPTY /\ d <= LENGTH obs.po_stack /\
  FLOOKUP (ptr_owner_view d obs).cf_state.vs_allocas aid = SOME (b,sz) ==>
  b + sz <= dyn_floor C vs
Proof
  strip_tac >> fs[ptr_observation_reachable_def] >>
  Cases_on `ctx_has_dalloca C` >> simp[dyn_floor_def]
  >- (drule frame_reachable_initial_fmp >> strip_tac >>
      Cases_on `d = LENGTH obs.po_stack`
      >- (`allocas_below_fmp obs.po_state` by metis_tac[ptr_discipline_upto_at] >>
          fs[ptr_owner_view_def, allocas_below_fmp_def] >> metis_tac[]) >>
      drule_all frame_reachable_saved_below_fmp_upto >> strip_tac >>
      qabbrev_tac `j = LENGTH obs.po_stack - d - 1` >>
      `j < LENGTH obs.po_stack` by (simp[Abbr `j`] >> decide_tac) >>
      `allocas_below_fmp (EL j obs.po_stack).cf_state /\
       (EL j obs.po_stack).cf_state.vs_initial_fmp = vs.vs_initial_fmp` by
        fs[EVERY_EL] >>
      fs[ptr_owner_view_def, allocas_below_fmp_def, Abbr `j`] >> metis_tac[]) >>
  drule_all ptr_frame_alloc_geometry >> strip_tac >>
  `obs.po_state.vs_alloca_next < dimword (:256)` by
    metis_tac[alloca_frontier_upto_def] >>
  `b + sz <= obs.po_state.vs_alloca_next` by
    (qabbrev_tac `states = obs.po_state :: MAP (\f. f.cf_state) obs.po_stack` >>
     `?k. k < LENGTH states /\ EL k states = (ptr_owner_view d obs).cf_state` by
       (Cases_on `d = LENGTH obs.po_stack`
        >- (qexists_tac `0` >> simp[Abbr `states`, ptr_owner_view_def]) >>
        `LENGTH obs.po_stack - d - 1 < LENGTH obs.po_stack` by decide_tac >>
        qexists_tac `SUC (LENGTH obs.po_stack - d - 1)` >>
        simp[Abbr `states`, ptr_owner_view_def, EL_MAP]) >>
     `b + sz <= (EL k states).vs_alloca_next` by
       (drule ptr_active_alloc_tables >> simp[EVERY_EL] >>
        disch_then (qspec_then `k` mp_tac) >>
        simp[ptr_alloc_table_ok_def] >> metis_tac[]) >>
     drule_all ptr_active_alloc_frontier >> fs[Abbr `states`] >> gvs[]) >>
  decide_tac
QED

(* At a fixed untainted byte, use the actual last writer, not a maximum
   output range; the retained target suffix cannot write it. *)
Theorem ptr_paired_fixed_read_recovery_upto[local]:
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
  `!j. j < LENGTH h ==> ptr_observation_reachable vs C (EL j h) /\
    gas_cut n vs (EL j h).po_state` by
    (qpat_assum `ptr_chrono_history vs C h endpoint`
       (mp_then Any strip_assume_tac ptr_chrono_history_reachable) >>
     `EVERY (\b. gas_cut n vs b.po_state) h` by
       (irule ptr_chrono_history_cut >> metis_tac[]) >>
     fs[EVERY_EL]) >>
  `(EL w h).po_inst.inst_opcode <> DRET /\
   dyn_floor C (EL w h).po_state = dyn_floor C vs` by
    (`w < LENGTH h` by decide_tac >>
     qpat_assum `!j. j < LENGTH h ==> _` (drule_then strip_assume_tac) >>
     fs[ptr_observation_reachable_def] >>
     drule ptr_frame_operand_instructions >> strip_tac >>
     drule ptr_frame_context_membership >> strip_tac >>
     drule ptr_discipline_upto_fn_ptr_ok >> strip_tac >>
     drule frame_reachable_initial_fmp >> strip_tac >>
     fs[dyn_floor_def, EVERY_MEM, fn_ptr_ok_def] >> metis_tac[]) >>
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
  suspend "byte"
QED

Resume ptr_paired_fixed_read_recovery_upto[byte]:
  rename1 `ptr_ledger_write_pair C C' reloc _ _ _ _` >>
  drule ptr_structural_transcript_ownership >>
  disch_then (qspec_then `SUC w` mp_tac) >> simp[] >>
  qabbrev_tac `snap = EL (SUC w) H` >> PairCases_on `snap` >>
  simp[ptr_snapshot_ownership_def] >> strip_tac >>
  drule ptr_source_ownership_caches >> strip_tac >>
  drule_all ptr_source_birth_caches_slices >> strip_tac >>
  drule ptr_source_birth_caches_activations >> strip_tac >>
  drule ptr_source_activations_length >> strip_tac >>
  `ptr_observation_reachable vs C (EL (SUC w) h) /\
   gas_cut n vs (EL (SUC w) h).po_state` by
    (qpat_assum `!j. j < LENGTH h ==> _` irule >> simp[]) >>
  `!d. d <= LENGTH (EL (SUC w) h).po_stack ==>
    allocas_from lo (ptr_owner_view d (EL (SUC w) h)).cf_state` by
    metis_tac[ptr_cut_owner_allocas_from] >>
  `vs.vs_allocas = FEMPTY` by fs[o1_initial_state_ok_def] >>
  `reloc x = x` by
    (`x < lo \/ (dyn_floor C (EL w h).po_state <= x /\
       !d aid b0 sz. d <= LENGTH (EL (SUC w) h).po_stack /\
         FLOOKUP (ptr_owner_view d (EL (SUC w) h)).cf_state.vs_allocas aid = SOME (b0,sz) ==>
         b0 + sz <= dyn_floor C (EL w h).po_state)` by
      (simp[] >> Cases_on `x < lo` >> simp[] >>
       `dyn_floor C vs <= x` by metis_tac[] >> simp[] >>
       rpt strip_tac >> metis_tac[ptr_cut_owner_below_floor]) >>
     metis_tac[ptr_paired_write_owner_fixed]) >>
  `read_byte x (EL (SUC w) h).po_state.vs_memory =
   read_byte x (EL (SUC q) ht).po_state.vs_memory` by
    (qpat_x_assum `ptr_ledger_write_pair _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ptr_ledger_write_pair_def, ptr_bytes_agree_def] >>
     strip_tac >>
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

Theorem ptr_paired_owned_read_recovery_upto[local]:
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
  drule_all ptr_paired_endpoint_cut_safety >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `vs.vs_allocas = FEMPTY` by fs[o1_initial_state_ok_def] >>
  drule_all ptr_endpoint_owned_actual_initializer >> strip_tac >>
  drule_all ptr_chrono_ordinary_non_revert >> strip_tac >>
  `w < LENGTH h` by decide_tac >>
  `d <= LENGTH (EL w h).po_stack /\
   FLOOKUP (ptr_owner_view d (EL w h)).cf_state.vs_allocas aid = SOME (b,sz)` by simp[] >>
  `~in_revert_forward (EL w h).po_fn (EL w h).po_state` by fs[EVERY_EL] >>
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
    (bp_analyze_fuel (concretize_memloc_fuel (ptr_owner_view d endpoint).cf_fn)
      (cfg_analyze (ptr_owner_view d endpoint).cf_fn) (ptr_owner_view d endpoint).cf_fn)
    mems (ptr_owner_view d endpoint).cf_inst` by
    (gen_tac >> irule ptr_source_owned_read_seed >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  suspend "interval"
QED

Resume ptr_paired_owned_read_recovery_upto[interval]:
  `EL (LENGTH h-1) h = endpoint /\ LENGTH h-1 < LENGTH h` by
    (qpat_assum `ptr_chrono_history vs C h endpoint`
       (mp_tac o MATCH_MP ptr_chrono_history_end) >>
     strip_tac >> Cases_on `h` >> gvs[LAST_EL]) >>
  `(ptr_owner_view d (EL w h)).cf_fn = (ptr_owner_view d endpoint).cf_fn` by
    (`(ptr_owner_view d (EL w h)).cf_fn =
       (ptr_owner_view d (EL (LENGTH h-1) h)).cf_fn` suffices_by simp[] >>
     irule ptr_owner_view_interval_function >> simp[] >>
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

Resume ptr_paired_owned_read_recovery_upto[post_write]:
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
  `read_byte x (EL (SUC w) h).po_state.vs_memory =
   read_byte (pa + (x-b)) (EL (SUC q) ht).po_state.vs_memory` by
    (qpat_x_assum `ptr_ledger_write_pair _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ptr_ledger_write_pair_def, ptr_bytes_agree_def] >>
     strip_tac >>
     qpat_x_assum `!i. _ ==> read_byte i _ = _` (qspec_then `x` mp_tac) >> simp[]) >>
  `read_byte x endpoint.po_state.vs_memory =
    read_byte x (EL (SUC w) h).po_state.vs_memory` by
    (`read_byte x (EL (LENGTH h-1) h).po_state.vs_memory =
      read_byte x (EL (SUC w) h).po_state.vs_memory` suffices_by simp[] >>
     irule ptr_chrono_history_actual_interval_byte_frame >>
     conj_tac >- (rpt strip_tac >>
       qpat_assum `!n. w < n /\ SUC n < LENGTH h ==> _`
         (qspec_then `k` mp_tac) >> simp[] >> decide_tac) >>
     simp[] >> metis_tac[]) >>
  drule ptr_structural_trace_target >> strip_tac >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  `LENGTH ht = SUC (LENGTH done)` by fs[ptr_event_embedding_def] >>
  `!j. q < j /\ j < LENGTH done ==> w < EL j done` by
    (qpat_assum `ptr_event_embedding _ _ _` mp_tac >>
     pure_rewrite_tac[ptr_event_embedding_def] >> strip_tac >>
     rpt strip_tac >> first_x_assum (qspecl_then [`q`,`j`] mp_tac) >>
     simp[EL_APPEND_EQN]) >>
  `!j. j < LENGTH done ==> SUC (EL j done) < LENGTH h` by
    (rpt strip_tac >>
     qpat_assum `ptr_event_embedding _ _ _` mp_tac >>
     pure_rewrite_tac[ptr_event_embedding_def] >> strip_tac >>
     `EL j done < LENGTH h - 1` by
       (first_x_assum (qspecl_then [`j`,`LENGTH done`] mp_tac) >>
        simp[EL_APPEND_EQN]) >> decide_tac) >>
  `!j. SUC q <= j /\ j < LENGTH ht - 1 ==>
    pa + (x-b) NOTIN range_bytes (step_writes (EL j ht).po_inst
      (EL j ht).po_state (EL (SUC j) ht).po_state)` by
    (qx_gen_tac `j` >> strip_tac >>
     `j < LENGTH done /\ q < j` by decide_tac >>
     `w < EL j done /\ SUC (EL j done) < LENGTH h` by simp[] >>
     `x NOTIN range_bytes (step_writes (EL (EL j done) h).po_inst
       (EL (EL j done) h).po_state (EL (SUC (EL j done)) h).po_state)` by
       (qpat_assum `!n. w < n /\ SUC n < LENGTH h ==> _`
         (qspec_then `EL j done` mp_tac) >> simp[]) >>
     `EL j done < LENGTH h` by decide_tac >>
     `~in_revert_forward (EL (EL j done) h).po_fn (EL (EL j done) h).po_state` by
       (qpat_assum `EVERY (\obs. ~in_revert_forward _ _) h`
          (mp_tac o REWRITE_RULE [EVERY_EL]) >>
        disch_then (qspec_then `EL j done` mp_tac) >> simp[]) >>
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
     `w <= LENGTH h-1 /\ w <= EL j done /\ EL j done <= LENGTH h-1` by decide_tac >>
     `EL (LENGTH h-1) H = (tokens,registry,births,PT,TG,saved,entries)` by
       (drule ptr_structural_transcript_endpoint >> strip_tac >>
        `H <> []` by (Cases_on `H` >> fs[]) >>
        qpat_x_assum `LAST H = _` mp_tac >> simp[LAST_EL, PRE_SUB1]) >>
     `!k. w <= k /\ k <= LENGTH h-1 ==> d <= LENGTH (EL k h).po_stack` by
       (rpt strip_tac >> `k < LENGTH h` by decide_tac >> simp[]) >>
     `EL (LENGTH (EL (LENGTH h-1) h).po_stack - d) tokens = token` by simp[] >>
     `EL (LENGTH (EL (EL j done) h).po_stack - d) tsj = token` by
       (drule_all (Q.INST [`i` |-> `w`, `j` |-> `LENGTH h-1`]
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
     qabbrev_tac `t = EL j done` >> qabbrev_tac `r = LENGTH h - 1` >>
     qabbrev_tac `fn = (ptr_owner_view d (EL t h)).cf_fn` >>
     `MEM fn C.ctx_functions` by
       (`ptr_observation_reachable vs C (EL t h)` by metis_tac[] >>
        qpat_x_assum `ptr_observation_reachable vs C (EL t h)`
          (strip_assume_tac o REWRITE_RULE [ptr_observation_reachable_def]) >>
        drule ptr_frame_context_membership >> strip_tac >>
        Cases_on `d = LENGTH (EL t h).po_stack` >>
        simp[Abbr `fn`, ptr_owner_view_def] >>
        `LENGTH (EL t h).po_stack - (d+1) < LENGTH (EL t h).po_stack` by decide_tac >>
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
      (ptr_owner_view d endpoint).cf_fn = fn` by
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
          (rpt strip_tac >> `w <= k /\ k < LENGTH h` by decide_tac >> simp[]) >>
        `!k. t <= k /\ k < r ==> ~in_revert_forward (EL k h).po_fn (EL k h).po_state /\
            x NOTIN range_bytes (step_writes (EL k h).po_inst (EL k h).po_state (EL (SUC k) h).po_state)` by
          (gen_tac >> strip_tac >>
           `w < k /\ SUC k < LENGTH h /\ k < LENGTH h` by decide_tac >>
           conj_tac
           >- (qpat_assum `EVERY (\obs. ~in_revert_forward _ _) h`
                  (mp_tac o REWRITE_RULE [EVERY_EL]) >>
               disch_then (qspec_then `k` mp_tac) >> simp[]) >>
           qpat_assum `!k. w < k /\ SUC k < LENGTH h ==> _`
             (qspec_then `k` mp_tac) >> simp[]) >>
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
     `0 < sz /\ 0 < sb /\ pa <= pa+(x-b) /\ pa+(x-b) < pa+sz` by decide_tac >>
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
        `LENGTH (EL t h).po_stack - (e+1) < LENGTH (EL t h).po_stack` by decide_tac >>
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
            rpt conj_tac >>
            (first_assum ACCEPT_TAC ORELSE
             (qpat_assum `bid <> aid` mp_tac >> simp[NoAsms, EQ_SYM]))) >>
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
            `?pc. MEM (Allocation bid,pc,sb) (imported_mems_used observed.cu_context fn) /\
              reserved_intervals_disjoint (pa,sz) (pc,sb)` by
              (qpat_assum `Abbrev (bp = _)`
                 (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
               irule ptr_output_suspended_descendant_separation_static >>
               rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE
                                 (qexists `P` >> first_assum ACCEPT_TAC))) >>
               qexistsl [`C`,`C'`,`Allocation aid`,
                 `((ptr_owner_view d (EL t h)).cf_state.vs_current_bb,
                   (ptr_owner_view d (EL t h)).cf_state.vs_inst_idx)`,
                 `db`,`owner`,`(ptr_owner_view e (EL t h)).cf_state`,`endpoint`,
                 `out.fpo_function`,`h`,`itemsA`,`LENGTH (EL t h).po_stack-e`,`xs`,
                 `LENGTH (EL t h).po_stack-d-1`,`names`,`out`,`reserved`,`rpolicy`,`s`,
                 `(EL t h).po_stack`,`t`,`vs`] >>
               rpt conj_tac >>
               (first_assum ACCEPT_TAC ORELSE
                (qpat_assum `ptr_owner_view d (EL t h) = _`
                   (fn th => rewrite_tac[GSYM th]) >>
                 simp[NoAsms] >> first_assum ACCEPT_TAC))) >>
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
        `?pc. MEM (Allocation aid,pc,sz) (imported_mems_used observedB.cu_context owner) /\
          reserved_intervals_disjoint (pb,sb) (pc,sz)` by
          (irule ptr_output_tagged_ancestor_destination_separation_static >>
           rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE
                             (qexists `P` >> first_assum ACCEPT_TAC))) >>
           qexistsl [`C`,`C'`,`PTj`,`TGj`,
             `((ptr_owner_view e (EL t h)).cf_state.vs_current_bb,
               (ptr_owner_view e (EL t h)).cf_state.vs_inst_idx)`,
             `bid`,`bj`,`b`,`fn`,`(ptr_owner_view d (EL t h)).cf_state`,
             `endpoint`,`outB.fpo_function`,`h`,`itemsB`,`LENGTH (EL t h).po_stack-d`,
             `LENGTH (EL t h).po_stack-e-1`,`names`,`outB`,`tok`,`TAKE (SUC t) h`,
             `rj`,`reserved'`,`rpolicy`,`supplyB`,`sj`,`(EL t h).po_stack`,`t`,`tsj`,`dv`,`vs`] >>
           rpt conj_tac >>
           (first_assum ACCEPT_TAC ORELSE
            (qpat_assum `ptr_owner_view e (EL t h) = _`
               (fn th => rewrite_tac[GSYM th]) >>
             simp[NoAsms] >> first_assum ACCEPT_TAC))) >>
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
  `EL (LENGTH ht-1) ht = at /\ LENGTH ht-1 < LENGTH ht` by
    (qpat_assum `ptr_chrono_history vs C' ht at`
       (mp_tac o MATCH_MP ptr_chrono_history_end) >>
     strip_tac >> Cases_on `ht` >> gvs[LAST_EL]) >>
  `read_byte (pa + (x-b)) at.po_state.vs_memory =
    read_byte (pa + (x-b)) (EL (SUC q) ht).po_state.vs_memory` by
    (`read_byte (pa + (x-b)) (EL (LENGTH ht-1) ht).po_state.vs_memory =
      read_byte (pa + (x-b)) (EL (SUC q) ht).po_state.vs_memory` suffices_by simp[] >>
     irule ptr_chrono_history_actual_interval_byte_frame >>
     conj_tac >- simp[] >> simp[] >> metis_tac[]) >>
  `pa + x - b = pa + (x - b)` by
    (qpat_assum `b <= x` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  qpat_assum `pa + x - b = _` SUBST1_TAC >>
  qpat_assum `read_byte (pa + (x-b)) at.po_state.vs_memory = _` SUBST1_TAC >>
  qpat_assum `read_byte x endpoint.po_state.vs_memory = _` SUBST1_TAC >>
  first_assum ACCEPT_TAC
QED

Finalise ptr_paired_owned_read_recovery_upto[local]
