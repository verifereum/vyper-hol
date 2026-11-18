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
  concretizePtrExactWriteTransport concretizePtrStageReserved concretizePtrStageBounds
  concretizePtrDallocaActualWrites concretizePtrValueTransport concretizePtrRequestHistory
  concretizePtrChronologicalDemand concretizePtrOwnershipErasure
  concretizePtrComparisonTransport concretizePtrWriteClassification ptrDiscipline
  concretizePtrOwnerPath concretizePtrAllocationOwnership
  concretizeLayoutAccessGeometry frameAllocationOwnership ptrDisciplineEmptyTaint
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
  qpat_x_assum `x < lo \/ _` (assume_tac o REWRITE_RULE [DISJ_EQ_IMP]) >>
  Cases_on `in_revert_forward (EL (EL q done) h).po_fn
    (EL (EL q done) h).po_state` >- simp[] >>
  simp[] >> drule_all ptr_paired_historical_event_upto >> strip_tac >>
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
  drule_all ptr_historical_write_classification_upto >>
  disch_then (DISJ_CASES_THEN2 (MAP_EVERY assume_tac o CONJUNCTS) strip_assume_tac)
  >- (`MEM (EL (EL q done) h).po_inst.inst_opcode [CALL;STATICCALL;DELEGATECALL] ==>
        LENGTH (EL (SUC (EL q done)) h).po_state.vs_returndata =
        LENGTH (EL (SUC q) ht).po_state.vs_returndata` by simp[] >>
      drule_all ptr_write_transport_fixed_exact >> simp[]) >>
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
  `w2n destt <= x /\ x < w2n destt + w2n z` by
    (drule_all ptr_step_write_max_containment >> simp[]) >>
  `pb <= x /\ x - pb < sb` by decide_tac >>
  Cases_on `x < lo`
  >- (`lo <= pb + (x-pb)` by
        (irule ptr_stage_placements_reserved_prefix >>
         rpt (goal_assum (drule_at Any)) >> simp[]) >>
      decide_tac) >>
  `dyn_floor C vs <= x` by metis_tac[] >>
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
