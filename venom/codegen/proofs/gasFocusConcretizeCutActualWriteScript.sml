Theory gasFocusConcretizeCutActualWrite
Ancestors
  gasFocusConcretizeEndpointCut gasFocusChronologicalCut
  concretizePtrPairedFields concretizePtrStageReserved concretizePtrPlacementBounds
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrChronologicalHistory concretizePtrDallocaActualWrites
  concretizePtrHistoricalWriteExclusion concretizePtrOperationalOpcodes
  concretizePtrExactWriteTransport concretizePtrValueTransport
  concretizePtrOwnershipErasure concretizePtrComparisonTransport
  concretizePtrWriteClassification concretizePtrOwnerPath
  concretizePtrAllocationOwnership frameAllocationOwnership
  concretizePtrActiveWriteOwner concretizePtrSourceOwnership
  concretizePtrActivationBirths concretizePtrActivationChronology
  concretizePtrPrefixLedger concretizePtrBytes
  concretizePtrPairedPrefix concretizeLayoutCutSafe concretizePtrStageBounds
  concretizePtrChronologicalDemand concretizePtrRequestHistory concretizePtrParamSupport
  gasFocusConcretizeHistoricalCut concretizeLayoutAccessGeometry
  o1PassContract o1SafeUpto o1LowerDloadPtrDiscipline unitShapeDefs unitTransformDefs
  venomWf venomInst ptrDiscipline ptrDisciplineEmptyTaint concretizeMemLocDefs memLocDefs
  frameOriginReachable finite_map list rich_list words pred_set

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

(* Reflect the actual byte. Only the scalar arm keeps the destination. *)
Theorem ptr_paired_actual_write_classification_upto[local]:
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
   (x < lo \/ dyn_floor C vs <= x) /\
   (!ops. mem_write_ops (EL (EL q done) h).po_inst = SOME ops ==>
     eval_operand ops.iao_ofst (EL q ht).po_state =
     eval_operand ops.iao_ofst (EL (EL q done) h).po_state)) \/
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
    metis_tac[ptr_erased_tagged_domain] >>
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
      conj_tac >- (qpat_x_assum `destt = dest` SUBST_ALL_TAC >> decide_tac) >>
      simp[]) >>
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

Theorem ptr_paired_actual_write_origin_upto:
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
  drule_all ptr_paired_actual_write_classification_upto >>
  disch_then (DISJ_CASES_THEN2 (fn th => disj1_tac >> simp[th])
    (fn th => disj2_tac >> ACCEPT_TAC th))
QED

Theorem ptr_paired_identity_write_reflection_upto[local]:
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
  ~in_revert_forward (EL (EL q done) h).po_fn (EL (EL q done) h).po_state /\
  x IN range_bytes (step_writes (EL q ht).po_inst
    (EL q ht).po_state (EL (SUC q) ht).po_state) ==>
  x IN range_bytes (step_writes (EL (EL q done) h).po_inst
    (EL (EL q done) h).po_state (EL (SUC (EL q done)) h).po_state) /\
  (!ops. mem_write_ops (EL (EL q done) h).po_inst = SOME ops ==>
    eval_operand ops.iao_ofst (EL q ht).po_state =
    eval_operand ops.iao_ofst (EL (EL q done) h).po_state)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ptr_paired_actual_write_classification_upto >>
  disch_then (DISJ_CASES_THEN2 (fn th => simp[th]) strip_assume_tac) >>
  drule ptr_paired_prefix_memory >> strip_tac >>
  drule ptr_paired_memory_placements >> strip_tac >>
  `x - pb < sb /\ pb + (x-pb) = x` by decide_tac >>
  Cases_on `x < lo`
  >- (`lo <= pb + (x-pb)` by
        (irule ptr_stage_placements_reserved_prefix >>
         rpt (goal_assum (drule_at Any)) >> simp[]) >>
      (gvs[])) >>
  `dyn_floor C vs <= x` by metis_tac[] >>
  `pb + sb < dimword (:256)` by
    (drule_all concretizePtrPlacementBoundsTheory.ptr_stage_placements_strict_bound >> simp[]) >>
  `pb + sb <= eom` by
    (irule ptr_stage_placements_endpoint_bound >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  Cases_on `ctx_has_dalloca C` >> fs[dyn_floor_def] >> decide_tac
QED

Theorem ptr_paired_fixed_actual_write_reflection_upto:
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
  simp[] >> drule_all ptr_paired_identity_write_reflection_upto >> simp[]
QED

Theorem ptr_cut_owner_allocas_from:
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
Theorem ptr_cut_owner_below_floor:
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

(* Keep the actual relocation and ledger pair, so clients can separately
   project write membership or (for a clean byte) agreement of the values. *)
Theorem ptr_cut_paired_write_ledger_identity:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  o1_initial_state_ok vs /\ alloca_frontier_upto n C vs /\
  ptr_discipline_upto lo n C vs /\ gas_cut n vs at.po_state /\
  q < LENGTH done /\ ~is_terminator (EL (EL q done) h).po_inst.inst_opcode /\
  (EL (EL q done) h).po_inst.inst_opcode <> INVOKE /\
  (x < lo \/ dyn_floor C vs <= x) /\
  x IN range_bytes (step_writes (EL (EL q done) h).po_inst
    (EL (EL q done) h).po_state (EL (SUC (EL q done)) h).po_state) ==>
  ?rho. MEM (EL q done,q,rho) ws /\ rho x = x /\
    ptr_ledger_write_pair C C' rho
      (EL (EL q done) h) (EL (SUC (EL q done)) h) (EL q ht) (EL (SUC q) ht)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_paired_prefix_writes >> strip_tac >>
  `?rho. MEM (EL q done,q,rho) ws` by
    (qpat_assum `ptr_paired_writes _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ptr_paired_writes_def] >> strip_tac >>
     first_x_assum (qspec_then `q` mp_tac) >> simp[] >> metis_tac[NOT_IN_EMPTY]) >>
  drule_all ptr_paired_write_event >> simp[ptr_paired_write_def] >> strip_tac >>
  rename1 `ptr_ledger_write_pair C C' reloc _ _ _ _` >>
  qexists `reloc` >> simp[] >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule_all ptr_paired_endpoint_cut_safety >> strip_tac >>
  drule_all ptr_chrono_history_cut >> simp[EVERY_EL] >> strip_tac >>
  drule ptr_chrono_history_reachable >> simp[EVERY_EL] >> strip_tac >>
  `EL q done < LENGTH h` by decide_tac >>
  `dyn_floor C (EL (EL q done) h).po_state = dyn_floor C vs` by
    (`ptr_observation_reachable vs C (EL (EL q done) h)` by simp[] >>
     fs[ptr_observation_reachable_def] >>
     drule frame_reachable_initial_fmp >> simp[dyn_floor_def]) >>
  drule ptr_structural_transcript_ownership >>
  disch_then (qspec_then `SUC (EL q done)` mp_tac) >> simp[] >>
  qabbrev_tac `snap = EL (SUC (EL q done)) H` >> PairCases_on `snap` >>
  simp[ptr_snapshot_ownership_def] >> strip_tac >>
  drule ptr_source_ownership_caches >> strip_tac >>
  drule_all ptr_source_birth_caches_slices >> strip_tac >>
  drule ptr_source_birth_caches_activations >> strip_tac >>
  drule ptr_source_activations_length >> strip_tac >>
  qmatch_asmsub_abbrev_tac `ptr_birth_slices post toks births'` >>
  `ptr_observation_reachable vs C post /\ gas_cut n vs post.po_state` by
    simp[Abbr `post`] >>
  `!d. d <= LENGTH post.po_stack ==> allocas_from lo (ptr_owner_view d post).cf_state` by
    metis_tac[ptr_cut_owner_allocas_from] >>
  `vs.vs_allocas = FEMPTY` by fs[o1_initial_state_ok_def] >>
  `x < lo \/ (dyn_floor C vs <= x /\
     !d aid b0 sz. d <= LENGTH post.po_stack /\
       FLOOKUP (ptr_owner_view d post).cf_state.vs_allocas aid = SOME (b0,sz) ==>
       b0 + sz <= dyn_floor C vs)` by
    (Cases_on `x < lo` >> simp[] >>
     `dyn_floor C vs <= x` by metis_tac[] >> simp[] >>
     rpt strip_tac >> metis_tac[ptr_cut_owner_below_floor]) >>
  gvs[] >> metis_tac[ptr_paired_write_owner_fixed]
QED

Theorem focus_cut_paired_actual_write_identity:
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
  q < LENGTH done /\
  ~in_revert_forward (EL (EL q done) h).po_fn (EL (EL q done) h).po_state /\
  ~is_terminator (EL (EL q done) h).po_inst.inst_opcode /\
  (EL (EL q done) h).po_inst.inst_opcode <> INVOKE ==>
  !x. (x < lo \/ dyn_floor C vs <= x) ==>
    (x IN range_bytes (step_writes (EL q ht).po_inst
      (EL q ht).po_state (EL (SUC q) ht).po_state) <=>
     x IN range_bytes (step_writes (EL (EL q done) h).po_inst
      (EL (EL q done) h).po_state (EL (SUC (EL q done)) h).po_state)) /\
    (x IN range_bytes (step_writes (EL q ht).po_inst
      (EL q ht).po_state (EL (SUC q) ht).po_state) ==>
     !ops. mem_write_ops (EL (EL q done) h).po_inst = SOME ops ==>
       eval_operand ops.iao_ofst (EL q ht).po_state =
       eval_operand ops.iao_ofst (EL (EL q done) h).po_state)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  gen_tac >> disch_tac >>
  simp[EQ_IMP_THM] >> rpt conj_tac
  >- (disch_tac >> drule_all ptr_paired_identity_write_reflection_upto >> simp[])
  >- (disch_tac >> drule_all ptr_cut_paired_write_ledger_identity >>
      simp[ptr_ledger_write_pair_def] >> strip_tac >>
      qpat_x_assum `!i. i IN range_bytes _ ==> _ IN range_bytes _`
        (qspec_then `x` mp_tac) >> simp[]) >>
  disch_tac >> drule_all ptr_paired_identity_write_reflection_upto >> simp[]
QED
