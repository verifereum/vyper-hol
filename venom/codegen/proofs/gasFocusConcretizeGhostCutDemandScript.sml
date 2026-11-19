Theory gasFocusConcretizeGhostCutDemand
Ancestors
  gasFocusConcretizeCutCoverage gasFocusConcretizeGhostCutEffect
  gasFocusConcretizeGhostCutPoints concretizePtrDallocaEarlierRead
  concretizePtrDallocaActualFresh concretizePtrDallocaStaticFresh
  concretizePtrDallocaMemoryProbe concretizePtrDallocaWriterTaint
  concretizePtrPrefixLedger concretizePtrStructuralTrace
  concretizePtrStructuralTranscript concretizePtrChronologicalHistory
  concretizePtrSourceOwnership concretizePtrActivationBirths concretizePtrOwnerPath
  concretizePtrActivationChronology concretizeLayoutAccessGeometry
  concretizeAllocationFree frameAllocationOwnership ptrDisciplineEmptyTaint
  o1LowerDloadPtrDiscipline o1SafeUpto unitTransformDefs o1PassContract
  concretizeLayoutCutSafe concretizePtrPairedPrefix concretizePtrStageBounds
  concretizePtrEventEmbedding concretizePtrRequestHistory concretizePtrTaintContent
  concretizePtrSharedFields concretizePtrOpaqueRetpc ptrDiscipline
  concretizePtrHistoricalWriteExclusion concretizePtrDallocaActualWrites
  concretizePtrOperationalOpcodes concretizePtrObservationInterface
  concretizePtrAllocationOwnership concretizePtrOwnerSeeds
  concretizePtrDallocaWriterGeometry concretizePtrWriteClassification
  concretizePtrRevertHistory concretizePtrChronologicalDemand
  gasFocusConcretizeTaggedSupport
  concretizePtrParamShape concretizePtrParamSupport concretizePtrPlacementBounds
  concretizePtrValueTransport concretizePtrComparisonTransport
  unitShapeDefs venomWf list arithmetic finite_map pred_set

(* Recover the writer's own snapshot, not the endpoint's tags. *)
Theorem cut_departed_writer_sample[local]:
  ptr_paired_prefix R lp positions lo vs C Ct
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  o1_ctx_shape C /\ ptr_observation_reachable vs C (EL w h) /\
  r < LENGTH done /\ EL r done = w /\
  EL w H = (ts,rw,bw,PTw,TGw,sw,ew) /\
  x IN range_bytes (step_writes (EL w h).po_inst
    (EL w h).po_state (EL (SUC w) h).po_state) ==>
  (EL r ht).po_inst = (EL w h).po_inst /\
  (EL w h).po_state.vs_labels = (EL r ht).po_state.vs_labels /\
  ptr_mixed_vars bw positions TGw (EL w h).po_taint
    (EL w h).po_fn (EL r ht).po_fn (EL w h).po_state (EL r ht).po_state
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_target >> strip_tac >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  `r < LENGTH ht /\ EL r (done ++ [LENGTH h-1]) = w` by simp[EL_APPEND_EQN] >>
  drule ptr_paired_prefix_memory >> strip_tac >>
  drule_all ptr_paired_memory_alignment >> simp[] >> strip_tac >>
  drule ptr_paired_prefix_samples >> strip_tac >>
  `EL (EL r (done ++ [LENGTH h-1])) H = (ts,rw,bw,PTw,TGw,sw,ew)` by simp[] >>
  drule_all ptr_paired_samples_mixed >> simp[] >> disch_tac >>
  drule_all ptr_paired_samples_history >> simp[] >> strip_tac >>
  drule ptr_history_content_labels >> simp[] >> disch_tac >>
  `MEM (EL w h).po_fn C.ctx_functions` by
    (fs[ptr_observation_reachable_def] >> drule ptr_frame_context_membership >> simp[]) >>
  `fn_inst_ids_distinct (EL w h).po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def,
        EVERY_MEM, wf_function_def] >> metis_tac[]) >>
  drule ptr_trace_departed_inst_ids >> disch_then (qspec_then `r` mp_tac) >>
  simp[] >> strip_tac >>
  `((EL r ht).po_inst = concretize_inst_with_positions (lp (EL w h).po_fn) (EL w h).po_inst)` by
    (irule ptr_departed_cursor_instruction >> simp[]) >>
  metis_tac[ptr_dalloca_written_instruction]
QED

Theorem cut_target_allocation_free[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) view C C' /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\ ~ctx_has_dalloca C ==>
  EVERY (\fn. EVERY (\inst. allocation_free_opcode inst.inst_opcode)
    (fn_insts fn)) C'.ctx_functions
Proof
  simp[ctx_pass_stage_def, ctx_has_dalloca_def] >> rpt strip_tac >>
  fs[LIST_REL_EL_EQN, EVERY_EL, EXISTS_MEM] >>
  qx_gen_tac `j` >> strip_tac >>
  `j < LENGTH C.ctx_functions` by simp[] >>
  qpat_x_assum `!n. _ ==> ?observed s out. _`
    (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
  `EVERY (\inst. allocation_free_opcode inst.inst_opcode)
    (fn_insts out.fpo_function)` suffices_by simp[EVERY_EL] >>
  irule concretize_fn_pass_opcode_property >> simp[allocation_free_opcode_def] >>
  qexistsl [`EL j C.ctx_functions`, `observed`, `rpolicy`, `s`] >>
  simp[allocation_free_opcode_def] >>
  fs[fn_ptr_ok_def, EVERY_EL] >> metis_tac[MEM_EL]
QED

Theorem cut_live_owner[local]:
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  FLOOKUP TG v = SOME (token,aid) /\ FLOOKUP births (token,aid) = SOME (b,sz) ==>
  ?d. d <= LENGTH a.po_stack /\
      EL (LENGTH a.po_stack - d) tokens = token /\
      FLOOKUP (ptr_owner_view d a).cf_state.vs_allocas aid = SOME (b,sz)
Proof
  strip_tac >>
  drule_all ptr_source_ownership_live_prov >> strip_tac >>
  drule ptr_source_ownership_caches >> strip_tac >>
  drule ptr_source_birth_caches_activations >> strip_tac >>
  drule ptr_source_activations_length >> strip_tac >>
  drule ptr_source_birth_caches_slices >> strip_tac >>
  gs[MEM_EL] >> rename1 `j < SUC (LENGTH a.po_stack)` >>
  qexists `LENGTH a.po_stack - j` >>
  `LENGTH a.po_stack - (LENGTH a.po_stack - j) = j` by decide_tac >> simp[] >>
  qpat_assum `ptr_birth_slices _ _ _` (mp_tac o REWRITE_RULE [ptr_birth_slices_def]) >>
  disch_then (qspecl_then [`LENGTH a.po_stack - j`,`aid`] mp_tac) >> simp[]
QED

Theorem cut_live_owner_bounds[local]:
  ptr_observation_reachable vs C a /\ ptr_discipline_upto lo n C vs /\
  gas_cut n vs a.po_state /\ ctx_has_dalloca C /\ d <= LENGTH a.po_stack /\
  FLOOKUP (ptr_owner_view d a).cf_state.vs_allocas aid = SOME (b,sz) ==>
  lo <= b /\ b + sz <= w2n vs.vs_initial_fmp
Proof
  strip_tac >> fs[ptr_observation_reachable_def] >>
  drule frame_reachable_initial_fmp >> strip_tac >>
  Cases_on `d = LENGTH a.po_stack`
  >- (drule_all ptr_discipline_upto_at >> strip_tac >>
      fs[ptr_owner_view_def, allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  drule_all frame_reachable_saved_allocas_from >> strip_tac >>
  drule_all frame_reachable_saved_below_fmp_upto >> strip_tac >>
  qabbrev_tac `j = LENGTH a.po_stack - d - 1` >>
  `j < LENGTH a.po_stack` by (simp[Abbr `j`] >> decide_tac) >>
  `allocas_from lo (EL j a.po_stack).cf_state /\
   allocas_below_fmp (EL j a.po_stack).cf_state /\
   (EL j a.po_stack).cf_state.vs_initial_fmp = vs.vs_initial_fmp` by fs[EVERY_EL] >>
  fs[ptr_owner_view_def, Abbr `j`, allocas_from_def, allocas_below_fmp_def] >> metis_tac[]
QED

Theorem cut_writer_point[local]:
  ptr_observation_reachable vs C a /\ o1_ctx_shape C /\
  EVERY (fn_ptr_ok P) C.ctx_functions ==>
  fn_ptr_ok P a.po_fn /\ opaque_use_ok a.po_fn /\
  MEM a.po_inst (fn_insts a.po_fn) /\ label_positions_ok a.po_inst /\
  a.po_inst.inst_opcode <> DRET
Proof
  simp[ptr_observation_reachable_def] >> strip_tac >>
  drule ptr_frame_operand_instructions >> strip_tac >>
  drule ptr_frame_context_membership >> strip_tac >>
  fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM,
     inst_shape_ok_def, fn_ptr_ok_def] >> metis_tac[]
QED

(* Classify the actual destination by its source range. The fixed and
   dynamic cases cannot contain a byte of the live relocated allocation. *)
Theorem cut_owned_write_offset[local]:
  ptr_source_ownership vs C h a tokens registry births PT TG saved /\
  ptr_ledger_erases (dyn_floor C vs) births TG a.po_prov /\
  access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
  ~in_revert_forward a.po_fn a.po_state /\
  ptr_active_alloc_geometry (a.po_state :: MAP (\f. f.cf_state) a.po_stack) /\
  d <= LENGTH a.po_stack /\
  FLOOKUP (ptr_owner_view d a).cf_state.vs_allocas aid = SOME (b,sz) /\
  lo <= b+k /\ k < sz /\ b+k < dyn_floor C vs /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
  pa+sz < dimword (:256) /\
  mem_write_ops a.po_inst = SOME ops /\
  MEM (w2n x,w2n z) (source_memory_write_ranges a.po_inst a.po_state) /\
  w2n x <= b+k /\ b+k < w2n x+w2n z /\
  ptr_lookup_transport births positions (op_prov TG ops.iao_ofst)
    (op_taint a.po_taint ops.iao_ofst) (SOME x) (SOME xt) ==>
  ?off. b+k = w2n x+off /\ pa+k = w2n xt+off /\ off < w2n z
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `w2n z <> 0 /\ lo < w2n x+w2n z` by decide_tac >>
  `?v ob osz. ops.iao_ofst = Var v /\ FLOOKUP a.po_prov v = SOME (ob,osz) /\
    ob <= w2n x /\ w2n x+w2n z <= ob+osz` by
    (fs[access_ok_def] >> metis_tac[]) >>
  `ptr_owner_erases (dyn_floor C vs) births (FLOOKUP TG v) (SOME (ob,osz))` by
    (fs[ptr_ledger_erases_def] >> metis_tac[]) >>
  Cases_on `FLOOKUP TG v` >- (fs[ptr_owner_erases_def] >> decide_tac) >>
  rename1 `FLOOKUP TG v = SOME tag` >> PairCases_on `tag` >>
  `FLOOKUP births (tag0,tag1) = SOME (ob,osz)` by fs[ptr_owner_erases_def] >>
  drule_all cut_live_owner >> strip_tac >>
  rename1 `FLOOKUP (ptr_owner_view e a).cf_state.vs_allocas tag1 = SOME (ob,osz)` >>
  `d = e /\ aid = tag1` by
    (irule ptr_owner_overlap_unique >>
     qexistsl [`b`,`ob`,`a`,`sz`,`osz`,`b+k`] >> simp[] >> decide_tac) >>
  `ob = b /\ osz = sz` by fs[] >>
  `xt = x - n2w b + n2w pa` by
    gvs[op_prov_def, ptr_lookup_transport_some, ptr_value_transport_def] >>
  `w2n xt = pa + (w2n x-b)` by
    (asm_rewrite_tac[] >> irule ptr_closed_relocation_value >>
     `b <= w2n x /\ w2n x <= b+sz` by decide_tac >>
     simp[] >> qexists `sz` >> simp[]) >>
  qexists `b+k-w2n x` >> decide_tac
QED

(* The allocated slot is below the target's dynamic bump, at every
   departed row, not just at the demanded endpoint. *)
Theorem cut_row_fmp_floor[local]:
  ptr_observation_reachable vs C a /\ allocas_below_fmp a.po_state /\
  ptr_history_content a.po_taint a.po_state t ==>
  w2n vs.vs_initial_fmp <= w2n t.vs_fmp
Proof
  simp[ptr_observation_reachable_def, allocas_below_fmp_def] >> strip_tac >>
  drule frame_reachable_initial_fmp >> strip_tac >>
  drule ptr_history_content_control >>
  simp[ptr_taint_control_def, ptr_core_shared_def, ptr_shared_fields_def]
  >> (metis_tac[])
QED

(* The writer and the reflecting copy input are both strictly before i.
   The demand itself may be at the not-yet-departed target endpoint. *)
Theorem focus_cut_frontier_demanded_reflection:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  i < LENGTH h /\ q <= LENGTH done /\
  (q = 0 \/ EL (q-1) done < i) /\ i <= EL q (done ++ [LENGTH h-1]) /\
  EL i H = (tsi,ri,bi,PTi,TGi,si,ei) /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ EVERY all_reachable C.ctx_functions /\
  EVERY ssa_form C.ctx_functions /\
  o1_initial_state_ok vs /\ vs.vs_fmp = vs.vs_initial_fmp /\
  code_layout_valid vs /\ EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  alloca_frontier_upto n C vs /\ fixed_region_reserved lo C /\
  o1_safe_upto D lo n C vs /\ gas_cut n vs at.po_state /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\ (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  FLOOKUP TGi v = SOME (token,aid) /\
  FLOOKUP (EL i h).po_prov v = SOME (b,sz) /\
  FLOOKUP bi (token,aid) = SOME (b,sz) /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\ k < sz /\
  ~in_revert_forward (EL i h).po_fn (EL i h).po_state /\
  (EL i h).po_inst.inst_opcode <> ASSIGN /\
  MEM (Var v) (EL i h).po_inst.inst_operands /\
  (inst_read_op (EL i h).po_inst = SOME (Var v) \/ (EL i h).po_inst.inst_opcode = INVOKE) /\
  (!j r op. j < i /\ r < LENGTH done /\ EL r done = j ==>
    op_taint (EL r ht).po_taint op SUBSET op_taint (EL j h).po_taint op) /\
  (!j r a. j < i /\ r < LENGTH done /\ EL r done = j /\ a < lo ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r a. j < i /\ r < LENGTH done /\ EL r done = j /\ dyn_floor C vs <= a ==>
    a IN (EL r ht).po_taint.t_mem ==> a IN (EL j h).po_taint.t_mem) /\
  (!j r u tok id base size pos ix ts rw bw PTw TGw sw ew.
    j < i /\ r < LENGTH done /\ EL r done = j /\
    ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
    (EL j h).po_inst.inst_opcode <> ASSIGN /\
    MEM (Var u) (EL j h).po_inst.inst_operands /\
    (inst_read_op (EL j h).po_inst = SOME (Var u) \/ (EL j h).po_inst.inst_opcode = INVOKE) /\
    EL j H = (ts,rw,bw,PTw,TGw,sw,ew) /\ FLOOKUP TGw u = SOME (tok,id) /\
    FLOOKUP (EL j h).po_prov u = SOME (base,size) /\
    FLOOKUP bw (tok,id) = SOME (base,size) /\
    FLOOKUP positions (Allocation id) = SOME (pos,size) /\ ix < size ==>
    pos+ix IN (EL r ht).po_taint.t_mem ==> base+ix IN (EL j h).po_taint.t_mem) ==>
  pa+k IN (EL q ht).po_taint.t_mem ==> b+k IN (EL i h).po_taint.t_mem
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> disch_tac >>
  spose_not_then assume_tac >>
  `ptr_discipline_upto lo n C vs` by fs[o1_safe_upto_def, o1_ptr_safe_upto_def] >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_target >> strip_tac >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  `q < LENGTH ht` by fs[ptr_event_embedding_def] >>
  reverse (Cases_on `ctx_has_dalloca C`)
  >- (drule ptr_discipline_upto_fn_ptr_ok >> strip_tac >>
      drule_all cut_target_allocation_free >> strip_tac >>
      `ptr_observation_reachable vs C' (EL q ht)` by
        (qpat_assum `ptr_chrono_history vs C' ht at`
           (mp_tac o MATCH_MP (cj 2 ptr_chrono_history_reachable)) >>
         simp[EVERY_EL]) >>
      `vs.vs_allocas = FEMPTY` by fs[o1_initial_state_ok_def] >>
      qpat_x_assum `ptr_observation_reachable vs C' _`
        (assume_tac o REWRITE_RULE [ptr_observation_reachable_def]) >>
      `taint_empty (EL q ht).po_taint` by (drule_all allocation_free_reachable_taint >> simp[]) >>
      qpat_x_assum `taint_empty _`
        (assume_tac o CONJUNCT1 o REWRITE_RULE [taint_empty_def]) >>
      fs[]) >>
  drule_all focus_concretize_ghost_cut_points >>
  disch_then (fn th =>
    assume_tac (cj 2 th) >> qspec_then `i` mp_tac (cj 2 th)) >>
  (impl_tac >- simp[]) >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `ptr_source_ownership vs C (TAKE (SUC i) h) (EL i h) tsi ri bi PTi TGi si` by
    (drule ptr_structural_transcript_ownership >>
     disch_then (qspec_then `i` mp_tac) >> simp[ptr_snapshot_ownership_def]) >>
  drule_all cut_live_owner >> strip_tac >>
  drule_all cut_live_owner_bounds >> strip_tac >>
  `lo <= b+k /\ b+k < dyn_floor C vs` by (simp[dyn_floor_def] >> decide_tac) >>
  `b <= b+k /\ b+k < b+sz /\ b+k-b = k` by decide_tac >>
  drule_all (Q.INST [`x` |-> `b+k`, `qi` |-> `q`]
    (SPEC_ALL focus_cut_owned_writer_path)) >>
  disch_then (qx_choose_then `w` (qx_choose_then `r`
    (qx_choose_then `reloc` (map_every assume_tac o CONJUNCTS)))) >>
  qpat_assum `ptr_ledger_write_pair _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ptr_ledger_write_pair_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `pa+k IN range_bytes (step_writes (EL r ht).po_inst
     (EL r ht).po_state (EL (SUC r) ht).po_state)` by metis_tac[] >>
  `w < LENGTH h` by decide_tac >>
  qpat_assum `!j. j < LENGTH h ==> _` (qspec_then `w` mp_tac) >>
  (impl_tac >- simp[]) >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `snap = EL w H` >> PairCases_on `snap` >>
  `EL w H = (snap0,snap1,snap2,snap3,snap4,snap5,snap6)` by fs[markerTheory.Abbrev_def] >>
  drule_all (Q.INST [`w` |-> `w`, `r` |-> `r`] (SPEC_ALL cut_departed_writer_sample)) >>
  strip_tac >>
  `ptr_source_ownership vs C (TAKE (SUC w) h) (EL w h)
    snap0 snap1 snap2 snap3 snap4 snap5` by
    (drule ptr_structural_transcript_ownership >>
     disch_then (qspec_then `w` mp_tac) >> simp[ptr_snapshot_ownership_def]) >>
  `ptr_ledger_erases (dyn_floor C vs) snap2 snap4 (EL w h).po_prov` by
    (qpat_assum `!a b c d e f g. _ ==> ptr_params_erases _ _ _ (EL w h).po_params /\ _`
       (qspecl_then [`snap0`,`snap1`,`snap2`,`snap3`,`snap4`,`snap5`,`snap6`] mp_tac) >> simp[]) >>
  `~in_revert_forward (EL w h).po_fn (EL w h).po_state` by
    (drule ptr_structural_trace_source >> strip_tac >>
     `ptr_chrono_history vs C (TAKE (SUC i) h) (EL i h)` by
       (drule ptr_chrono_history_prefix >> simp[]) >>
     drule_all ptr_chrono_ordinary_non_revert >>
     disch_then (mp_tac o REWRITE_RULE [EVERY_EL]) >>
     disch_then (qspec_then `w` mp_tac) >> simp[LENGTH_TAKE,EL_TAKE]) >>
  `ptr_active_alloc_geometry ((EL w h).po_state :: MAP (\f. f.cf_state) (EL w h).po_stack)` by
    (fs[ptr_observation_reachable_def, o1_initial_state_ok_def] >>
     drule_all ptr_frame_alloc_geometry >> simp[]) >>
  drule ptr_discipline_upto_fn_ptr_ok >> strip_tac >>
  drule o1_ctx_shape_instructions_wf >> strip_tac >>
  drule_all (Q.INST [`a` |-> `EL w h`] (SPEC_ALL cut_writer_point)) >> strip_tac >>
  `!u. u IN FDOM snap4 ==> u IN fn_pv P (EL w h).po_fn` by
    (drule_all (Q.SPECL [`vs`,`C`,`TAKE (SUC w) h`,`EL w h`]
       ptr_focus_source_tagged_support) >>
     simp[ptr_static_support_def] >> metis_tac[FLOOKUP_DEF]) >>
  drule ptr_paired_prefix_placements >> strip_tac >>
  `!a p s. FLOOKUP positions (Allocation a) = SOME (p,s) ==> p+s < dimword (:256)` by
    (rpt strip_tac >> drule_all ptr_stage_placements_strict_bound >> simp[]) >>
  drule_all ptr_dalloca_forward_write_operands >>
  disch_then (qx_choose_then `ops` (qx_choose_then `sizeop` (qx_choose_then `x` (qx_choose_then `z`
    (qx_choose_then `xt` (map_every assume_tac o CONJUNCTS)))))) >>
  `w2n x <= b+k /\ b+k < w2n x+w2n z` by
    (drule_all ptr_step_write_max_containment >> simp[]) >>
  `d <= LENGTH (EL w h).po_stack /\
   FLOOKUP (ptr_owner_view d (EL w h)).cf_state.vs_allocas aid = SOME (b,sz)` by simp[] >>
  `pa+sz < dimword (:256)` by
    (qpat_assum `!a p s. FLOOKUP positions (Allocation a) = _ ==> _`
       (qspecl_then [`aid`,`pa`,`sz`] mp_tac) >> simp[]) >>
  `ptr_lookup_transport snap2 positions (op_prov snap4 ops.iao_ofst)
     (op_taint (EL w h).po_taint ops.iao_ofst) (SOME x) (SOME xt)` by (fs[] >> (gvs[])) >>
  drule_all cut_owned_write_offset >> strip_tac >>
  `pa+k NOTIN (EL (SUC r) ht).po_taint.t_mem` by
    (`(EL (SUC r) ht).po_taint.t_mem =
      (step_taint (EL r ht).po_inst (EL r ht).po_state
        (EL (SUC r) ht).po_state (EL r ht).po_taint).t_mem` by
       (qpat_assum `ptr_chrono_step C' _ _`
          (mp_tac o MATCH_MP ptr_dalloca_chrono_ordinary_taint_fields) >> simp[]) >>
     `(EL (SUC w) h).po_taint.t_mem =
      (step_taint (EL w h).po_inst (EL w h).po_state
        (EL (SUC w) h).po_state (EL w h).po_taint).t_mem` by
       (qpat_assum `ptr_chrono_step C _ _`
          (mp_tac o MATCH_MP ptr_dalloca_chrono_ordinary_taint_fields) >> simp[]) >>
     `pa+k IN written_taint (EL r ht).po_taint (EL r ht).po_inst (EL r ht).po_state ==>
      b+k IN written_taint (EL w h).po_taint (EL w h).po_inst (EL w h).po_state` by
       (qpat_assum `(EL r ht).po_inst = (EL w h).po_inst` (pure_rewrite_tac o single) >>
        MATCH_MP_TAC focus_cut_writer_taint_effect >>
        conj_tac
        >- (map_every qx_gen_tac [`dst`,`value`,`dt`] >> strip_tac >>
            `ops.iao_ofst = dst` by
              (qpat_x_assum `mem_write_ops _ = SOME ops` mp_tac >>
               simp[memLocDefsTheory.mem_write_ops_def] >> disch_then (SUBST1_TAC o SYM) >> simp[]) >>
            `dt = xt` by metis_tac[optionTheory.SOME_11] >>
            qexists `x` >> (conj_tac >- metis_tac[]) >>
            (conj_tac >- metis_tac[]) >> rpt strip_tac >> gvs[] >> decide_tac) >>
        map_every qx_gen_tac [`dst`,`src`,`len`,`dt`,`rt`,`tlen`] >> strip_tac >>
        `ops.iao_ofst = dst /\ sizeop = len` by
          (qpat_x_assum `mem_write_ops _ = SOME ops` mp_tac >>
           simp[memLocDefsTheory.mem_write_ops_def] >>
           disch_then (SUBST_ALL_TAC o SYM) >> fs[]) >>
        `dt = xt /\ tlen = z` by metis_tac[optionTheory.SOME_11] >>
        `?rs. eval_operand src (EL w h).po_state = SOME rs` by
          (qpat_assum `!op. IS_SOME (eval_operand op _) <=> _`
             (qspec_then `src` assume_tac) >>
           Cases_on `eval_operand src (EL w h).po_state` >> fs[]) >>
        `eval_operand dst (EL w h).po_state = SOME x` by metis_tac[] >>
        `eval_operand len (EL w h).po_state = SOME z` by metis_tac[] >>
        qexistsl [`x`,`rs`,`z`] >> simp[] >>
        ONCE_REWRITE_TAC[arithmeticTheory.ADD_COMM] >>
        `ptr_lookup_transport snap2 positions (op_prov snap4 src) {} (SOME rs) (SOME rt)` by
          (drule_all ptr_dalloca_copy_read_transport >> simp[]) >>
        `mem_read_ops (EL w h).po_inst = SOME
           <|iao_ofst := src; iao_size := SOME len; iao_max_size := SOME len|> /\
         MEM (w2n rs,w2n z) (source_memory_read_ranges (EL w h).po_inst (EL w h).po_state)` by
          (simp[memLocDefsTheory.mem_read_ops_def, contextCodegenRelTheory.source_memory_read_ranges_def] >>
           metis_tac[]) >>
        drule_all (SPEC_ALL ptr_dalloca_read_byte_classification
          |> Q.INST [`ops` |-> `<|iao_ofst := src; iao_size := SOME len; iao_max_size := SOME len|>`,
                     `off` |-> `off`, `n` |-> `w2n z`]
          |> SIMP_RULE (srw_ss()) []) >>
        disch_then strip_assume_tac
        >- (qpat_assum `!j r a. j < i /\ r < LENGTH done /\ EL r done = j /\ a < lo ==> _`
              (qspecl_then [`w`,`r`,`w2n rs+off`] mp_tac) >> simp[])
        >- (qpat_assum `!j r a. j < i /\ r < LENGTH done /\ EL r done = j /\ dyn_floor C vs <= a ==> _`
              (qspecl_then [`w`,`r`,`w2n rs+off`] mp_tac) >> simp[]) >>
        `inst_read_op (EL w h).po_inst = SOME src` by simp[concretizeMemLocDefsTheory.inst_read_op_def] >>
        `MEM src (EL w h).po_inst.inst_operands` by simp[] >>
        qpat_assum `!j r u tok id base size pos ix ts rw bw PTw TGw sw ew. _`
          (qspecl_then [`w`,`r`] mp_tac) >>
        simp[] >> metis_tac[]) >>
     metis_tac[ptr_dalloca_writer_taint_transport]) >>
  `pa+k NOTIN (EL q ht).po_taint.t_mem` by
    (irule ptr_dalloca_chrono_untainted_suffix >>
     conj_tac >- simp[] >>
     qexistsl [`C'`, `at`, `SUC r`, `vs`] >> simp[] >>
     `SUC r <= q` by decide_tac >> simp[] >>
     drule ptr_paired_prefix_placements >> strip_tac >>
     drule_all ptr_stage_placements_endpoint_bound >> strip_tac >>
     `eom <= w2n vs.vs_initial_fmp` by simp[] >>
     `pa+k < w2n vs.vs_initial_fmp` by decide_tac >>
     drule ptr_paired_prefix_samples >> strip_tac >>
     qx_gen_tac `j` >> strip_tac >> conj_tac
     >- (qpat_assum `!l. SUC r <= l /\ l < q ==> _`
           (qspec_then `j` mp_tac) >> simp[arithmeticTheory.ADD_COMM] >>
         metis_tac[arithmeticTheory.ADD_COMM]) >>
     `j < LENGTH done /\ j < LENGTH ht` by decide_tac >>
     `EL j (done ++ [LENGTH h-1]) = EL j done` by simp[EL_APPEND_EQN] >>
     `EL j done < LENGTH h` by
       (qpat_assum `ptr_event_embedding _ _ _`
          (mp_tac o cj 2 o REWRITE_RULE [ptr_event_embedding_def]) >>
        rewrite_tac[EVERY_EL] >> disch_then (qspec_then `j` mp_tac) >> simp[]) >>
     `ptr_history_content (EL (EL j done) h).po_taint
        (EL (EL j done) h).po_state (EL j ht).po_state` by
       (drule ptr_paired_samples_history >> disch_then (qspec_then `j` mp_tac) >> simp[]) >>
     qpat_assum `!i. i < LENGTH h ==> _` (qspec_then `EL j done` mp_tac) >>
     (impl_tac >- simp[]) >> disch_then (map_every assume_tac o CONJUNCTS) >>
     `allocas_below_fmp (EL (EL j done) h).po_state` by simp[] >>
     drule_all cut_row_fmp_floor >> strip_tac >>
     `(EL j ht).po_inst.inst_opcode <> ALLOCA` by
       (irule ptr_dalloca_departed_no_alloca >>
        rpt (goal_assum (drule_at Any)) >> simp[]) >>
     rpt gen_tac >> strip_tac >> irule ptr_dalloca_preserved_allocas_fresh_exclusion >>
     `k+pa < w2n (EL j ht).po_state.vs_fmp` by decide_tac >>
     conj_tac >- decide_tac >>
     qexistsl [`C'`, `fuel`, `(EL j ht).po_inst`] >> simp[]) >>
  fs[]
QED
