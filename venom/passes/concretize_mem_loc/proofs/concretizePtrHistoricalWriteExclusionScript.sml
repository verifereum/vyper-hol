Theory concretizePtrHistoricalWriteExclusion
Ancestors
  concretizePtrPairedPrefix concretizePtrHistoricalWriteClassification
  concretizePtrDemandWriteExclusion concretizePtrWritePurity
  concretizePtrOpaqueRetpc concretizePtrChronologicalHistory concretizePtrRequestHistory
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrEventEmbedding concretizePtrLedgerAlignment concretizePtrPairedFields
  concretizePtrOperationalOpcodes concretizePtrHistoricalSupport concretizePtrValueTransport
  concretizeStepStructure concretizeStepShape concretizeStepCallChecks
  concretizeStepRetpc concretizeStageShape
  venomExecSemantics venomWf unitShapeDefs ptrDiscipline finite_map list
  stackPlanGen unitMemInv o1PassContract concretizePtrOwnerPath
  contextCodegenRel venomInst concretizeMemLocDefs concretizePtrWriteClassification
  codegenRel passSharedDefs concretizePtrLifetime arithmetic pred_set memLocDefs words venomState stackPlanTypes

Theorem ptr_fn_inst_wf_flat:
  fn_inst_wf fn ==> EVERY inst_wf (fn_insts fn)
Proof
  gvs[fn_inst_wf_def, EVERY_MEM, fn_insts_def, fn_insts_blocks_MEM] >>
  metis_tac[]
QED

Theorem ptr_trace_departed_inst_ids:
  !R vs C Ct h a ht at done tokens registry births PT TG saved entries.
  ptr_structural_trace R vs C Ct h a ht at done tokens registry births PT TG saved entries ==>
  !q. q < LENGTH done ==>
    (EL (EL q done) h).po_inst.inst_id = (EL q ht).po_inst.inst_id
Proof
  ho_match_mp_tac ptr_structural_trace_strongind >> rpt conj_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS)
  >- simp[]
  >- (rpt strip_tac >>
      drule ptr_structural_trace_embedding >>
      simp[ptr_event_embedding_def, EVERY_MEM] >> strip_tac >>
      `EL q done < LENGTH h` by
        (first_x_assum irule >> simp[MEM_EL] >> qexists_tac `q` >> simp[]) >>
      simp[EL_APPEND_EQN]) >>
  rpt strip_tac >>
  Cases_on `q < LENGTH done`
  >- (drule ptr_structural_trace_embedding >>
      simp[ptr_event_embedding_def, EVERY_MEM] >> strip_tac >>
      `EL q done < LENGTH h` by
        (first_x_assum irule >> simp[MEM_EL] >> qexists_tac `q` >> simp[]) >>
      simp[EL_APPEND_EQN]) >>
  `q = LENGTH done` by fs[] >> gvs[] >>
  (drule ptr_structural_trace_source >>
   disch_then (mp_tac o MATCH_MP ptr_chrono_history_end) >> strip_tac >>
   drule ptr_structural_trace_target >>
   disch_then (mp_tac o MATCH_MP ptr_chrono_history_end) >> strip_tac >>
   drule ptr_structural_trace_embedding >> strip_tac >>
   `0 < LENGTH h` by (Cases_on `h` >> fs[]) >>
   `LENGTH done = LENGTH ht - 1` by decide_tac >>
   fs[EL_APPEND_EQN] >>
   `LENGTH h - 1 = PRE (LENGTH h) /\
    LENGTH ht - 1 = PRE (LENGTH ht)` by decide_tac >>
   metis_tac[LAST_EL])
QED

Theorem ptr_departed_cursor_instruction:
  ptr_paired_cursor lp a at /\ fn_inst_ids_distinct a.po_fn /\
  a.po_inst.inst_id = at.po_inst.inst_id ==>
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst
Proof
  simp[ptr_paired_cursor_def] >> strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    (fs[fn_inst_ids_distinct_def] >>
     `?xs ys. a.po_fn.fn_blocks = xs ++ bb::ys` by metis_tac[MEM_SPLIT] >>
     gvs[MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND]) >>
  drule ptr_ledger_alignment_cursor >> strip_tac >>
  `EL at.po_state.vs_inst_idx indices < LENGTH bb.bb_instructions /\
   EL at.po_state.vs_inst_idx bbt.bb_instructions =
     concretize_inst_with_positions (lp a.po_fn)
       (EL (EL at.po_state.vs_inst_idx indices) bb.bb_instructions)` by
    (qpat_x_assum `!j. j < LENGTH bbt.bb_instructions ==> _`
       (qspec_then `at.po_state.vs_inst_idx` mp_tac) >> simp[]) >>
  `a.po_state.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >>
  `a.po_state.vs_inst_idx = EL at.po_state.vs_inst_idx indices` by
    (drule ALL_DISTINCT_EL_IMP >>
     disch_then (qspecl_then [`a.po_state.vs_inst_idx`,
       `EL at.po_state.vs_inst_idx indices`] mp_tac) >>
     simp[EL_MAP] >>
     gvs[concretize_positions_inst_id]) >>
  gvs[]
QED

Theorem ptr_paired_historical_event:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\
  ~in_revert_forward (EL (EL q done) h).po_fn (EL (EL q done) h).po_state /\
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
    access_ok lo (EL (EL q done) h).po_prov (EL (EL q done) h).po_fn
      (EL (EL q done) h).po_inst (EL (EL q done) h).po_state /\
    taint_ok (EL (EL q done) h).po_fn (EL (EL q done) h).po_taint
      (EL (EL q done) h).po_inst (EL (EL q done) h).po_state /\
    ~in_revert_forward (EL (EL q done) h).po_fn (EL (EL q done) h).po_state /\
    (EL q ht).po_inst = concretize_inst_with_positions
      (lp (EL (EL q done) h).po_fn) (EL (EL q done) h).po_inst
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_paired_prefix_samples >> strip_tac >>
  `q < LENGTH ht` by fs[ptr_paired_samples_def, ptr_sample_list_def] >>
  drule_all ptr_paired_prefix_alignment >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_paired_prefix_placements >> strip_tac >>
  `SUC q < LENGTH ht` by fs[ptr_paired_samples_def, ptr_sample_list_def] >>
  `EL q (done ++ [LENGTH h - 1]) = EL q done` by
    simp[EL_APPEND_EQN] >>
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
    (qpat_x_assum `ptr_paired_samples _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ptr_paired_samples_def, ptr_sample_list_def] >> strip_tac >>
     qpat_x_assum `!j. j < LENGTH ht ==> _` (qspec_then `q` mp_tac) >>
     simp[ptr_paired_sample_def, Abbr `aa`]) >>
  `ptr_history_content aa.po_taint aa.po_state (EL q ht).po_state` by
    (drule ptr_paired_samples_history >>
     disch_then (qspec_then `q` mp_tac) >> simp[Abbr `aa`]) >>
  `ptr_observation_reachable vs C aa` by
    (drule ptr_structural_trace_source >>
     disch_then (mp_tac o MATCH_MP ptr_chrono_history_reachable) >>
     simp[EVERY_MEM] >> strip_tac >>
     first_x_assum irule >> simp[Abbr `aa`, MEM_EL] >>
     qexists_tac `EL q done` >> simp[]) >>
  `access_ok lo aa.po_prov aa.po_fn aa.po_inst aa.po_state /\
   taint_ok aa.po_fn aa.po_taint aa.po_inst aa.po_state` by
    (fs[ptr_observation_reachable_def, ptr_discipline_def] >>
     qpat_x_assum `!stk PG G tn fn inst s. frame_reachable _ _ _ _ _ _ _ _ _ ==> _`
       drule >> simp[]) >>

  `aa.po_inst.inst_id = (EL q ht).po_inst.inst_id` by
    (drule ptr_trace_departed_inst_ids >>
     disch_then (qspec_then `q` mp_tac) >> simp[Abbr `aa`]) >>
  `MEM aa.po_fn C.ctx_functions` by
    (fs[ptr_observation_reachable_def] >>
     drule ptr_frame_context_membership >> simp[]) >>
  `fn_inst_ids_distinct aa.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def,
        EVERY_MEM, wf_function_def] >> metis_tac[]) >>
  `(EL q ht).po_inst = concretize_inst_with_positions (lp aa.po_fn) aa.po_inst` by
    (irule ptr_departed_cursor_instruction >> simp[]) >>
  simp[ptr_snapshot_step_def]
QED

Theorem ptr_ordinary_write_descriptor:
  inst.inst_opcode <> DRET /\ label_positions_ok inst /\
  (!op. IS_SOME (eval_operand op src) = IS_SOME (eval_operand op tgt)) /\
  q IN range_bytes (step_writes inst tgt postt) ==>
  ?ops sizeop x z.
    mem_write_ops inst = SOME ops /\ ops.iao_max_size = SOME sizeop /\
    eval_operand ops.iao_ofst src = SOME x /\ eval_operand sizeop src = SOME z /\
    MEM (w2n x,w2n z) (source_memory_write_ranges inst src) /\
    ((?u. ops.iao_ofst = Var u) \/ (?y. ops.iao_ofst = Lit y)) /\
    ((?u. sizeop = Var u) \/ (?y. sizeop = Lit y)) /\
    MEM ops.iao_ofst inst.inst_operands /\
    (MEM sizeop inst.inst_operands \/ (?n. sizeop = Lit n))
Proof
  strip_tac >>
  `!op. IS_SOME (eval_operand op tgt) ==> ?x. eval_operand op src = SOME x` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `!op. IS_SOME _ = _` (qspec_then `op` mp_tac) >>
     Cases_on `eval_operand op src` >> simp[]) >>
  `!op y. eval_operand op tgt = SOME y ==> ?x. eval_operand op src = SOME x` by
    (rpt strip_tac >> first_x_assum irule >> simp[]) >>
  qpat_x_assum `q IN range_bytes _` mp_tac >>
  pure_rewrite_tac[ptr_step_write_range] >> strip_tac >>
  drule (iffLR ptr_source_write_classification) >>
  simp[ptr_classified_write_range_def] >> strip_tac >>
  qpat_assum `!op y. eval_operand op tgt = SOME y ==> _` imp_res_tac >>
  gvs[mem_write_ops_def] >>
  gvs[label_positions_ok_def, eval_operand_def,
      dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  simp[ptr_source_write_classification, ptr_classified_write_range_def] >>
  rpt conj_tac >> qmatch_goalsub_rename_tac `dest = Var _` >>
  Cases_on `dest` >> gvs[is_label_operand_def] >>
  BasicProvers.FULL_CASE_TAC >> gvs[is_label_operand_def]
QED

Theorem ptr_ordinary_write_operand_transport:
  ptr_mixed_vars births positions TG tn fn ft src tgt /\
  src.vs_labels = tgt.vs_labels /\
  fn_ptr_ok P fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst src /\ label_positions_ok inst /\ inst.inst_opcode <> DRET /\
  (!u. u IN FDOM TG ==> u IN fn_pv P fn) /\
  q IN range_bytes (step_writes inst tgt postt) ==>
  ?ops sizeop x z xt.
    mem_write_ops inst = SOME ops /\ ops.iao_max_size = SOME sizeop /\
    eval_operand ops.iao_ofst src = SOME x /\ eval_operand sizeop src = SOME z /\
    MEM (w2n x,w2n z) (source_memory_write_ranges inst src) /\
    eval_operand ops.iao_ofst tgt = SOME xt /\ eval_operand sizeop tgt = SOME z /\
    ptr_lookup_transport births positions (op_prov TG ops.iao_ofst)
      (op_taint tn ops.iao_ofst) (eval_operand ops.iao_ofst src)
      (eval_operand ops.iao_ofst tgt) /\ w2n z <> 0 /\
    ptr_lookup_transport births positions (op_prov TG sizeop)
      (op_taint tn sizeop) (eval_operand sizeop src) (eval_operand sizeop tgt) /\
    op_prov TG sizeop = NONE /\ op_taint tn sizeop = {} /\
    (!op. IS_SOME (eval_operand op src) = IS_SOME (eval_operand op tgt)) /\
    ((?u. ops.iao_ofst = Var u) \/ (?y. ops.iao_ofst = Lit y)) /\
    ((?u. sizeop = Var u) \/ (?y. sizeop = Lit y))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!op. IS_SOME (eval_operand op src) = IS_SOME (eval_operand op tgt)` by
    (drule_all ptr_mixed_vars_eval_presence >> simp[]) >>
  drule_all ptr_ordinary_write_descriptor >>
  disch_then (qx_choose_then `ops` (qx_choose_then `sizeop`
    (qx_choose_then `x` (qx_choose_then `z`
      (map_every assume_tac o CONJUNCTS))))) >>
  `EVERY (ptr_nonopaque_operand fn) inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> simp[] >>
     drule ptr_step_write_opcode >> simp[] >> strip_tac >> gvs[]) >>
  `ptr_nonopaque_operand fn ops.iao_ofst /\ ptr_nonopaque_operand fn sizeop` by
    (gvs[EVERY_MEM] >> metis_tac[ptr_nonopaque_operand_def]) >>
  `ptr_lookup_transport births positions (op_prov TG ops.iao_ofst)
    (op_taint tn ops.iao_ofst) (eval_operand ops.iao_ofst src)
    (eval_operand ops.iao_ofst tgt)` by
    (irule ptr_mixed_vars_eval >> simp[] >> qexistsl_tac [`fn`,`ft`] >> simp[]) >>
  `ptr_lookup_transport births positions (op_prov TG sizeop)
    (op_taint tn sizeop) (eval_operand sizeop src) (eval_operand sizeop tgt)` by
    (irule ptr_mixed_vars_eval >> simp[] >> qexistsl_tac [`fn`,`ft`] >> simp[]) >>
  `op_taint tn sizeop = {}` by (drule_all ptr_write_max_size_untainted >> simp[]) >>
  `op_prov TG sizeop = NONE` by (drule_all ptr_write_max_size_no_provenance >> simp[]) >>
  `eval_operand sizeop tgt = SOME z` by
    (qpat_x_assum `ptr_lookup_transport _ _ (op_prov _ sizeop) _ _ _` mp_tac >>
     Cases_on `eval_operand sizeop tgt` >>
     simp[ptr_lookup_transport_def, ptr_value_transport_scalar_empty]) >>
  `?xt. eval_operand ops.iao_ofst tgt = SOME xt` by
    (qpat_x_assum `!op. IS_SOME _ = _` (qspec_then `ops.iao_ofst` mp_tac) >>
     Cases_on `eval_operand ops.iao_ofst tgt` >> simp[]) >>
  `w2n z <> 0` by (drule_all ptr_step_write_max_containment >> decide_tac) >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem ptr_chrono_nonwrite_footprint[local]:
  ~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE /\
  (?fuel post. step_inst fuel C a.po_inst a.po_state = OK post) /\
  ~ptr_chrono_write C addr a ==>
  addr NOTIN range_bytes (step_writes a.po_inst a.po_state posts)
Proof
  strip_tac >> spose_not_then assume_tac >>
  qpat_x_assum `addr IN range_bytes (step_writes _ _ _)` mp_tac >>
  pure_rewrite_tac[ptr_step_write_range] >> strip_tac >>
  `addr < off + len` by (Cases_on `MEM a.po_inst.inst_opcode
    [CALL;STATICCALL;DELEGATECALL]` >> gvs[MIN_DEF] >> decide_tac) >>
  fs[ptr_chrono_write_def, range_bytes_def] >> metis_tac[ADD_COMM]
QED

Theorem ptr_historical_ordinary_assembly[local]:
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w /\ w < j /\ j+1 < LENGTH h /\
  EL j H = (tsj,rj,bj,PTj,TGj,sj,ej) /\
  ptr_stage_placements C' positions /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
  fixed_region_reserved lo C /\
  ptr_mixed_vars bj positions TGj (EL j h).po_taint
    (EL j h).po_fn ft (EL j h).po_state t /\
  (EL j h).po_state.vs_labels = t.vs_labels /\
  taint_ok (EL j h).po_fn (EL j h).po_taint (EL j h).po_inst (EL j h).po_state /\
  fn_ptr_ok P (EL j h).po_fn /\ opaque_use_ok (EL j h).po_fn /\
  MEM (EL j h).po_inst (fn_insts (EL j h).po_fn) /\
  label_positions_ok (EL j h).po_inst /\
  (EL j h).po_inst.inst_opcode <> DRET /\
  ~is_terminator (EL j h).po_inst.inst_opcode /\
  (EL j h).po_inst.inst_opcode <> INVOKE /\
  (?fuel post. step_inst fuel C (EL j h).po_inst (EL j h).po_state = OK post) /\
  LENGTH (EL (SUC j) h).po_state.vs_returndata = LENGTH postt.vs_returndata ==>
  pa+k NOTIN range_bytes (step_writes (EL j h).po_inst t postt)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  spose_not_then assume_tac >>
  `j < LENGTH h` by decide_tac >>
  `ptr_structural_transcript R vs C C' h endpoint ht at done tokens registry
     births PT TG saved entries H /\
   EVERY (fn_ptr_ok P) C.ctx_functions /\
   EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
   EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions`
    by fs[ptr_demand_interval_def] >>
  `!u. u IN FDOM TGj ==> u IN fn_pv P (EL j h).po_fn` by
    (rpt strip_tac >> irule ptr_transcript_tagged_domain_support >> simp[] >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  drule_all ptr_ordinary_write_operand_transport >>
  disch_then (qx_choose_then `ops` (qx_choose_then `sizeop`
    (qx_choose_then `x` (qx_choose_then `z` (qx_choose_then `xt`
      (map_every assume_tac o CONJUNCTS)))))) >>
  `ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
      (o1_walk_view rpolicy 2) C C' /\
   EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
   ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
   o1_run_state_ok vs /\ ~ctx_has_dalloca C /\
   access_ok lo (EL j h).po_prov (EL j h).po_fn
      (EL j h).po_inst (EL j h).po_state /\
   ~in_revert_forward (EL j h).po_fn (EL j h).po_state /\
   b+k NOTIN range_bytes (step_writes (EL j h).po_inst (EL j h).po_state
     (EL (SUC j) h).po_state)` by
    (fs[ptr_demand_interval_def] >>
     metis_tac[rich_listTheory.EL_MEM, LESS_IMP_LESS_OR_EQ]) >>
  drule_all ptr_historical_write_classification >>
  disch_then assume_tac >>
  `MEM (EL j h).po_inst.inst_opcode [CALL;STATICCALL;DELEGATECALL] ==>
    LENGTH (EL (SUC j) h).po_state.vs_returndata = LENGTH postt.vs_returndata` by simp[] >>
  drule_all ptr_demand_ordinary_write_exclusion >> simp[]
QED

Theorem ptr_paired_historical_owned_write_exclusion:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_demand_interval R vs C C' h endpoint ht at done tokens registry births
    PT TG saved entries H lo P d aid b sz k v token fn bp mems observed
    rpolicy s out names w /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  max_live_eom C' = SOME eom /\
  FLOOKUP positions (Allocation aid) = SOME (pa,sz) /\
  w < EL q done /\ q < LENGTH done ==>
  pa+k NOTIN range_bytes
    (step_writes (EL q ht).po_inst (EL q ht).po_state
      (EL (SUC q) ht).po_state)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~in_revert_forward (EL (EL q done) h).po_fn
      (EL (EL q done) h).po_state` by
    (drule ptr_paired_prefix_transcript >> strip_tac >>
     drule ptr_structural_transcript_erasure >> strip_tac >>
     drule ptr_structural_trace_embedding >>
     simp[ptr_event_embedding_def, EVERY_MEM] >> strip_tac >>
     `EL q done < LENGTH h` by
       (first_x_assum irule >> simp[MEM_EL] >> qexists `q` >> simp[]) >>
     fs[ptr_demand_interval_def] >>
     qpat_x_assum `!j. w <= j /\ j < LENGTH h ==> _`
       (qspec_then `EL q done` mp_tac) >> simp[]) >>
  drule_all ptr_paired_historical_event >> strip_tac >>
  qmatch_asmsub_abbrev_tac `ptr_mixed_vars bj positions TGj aa.po_taint
    aa.po_fn tat.po_fn aa.po_state tat.po_state` >>
  `MEM aa.po_fn C.ctx_functions` by
    (fs[ptr_observation_reachable_def] >>
     drule ptr_frame_context_membership >> simp[]) >>
  `fn_ptr_ok P aa.po_fn` by
    (fs[ptr_demand_interval_def, EVERY_MEM] >> metis_tac[]) >>
  `opaque_use_ok aa.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM] >>
     metis_tac[]) >>
  `active_inst aa.po_fn aa.po_inst aa.po_state` by
    (drule (cj 1 ptr_owner_view_active) >>
     disch_then (qspec_then `LENGTH aa.po_stack` mp_tac) >>
     simp[ptr_owner_view_def]) >>
  `MEM aa.po_inst (fn_insts aa.po_fn)` by
    (fs[active_inst_def, fn_insts_def, MEM_fn_insts_blocks_iff, lookup_block_def] >>
     metis_tac[MEM_EL]) >>
  `aa.po_inst.inst_opcode <> DRET` by
    (drule_all ptr_discipline_no_dret >> simp[]) >>
  `aa.po_state.vs_labels = tat.po_state.vs_labels` by
    metis_tac[ptr_history_content_labels] >>

  `(EL (SUC (EL q done)) h).po_state.vs_returndata =
    (EL (SUC q) ht).po_state.vs_returndata` by
    (drule ptr_paired_prefix_samples >> strip_tac >>
     drule ptr_structural_transcript_erasure >> strip_tac >>
     drule_all ptr_paired_samples_post_returndata >> simp[]) >>
  spose_not_then assume_tac >>
  Cases_on `aa.po_inst.inst_opcode = ALLOCA`
  >- (qpat_x_assum `tat.po_inst = _` mp_tac >>
      simp[concretize_inst_with_positions_def] >>
      rpt BasicProvers.TOP_CASE_TAC >> strip_tac >>
      gvs[mk_assign_inst_def, mk_nop_inst_def, instruction_component_equality] >>
      fs[ptr_step_write_range, source_memory_write_ranges_def]) >>
  `tat.po_inst = aa.po_inst` by metis_tac[concretize_positions_unchanged] >>
  qpat_x_assum `tat.po_inst = concretize_inst_with_positions _ _` kall_tac >>
  gvs[] >>
  `~is_terminator aa.po_inst.inst_opcode /\ aa.po_inst.inst_opcode <> INVOKE` by
    (drule ptr_step_write_opcode >> simp[] >> strip_tac >>
     gvs[is_terminator_def]) >>
  `ptr_chrono_step C aa (EL (SUC (EL q done)) h)` by
    (drule ptr_structural_transcript_erasure >> strip_tac >>
     drule ptr_structural_trace_source >>
     disch_then (mp_tac o MATCH_MP ptr_chrono_history_adjacent) >>
     disch_then (qspec_then `EL q done` mp_tac) >> simp[Abbr `aa`]) >>
  `?fuel post. step_inst fuel C aa.po_inst aa.po_state = OK post` by
    (drule_all ptr_chrono_ordinary_step_success >> simp[]) >>
  `label_positions_ok aa.po_inst` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM,
        inst_shape_ok_def] >> metis_tac[]) >>
  `EL q done + 1 < LENGTH h` by decide_tac >>
  `LENGTH (EL (SUC (EL q done)) h).po_state.vs_returndata =
    LENGTH (EL (SUC q) ht).po_state.vs_returndata` by simp[] >>
  unabbrev_all_tac >>
  `pa+k NOTIN range_bytes (step_writes (EL (EL q done) h).po_inst
     (EL q ht).po_state (EL (SUC q) ht).po_state)` suffices_by simp[ADD_COMM] >>
  irule ptr_historical_ordinary_assembly >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  metis_tac[]
QED

Theorem ptr_structural_trace_actual_writer_retained:
  !R vs C Ct h a ht at done tokens registry births PT TG saved entries.
  ptr_structural_trace R vs C Ct h a ht at done tokens registry births PT TG saved entries ==>
  !w x. SUC w < LENGTH h /\
    x IN range_bytes (step_writes (EL w h).po_inst (EL w h).po_state
      (EL (SUC w) h).po_state) ==>
    ?q. q < LENGTH done /\ EL q done = w
Proof
  ho_match_mp_tac ptr_structural_trace_strongind >> rpt conj_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS)
  >- simp[]
  >- (rpt strip_tac >> Cases_on `SUC w < LENGTH h`
      >- (first_x_assum irule >> simp[] >> qexists `x` >> gvs[EL_APPEND_EQN]) >>
      drule ptr_structural_trace_source >>
      disch_then (mp_tac o MATCH_MP ptr_chrono_history_end) >> strip_tac >>
      `0 < LENGTH h` by (Cases_on `h` >> fs[]) >>
      `w = LENGTH h - 1 /\ w < LENGTH h` by fs[] >>
      `EL w h = a` by metis_tac[LAST_EL, PRE_SUB1] >>
      gvs[EL_APPEND_EQN, step_writes_def, source_memory_write_ranges_def,
          range_bytes_def]) >>
  rpt strip_tac >> Cases_on `SUC w < LENGTH h`
  >- (`?q. q < LENGTH done /\ EL q done = w` by
        (first_x_assum irule >> simp[] >> qexists `x` >> gvs[EL_APPEND_EQN]) >>
      qexists `q` >> simp[EL_APPEND_EQN]) >>
  qexists `LENGTH done` >> simp[EL_APPEND_EQN] >> fs[]
QED
