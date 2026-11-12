Theory concretizePtrMstoreProducer
Ancestors
  concretizePtrPairedPrefix concretizePtrPairedPrefixProbe concretizePtrStoreSteps
  concretizePtrPairedFields concretizePtrLedgerAlignment concretizeMemLocDefs
  concretizePtrExecutedCoverage concretizePtrStagePlacements concretizePtrDeletedGaps
  concretizePtrEventEmbedding
  concretizePtrOpaqueRetpc concretizePtrSharedFields concretizePtrAllocationSize
  unitShapeDefs passSimulationDefs venomExecProofs unitLabelMapIdentity
  concretizePtrTaggedSupport concretizePtrDeletedGapHistory concretizePtrLedgerProbe
  concretizePtrSourceOwnership concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrActivationChronology
  concretizePtrChronologicalHistory concretizePtrHistoricalWriteClassification
  concretizeStepStructure concretizeStepShape
  concretizeStepRetpc concretizeStageShape o1PassContract
  o1ScheduleDecomp venomWf cfgWf ptrDiscipline unitMemInv
  contextCodegenRel codegenRel memLocDefs venomExecSemantics venomState venomInst
  concretizePtrValueTransport concretizePtrPrefixLedger concretizePtrBytes
  concretizePtrComparisonTransport concretizePtrRequestHistory finite_map list arithmetic

Theorem ptr_mstore_transcript_successor:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
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
  a.po_inst.inst_opcode = MSTORE /\ ptr_chrono_step C' at zt ==>
  ?z. ptr_structural_transcript R vs C C' (h ++ [z]) z (ht ++ [zt]) zt
      (done ++ [LENGTH h - 1]) tokens registry births PT TG saved entries
      (H ++ [(tokens,registry,births,PT,TG,saved,entries)]) /\
    ptr_tagged_chrono_step C (HD tokens) a z PT TG saved PT TG saved /\
    z.po_state.vs_allocas = a.po_state.vs_allocas /\ z.po_stack = a.po_stack
Proof
  strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `MEM a.po_fn C.ctx_functions` by
    (drule_all ptr_frame_sizes >> simp[]) >>
  `inst_wf a.po_inst` by
    (gvs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, wf_function_def] >>
     `MEM a.po_inst (fn_insts a.po_fn)` by
       (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
        simp[Once frame_reachable_cases] >> rpt strip_tac >>
        gvs[active_inst_def, fn_insts_MEM] >> metis_tac[lookup_block_MEM, MEM_EL]) >>
     fs[fn_inst_wf_def, EVERY_MEM, fn_insts_MEM] >> metis_tac[]) >>
  `a.po_inst.inst_outputs = []` by gvs[inst_wf_def] >>
  `at.po_inst = a.po_inst` by
    (qpat_x_assum `ptr_paired_cursor lp a at` mp_tac >>
     simp[ptr_paired_cursor_def] >> strip_tac >>
     `a.po_state.vs_inst_idx = EL at.po_state.vs_inst_idx indices` by
       (spose_not_then assume_tac >>
        `a.po_state.vs_inst_idx < EL at.po_state.vs_inst_idx indices` by decide_tac >>
        qpat_x_assum `!k. _ ==> _.inst_opcode = NOP`
          (qspec_then `a.po_state.vs_inst_idx` mp_tac) >> simp[] >>
        qpat_x_assum `a.po_inst = _` (SUBST_ALL_TAC) >> gvs[]) >>
     drule ptr_ledger_alignment_cursor >> strip_tac >>
     first_x_assum (qspec_then `at.po_state.vs_inst_idx` mp_tac) >> simp[] >>
     strip_tac >> gvs[concretize_inst_with_positions_def]) >>
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[is_terminator_def]
  >- suspend "successor"
  >> qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac
  >> simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()]
QED

Resume ptr_mstore_transcript_successor[successor]:
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def,
    AllCaseEqs()] >> strip_tac >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
     a.po_state at.po_state /\ a.po_state.vs_labels = at.po_state.vs_labels` by
    (fs[ptr_paired_sample_def] >> metis_tac[ptr_history_content_labels]) >>
  drule_all ptr_mixed_vars_eval_presence >>
  disch_then (fn th => map_every (mp_tac o C Q.SPEC th) [`op1`,`op2`]) >>
  simp[] >> rpt strip_tac >>
  Cases_on `eval_operand op1 a.po_state` >> gvs[] >>
  Cases_on `eval_operand op2 a.po_state` >> gvs[] >>
  `?i. active_inst a.po_fn i
    (mstore (w2n x) x' a.po_state with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    suspend "source_cursor" >>
  qmatch_asmsub_abbrev_tac `active_inst a.po_fn i (post with vs_inst_idx := _)` >>
  `step_inst 0 C a.po_inst a.po_state = OK post` by
    simp[Abbr `post`, step_inst_non_invoke, step_inst_base_def, exec_write2_def] >>
  qabbrev_tac `z = ptr_ledger_next a i post` >>
  `z.po_stack = a.po_stack /\ z.po_state.vs_allocas = a.po_state.vs_allocas` by
    simp[Abbr `z`, Abbr `post`, ptr_ledger_next_def, ptr_observe_def, mstore_def] >>
  `ptr_tagged_chrono_step C (HD tokens) a z PT TG saved PT TG saved` by
    suspend "tagged_step" >>
  qexists_tac `z` >> simp[] >>
  drule ptr_ownership_overlay_fixed >> strip_tac >>
  drule (cj 3 ptr_structural_transcript_rules) >>
  disch_then drule >> disch_then drule >>
  simp[ptr_activation_tokens_def, ptr_activation_registry_def]
QED

Resume ptr_mstore_transcript_successor[source_cursor]:
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  qpat_x_assum `active_inst a.po_fn a.po_inst a.po_state` mp_tac >>
  simp[active_inst_def] >> strip_tac >>
  `bb_well_formed bb` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, wf_function_def] >> metis_tac[]) >>
  `SUC a.po_state.vs_inst_idx < LENGTH bb.bb_instructions` by
    (spose_not_then assume_tac >>
     `a.po_state.vs_inst_idx = LENGTH bb.bb_instructions - 1` by decide_tac >>
     `LAST bb.bb_instructions = a.po_inst` by
       (fs[bb_well_formed_def] >> metis_tac[LAST_EL, PRE_SUB1]) >>
     gvs[bb_well_formed_def, is_terminator_def]) >>
  simp[active_inst_def, mstore_def] >> qexists_tac `bb` >> simp[]
QED

Resume ptr_mstore_transcript_successor[tagged_step]:
  `ptr_tagged_step (HD tokens) PT TG a.po_inst post = TG` by
    simp[ptr_tagged_step_def, step_prov_def, set_prov_def, DRESTRICT_UNIV] >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE` by
    simp[is_terminator_def] >>
  drule_all (cj 1 ptr_tagged_chrono_step_rules) >> strip_tac >>
  `ptr_observe a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state = a` by
    simp[NoAsms, ptr_observe_def, ptr_observation_component_equality] >>
  fs[Abbr `z`, ptr_ledger_next_def] >> metis_tac[]
QED

Finalise ptr_mstore_transcript_successor

Theorem ptr_mstore_write_producer:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
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
  a.po_inst.inst_opcode = MSTORE /\ ptr_chrono_step C' at zt ==>
  ?z reloc.
    ptr_structural_transcript R vs C C' (h ++ [z]) z (ht ++ [zt]) zt
      (done ++ [LENGTH h - 1]) tokens registry births PT TG saved entries
      (H ++ [(tokens,registry,births,PT,TG,saved,entries)]) /\
    ptr_paired_write lo positions C C' (h ++ [z]) (ht ++ [zt])
      (done ++ [LENGTH h - 1])
      (H ++ [(tokens,registry,births,PT,TG,saved,entries)])
      (LENGTH h - 1,LENGTH done,reloc)
Proof
  strip_tac >>
  drule_all ptr_mstore_transcript_successor >> strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `MEM a.po_fn C.ctx_functions` by
    (drule_all ptr_frame_sizes >> simp[]) >>
  `~in_revert_forward a.po_fn a.po_state` by
    suspend "nonrevert" >>
  suspend "certificate"
QED

Resume ptr_mstore_write_producer[nonrevert]:
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `ALL_DISTINCT (fn_labels a.po_fn)` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >>
     metis_tac[]) >>
  qpat_x_assum `active_inst a.po_fn a.po_inst a.po_state` mp_tac >>
  simp[active_inst_def] >> strip_tac >>
  `lookup_block a.po_state.vs_current_bb a.po_fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> fs[fn_labels_def]) >>
  `get_instruction bb a.po_state.vs_inst_idx = SOME a.po_inst` by
    simp[get_instruction_def] >>
  simp[in_revert_forward_def] >> strip_tac >>
  drule_all memSafeRunTheory.revert_forward_at_opcode >> simp[]
QED

Resume ptr_mstore_write_producer[certificate]:
  `access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
   taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  `opaque_use_ok a.po_fn /\ MEM a.po_inst (fn_insts a.po_fn)` by
    suspend "shape" >>
  `EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> simp[]) >>
  `at.po_inst = a.po_inst` by
    (qpat_x_assum `ptr_paired_cursor lp a at` mp_tac >>
     simp[ptr_paired_cursor_def] >> strip_tac >>
     `a.po_state.vs_inst_idx = EL at.po_state.vs_inst_idx indices` by
       (spose_not_then assume_tac >>
        `a.po_state.vs_inst_idx < EL at.po_state.vs_inst_idx indices` by decide_tac >>
        qpat_x_assum `!k. _ ==> _.inst_opcode = NOP`
          (qspec_then `a.po_state.vs_inst_idx` mp_tac) >> simp[] >>
        qpat_x_assum `a.po_inst = _` (SUBST_ALL_TAC) >> gvs[]) >>
     drule ptr_ledger_alignment_cursor >> strip_tac >>
     first_x_assum (qspec_then `at.po_state.vs_inst_idx` mp_tac) >> simp[] >>
     strip_tac >> gvs[concretize_inst_with_positions_def]) >>
  qpat_assum `ptr_tagged_chrono_step C (HD tokens) a z PT TG saved PT TG saved` mp_tac >>
  once_rewrite_tac[ptr_tagged_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[is_terminator_def] >>
  qpat_x_assum `step_inst _ C _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()] >>
  strip_tac >>
  gvs[] >>
  `ptr_lookup_transport births positions (op_prov TG op1) (op_taint a.po_taint op1)
    (eval_operand op1 a.po_state) (eval_operand op1 at.po_state) /\
   ptr_lookup_transport births positions (op_prov TG op2) (op_taint a.po_taint op2)
    (eval_operand op2 a.po_state) (eval_operand op2 at.po_state)` by
    (conj_tac >>
     (irule ptr_mixed_vars_eval >>
      conj_tac
      >- (fs[ptr_paired_sample_def] >> metis_tac[ptr_history_content_labels]) >>
      qexistsl_tac [`a.po_fn`,`at.po_fn`] >> fs[ptr_paired_sample_def])) >>
  suspend "classified"
QED

Resume ptr_mstore_write_producer[shape]:
  conj_tac
  >- (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM] >>
      metis_tac[]) >>
  qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[Once frame_reachable_cases] >> rpt strip_tac >>
  gvs[active_inst_def, fn_insts_MEM] >> metis_tac[lookup_block_MEM, MEM_EL]
QED

Resume ptr_mstore_write_producer[classified]:
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `fn_ptr_ok P a.po_fn` by fs[EVERY_MEM] >>
  `EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, fn_inst_wf_def, EVERY_MEM,
        fn_insts_MEM] >> metis_tac[]) >>
  `EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions` by
    (fs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `!x. x IN FDOM TG ==> x IN fn_pv P a.po_fn` by
    (rpt strip_tac >>
     `?tag. FLOOKUP TG x = SOME tag` by metis_tac[FLOOKUP_DEF] >>
     drule_all ptr_source_tagged_var_support >> simp[]) >>
  `ptr_stage_placements C' positions` by fs[ptr_paired_prefix_def] >>
  qpat_assum `ptr_structural_transcript R vs C C' h a ht at done tokens registry births PT TG saved entries H`
    (mp_tac o MATCH_MP ptr_structural_transcript_endpoint) >> strip_tac >>
  `EL (LENGTH h - 1) H = (tokens,registry,births,PT,TG,saved,entries)` by
    (`H <> []` by (Cases_on `H` >> gvs[]) >>
     qpat_x_assum `LAST H = _` mp_tac >> simp[LAST_EL, PRE_SUB1]) >>
  `EL (LENGTH h - 1) h = a` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_end >> strip_tac >>
     qpat_x_assum `LAST h = a` mp_tac >> simp[LAST_EL, PRE_SUB1]) >>
  `mem_write_ops a.po_inst = SOME <|iao_ofst := op1; iao_size := SOME (Lit 32w); iao_max_size := SOME (Lit 32w)|>` by
    simp[mem_write_ops_def] >>
  `MEM (w2n addr,32) (source_memory_write_ranges a.po_inst a.po_state)` by
    simp[source_memory_write_ranges_def, fixed_source_write_range_def, mem_write_ops_def] >>
  qabbrev_tac `ops = <|iao_ofst := op1; iao_size := SOME (Lit 32w);
    iao_max_size := SOME (Lit 32w)|>` >>
  `(op_prov TG ops.iao_ofst = NONE /\
    op_taint (EL (LENGTH h - 1) h).po_taint ops.iao_ofst = {} /\ w2n addr + 32 <= lo) \/
   (?dv token bid db sb pb. ops.iao_ofst = Var dv /\ FLOOKUP TG dv = SOME (token,bid) /\
    FLOOKUP (EL (LENGTH h - 1) h).po_prov dv = SOME (db,sb) /\
    FLOOKUP positions (Allocation bid) = SOME (pb,sb) /\ db <= w2n addr /\
    w2n addr + 32 <= db+sb /\ pb+sb < dimword(:256))` by
    (irule ptr_historical_write_classification >>
     simp[Abbr `ops`] >>
     conj_tac
     >- (qexists_tac `a.po_fn` >> simp[]) >>
     rpt (goal_assum (drule_at Any)) >> simp[]) 
  >- (fs[Abbr `ops`] >> suspend "fixed") >>
  fs[Abbr `ops`] >> suspend "owned"
QED

Resume ptr_mstore_write_producer[fixed]:
  drule ptr_structural_trace_embedding >> strip_tac >>
  drule ptr_structural_trace_target >> strip_tac >>
  drule ptr_chrono_history_end >> strip_tac >>
  `SUC (LENGTH h - 1) = LENGTH h /\ SUC (LENGTH done) = LENGTH ht` by decide_tac >>
  `EL (LENGTH done) ht = at` by
    (`LENGTH ht - 1 = LENGTH done` by decide_tac >>
     qpat_x_assum `LAST ht = at` mp_tac >> simp[LAST_EL, PRE_SUB1]) >>
  qexistsl_tac [`z`,`\x:num. x`] >> simp[] >>
  simp[ptr_paired_write_def, EL_APPEND_EQN] >>
  conj_tac
  >- (simp[step_writes_def, source_memory_write_ranges_def,
        fixed_source_write_range_def, range_bytes_def, pred_setTheory.EXTENSION] >>
      qexists_tac `w2n addr` >> simp[]) >>
  reverse conj_tac
  >- (simp[ptr_paired_write_owner_def, step_writes_def,
        source_memory_write_ranges_def, fixed_source_write_range_def, range_bytes_def] >>
      rpt strip_tac >> disj1_tac >> decide_tac) >>
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality, is_terminator_def] >>
  strip_tac
  >- (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
      simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()] >>
      strip_tac >> suspend "fixed_bytes") >>
  qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()]
QED

Resume ptr_mstore_write_producer[fixed_bytes]:
  `op_prov TG op2 = NONE` by
    (drule_all concretizePtrWritePurityTheory.ptr_mstore_value_no_provenance >> simp[]) >>
  `addr' = addr /\ word_agree_except (op_taint a.po_taint op2) val val'` by
    (gvs[ptr_lookup_transport_def, ptr_value_transport_def] >>
     gvs[word_agree_except_bits, fcpTheory.CART_EQ]) >>
  `ptr_chrono_step C a z` by
    (drule ptr_tagged_chrono_step_projection >> simp[]) >>
  simp[ptr_ledger_write_pair_def, is_terminator_def] >>
  conj_tac
  >- simp[step_writes_def, source_memory_write_ranges_def,
          fixed_source_write_range_def] >>
  simp[ptr_bytes_agree_def, step_writes_def, source_memory_write_ranges_def,
       fixed_source_write_range_def, range_bytes_def, step_taint_def,
       mem_taint_def, written_taint_def] >>
  rpt strip_tac >>
  `x = w2n addr + (x - w2n addr)` by decide_tac >>
  `x - w2n addr < 32 /\ x - w2n addr NOTIN op_taint a.po_taint op2` by
    (conj_tac >- decide_tac >>
     first_x_assum (qspec_then `x - w2n addr` mp_tac) >> simp[ADD_COMM]) >>
  `EL (x - w2n addr) (word_to_bytes val T) =
   EL (x - w2n addr) (word_to_bytes val' T)` by
    metis_tac[word_agree_except_def] >>
  qpat_x_assum `mstore _ _ _ = s'` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `addr' = addr` SUBST_ALL_TAC >>
  qpat_x_assum `x = w2n addr + (x - w2n addr)` (fn th => once_rewrite_tac[th]) >>
  irule ptr_mstore_written_bytes >> simp[]
QED

Resume ptr_mstore_write_producer[owned]:
  `MEM token tokens` by
    (drule_all ptr_source_ownership_live_prov >> simp[]) >>
  `FLOOKUP births (token,bid) = SOME (db,sb)` by
    (drule_all ptr_source_ownership_prov_erases >>
     simp[ptr_ledger_erases_def] >> strip_tac >>
     first_x_assum (qspec_then `dv` mp_tac) >> gvs[]) >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  drule ptr_structural_trace_target >> strip_tac >>
  drule ptr_chrono_history_end >> strip_tac >>
  `SUC (LENGTH h - 1) = LENGTH h /\ SUC (LENGTH done) = LENGTH ht` by decide_tac >>
  `EL (LENGTH done) ht = at` by
    (`LENGTH ht - 1 = LENGTH done` by decide_tac >>
     qpat_x_assum `LAST ht = at` mp_tac >> simp[LAST_EL, PRE_SUB1]) >>
  qexistsl_tac [`z`,`\x:num. pb + (x - db)`] >> simp[] >>
  simp[ptr_paired_write_def, EL_APPEND_EQN] >>
  conj_tac
  >- (simp[step_writes_def, source_memory_write_ranges_def,
        fixed_source_write_range_def, range_bytes_def, pred_setTheory.EXTENSION] >>
      qexists_tac `w2n addr` >> simp[]) >>
  reverse conj_tac
  >- (simp[ptr_paired_write_owner_def, step_writes_def,
        source_memory_write_ranges_def, fixed_source_write_range_def, range_bytes_def] >>
      rpt strip_tac >> disj2_tac >>
      qexistsl_tac [`token`,`bid`,`db`,`sb`,`pb`,`x-db`] >> simp[] >> decide_tac) >>
  suspend "owned_ledger"
QED

Resume ptr_mstore_write_producer[owned_ledger]:
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality, is_terminator_def] >>
  strip_tac
  >- (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
      simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()] >>
      strip_tac >> suspend "owned_bytes") >>
  qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()]
QED

Resume ptr_mstore_write_producer[owned_bytes]:
  `op_prov TG op2 = NONE` by
    (drule_all concretizePtrWritePurityTheory.ptr_mstore_value_no_provenance >> simp[]) >>
  `addr' = addr - n2w db + n2w pb /\
   word_agree_except (op_taint a.po_taint op2) val val'` by
    gvs[ptr_lookup_transport_def, ptr_value_transport_def, op_prov_def] >>
  `w2n addr' = pb + (w2n addr - db)` by
    (irule ptr_closed_relocation_value >> simp[] >> qexists_tac `sb` >> simp[] >> decide_tac) >>
  qpat_x_assum `addr' = addr - n2w db + n2w pb` kall_tac >>
  `ptr_chrono_step C a z` by
    (drule ptr_tagged_chrono_step_projection >> simp[]) >>
  simp[ptr_ledger_write_pair_def, is_terminator_def] >>
  conj_tac
  >- (simp[step_writes_def, source_memory_write_ranges_def,
           fixed_source_write_range_def, range_bytes_def] >>
      rpt strip_tac >> decide_tac) >>
  simp[ptr_bytes_agree_def, step_writes_def, source_memory_write_ranges_def,
       fixed_source_write_range_def, range_bytes_def, step_taint_def,
       mem_taint_def, written_taint_def] >>
  rpt strip_tac >>
  `x = w2n addr + (x - w2n addr)` by decide_tac >>
  `x - w2n addr < 32 /\ x - w2n addr NOTIN op_taint a.po_taint op2` by
    (conj_tac >- decide_tac >>
     first_x_assum (qspec_then `x - w2n addr` mp_tac) >> simp[ADD_COMM]) >>
  `EL (x - w2n addr) (word_to_bytes val T) =
   EL (x - w2n addr) (word_to_bytes val' T)` by
    metis_tac[word_agree_except_def] >>
  `pb + x - db = w2n addr' + (x - w2n addr)` by decide_tac >>
  qpat_x_assum `mstore _ _ _ = s'` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `pb + x - db = _` (fn th => once_rewrite_tac[th]) >>
  qpat_x_assum `x = w2n addr + (x - w2n addr)`
    (fn th => CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [th]))) >>
  irule ptr_mstore_written_bytes >> simp[]
QED

Finalise ptr_mstore_write_producer

Theorem ptr_paired_prefix_mstore:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
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
  a.po_inst.inst_opcode = MSTORE /\ ptr_chrono_step C' at zt ==>
  ?z reloc. ptr_paired_prefix R lp positions lo vs C C'
    (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
    tokens registry births PT TG saved entries
    (H ++ [(tokens,registry,births,PT,TG,saved,entries)]) calls
    (ws ++ [(LENGTH h - 1,LENGTH done,reloc)])
Proof
  strip_tac >> drule_all ptr_mstore_write_producer >> strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_structural_trace_target >> strip_tac >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  `LAST h = a /\ LAST ht = at /\ 0 < LENGTH h /\ LENGTH ht = SUC (LENGTH done)` by
    (imp_res_tac ptr_chrono_history_end >>
     fs[ptr_paired_prefix_def, ptr_paired_samples_def, ptr_sample_list_def]) >>
  `EL (LENGTH h - 1) h = a /\ EL (LENGTH done) ht = at` by
    (`h <> [] /\ ht <> []` by
       (conj_tac >> strip_tac >> gvs[]) >>
     conj_tac
     >- (qpat_x_assum `LAST h = a` mp_tac >> simp[LAST_EL, PRE_SUB1]) >>
     `LENGTH ht - 1 = LENGTH done` by decide_tac >>
     qpat_x_assum `LAST ht = at` mp_tac >> simp[LAST_EL, PRE_SUB1]) >>
  `SUC (LENGTH h - 1) = LENGTH h` by decide_tac >>
  `ptr_ledger_write_pair C C' reloc a z at zt` by
    (qpat_assum `ptr_paired_write _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ptr_paired_write_def]) >>
     gvs[EL_APPEND_EQN]) >>
  `at.po_inst = a.po_inst` by
    (qpat_x_assum `ptr_paired_cursor lp a at` mp_tac >>
     simp[ptr_paired_cursor_def] >> strip_tac >>
     `a.po_state.vs_inst_idx = EL at.po_state.vs_inst_idx indices` by
       (spose_not_then assume_tac >>
        `a.po_state.vs_inst_idx < EL at.po_state.vs_inst_idx indices` by decide_tac >>
        qpat_x_assum `!k. _ ==> _.inst_opcode = NOP`
          (qspec_then `a.po_state.vs_inst_idx` mp_tac) >> simp[] >>
        qpat_x_assum `a.po_inst = _` SUBST_ALL_TAC >> gvs[]) >>
     drule ptr_ledger_alignment_cursor >> strip_tac >>
     first_x_assum (qspec_then `at.po_state.vs_inst_idx` mp_tac) >> simp[] >>
     strip_tac >> gvs[concretize_inst_with_positions_def]) >>
  `a.po_inst.inst_outputs = [] /\ ALL_DISTINCT (fn_labels a.po_fn)` by
    (`frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
        a.po_fn a.po_inst a.po_state` by
       (qpat_x_assum `ptr_chrono_history vs C' ht at` kall_tac >>
        drule ptr_chrono_history_reachable >>
        simp[ptr_observation_reachable_def]) >>
     `MEM a.po_fn C.ctx_functions` by (drule_all ptr_frame_sizes >> simp[]) >>
     `MEM a.po_inst (fn_insts a.po_fn)` by
       (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
        simp[Once frame_reachable_cases] >> rpt strip_tac >>
        gvs[active_inst_def, fn_insts_MEM] >> metis_tac[lookup_block_MEM, MEM_EL]) >>
     `inst_wf a.po_inst` by
       (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, wf_function_def,
           fn_inst_wf_def, fn_insts_MEM] >> metis_tac[]) >>
     gvs[inst_wf_def, o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, wf_function_def] >>
     metis_tac[]) >>
  `ALL_DISTINCT (fn_labels at.po_fn)` by
    (fs[ptr_paired_code_def] >>
     metis_tac[fn_labels_def, concretize_positions_labels]) >>
  `!i. MEM i (fn_insts a.po_fn) /\ i.inst_opcode = ALLOCA ==>
       ?p. FLOOKUP (lp a.po_fn) (Allocation i.inst_id) = SOME p` by
    (rpt strip_tac >>
     `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
        a.po_fn a.po_inst a.po_state` by
       (qpat_x_assum `ptr_chrono_history vs C' ht at` kall_tac >>
        drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
     `MEM a.po_fn C.ctx_functions` by (drule_all ptr_frame_sizes >> simp[]) >>
     drule_all ptr_stage_alloca_mems >> strip_tac >>
     `MEM g C'.ctx_functions` by metis_tac[lookup_function_MEM] >>
     `FLOOKUP positions (Allocation i.inst_id) =
       SOME (p,get_alloca_size a.po_fn (Allocation i.inst_id))` by
       (fs[ptr_paired_prefix_def, ptr_stage_placements_def] >> metis_tac[]) >>
     fs[ptr_paired_code_def, fn_insts_MEM] >>
     qpat_x_assum `!bb inst. _` (qspecl_then [`bb`,`i`] mp_tac) >> simp[]) >>
  qexistsl_tac [`z`,`reloc`] >>
  qpat_x_assum `ptr_paired_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ptr_paired_prefix_def]) >>
  rewrite_tac[ptr_paired_prefix_def] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "sample" >>
  conj_tac >- suspend "alignment" >>
  conj_tac >- suspend "callers" >>
  suspend "writes"
QED

Resume ptr_paired_prefix_mstore[sample]:
  irule ptr_paired_samples_pair >> simp[] >>
  `ptr_chrono_step C a z` by fs[ptr_ledger_write_pair_def] >>
  qpat_x_assum `ptr_chrono_step C a z` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality, is_terminator_def] >>
  strip_tac
  >- (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
      simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()] >>
      strip_tac >> suspend "sample_target") >>
  qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()]
QED
Resume ptr_paired_prefix_mstore[sample_target]:
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality, is_terminator_def] >>
  strip_tac
  >- (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
      simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()] >>
      strip_tac >>
      fs[ptr_paired_sample_def] >>
      simp[ptr_paired_sample_def] >> reverse conj_tac
      >- (gvs[mstore_def] >> irule ptr_history_content_masks >>
          qexists_tac `(LAST h).po_taint` >>
          simp[step_taint_def, set_var_taint_def, adopt_reset_def,
               store_taint_def, imm_taint_def]) >>
      gvs[ptr_mixed_vars_def, ptr_opaque_env_def, step_taint_def,
          op_taint_def, lookup_var_def, mstore_def, set_var_taint_def,
          DRESTRICT_UNIV] >> metis_tac[]) >>
  qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()]
QED
Resume ptr_paired_prefix_mstore[alignment]:
  `ptr_chrono_step C a z` by fs[ptr_ledger_write_pair_def] >>
  qpat_x_assum `ptr_chrono_step C a z` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality, is_terminator_def] >>
  strip_tac
  >- (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
      simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()] >>
      strip_tac >> suspend "alignment_target") >>
  qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()]
QED
Resume ptr_paired_prefix_mstore[alignment_target]:
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality, is_terminator_def] >>
  strip_tac
  >- (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
      simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()] >>
      strip_tac >>
      irule ptr_paired_alignment_pair >> simp[] >>
      reverse conj_tac >- gvs[ptr_paired_params_def, mstore_def] >>
      gvs[ptr_paired_cursor_def, mstore_def] >> suspend "cursor") >>
  qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()]
QED
Resume ptr_paired_prefix_mstore[cursor]:
  `SUC (LAST h).po_state.vs_inst_idx < LENGTH bb.bb_instructions /\
   z.po_inst = EL (SUC (LAST h).po_state.vs_inst_idx) bb.bb_instructions` by
    (qpat_assum `active_inst _ z.po_inst _` mp_tac >>
     qpat_assum `lookup_block _ (LAST h).po_fn.fn_blocks = SOME bb` mp_tac >>
     qpat_assum `(LAST h).po_state.vs_current_bb = (LAST ht).po_state.vs_current_bb` mp_tac >>
     qpat_assum `ALL_DISTINCT (fn_labels (LAST h).po_fn)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[active_inst_def, fn_labels_def] >> rpt strip_tac >>
     rename1 `MEM nextbb (LAST h).po_fn.fn_blocks` >>
     `lookup_block (LAST ht).po_state.vs_current_bb (LAST h).po_fn.fn_blocks = SOME nextbb` by
       (irule MEM_lookup_block >> simp[]) >> gvs[]) >>
  `SUC (LAST ht).po_state.vs_inst_idx < LENGTH bbt.bb_instructions /\
   zt.po_inst = EL (SUC (LAST ht).po_state.vs_inst_idx) bbt.bb_instructions` by
    (qpat_assum `active_inst _ zt.po_inst _` mp_tac >>
     qpat_assum `lookup_block _ (LAST ht).po_fn.fn_blocks = SOME bbt` mp_tac >>
     qpat_assum `ALL_DISTINCT (fn_labels (LAST ht).po_fn)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[active_inst_def, fn_labels_def] >> rpt strip_tac >>
     rename1 `MEM nextbb (LAST ht).po_fn.fn_blocks` >>
     `lookup_block (LAST ht).po_state.vs_current_bb (LAST ht).po_fn.fn_blocks = SOME nextbb` by
       (irule MEM_lookup_block >> simp[]) >> gvs[]) >>
  suspend "cursor_order"
QED
Resume ptr_paired_prefix_mstore[cursor_order]:
  ` (LAST h).po_state.vs_inst_idx = EL (LAST ht).po_state.vs_inst_idx indices` by
    (spose_not_then assume_tac >>
     ` (LAST h).po_state.vs_inst_idx < EL (LAST ht).po_state.vs_inst_idx indices` by decide_tac >>
     qpat_x_assum `!k. _ ==> _.inst_opcode = NOP`
       (qspec_then `(LAST h).po_state.vs_inst_idx` mp_tac) >> simp[]) >>
  `LENGTH bbt.bb_instructions = LENGTH indices` by
    (drule ptr_ledger_alignment_cursor >> simp[]) >>
  `SUC (LAST ht).po_state.vs_inst_idx < LENGTH indices` by decide_tac >>
  `EL (LAST ht).po_state.vs_inst_idx indices <
   EL (SUC (LAST ht).po_state.vs_inst_idx) indices` by
    (qpat_assum `ptr_ledger_block_alignment _ _ _ indices` mp_tac >>
     qpat_assum `SUC (LAST ht).po_state.vs_inst_idx < LENGTH indices` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     irule ptr_ledger_alignment_order >> simp[] >>
     qexistsl_tac [`lp (LAST h).po_fn`,`bb.bb_instructions`,`bbt.bb_instructions`] >> simp[]) >>
  qexists_tac `indices` >> simp[] >>
  rpt strip_tac >>
  ` (concretize_inst_with_positions (lp (LAST h).po_fn)
      (EL k bb.bb_instructions)).inst_opcode = NOP` by
    (irule ptr_ledger_alignment_gap >>
     qexistsl_tac [`indices`,`SUC (LAST ht).po_state.vs_inst_idx`,`bbt.bb_instructions`] >>
     simp[] >> decide_tac) >>
  `k < LENGTH bb.bb_instructions` by
    (drule ptr_ledger_alignment_cursor >> strip_tac >>
     `EL (SUC (LAST ht).po_state.vs_inst_idx) indices < LENGTH bb.bb_instructions` by
       (qpat_x_assum `!j. j < LENGTH bbt.bb_instructions ==> _`
          (qspec_then `SUC (LAST ht).po_state.vs_inst_idx` mp_tac) >> simp[]) >> decide_tac) >>
  drule_all ptr_positioned_block_nop_iff >> simp[]
QED
Resume ptr_paired_prefix_mstore[callers]:
  `z.po_stack = a.po_stack /\ zt.po_stack = at.po_stack` by
    (`ptr_chrono_step C a z` by fs[ptr_ledger_write_pair_def] >>
     conj_tac
     >- (qpat_x_assum `ptr_chrono_step C a z` mp_tac >>
         once_rewrite_tac[ptr_chrono_step_cases] >>
         simp[ptr_observe_def, ptr_observation_component_equality, is_terminator_def] >>
         rpt strip_tac >>
         gvs[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()]) >>
     qpat_x_assum `ptr_chrono_step C' at zt` mp_tac >>
     once_rewrite_tac[ptr_chrono_step_cases] >>
     simp[ptr_observe_def, ptr_observation_component_equality, is_terminator_def] >>
     rpt strip_tac >>
     gvs[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()]) >>
  irule ptr_paired_callers_retained >> simp[] >>
  conj_tac >- fs[ptr_paired_samples_def, ptr_sample_list_def] >>
  fs[ptr_event_embedding_def, EVERY_EL] >>
  qexistsl_tac [`a`,`at`] >> simp[]
QED
Resume ptr_paired_prefix_mstore[writes]:
  drule ptr_structural_transcript_erasure >> strip_tac >>
  `EVERY (\n. SUC n < LENGTH h) done` by
    (qpat_assum `ptr_event_embedding h ht (done ++ _)` mp_tac >>
     qpat_assum `SUC (LENGTH h - 1) = LENGTH h` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     simp[ptr_event_embedding_def, EVERY_EL] >> strip_tac >>
     gen_tac >> strip_tac >>
     qpat_x_assum `!i j. _` (qspecl_then [`n`,`LENGTH done`] mp_tac) >>
     simp[EL_APPEND_EQN] >> decide_tac) >>
  irule ptr_paired_writes_pair >>
  gvs[ptr_paired_samples_def, ptr_sample_list_def] >> metis_tac[]
QED
Finalise ptr_paired_prefix_mstore
