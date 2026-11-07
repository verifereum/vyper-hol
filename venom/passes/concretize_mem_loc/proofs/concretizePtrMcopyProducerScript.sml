Theory concretizePtrMcopyProducer
Ancestors concretizePtrMcopyContent concretizePtrMcopyEndpoint concretizePtrOrdinaryNext
  concretizePtrMstoreProducer concretizePtrHistoricalWriteClassification
  concretizePtrPairedPrefix concretizePtrPairedFields concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrSourceOwnership concretizePtrChronologicalHistory
  concretizePtrActivationChronology concretizePtrDeletedGapHistory
  concretizePtrTaggedSupport concretizePtrLedgerProbe concretizePtrPrefixLedger
  concretizePtrStagePlacements concretizePtrSharedFields concretizePtrOpaqueRetpc
  concretizePtrAllocationSize concretizePtrPairedNextAttach
  concretizePtrValueTransport concretizePtrBytes concretizePtrComparisonTransport
  concretizeMemLocDefs stackPlanGen stackPlanTypes ptrDiscipline o1PassContract
  unitShapeDefs unitLabelMapIdentity venomWf cfgWf o1ScheduleDecomp unitMemInv contextCodegenRel codegenRel memLocDefs
  venomExecSemantics venomExecProofs venomState venomInst passSimulationDefs
  finite_map words list arithmetic

Theorem ptr_mcopy_transcript_successor:
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
  max_live_eom C' = SOME eom /\
  a.po_inst.inst_opcode = MCOPY /\ ptr_chrono_step C' at zt ==>
  ?z. ptr_structural_transcript R vs C C' (h ++ [z]) z (ht ++ [zt]) zt
      (done ++ [LENGTH h - 1]) tokens registry births PT TG saved entries
      (H ++ [(tokens,registry,births,PT,TG,saved,entries)]) /\
    ptr_tagged_chrono_step C (HD tokens) a z PT TG saved PT TG saved /\
    z.po_state.vs_allocas = a.po_state.vs_allocas /\ z.po_stack = a.po_stack
Proof
  strip_tac >> drule_all ptr_paired_mcopy_postwrite_bytes >> strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `MEM a.po_fn C.ctx_functions` by (drule_all ptr_frame_sizes >> simp[]) >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
  `inst_wf a.po_inst` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, fn_inst_wf_def,
        EVERY_MEM, fn_insts_MEM] >> metis_tac[]) >>
  `a.po_inst.inst_outputs = []` by gvs[inst_wf_def] >>
  `EVERY bb_well_formed a.po_fn.fn_blocks` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  `?i. active_inst a.po_fn i
      (mcopy (w2n d) (w2n r) (w2n n) a.po_state with
        vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (qpat_assum `active_inst a.po_fn a.po_inst a.po_state`
       (mp_then Any mp_tac ptr_ordinary_next_active) >>
     disch_then irule >> simp[mcopy_def, write_memory_with_expansion_def, is_terminator_def]) >>
  qabbrev_tac `post = mcopy (w2n d) (w2n r) (w2n n) a.po_state` >>
  qabbrev_tac `z = ptr_ledger_next a i post` >>
  `z.po_stack = a.po_stack /\ z.po_state.vs_allocas = a.po_state.vs_allocas` by
    simp[Abbr `z`, Abbr `post`, ptr_ledger_next_def, ptr_observe_def, mcopy_def] >>
  `ptr_tagged_chrono_step C (HD tokens) a z PT TG saved PT TG saved` by
    ( `ptr_tagged_step (HD tokens) PT TG a.po_inst post = TG` by
        simp[ptr_tagged_step_def, step_prov_def, set_prov_def, DRESTRICT_UNIV] >>
      `~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE` by
        simp[is_terminator_def] >>
      `step_inst 0 C a.po_inst a.po_state = OK post` by simp[Abbr `post`] >>
      drule_all (cj 1 ptr_tagged_chrono_step_rules) >> strip_tac >>
      `ptr_observe a.po_stack a.po_params a.po_prov a.po_taint
        a.po_fn a.po_inst a.po_state = a` by
        simp[NoAsms, ptr_observe_def, ptr_observation_component_equality] >>
      fs[Abbr `z`, ptr_ledger_next_def] >> metis_tac[]) >>
  `zt.po_stack = at.po_stack` by
    (qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
     once_rewrite_tac[ptr_chrono_step_cases] >>
     simp[ptr_observe_def, ptr_observation_component_equality, is_terminator_def] >>
     strip_tac >>
     qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
     simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()]) >>
  qexists_tac `z` >> simp[] >>
  drule ptr_ownership_overlay_fixed >> strip_tac >>
  drule (cj 3 ptr_structural_transcript_rules) >>
  disch_then drule >> disch_then drule >>
  simp[ptr_activation_tokens_def, ptr_activation_registry_def]
QED

Theorem ptr_mcopy_write_producer:
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
  max_live_eom C' = SOME eom /\
  a.po_inst.inst_opcode = MCOPY /\ ptr_chrono_step C' at zt ==>
  ?z dop sop nop d r dt rt n.
    a.po_inst.inst_operands = [dop;sop;nop] /\ at.po_inst = a.po_inst /\
    eval_operand dop a.po_state = SOME d /\
    eval_operand sop a.po_state = SOME r /\
    eval_operand nop a.po_state = SOME n /\
    eval_operand dop at.po_state = SOME dt /\
    eval_operand sop at.po_state = SOME rt /\
    eval_operand nop at.po_state = SOME n /\
    ptr_tagged_chrono_step C (HD tokens) a z PT TG saved PT TG saved /\
    ptr_structural_transcript R vs C C' (h ++ [z]) z (ht ++ [zt]) zt
      (done ++ [LENGTH h - 1]) tokens registry births PT TG saved entries
      (H ++ [(tokens,registry,births,PT,TG,saved,entries)]) /\
    (w2n n = 0 ==>
      range_bytes (step_writes a.po_inst a.po_state z.po_state) = {} /\
      range_bytes (step_writes at.po_inst at.po_state zt.po_state) = {}) /\
    (range_bytes (step_writes a.po_inst a.po_state z.po_state) <> {} ==>
      ?rho. ptr_paired_write lo positions C C' (h ++ [z]) (ht ++ [zt])
        (done ++ [LENGTH h - 1])
        (H ++ [(tokens,registry,births,PT,TG,saved,entries)])
        (LENGTH h - 1,LENGTH ht - 1,rho))
Proof
  strip_tac >> drule_all ptr_mcopy_transcript_successor >> strip_tac >>
  drule_all ptr_paired_mcopy_postwrite_bytes >> strip_tac >>
  qexistsl_tac [`z`,`dop`,`sop`,`nop`,`d`,`r`,`dt`,`rt`,`n`] >> simp[] >>
  conj_tac
  >- (simp[step_writes_def, source_memory_write_ranges_def,
        fixed_source_write_range_def, sized_source_write_range_def, mem_write_ops_def, range_bytes_def,
        pred_setTheory.EXTENSION]) >>
  strip_tac >> suspend "certificate"
QED

Resume ptr_mcopy_write_producer[certificate]:
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `MEM a.po_fn C.ctx_functions` by (drule_all ptr_frame_sizes >> simp[]) >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `~in_revert_forward a.po_fn a.po_state` by
    ( `ALL_DISTINCT (fn_labels a.po_fn)` by
        (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
      qpat_x_assum `active_inst a.po_fn a.po_inst a.po_state` mp_tac >>
      simp[active_inst_def] >> strip_tac >>
      `lookup_block a.po_state.vs_current_bb a.po_fn.fn_blocks = SOME bb` by
        (irule MEM_lookup_block >> fs[fn_labels_def]) >>
      `get_instruction bb a.po_state.vs_inst_idx = SOME a.po_inst` by
        simp[get_instruction_def] >>
      simp[in_revert_forward_def] >> strip_tac >>
      drule_all memSafeRunTheory.revert_forward_at_opcode >> simp[]) >>
  `ptr_chrono_step C a z` by
    (drule ptr_tagged_chrono_step_projection >> simp[]) >>
  `z.po_state = (mcopy (w2n d) (w2n r) (w2n n) a.po_state with
       vs_inst_idx := SUC a.po_state.vs_inst_idx) /\
   z.po_taint = step_taint a.po_inst a.po_state
       (mcopy (w2n d) (w2n r) (w2n n) a.po_state) a.po_taint` by
    (qpat_assum `ptr_chrono_step C a z` mp_tac >>
     once_rewrite_tac[ptr_chrono_step_cases] >>
     simp[ptr_observe_def, ptr_observation_component_equality, is_terminator_def] >>
     strip_tac >>
     qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     simp[step_inst_non_invoke, step_inst_base_def] >> strip_tac >> gvs[]) >>
  `zt.po_state = (mcopy (w2n dt) (w2n rt) (w2n n) at.po_state with
       vs_inst_idx := SUC at.po_state.vs_inst_idx)` by
    (qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
     once_rewrite_tac[ptr_chrono_step_cases] >>
     simp[ptr_observe_def, ptr_observation_component_equality, is_terminator_def] >>
     strip_tac >>
     qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     simp[step_inst_non_invoke, step_inst_base_def] >> strip_tac >> gvs[]) >>
  `!j. j < w2n n /\ w2n d+j NOTIN z.po_taint.t_mem ==>
     read_byte (w2n d+j) z.po_state.vs_memory =
     read_byte (w2n dt+j) zt.po_state.vs_memory` by
    (qpat_x_assum `!post postt. _`
       (qspecl_then [`mcopy (w2n d) (w2n r) (w2n n) a.po_state`,
                     `mcopy (w2n dt) (w2n rt) (w2n n) at.po_state`] mp_tac) >>
     simp[step_inst_base_def, step_taint_def]) >>
  suspend "classify"
QED

Resume ptr_mcopy_write_producer[classify]:
  `access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
   taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `fn_ptr_ok P a.po_fn` by fs[EVERY_MEM] >>
  `EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, fn_inst_wf_def,
        EVERY_MEM, fn_insts_MEM] >> metis_tac[]) >>
  `EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions` by
    (fs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `!x. x IN FDOM TG ==> x IN fn_pv P a.po_fn` by
    (rpt strip_tac >>
     `?tag. FLOOKUP TG x = SOME tag` by metis_tac[FLOOKUP_DEF] >>
     drule_all ptr_source_tagged_var_support >> simp[]) >>
  `opaque_use_ok a.po_fn /\ MEM a.po_inst (fn_insts a.po_fn)` by
    (conj_tac
     >- (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM] >> metis_tac[]) >>
     fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
  `EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> simp[]) >>
  `ptr_nonopaque_operand a.po_fn dop` by
    (qpat_x_assum `EVERY (ptr_nonopaque_operand _) _` mp_tac >> simp[]) >>
  `ptr_lookup_transport births positions (op_prov TG dop) (op_taint a.po_taint dop)
     (SOME d) (SOME dt)` by
    ( `ptr_lookup_transport births positions (op_prov TG dop) (op_taint a.po_taint dop)
        (eval_operand dop a.po_state) (eval_operand dop at.po_state)` suffices_by simp[] >>
      irule ptr_mixed_vars_eval >> conj_tac
      >- fs[ptr_paired_sample_def, ptr_core_shared_def, ptr_shared_fields_def] >>
      qexistsl_tac [`a.po_fn`,`at.po_fn`] >> fs[ptr_paired_sample_def]) >>
  `0 < LENGTH h` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_end >> strip_tac >> Cases_on `h` >> gvs[]) >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  drule ptr_structural_trace_target >> strip_tac >>
  drule ptr_chrono_history_end >> strip_tac >>
  `SUC (LENGTH h - 1) = LENGTH h /\ SUC (LENGTH done) = LENGTH ht /\
   LENGTH ht - 1 = LENGTH done` by decide_tac >>
  `EL (LENGTH done) ht = at` by
    (qpat_x_assum `LAST ht = at` mp_tac >> simp[LAST_EL, PRE_SUB1]) >>
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
  `0 < w2n n` by
    (qpat_x_assum `range_bytes _ <> {}` mp_tac >>
     simp[step_writes_def, source_memory_write_ranges_def, sized_source_write_range_def,
       range_bytes_def, pred_setTheory.EXTENSION] >> metis_tac[]) >>
  `n <> 0w` by (strip_tac >> gvs[]) >>
  qabbrev_tac `ops = <|iao_ofst := dop; iao_size := SOME nop; iao_max_size := SOME nop|>` >>
  `(op_prov TG ops.iao_ofst = NONE /\
    op_taint (EL (LENGTH h - 1) h).po_taint ops.iao_ofst = {} /\ w2n d + w2n n <= lo) \/
   (?dv token bid db sb pb. ops.iao_ofst = Var dv /\ FLOOKUP TG dv = SOME (token,bid) /\
    FLOOKUP (EL (LENGTH h - 1) h).po_prov dv = SOME (db,sb) /\
    FLOOKUP positions (Allocation bid) = SOME (pb,sb) /\ db <= w2n d /\
    w2n d + w2n n <= db+sb /\ pb+sb < dimword(:256))` by
    (irule (Q.INST [`ops` |-> `ops`] (SPEC_ALL ptr_historical_write_classification)) >>
     simp[Abbr `ops`, mem_write_ops_def, source_memory_write_ranges_def,
       sized_source_write_range_def] >>
     conj_tac >- (qexists_tac `a.po_fn` >> simp[]) >>
     rpt (goal_assum (drule_at Any)) >> simp[])
  >- suspend "fixed" >>
  suspend "owned"
QED

Resume ptr_mcopy_write_producer[fixed]:
  fs[Abbr `ops`] >>
  `SUC (LENGTH h - 1) = LENGTH h` by decide_tac >>
  `dt = d` by
    (gvs[ptr_lookup_transport_def, ptr_value_transport_def] >>
     gvs[word_agree_except_bits, fcpTheory.CART_EQ]) >>
  qexists_tac `\x:num. x` >>
  simp[ptr_paired_write_def, EL_APPEND_EQN] >>
  reverse conj_tac
  >- (simp[ptr_paired_write_owner_def, step_writes_def, source_memory_write_ranges_def,
        sized_source_write_range_def, range_bytes_def] >> rpt strip_tac >>
      disj1_tac >> decide_tac) >>
  simp[ptr_ledger_write_pair_def, is_terminator_def, ptr_bytes_agree_def,
       step_writes_def, source_memory_write_ranges_def, sized_source_write_range_def,
       range_bytes_def] >>
  rpt strip_tac >>
  `x = w2n d + (x - w2n d) /\ x - w2n d < w2n n` by decide_tac >>
  qpat_x_assum `!j. j < w2n n /\ _ ==> _` (qspec_then `x-w2n d` mp_tac) >>
  simp[ADD_COMM]
QED

Resume ptr_mcopy_write_producer[owned]:
  fs[Abbr `ops`] >>
  `SUC (LENGTH h - 1) = LENGTH h` by decide_tac >>
  `MEM token tokens` by
    (drule_all ptr_source_ownership_live_prov >> simp[]) >>
  `FLOOKUP births (token,bid) = SOME (db,sb)` by
    (drule_all ptr_source_ownership_prov_erases >>
     simp[ptr_ledger_erases_def] >> strip_tac >>
     first_x_assum (qspec_then `dv` mp_tac) >> gvs[]) >>
  `dt = d - n2w db + n2w pb` by
    gvs[ptr_lookup_transport_def, ptr_value_transport_def, op_prov_def] >>
  `w2n dt = pb + (w2n d - db)` by
    (irule ptr_closed_relocation_value >> simp[] >> qexists_tac `sb` >> simp[] >> decide_tac) >>
  qpat_x_assum `dt = d - n2w db + n2w pb` kall_tac >>
  qexists_tac `\x:num. pb + (x-db)` >>
  simp[ptr_paired_write_def, EL_APPEND_EQN] >>
  reverse conj_tac
  >- (simp[ptr_paired_write_owner_def, step_writes_def, source_memory_write_ranges_def,
        sized_source_write_range_def, range_bytes_def] >> rpt strip_tac >>
      disj2_tac >> qexistsl_tac [`token`,`bid`,`db`,`sb`,`pb`,`x-db`] >> simp[] >> decide_tac) >>
  simp[ptr_ledger_write_pair_def, is_terminator_def] >>
  conj_tac
  >- (simp[step_writes_def, source_memory_write_ranges_def, sized_source_write_range_def,
        range_bytes_def] >> rpt strip_tac >> decide_tac) >>
  simp[ptr_bytes_agree_def, step_writes_def, source_memory_write_ranges_def,
       sized_source_write_range_def, range_bytes_def] >>
  rpt strip_tac >>
  `x = w2n d + (x - w2n d) /\ x - w2n d < w2n n /\
   pb + (x-db) = w2n dt + (x-w2n d)` by decide_tac >>
  qpat_x_assum `!j. j < w2n n /\ _ ==> _` (qspec_then `x-w2n d` mp_tac) >>
  simp[ADD_COMM]
QED

Finalise ptr_mcopy_write_producer

Theorem ptr_paired_prefix_mcopy:
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
  max_live_eom C' = SOME eom /\
  a.po_inst.inst_opcode = MCOPY /\ ptr_chrono_step C' at zt ==>
  ?z extra. ptr_paired_prefix R lp positions lo vs C C'
    (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
    tokens registry births PT TG saved entries
    (H ++ [(tokens,registry,births,PT,TG,saved,entries)]) calls (ws ++ extra) /\
    (range_bytes (step_writes a.po_inst a.po_state z.po_state) = {} ==> extra = []) /\
    (range_bytes (step_writes a.po_inst a.po_state z.po_state) <> {} ==>
      ?rho. extra = [(LENGTH h - 1,LENGTH done,rho)])
Proof
  strip_tac >> drule_all ptr_mcopy_write_producer >> strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  `ptr_chrono_step C a z` by
    (drule ptr_tagged_chrono_step_projection >> simp[]) >>
  `z.po_fn = a.po_fn /\ z.po_stack = a.po_stack /\
   z.po_params = a.po_params /\
   z.po_state = (mcopy (w2n d) (w2n r) (w2n n) a.po_state with
     vs_inst_idx := SUC a.po_state.vs_inst_idx) /\
   z.po_taint = step_taint a.po_inst a.po_state
     (mcopy (w2n d) (w2n r) (w2n n) a.po_state) a.po_taint /\
   active_inst z.po_fn z.po_inst z.po_state` by
    (qpat_assum `ptr_chrono_step C a z` mp_tac >>
     once_rewrite_tac[ptr_chrono_step_cases] >>
     simp[ptr_observe_def, ptr_observation_component_equality, is_terminator_def] >>
     strip_tac >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     simp[step_inst_non_invoke] >>
     PURE_REWRITE_TAC[step_inst_base_def] >>
     ASM_REWRITE_TAC[] >> simp[Once opcode_case_def] >> strip_tac >> gvs[]) >>
  `zt.po_fn = at.po_fn /\ zt.po_stack = at.po_stack /\
   zt.po_state = (mcopy (w2n dt) (w2n rt) (w2n n) at.po_state with
     vs_inst_idx := SUC at.po_state.vs_inst_idx) /\
   active_inst zt.po_fn zt.po_inst zt.po_state` by
    (qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
     once_rewrite_tac[ptr_chrono_step_cases] >>
     simp[ptr_observe_def, ptr_observation_component_equality, is_terminator_def] >>
     strip_tac >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     simp[step_inst_non_invoke] >>
     PURE_REWRITE_TAC[step_inst_base_def] >>
     ASM_REWRITE_TAC[] >> simp[Once opcode_case_def] >> strip_tac >> gvs[]) >>
  `ptr_paired_sample positions z zt (tokens,registry,births,PT,TG,saved,entries)` by
    suspend "sample" >>
  `ptr_paired_params positions z zt (tokens,registry,births,PT,TG,saved,entries)` by
    gvs[ptr_paired_params_def, mcopy_def, write_memory_with_expansion_def] >>
  `ptr_paired_code R lp positions z.po_fn zt.po_fn` by simp[] >>
  `ptr_paired_cursor lp z zt` by suspend "cursor" >>
  Cases_on `range_bytes (step_writes a.po_inst a.po_state z.po_state) = {}`
  >- (qexistsl_tac [`z`,`[]`] >> simp[] >>
      drule ptr_paired_prefix_nonwrite_attach >> disch_then irule >> simp[]) >>
  first_x_assum drule >> disch_then (qx_choose_then `reloc` assume_tac) >>
  qexistsl_tac [`z`,`[(LENGTH h - 1,LENGTH done,reloc)]`] >> simp[] >>
  suspend "retention"
QED

Resume ptr_paired_prefix_mcopy[sample]:
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by
    (drule ptr_paired_prefix_transcript >> strip_tac >>
     drule ptr_structural_transcript_erasure >> strip_tac >>
     drule ptr_structural_trace_source >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `MEM a.po_fn C.ctx_functions` by (drule_all ptr_frame_sizes >> simp[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> rpt strip_tac >>
     gvs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
  `inst_wf a.po_inst` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, fn_inst_wf_def,
        EVERY_MEM, fn_insts_MEM] >> metis_tac[]) >>
  `a.po_inst.inst_outputs = []` by gvs[inst_wf_def] >>
  gvs[ptr_paired_sample_def, ptr_mixed_vars_def, ptr_opaque_env_def,
      ptr_core_shared_def, ptr_shared_fields_def, step_taint_def,
      mcopy_def, write_memory_with_expansion_def, set_var_taint_def,
      lookup_var_def, op_taint_def, DRESTRICT_UNIV] >> metis_tac[]
QED

Resume ptr_paired_prefix_mcopy[cursor]:
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by
    (drule ptr_paired_prefix_transcript >> strip_tac >>
     drule ptr_structural_transcript_erasure >> strip_tac >>
     drule ptr_structural_trace_source >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `MEM a.po_fn C.ctx_functions` by (drule_all ptr_frame_sizes >> simp[]) >>
  `ALL_DISTINCT (fn_labels a.po_fn)` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  `ALL_DISTINCT (fn_labels at.po_fn)` by
    (fs[ptr_paired_code_def] >>
     metis_tac[fn_labels_def, concretizeStepStructureTheory.concretize_positions_labels]) >>
  `!ai. MEM ai (fn_insts a.po_fn) /\ ai.inst_opcode = ALLOCA ==>
     ?p. FLOOKUP (lp a.po_fn) (Allocation ai.inst_id) = SOME p` by
    (match_mp_tac (Q.INST [`view` |-> `o1_walk_view rpolicy 2`] ptr_paired_stage_local_allocas) >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  irule ptr_ordinary_next_cursor >>
  rpt (goal_assum (drule_at Any)) >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Resume ptr_paired_prefix_mcopy[retention]:
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  `LAST h = a /\ 0 < LENGTH h /\ LENGTH ht = SUC (LENGTH done)` by
    (drule ptr_chrono_history_end >> strip_tac >>
     fs[ptr_paired_prefix_def, ptr_paired_samples_def]) >>
  `LENGTH ht - 1 = LENGTH done` by decide_tac >>
  `EVERY (\n. SUC n < LENGTH h) done` by
    (qpat_assum `ptr_event_embedding h ht (done ++ _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[concretizePtrEventEmbeddingTheory.ptr_event_embedding_def, EVERY_EL] >> strip_tac >>
     gen_tac >> strip_tac >>
     qpat_x_assum `!i j. _` (qspecl_then [`n`,`LENGTH done`] mp_tac) >>
     simp[EL_APPEND_EQN]) >>
  fs[ptr_paired_prefix_def] >>
  conj_tac >- (irule ptr_paired_samples_pair >> simp[]) >>
  conj_tac >- (irule ptr_paired_alignment_pair >> simp[]) >>
  conj_tac >- (irule ptr_paired_callers_retained >> simp[] >>
               fs[ptr_paired_samples_def] >> qexistsl_tac [`a`,`at`] >> simp[]) >>
  irule ptr_paired_writes_pair >> simp[] >> fs[ptr_paired_samples_def]
QED

Finalise ptr_paired_prefix_mcopy
