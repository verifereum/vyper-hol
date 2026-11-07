Theory concretizePtrShiftProducer
Ancestors concretizePtrRequestHistory concretizePtrScalarCoreProducer concretizePtrReturnTransport
  concretizePtrTaggedSupport concretizePtrPairedNextAttach concretizePtrPairedPrefixProbe

  concretizeStepStructure concretizeStepShape concretizeStepCallChecks concretizeStageShape
  concretizePtrOperationalOpcodes concretizePtrParamProducer concretizePtrOrdinaryNext
  concretizePtrPairedPrefix concretizePtrPairedFields concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrChronologicalHistory concretizePtrAllocationSize
  concretizePtrDeletedGapHistory concretizePtrLedgerProbe concretizePtrLedgerAlignment
  concretizePtrPrefixLedger concretizePtrSharedFields concretizePtrStagePlacements
  concretizePtrDeletedGaps concretizePtrExecutedCoverage o1PassContract o1ScheduleDecomp
  cfgWf unitLabelMapIdentity contextCodegenRel codegenRel frameViewFacts
  concretizePtrOpaqueRetpc
  concretizePtrValueTransport ptrDiscipline venomExecSemantics venomWf
  pointerConfinedDefs memLocDefs concretizePtrSourceOwnership
  concretizeStepRetpc unitShapeDefs venomInst venomState words finite_map list pred_set

Theorem ptr_shift_operand_discipline[local]:
  fn_ptr_ok P fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\
  (!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P fn) /\
  MEM inst.inst_opcode [SHL; SHR; SAR] /\ inst.inst_operands = [n; a] ==>
  EVERY (\op. ptr_nonopaque_operand fn op /\ op_prov TG op = NONE)
    inst.inst_operands /\ op_taint tn n = {}
Proof
  strip_tac >>
  `!v. MEM (Var v) inst.inst_operands ==> v NOTIN fn_pv P fn` by
    (qpat_x_assum `fn_ptr_ok P fn` mp_tac >>
     simp[fn_ptr_ok_def] >> strip_tac >>
     qpat_x_assum `!inst. MEM inst (fn_insts fn) ==> _`
       (qspec_then `inst` mp_tac) >> fs[MEM] >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def,
          mem_write_ops_def, mem_read_ops_def] >> metis_tac[]) >>
  reverse conj_tac
  >- (qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
      fs[MEM] >> simp[taint_ok_def] >> metis_tac[]) >>
  rewrite_tac[EVERY_MEM] >> qx_gen_tac `op` >> disch_tac >> BETA_TAC >> conj_tac
  >- (Cases_on `op` >> simp[ptr_nonopaque_operand_def] >> strip_tac >>
      `retpc_use_ok inst s'` by metis_tac[opaque_use_ok_retpc_use] >>
      fs[retpc_use_ok_def, MEM] >> gvs[]) >>
  Cases_on `op` >> simp[op_prov_def] >>
  Cases_on `FLOOKUP TG s'` >> simp[] >> metis_tac[]
QED

Theorem ptr_shift_execution[local]:
  ptr_mixed_vars births positions TG tn f g s t /\
  s.vs_labels = t.vs_labels /\
  EVERY (\op. ptr_nonopaque_operand f op /\ op_prov TG op = NONE)
    inst.inst_operands /\
  MEM inst.inst_opcode [SHL; SHR; SAR] /\
  inst.inst_operands = [n; a] /\ op_taint tn n = {} /\
  inst.inst_outputs = [out] /\ step_inst fuel Ct inst t = OK t' ==>
  ?v w. step_inst 0 C inst s = OK (update_var out v s) /\
    t' = update_var out w t /\
    ptr_value_transport births positions NONE (out_taint tn inst s) v w
Proof
  strip_tac >>
  `ptr_nonopaque_operand f n /\ op_prov TG n = NONE /\
   ptr_nonopaque_operand f a /\ op_prov TG a = NONE` by fs[] >>
  `ptr_lookup_transport births positions NONE {} (eval_operand n s) (eval_operand n t)` by
    (qpat_assum `ptr_mixed_vars _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac ptr_mixed_vars_eval) >>
     disch_then (qspec_then `n` mp_tac) >> simp[]) >>
  `ptr_lookup_transport births positions NONE (op_taint tn a)
     (eval_operand a s) (eval_operand a t)` by
    (qpat_assum `ptr_mixed_vars _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac ptr_mixed_vars_eval) >>
     disch_then (qspec_then `a` mp_tac) >> simp[]) >>
  fs[MEM] >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke] >> PURE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[] >> simp[Once opcode_case_def] >>
  simp[exec_pure2_def, eval_operands_def, AllCaseEqs()] >> strip_tac >>
  gvs[ptr_lookup_transport_some_right, ptr_value_transport_scalar_empty] >>
  simp[step_inst_non_invoke] >> PURE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[] >> simp[Once opcode_case_def] >>
  simp[exec_pure2_def, eval_operands_def, out_taint_def, ptr_value_transport_def] >>
  fs[ptr_value_transport_def] >>
  metis_tac[word_agree_except_shl, word_agree_except_shr, word_agree_except_sar]
QED

Theorem ptr_mixed_shift_execution[local]:
  ptr_mixed_vars births positions TG tn f g s t /\
  s.vs_labels = t.vs_labels /\
  EVERY (\op. ptr_nonopaque_operand f op /\ op_prov TG op = NONE)
    inst.inst_operands /\
  MEM inst.inst_opcode [SHL; SHR; SAR] /\
  inst.inst_operands = [n; a] /\ op_taint tn n = {} /\
  inst.inst_outputs = [out] /\ ~retpc_var f out /\
  step_inst fuel Ct inst t = OK t' ==>
  ?v w. step_inst 0 C inst s = OK (update_var out v s) /\
    t' = update_var out w t /\
    ptr_mixed_vars births positions
      (step_prov PT TG inst (update_var out v s))
      (step_taint inst s (update_var out v s) tn)
      f g (update_var out v s) t'
Proof
  strip_tac >> drule_all ptr_shift_execution >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  qexistsl_tac [`v`,`w`] >> simp[] >> gvs[] >>
  drule ptr_mixed_vars_update >> disch_then irule >> simp[] >>
  fs[MEM] >>
  simp[step_prov_def, out_prov_def, set_prov_def,
       step_taint_def, set_var_taint_def, op_taint_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> fs[ptr_mixed_vars_def, op_taint_def] >>
  gvs[FLOOKUP_UPDATE]
QED

Theorem ptr_paired_prefix_shift:
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
  MEM a.po_inst.inst_opcode [SHL; SHR; SAR] /\
  ptr_chrono_step C' at zt ==>
  ?z TG'.
    TG' = step_prov PT TG a.po_inst z.po_state /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens registry births PT TG' saved entries
      (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) calls ws
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
  `MEM a.po_fn C.ctx_functions` by (drule_all ptr_frame_sizes >> simp[]) >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `MEM a.po_inst (fn_insts a.po_fn) /\ inst_wf a.po_inst` by suspend "shape" >>
  `?out n data. a.po_inst.inst_outputs = [out] /\
      a.po_inst.inst_operands = [n; data]` by
    (fs[MEM] >> gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute]) >>
  `a.po_inst.inst_opcode <> ALLOCA /\ a.po_inst.inst_opcode <> NOP /\
   a.po_inst.inst_opcode <> INVOKE /\ a.po_inst.inst_opcode <> ASSIGN /\
   a.po_inst.inst_opcode <> PHI /\ a.po_inst.inst_opcode <> RETPC_PARAM /\
   ~is_terminator a.po_inst.inst_opcode` by (fs[MEM] >> simp[is_terminator_def]) >>
  `~retpc_var a.po_fn out` by
    (irule noncopy_output_not_retpc >>
     conj_tac >- fs[EVERY_MEM] >> qexists_tac `a.po_inst` >> simp[]) >>
  `EVERY (\op. ptr_nonopaque_operand a.po_fn op /\ op_prov TG op = NONE)
      a.po_inst.inst_operands /\ op_taint a.po_taint n = {}` by suspend "operands" >>
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
     strip_tac >> gvs[concretize_positions_unchanged]) >>
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[Excl "MEM"] >>
  IF (qpat_assum `step_inst _ _ _ _ = OK _` (K all_tac)) all_tac
    (fs[MEM] >> qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
     simp[step_inst_non_invoke] >> PURE_REWRITE_TAC[step_inst_base_def] >>
     ASM_REWRITE_TAC[] >> simp[Once opcode_case_def] >>
     simp[exec_pure2_def, AllCaseEqs()]) >>
  `?v w. step_inst 0 C a.po_inst a.po_state = OK (update_var out v a.po_state) /\
     s' = update_var out w at.po_state /\
     ptr_mixed_vars births positions
       (step_prov PT TG a.po_inst (update_var out v a.po_state))
       (step_taint a.po_inst a.po_state (update_var out v a.po_state) a.po_taint)
       a.po_fn at.po_fn (update_var out v a.po_state) s'` by
    (fs[ptr_paired_sample_def] >>
     `MEM a.po_inst.inst_opcode [SHL; SHR; SAR]` by simp[] >>
     `a.po_state.vs_labels = at.po_state.vs_labels` by
       (drule ptr_history_content_labels >> simp[]) >>
     `EVERY (\op. ptr_nonopaque_operand a.po_fn op /\ op_prov TG op = NONE)
       a.po_inst.inst_operands` by simp[] >>
     drule_all ptr_mixed_shift_execution >>
     disch_then (qspecl_then [`PT`,`C`] mp_tac) >> simp[]) >>
  `?i. active_inst a.po_fn i
     ((update_var out v a.po_state) with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (`EVERY bb_well_formed a.po_fn.fn_blocks` by
       (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
     qpat_assum `active_inst a.po_fn a.po_inst a.po_state`
       (mp_then Any mp_tac ptr_ordinary_next_active) >>
     disch_then irule >> simp[update_var_def]) >>
  qabbrev_tac `z = ptr_ledger_next a i (update_var out v a.po_state)` >>
  qexists_tac `z` >>
  `ALL_DISTINCT (fn_labels a.po_fn)` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  `ALL_DISTINCT (fn_labels at.po_fn)` by
    (fs[ptr_paired_code_def] >> metis_tac[fn_labels_def, concretize_positions_labels]) >>
  drule ptr_paired_stage_local_allocas >>
  disch_then (qspecl_then [`o1_walk_view rpolicy 2`,`rpolicy`] mp_tac) >>
  simp[] >> strip_tac >>
  `ptr_paired_sample positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    (simp[ptr_paired_sample_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
     (reverse conj_tac
      >- (fs[ptr_paired_sample_def] >>
          simp[step_taint_def, mem_taint_def, store_taint_def, adopt_reset_def,
               imm_taint_def, set_var_taint_def, GSYM update_var_def] >>
          irule ptr_history_content_masks >>
          qexists_tac `a.po_taint` >> simp[]) >>
      gvs[step_prov_def, out_prov_def] >>
      irule ptr_mixed_vars_fields >> rpt (goal_assum (drule_at Any)) >>
      simp[update_var_def])) >>
  `ptr_paired_params positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    (fs[ptr_paired_params_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def, update_var_def]) >>
  drule ptr_paired_prefix_ordinary_nonwrite >> disch_then irule >>
  simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def, update_var_def,
       ptr_tagged_step_def] >>
  fs[MEM] >> simp[step_prov_def, out_prov_def, step_writes_def,
       source_memory_write_ranges_def, fixed_source_write_range_def, range_bytes_def] >>
  (reverse conj_tac >- fs[update_var_def] >>
   qexistsl_tac [`0`, `update_var out v a.po_state`] >> fs[update_var_def])
QED

Resume ptr_paired_prefix_shift[shape]:
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
  fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def,
     wf_function_def, fn_inst_wf_def, EVERY_MEM, fn_insts_MEM] >> metis_tac[]
QED

Resume ptr_paired_prefix_shift[operands]:
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def,
        EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >> metis_tac[]) >>
  `EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions` by
    (fs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P a.po_fn` by
    (rpt strip_tac >> irule ptr_source_tagged_var_support >>
     rpt (goal_assum (drule_at Any))) >>
  `taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `fn_ptr_ok P a.po_fn /\ opaque_use_ok a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM] >> metis_tac[]) >>
  drule_all ptr_shift_operand_discipline >> simp[]
QED
Finalise ptr_paired_prefix_shift

Theorem ptr_paired_shift_prefix_normalize:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  LIST_REL (ptr_paired_code R lp positions) C.ctx_functions C'.ctx_functions /\
  EVERY (\f. fn_inst_wf f /\ retpc_shape_ok f /\ opaque_use_ok f /\
    first_block_no_phi f /\ EVERY bb_well_formed f.fn_blocks /\
    ALL_DISTINCT (fn_labels f) /\
    (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions /\
  EVERY (\g. ALL_DISTINCT (fn_labels g)) C'.ctx_functions /\
  (!f g. ptr_paired_code R lp positions f g ==> g.fn_name = f.fn_name) /\
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode <> NOP /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt /\
  MEM a.po_inst.inst_opcode [SHL; SHR; SAR] ==>
  ?delta z tokens' registry' births' PT' TG' saved' entries' snapshots calls' ws'.
    delta <> [] /\ LENGTH snapshots = LENGTH delta /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ delta) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens' registry' births' PT' TG' saved' entries'
      (H ++ snapshots) calls' ws' /\
    z.po_inst.inst_opcode <> NOP /\
    zt.po_inst = concretize_inst_with_positions (lp z.po_fn) z.po_inst
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ptr_paired_prefix_shift >> strip_tac >>
  `fn_inst_wf z.po_fn` by
    (qpat_assum `ptr_paired_prefix _ _ _ _ _ _ _ (_ ++ [_]) _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac ptr_paired_prefix_transcript) >> strip_tac >>
     drule ptr_structural_transcript_erasure >> strip_tac >>
     drule ptr_structural_trace_source >> strip_tac >>
     drule ptr_chrono_history_reachable >> strip_tac >>
     fs[ptr_observation_reachable_def] >>
     drule ptr_frame_context_membership >> strip_tac >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  qpat_assum `ptr_paired_prefix _ _ _ _ _ _ _ (_ ++ [_]) _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_then Any mp_tac ptr_paired_prefix_normalize) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`[z] ++ delta`, `ptr_gap_scan bb (LENGTH delta) z`,
    `tokens`, `registry`, `births`, `PT`, `TG'`, `saved`, `entries`,
    `[(tokens,registry,births,PT,TG',saved,entries)] ++ snapshots`, `calls`, `ws`] >>
  simp[APPEND_ASSOC, ptr_gap_scan_fields]
QED
