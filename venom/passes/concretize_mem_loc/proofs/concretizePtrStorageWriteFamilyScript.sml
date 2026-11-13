(*
 * Paired-prefix extension for the N12 opcode family (SSTORE; TSTORE).
 *)
Theory concretizePtrStorageWriteFamily
Ancestors
  concretizePtrStorageReadProducer concretizePtrOpaqueRetpc
  concretizePtrRequestCompletionProbe concretizePtrTaintStorageProbe
  concretizePtrRequestHistory concretizePtrTaintContent concretizePtrValueTransport
  ptrDiscipline pointerConfinedDefs memLocDefs venomInst venomState
  venomExecSemantics codegenRel list finite_map pred_set
  concretizePtrReturnTransport concretizePtrTaggedSupport
  concretizePtrPairedNextAttach concretizePtrPairedPrefixProbe
  concretizePtrSourceOwnership concretizeStepStructure concretizeStepShape
  concretizeStepRetpc concretizeStageShape
  concretizePtrOperationalOpcodes opcodeClass concretizePtrParamProducer
  concretizePtrOrdinaryNext concretizePtrPairedPrefix concretizePtrPairedFields
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrChronologicalHistory concretizePtrAllocationSize concretizePtrDeletedGapHistory
  concretizePtrLedgerProbe concretizePtrLedgerAlignment concretizePtrPrefixLedger
  concretizePtrSharedFields concretizePtrStagePlacements concretizePtrDeletedGaps
  concretizePtrExecutedCoverage o1PassContract o1ScheduleDecomp venomWf cfgWf
  unitLabelMapIdentity contextCodegenRel frameViewFacts unitShapeDefs

Theorem ptr_storage_write_operand_discipline[local]:
  fn_ptr_ok P fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\ inst.inst_operands = [key; data] /\
  (!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P fn) /\
  MEM inst.inst_opcode [SSTORE; TSTORE] ==>
  EVERY (\op. ptr_nonopaque_operand fn op /\ op_prov TG op = NONE)
    inst.inst_operands /\ op_taint tn key = {}
Proof
  strip_tac >>
  `EVERY (ptr_nonopaque_operand fn) inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> simp[] >> fs[MEM]) >>
  `!v. MEM (Var v) inst.inst_operands ==> v NOTIN fn_pv P fn` by
    (qpat_x_assum `fn_ptr_ok P fn` mp_tac >>
     simp[fn_ptr_ok_def] >> strip_tac >>
     qpat_x_assum `!inst. MEM inst (fn_insts fn) ==> _`
       (qspec_then `inst` mp_tac) >> fs[MEM] >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def,
          mem_write_ops_def, mem_read_ops_def] >> metis_tac[]) >>
  conj_tac
  >- (simp[EVERY_MEM] >> gen_tac >> strip_tac >>
      `ptr_nonopaque_operand fn op` by fs[EVERY_MEM] >> simp[] >>
      Cases_on `op` >> gvs[op_prov_def] >>
      Cases_on `FLOOKUP TG s'` >> simp[] >> metis_tac[]) >>
  qpat_x_assum `taint_ok _ _ _ _` mp_tac >> fs[MEM] >>
  simp[taint_ok_def] >> metis_tac[]
QED

Theorem ptr_history_tstore[local]:
  ptr_history_content tn s t /\ word_agree_except m u v ==>
  ptr_history_content (tn with t_trans := key_update tn.t_trans k m)
    (tstore k u s) (tstore k v t)
Proof
  simp[ptr_history_content_def] >> strip_tac >>
  drule_all ptr_taint_content_tstore >>
  disch_then (qspec_then `k` mp_tac) >> simp[tstore_def]
QED

Theorem ptr_storage_write_history_execution[local]:
  ptr_history_content tn s t /\ MEM inst.inst_opcode [SSTORE; TSTORE] /\
  inst.inst_operands = [a; d] /\ inst.inst_outputs = [] /\
  eval_operand a s = SOME k /\ eval_operand a t = SOME k /\
  eval_operand d s = SOME u /\ eval_operand d t = SOME v /\
  word_agree_except (op_taint tn d) u v /\
  step_inst fuel Ct inst t = OK t' ==>
  ?s'. step_inst 0 C inst s = OK s' /\
    ptr_history_content (step_taint inst s s' tn) s' t' /\
    ((s' = sstore k u s /\ t' = sstore k v t) \/
     (s' = tstore k u s /\ t' = tstore k v t))
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    metis_tac[ptr_history_content_call_ctx] >>
  fs[MEM] >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke] >> PURE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[] >> simp[Once opcode_case_def] >>
  simp[eval_operands_def, exec_write2_def] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  simp[step_inst_non_invoke, step_inst_base_def, Once opcode_case_def,
       exec_write2_def, eval_operands_def] >>
  fs[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
     mem_taint_def, set_var_taint_def, new_site_bytes_def,
     step_writes_def, written_taint_def, range_bytes_def,
     source_memory_write_ranges_def, FLOOKUP_DEF]
  >- (irule ptr_history_content_masks >>
      qexists_tac `tn with t_stor := key_update tn.t_stor k (op_taint tn d)` >>
      simp[] >> metis_tac[ptr_history_sstore]) >>
  irule ptr_history_content_masks >>
  qexists_tac `tn with t_trans := key_update tn.t_trans k (op_taint tn d)` >>
  simp[] >> metis_tac[ptr_history_tstore]
QED

Theorem ptr_mixed_storage_write_execution[local]:
  ptr_mixed_vars births positions TG tn f g s t /\ ptr_history_content tn s t /\
  EVERY (\op. ptr_nonopaque_operand f op /\ op_prov TG op = NONE)
    inst.inst_operands /\ op_taint tn key = {} /\
  inst.inst_operands = [key; data] /\ inst.inst_outputs = [] /\
  MEM inst.inst_opcode [SSTORE; TSTORE] /\
  step_inst fuel Ct inst t = OK t' ==>
  ?s'. step_inst 0 C inst s = OK s' /\
    ptr_history_content (step_taint inst s s' tn) s' t' /\
    ptr_mixed_vars births positions (step_prov PT TG inst s')
      (step_taint inst s s' tn) f g s' t'
Proof
  strip_tac >>
  `s.vs_labels = t.vs_labels` by metis_tac[ptr_history_content_labels] >>
  `ptr_lookup_transport births positions NONE {} (eval_operand key s)
     (eval_operand key t)` by
    (fs[EVERY_DEF] >> metis_tac[ptr_mixed_vars_eval]) >>
  `ptr_lookup_transport births positions NONE (op_taint tn data)
     (eval_operand data s) (eval_operand data t)` by
    (fs[EVERY_DEF] >> metis_tac[ptr_mixed_vars_eval]) >>
  Cases_on `eval_operand key t`
  >- (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
      fs[MEM] >> simp[step_inst_non_invoke, step_inst_base_def,
        Once opcode_case_def, exec_write2_def, eval_operands_def]) >>
  Cases_on `eval_operand data t`
  >- (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
      fs[MEM] >> simp[step_inst_non_invoke, step_inst_base_def,
        Once opcode_case_def, exec_write2_def, eval_operands_def]) >>
  Cases_on `eval_operand key s` >>
  gvs[ptr_lookup_transport_def, ptr_value_transport_scalar_empty] >>
  Cases_on `eval_operand data s` >>
  gvs[ptr_lookup_transport_def, ptr_value_transport_def] >>
  `MEM inst.inst_opcode [SSTORE; TSTORE]` by simp[] >>
  drule_all ptr_storage_write_history_execution >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  qexists_tac `s'` >> simp[] >>
  irule ptr_mixed_vars_fields >>
  qexistsl_tac [`s`, `t`, `tn`] >>
  fs[MEM, step_prov_def, out_prov_def, set_prov_def,
     step_taint_def, set_var_taint_def, sstore_def, tstore_def,
     DRESTRICT_UNIV]
QED

Theorem ptr_paired_prefix_storage_write[local]:
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
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  MEM a.po_inst.inst_opcode [SSTORE; TSTORE] /\
  ptr_chrono_step C' at zt ==>
  ?z TG'. TG' = step_prov PT TG a.po_inst z.po_state /\
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
  `?key data. a.po_inst.inst_operands = [key; data] /\
     a.po_inst.inst_outputs = []` by
    (fs[MEM] >> gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute]) >>
  `a.po_inst.inst_opcode <> ALLOCA /\ a.po_inst.inst_opcode <> NOP /\
   a.po_inst.inst_opcode <> INVOKE /\ a.po_inst.inst_opcode <> ASSIGN /\
   a.po_inst.inst_opcode <> PHI /\ a.po_inst.inst_opcode <> RETPC_PARAM /\
   ~is_terminator a.po_inst.inst_opcode` by (fs[MEM] >> simp[is_terminator_def]) >>
  `EVERY (\op. ptr_nonopaque_operand a.po_fn op /\ op_prov TG op = NONE)
      a.po_inst.inst_operands /\ op_taint a.po_taint key = {}` by suspend "operands" >>
  `at.po_inst = a.po_inst` by (fs[MEM] >> gvs[concretize_positions_unchanged]) >>
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[Excl "MEM"] >>
  IF (qpat_assum `step_inst _ _ _ _ = OK _` (K all_tac)) all_tac
    (qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
     simp[step_inst_non_invoke] >> strip_tac >>
     drule step_inst_base_intret_opcodes >> fs[MEM]) >>
  `?post. step_inst 0 C a.po_inst a.po_state = OK post /\
     ptr_history_content (step_taint a.po_inst a.po_state post a.po_taint) post s' /\
     ptr_mixed_vars births positions (step_prov PT TG a.po_inst post)
       (step_taint a.po_inst a.po_state post a.po_taint) a.po_fn at.po_fn post s'` by
    (fs[ptr_paired_sample_def] >>
     `MEM a.po_inst.inst_opcode [SSTORE; TSTORE]` by simp[] >>
     `EVERY (\op. ptr_nonopaque_operand a.po_fn op /\ op_prov TG op = NONE)
        a.po_inst.inst_operands` by simp[] >>
     drule_all ptr_mixed_storage_write_execution >>
     disch_then (qspecl_then [`PT`,`C`] mp_tac) >> metis_tac[]) >>
  `post.vs_allocas = a.po_state.vs_allocas /\
   post.vs_current_bb = a.po_state.vs_current_bb /\
   post.vs_prev_bb = a.po_state.vs_prev_bb /\
   post.vs_params = a.po_state.vs_params /\
   post.vs_halted = a.po_state.vs_halted /\
   s'.vs_current_bb = at.po_state.vs_current_bb /\
   s'.vs_prev_bb = at.po_state.vs_prev_bb /\
   s'.vs_params = at.po_state.vs_params` by suspend "fields" >>
  `?i. active_inst a.po_fn i
     (post with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (`EVERY bb_well_formed a.po_fn.fn_blocks` by
       (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
     qpat_assum `active_inst a.po_fn a.po_inst a.po_state`
       (mp_then Any mp_tac ptr_ordinary_next_active) >>
     disch_then irule >> simp[]) >>
  qabbrev_tac `z = ptr_ledger_next a i post` >> qexists_tac `z` >>
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
     gvs[step_prov_def, out_prov_def] >>
     irule ptr_mixed_vars_fields >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `ptr_paired_params positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    (fs[ptr_paired_params_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def]) >>
  drule ptr_paired_prefix_ordinary_nonwrite >> disch_then irule >>
  simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def, ptr_tagged_step_def] >>
  fs[MEM] >> simp[step_prov_def, out_prov_def, step_writes_def,
       source_memory_write_ranges_def, range_bytes_def] >>
  qexistsl_tac [`0`, `post`] >> simp[]
QED

Resume ptr_paired_prefix_storage_write[shape]:
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
  fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def,
     wf_function_def, fn_inst_wf_def, EVERY_MEM, fn_insts_MEM] >> metis_tac[]
QED

Resume ptr_paired_prefix_storage_write[operands]:
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
  drule_all ptr_storage_write_operand_discipline >> simp[]
QED

Resume ptr_paired_prefix_storage_write[fields]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `_ = concretize_inst_with_positions _ _` kall_tac >>
  qpat_x_assum `step_inst 0 _ _ _ = OK _` mp_tac >>
  qpat_x_assum `step_inst fuel _ _ _ = OK _` mp_tac >>
  fs[MEM] >> simp[step_inst_non_invoke] >>
  PURE_REWRITE_TAC[step_inst_base_def] >> ASM_REWRITE_TAC[] >>
  simp[Once opcode_case_def] >>
  simp[exec_write2_def, eval_operands_def, AllCaseEqs()] >>
  rpt strip_tac >>
  qpat_x_assum `_ = post` (SUBST1_TAC o SYM) >>
  qpat_x_assum `_ = s'` (SUBST1_TAC o SYM) >>
  simp[sstore_def, tstore_def]
QED
Finalise ptr_paired_prefix_storage_write

Theorem ptr_paired_storage_write_prefix_normalize:
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
  ptr_chrono_step C' at zt /\ MEM a.po_inst.inst_opcode [SSTORE; TSTORE] ==>
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
  drule_all ptr_paired_prefix_storage_write >> strip_tac >>
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
