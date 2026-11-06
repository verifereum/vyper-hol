Theory concretizePtrReturnProduction
Ancestors concretizePtrUniversalStepSchema concretizePtrReturnTransport
  concretizePtrOpaqueRetpc concretizePtrHistoricalPlacement
  concretizePtrPairedPrefix contextCodegenRel unitLabelMapIdentity
  concretizePtrTaggedSupport concretizePtrParamSupport concretizePtrStructuralTrace
  concretizePtrStructuralTranscript concretizePtrDeletedGapHistory
  concretizePtrChronologicalHistory concretizeStepStructure
  ptrDiscipline memLocDefs unitShapeDefs o1PassContract venomExecSemantics venomState
  venomInst venomWf pointerConfinedDefs finite_map list pred_set

Theorem ptr_paired_ret_scalar_operands:
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
  a.po_inst.inst_opcode = RET /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt ==>
  ?ops last. a.po_inst.inst_operands = ops ++ [last] /\
    EVERY (\op. ptr_nonopaque_operand a.po_fn op /\
      op_prov TG op = NONE /\ op_taint a.po_taint op = {}) ops
Proof
  strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >> metis_tac[]) >>
  `EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions` by
    (fs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P a.po_fn` by
    (rpt strip_tac >> irule ptr_source_tagged_var_support >>
     rpt (goal_assum (drule_at Any))) >>
  `taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  drule_all ptr_frame_current_static >> strip_tac >>
  `fn_ptr_ok P a.po_fn /\ opaque_use_ok a.po_fn` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `!vs0 ctx stk PG G tn fn inst s.
    frame_reachable vs0 ctx stk PG G tn fn inst s ==> active_inst fn inst s` by
    (ho_match_mp_tac frame_reachable_ind >> simp[]) >>
  `active_inst a.po_fn a.po_inst a.po_state` by metis_tac[] >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[EL_MEM]) >>
  `!v. MEM (Var v) a.po_inst.inst_operands ==> v NOTIN fn_pv P a.po_fn` by
    (qpat_x_assum `fn_ptr_ok P a.po_fn` mp_tac >>
     simp[fn_ptr_ok_def] >> strip_tac >>
     qpat_x_assum `!inst. MEM inst (fn_insts a.po_fn) ==> _`
       (qspec_then `a.po_inst` mp_tac) >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def,
       mem_write_ops_def, mem_read_ops_def] >> metis_tac[]) >>
  `at.po_inst = a.po_inst` by
    (gvs[concretize_positions_unchanged]) >>
  `a.po_inst.inst_operands <> []` by
    (qpat_x_assum `ptr_chrono_step C' at zt` mp_tac >>
     simp[Once ptr_chrono_step_cases, ptr_observe_def] >>
     rpt strip_tac >> gvs[is_terminator_def] >>
     gvs[Once run_defs, step_inst_base_def, AllCaseEqs()] >>
     Cases_on `a.po_inst.inst_operands` >> gvs[eval_operands_def]) >>
  qexistsl_tac [`FRONT a.po_inst.inst_operands`, `LAST a.po_inst.inst_operands`] >>
  simp[APPEND_FRONT_LAST] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  `MEM op a.po_inst.inst_operands` by metis_tac[APPEND_FRONT_LAST, MEM_APPEND] >>
  `op_taint a.po_taint op = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >> simp[taint_ok_def] >> metis_tac[]) >>
  `op_prov TG op = NONE` by
    (Cases_on `op` >> simp[op_prov_def] >>
     Cases_on `FLOOKUP TG s` >> simp[] >> metis_tac[]) >>
  simp[] >> Cases_on `op` >> simp[ptr_nonopaque_operand_def] >>
  strip_tac >>
  `retpc_use_ok a.po_inst s` by metis_tac[opaque_use_ok_retpc_use] >>
  gvs[retpc_use_ok_def] >> gvs[rich_listTheory.FRONT_APPEND_NOT_NIL]
QED

Theorem ptr_paired_ret_execution_back:
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
  a.po_inst.inst_opcode = RET /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt ==>
  ?ret sr tr.
    step_inst 0 C a.po_inst a.po_state = IntRet ret a.po_state /\
    step_inst 0 C' at.po_inst at.po_state = IntRet ret at.po_state /\
    ret.iret_adopt_fmp = NONE /\
    a.po_stack <> [] /\ at.po_stack <> [] /\
    (HD a.po_stack).cf_inst.inst_outputs = (HD at.po_stack).cf_inst.inst_outputs /\
    bind_outputs (HD a.po_stack).cf_inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state (HD a.po_stack).cf_state a.po_state)) = SOME sr /\
    bind_outputs (HD at.po_stack).cf_inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state (HD at.po_stack).cf_state at.po_state)) = SOME tr
Proof
  strip_tac >>
  drule_all ptr_paired_ret_scalar_operands >> strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  `at.po_inst = a.po_inst` by gvs[concretize_positions_unchanged] >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
    a.po_state at.po_state /\ a.po_state.vs_labels = at.po_state.vs_labels` by
    fs[ptr_paired_sample_def, ptr_core_shared_def,
      concretizePtrSharedFieldsTheory.ptr_shared_fields_def] >>
  `?ret tr. step_inst 0 C' at.po_inst at.po_state = IntRet ret at.po_state /\
    ret.iret_adopt_fmp = NONE /\ at.po_stack <> [] /\
    bind_outputs (HD at.po_stack).cf_inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state (HD at.po_stack).cf_state at.po_state)) = SOME tr` by
    (qpat_x_assum `ptr_chrono_step C' at zt` mp_tac >>
     simp[Once ptr_chrono_step_cases, ptr_observe_def] >>
     rpt strip_tac >> gvs[is_terminator_def] >>
     gvs[Once run_defs, step_inst_base_def, AllCaseEqs()] >>
     qexistsl_tac [`<|iret_values := FRONT (v3::v4); iret_adopt_fmp := NONE|>`, `s'`] >>
     simp[Once run_defs, step_inst_base_def, adopt_return_fmp_def]) >>
  `?ys. eval_operands (ops ++ [last]) at.po_state = SOME ys /\
    ys <> [] /\ ret.iret_values = FRONT ys` by
    (qpat_x_assum `step_inst 0 C' _ _ = _` mp_tac >>
     simp[Once run_defs, step_inst_base_def] >>
     gvs[AllCaseEqs()] >> strip_tac >> gvs[] >> metis_tac[]) >>
  drule_all ptr_mixed_return_front >> strip_tac >>
  `step_inst 0 C a.po_inst a.po_state = IntRet ret a.po_state` by
    (simp[Once run_defs, step_inst_base_def] >>
     Cases_on `xs` >> gvs[] >> Cases_on `ret` >> gvs[internal_return_component_equality]) >>
  drule ptr_paired_prefix_callers >> strip_tac >>
  `a.po_stack <> []` by
    (fs[concretizePtrPairedFieldsTheory.ptr_paired_callers_def] >>
     Cases_on `a.po_stack` >> Cases_on `at.po_stack` >> gvs[]) >>
  `(HD a.po_stack).cf_inst.inst_outputs = (HD at.po_stack).cf_inst.inst_outputs` by
    (qpat_x_assum `ptr_paired_callers _ _ _ _ _ _ _ _` mp_tac >>
     simp[concretizePtrPairedFieldsTheory.ptr_paired_callers_def] >> strip_tac >>
     first_x_assum (qspec_then `0` mp_tac) >>
     `0 < LENGTH calls` by (Cases_on `calls` >> gvs[]) >>
     simp[concretizePtrPairedFieldsTheory.ptr_paired_call_def] >>
     Cases_on `HD calls` >>
     simp[concretizePtrPairedFieldsTheory.ptr_paired_call_def] >> strip_tac >>
     drule ptr_paired_prefix_alignment >>
     disch_then (qspec_then `r` mp_tac) >>
     `r < LENGTH ht` by
       (drule ptr_paired_prefix_samples >> simp[ptr_paired_samples_def] >> decide_tac) >>
     simp[EL_APPEND_EQN] >> strip_tac >>
     qpat_x_assum `ptr_paired_cursor lp (EL _ h) _` mp_tac >>
     simp[concretizePtrPairedFieldsTheory.ptr_paired_cursor_def] >> strip_tac >>
     drule concretizePtrLedgerAlignmentTheory.ptr_ledger_alignment_cursor >> strip_tac >>
     `((EL (EL r done) h).po_state.vs_inst_idx) =
       EL (EL r ht).po_state.vs_inst_idx indices` by
       (qpat_x_assum `!k. _ <= k /\ _ ==> _`
          (qspec_then `(EL (EL r done) h).po_state.vs_inst_idx` mp_tac) >>
        gvs[] >> decide_tac) >>
     qpat_x_assum `!j. j < LENGTH bbt.bb_instructions ==> _`
       (qspec_then `(EL r ht).po_state.vs_inst_idx` mp_tac) >>
     simp[] >> strip_tac >>
     gvs[concretize_positions_unchanged,
       concretizePtrPairedFieldsTheory.ptr_paired_frame_def]) >>
  qexists_tac `ret` >> simp[] >>
  qpat_x_assum `bind_outputs _ _ _ = SOME tr` mp_tac >>
  simp[bind_outputs_def] >> strip_tac >> simp[]
QED

Theorem ptr_paired_ret_restored_vars:
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
  a.po_inst.inst_opcode = RET /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt ==>
  ?ret sr tr PTc TGc tnc outs.
    step_inst 0 C a.po_inst a.po_state = IntRet ret a.po_state /\
    step_inst 0 C' at.po_inst at.po_state = IntRet ret at.po_state /\
    ret.iret_adopt_fmp = NONE /\
    a.po_stack <> [] /\ at.po_stack <> [] /\
    (HD a.po_stack).cf_inst.inst_outputs = (HD at.po_stack).cf_inst.inst_outputs /\
    bind_outputs (HD a.po_stack).cf_inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state (HD a.po_stack).cf_state a.po_state)) = SOME sr /\
    bind_outputs (HD at.po_stack).cf_inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state (HD at.po_stack).cf_state at.po_state)) = SOME tr /\
    saved <> [] /\ HD saved = (PTc,TGc) /\
    outs = (HD a.po_stack).cf_inst.inst_outputs /\
    tnc.t_var = (HD a.po_stack).cf_tvar /\
    ptr_mixed_vars births positions (DRESTRICT TGc (COMPL (set outs)))
      (tnc with t_var := DRESTRICT tnc.t_var (COMPL (set outs)))
      (HD a.po_stack).cf_fn (HD at.po_stack).cf_fn sr tr
Proof
  strip_tac >> drule_all ptr_paired_ret_execution_back >> strip_tac >>
  drule ptr_paired_prefix_callers >>
  simp[concretizePtrPairedFieldsTheory.ptr_paired_callers_def] >> strip_tac >>
  `0 < LENGTH calls` by (Cases_on `calls` >> Cases_on `a.po_stack` >> gvs[]) >>
  `saved <> []` by (Cases_on `saved` >> gvs[]) >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >>
  Cases_on `HD calls` >>
  simp[concretizePtrPairedFieldsTheory.ptr_paired_call_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `ptr_paired_saved_tags _ snap` >>
  PairCases_on `snap` >>
  fs[concretizePtrPairedFieldsTheory.ptr_paired_saved_tags_def] >>
  drule ptr_paired_prefix_samples >> strip_tac >>
  `r < LENGTH ht` by fs[ptr_paired_samples_def] >>
  `ptr_mixed_vars snap2 positions snap4 (EL q h).po_taint
    (EL q h).po_fn (EL r ht).po_fn (EL q h).po_state (EL r ht).po_state` by
    (gvs[] >> fs[ptr_paired_samples_def] >>
     qpat_x_assum `!j. j < LENGTH ht ==> _` (qspec_then `r` mp_tac) >>
     simp[EL_APPEND_EQN, ptr_paired_sample_def]) >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_endpoint >> strip_tac >>
  `q < LENGTH h` by
    (fs[ptr_paired_samples_def, EVERY_MEM] >> metis_tac[EL_MEM]) >>
  `EL (LENGTH h - 1) H = (tokens,registry,births,PT,TG,saved,entries)` by
    (Cases_on `H` >> gvs[LAST_EL, arithmeticTheory.PRE_SUB1]) >>
  `EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions` by
    (fs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `!key site. FLOOKUP snap2 key = SOME site ==> FLOOKUP births key = SOME site` by
    (rpt strip_tac >>
     `q <= LENGTH h - 1 /\ LENGTH h - 1 < LENGTH h` by decide_tac >>
     drule_all (ptr_transcript_birth_retained |> Q.SPEC `LENGTH h - 1`) >>
     simp[]) >>
  `ptr_mixed_vars births positions snap4 (EL q h).po_taint
    (EL q h).po_fn (EL r ht).po_fn (EL q h).po_state (EL r ht).po_state` by
    (irule ptr_mixed_vars_retained_births_tvar >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_chrono_history_reachable >> strip_tac >>
  `frame_reachable vs C (EL q h).po_stack (EL q h).po_params
    (EL q h).po_prov (EL q h).po_taint (EL q h).po_fn
    (EL q h).po_inst (EL q h).po_state` by
    (fs[EVERY_MEM, ptr_observation_reachable_def] >> metis_tac[EL_MEM]) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >> metis_tac[]) >>
  drule_all ptr_frame_current_static >> strip_tac >>
  `retpc_shape_ok (EL q h).po_fn` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `MEM (EL q h).po_inst (fn_insts (EL q h).po_fn)` by
    (`!vs0 ctx stk PG G tn fn inst s.
        frame_reachable vs0 ctx stk PG G tn fn inst s ==> active_inst fn inst s` by
       (ho_match_mp_tac frame_reachable_ind >> simp[]) >>
     `active_inst (EL q h).po_fn (EL q h).po_inst (EL q h).po_state` by metis_tac[] >>
     fs[active_inst_def, fn_insts_MEM] >> metis_tac[EL_MEM]) >>
  drule_all ptr_retpc_invoke_outputs >> strip_tac >>
  qexistsl_tac [`sr`, `(EL q h).po_taint`] >>
  gvs[concretizePtrPairedFieldsTheory.ptr_paired_frame_def] >>
  irule (cj 2 ptr_mixed_return_bind) >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED
