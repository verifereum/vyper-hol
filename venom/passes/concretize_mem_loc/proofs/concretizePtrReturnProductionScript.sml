Theory concretizePtrReturnProduction
Ancestors concretizePtrReturnTransport
  concretizePtrOpaqueRetpc concretizePtrHistoricalPlacement
  concretizePtrPairedPrefix contextCodegenRel unitLabelMapIdentity
  concretizePtrSourceOwnership concretizePtrTaggedSupport concretizePtrParamSupport concretizePtrStructuralTrace
  concretizePtrStructuralTranscript concretizePtrDeletedGapHistory
  concretizePtrChronologicalHistory concretizeStepStructure
  ptrDiscipline memLocDefs unitShapeDefs o1PassContract venomExecSemantics venomState
  venomInst venomWf venomInstProofs1 venomExecProofs
  concretizePtrOperationalOpcodes pointerConfinedDefs finite_map list pred_set

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
    (fs[ptr_paired_sample_def] >>
     drule concretizePtrRequestHistoryTheory.ptr_history_content_control >>
     simp[concretizePtrTaintContentTheory.ptr_taint_control_def,
       ptr_core_shared_def, concretizePtrSharedFieldsTheory.ptr_shared_fields_def]) >>
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
       (drule ptr_paired_prefix_samples >> simp[ptr_paired_samples_def, ptr_sample_list_def] >> decide_tac) >>
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
  `r < LENGTH ht` by fs[ptr_paired_samples_def, ptr_sample_list_def] >>
  `ptr_mixed_vars snap2 positions snap4 (EL q h).po_taint
    (EL q h).po_fn (EL r ht).po_fn (EL q h).po_state (EL r ht).po_state` by
    (gvs[] >> fs[ptr_paired_samples_def, ptr_sample_list_def] >>
     qpat_x_assum `!j. j < LENGTH ht ==> _` (qspec_then `r` mp_tac) >>
     simp[EL_APPEND_EQN, ptr_paired_sample_def]) >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_endpoint >> strip_tac >>
  `q < LENGTH h` by
    (fs[ptr_paired_samples_def, ptr_sample_list_def, EVERY_MEM] >> metis_tac[EL_MEM]) >>
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

Theorem ptr_ret_cursor_active[local]:
  ptr_paired_cursor lp a at ==> active_inst a.po_fn a.po_inst a.po_state
Proof
  simp[concretizePtrPairedFieldsTheory.ptr_paired_cursor_def] >> strip_tac >>
  drule concretizePtrLedgerAlignmentTheory.ptr_ledger_alignment_cursor >> strip_tac >>
  `EL at.po_state.vs_inst_idx indices < LENGTH bb.bb_instructions` by
    (first_x_assum (qspec_then `at.po_state.vs_inst_idx` mp_tac) >> simp[]) >>
  `bb.bb_label = a.po_state.vs_current_bb` by metis_tac[lookup_block_label] >>
  simp[active_inst_def] >> qexists_tac `bb` >> simp[] >> decide_tac
QED

Theorem ptr_ret_bind_control[local]:
  bind_outputs os vals s = SOME t ==>
  t.vs_current_bb = s.vs_current_bb /\ t.vs_prev_bb = s.vs_prev_bb /\
  t = (s with vs_vars := t.vs_vars)
Proof
  strip_tac >>
  `t = (s with vs_vars := t.vs_vars)` by
    (qspec_then `(\u. u with vs_vars := t.vs_vars)` mp_tac bind_outputs_preserves >>
     simp[update_var_def] >> disch_then drule >> simp[]) >>
  conj_tac >- (pop_assum (fn th => once_rewrite_tac[th]) >> simp[]) >>
  conj_tac >- (pop_assum (fn th => once_rewrite_tac[th]) >> simp[]) >> simp[]
QED

Theorem ptr_ret_caller_cursor[local]:
  ptr_paired_cursor lp u ut /\ u.po_inst.inst_opcode = INVOKE /\
  ALL_DISTINCT (fn_labels ut.po_fn) /\
  (!i. MEM i (fn_insts u.po_fn) /\ i.inst_opcode = ALLOCA ==>
    ?p. FLOOKUP (lp u.po_fn) (Allocation i.inst_id) = SOME p) /\
  b.po_fn = u.po_fn /\ bt.po_fn = ut.po_fn /\
  b.po_state.vs_current_bb = u.po_state.vs_current_bb /\
  bt.po_state.vs_current_bb = ut.po_state.vs_current_bb /\
  b.po_state.vs_prev_bb = u.po_state.vs_prev_bb /\
  bt.po_state.vs_prev_bb = ut.po_state.vs_prev_bb /\
  b.po_state.vs_inst_idx = SUC u.po_state.vs_inst_idx /\
  bt.po_state.vs_inst_idx = SUC ut.po_state.vs_inst_idx /\
  active_inst bt.po_fn bt.po_inst bt.po_state ==>
  ?i. active_inst b.po_fn i b.po_state /\
      ptr_paired_cursor lp (b with po_inst := i) bt
Proof
  simp[concretizePtrPairedFieldsTheory.ptr_paired_cursor_def] >> strip_tac >>
  `u.po_state.vs_inst_idx = EL ut.po_state.vs_inst_idx indices` by
    (first_x_assum (qspec_then `u.po_state.vs_inst_idx` mp_tac) >>
     gvs[] >> decide_tac) >>
  `SUC ut.po_state.vs_inst_idx < LENGTH indices /\
   bt.po_inst = EL (SUC ut.po_state.vs_inst_idx) bbt.bb_instructions` by
    (qpat_x_assum `active_inst _ _ _` mp_tac >>
     simp[active_inst_def] >> strip_tac >>
     `lookup_block ut.po_state.vs_current_bb ut.po_fn.fn_blocks = SOME bb'` by
       (irule MEM_lookup_block >> gvs[fn_labels_def]) >>
     gvs[] >> drule concretizePtrLedgerAlignmentTheory.ptr_ledger_alignment_cursor >> simp[]) >>
  `SUC u.po_state.vs_inst_idx <= EL (SUC ut.po_state.vs_inst_idx) indices /\
   EL (SUC ut.po_state.vs_inst_idx) indices < LENGTH bb.bb_instructions` by
    (drule concretizePtrLedgerAlignmentTheory.ptr_ledger_alignment_cursor >> strip_tac >>
     `EL ut.po_state.vs_inst_idx indices < EL (SUC ut.po_state.vs_inst_idx) indices` by
       (irule concretizePtrLedgerAlignmentTheory.ptr_ledger_alignment_order >>
        simp[] >> rpt (goal_assum (drule_at Any))) >>
     first_x_assum (qspec_then `SUC ut.po_state.vs_inst_idx` mp_tac) >>
     simp[] >> decide_tac) >>
  qexists_tac `EL (SUC u.po_state.vs_inst_idx) bb.bb_instructions` >>
  conj_tac
  >- (simp[active_inst_def] >> qexists_tac `bb` >> simp[] >>
      `bb.bb_label = u.po_state.vs_current_bb` by metis_tac[lookup_block_label] >>
      simp[] >> decide_tac) >>
  simp[] >> qexistsl_tac [`bb`, `indices`] >>
  `lookup_block ut.po_state.vs_current_bb u.po_fn.fn_blocks = SOME bb` by metis_tac[] >>
  simp[] >>
  rpt strip_tac >> irule concretizePtrDeletedGapsTheory.ptr_ledger_source_gap >>
  rpt (goal_assum (drule_at Any)) >> simp[] >> decide_tac
QED

Theorem ptr_ret_phis_call_context[local]:
  !s t. eval_phis s insts = OK t ==> t.vs_call_ctx = s.vs_call_ctx
Proof
  Induct_on `insts` >- simp[eval_phis_def] >>
  rpt gen_tac >> simp[Once eval_phis_def] >>
  strip_tac >> gvs[AllCaseEqs(), update_var_def] >> metis_tac[]
QED

Theorem ptr_ret_block_call_context[local]:
  enters_block fn s t ==> t.vs_call_ctx = s.vs_call_ctx
Proof
  rw[enters_block_def] >> drule ptr_ret_phis_call_context >> simp[]
QED

Theorem ptr_ret_terminator_call_context[local]:
  is_terminator inst.inst_opcode /\ step_inst fuel C inst s = OK t ==>
  t.vs_call_ctx = s.vs_call_ctx
Proof
  Cases_on `inst.inst_opcode` >> simp[is_terminator_def] >>
  strip_tac >> gvs[Once step_inst_def, step_inst_base_opcode_eqs] >>
  gvs[AllCaseEqs(), jump_to_def] >> pairarg_tac >> gvs[]
QED

Theorem ptr_ret_reachable_stack_context[local]:
  !vs C stk PG G tn fn inst s. frame_reachable vs C stk PG G tn fn inst s ==>
  !f. MEM f stk ==> s.vs_call_ctx = f.cf_state.vs_call_ctx
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- simp[]
  >- (rpt strip_tac >> drule_all venomInstProofsTheory.step_preserves_call_ctx >>
      strip_tac >> simp[])
  >- (rpt strip_tac >> drule_all ptr_ret_terminator_call_context >>
      drule ptr_ret_block_call_context >> metis_tac[])
  >- (rpt strip_tac >> drule ptr_ret_block_call_context >>
      qpat_x_assum `setup_callee _ _ _ = _` mp_tac >>
      simp[setup_callee_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >> metis_tac[])
  >> rpt strip_tac >>
  `s'.vs_call_ctx = f.cf_state.vs_call_ctx` by
    (qspec_then `(\u. u.vs_call_ctx)` mp_tac bind_outputs_preserves >>
     simp[update_var_def] >> disch_then drule >>
     Cases_on `ret.iret_adopt_fmp` >> simp[adopt_return_fmp_def, merge_callee_state_def]) >>
  gvs[] >> metis_tac[]
QED

Theorem ptr_ret_reachable_caller_address[local]:
  ptr_observation_reachable vs C a /\ a.po_stack <> [] ==>
  a.po_state.vs_call_ctx.cc_address =
    (HD a.po_stack).cf_state.vs_call_ctx.cc_address
Proof
  strip_tac >> fs[ptr_observation_reachable_def] >>
  drule ptr_ret_reachable_stack_context >>
  disch_then (qspec_then `HD a.po_stack` mp_tac) >>
  Cases_on `a.po_stack` >> gvs[]
QED

Theorem ptr_paired_ret_successor:
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
  ?b ret sr tr PTc TGc outs B'.
    step_inst 0 C a.po_inst a.po_state = IntRet ret a.po_state /\
    step_inst 0 C' at.po_inst at.po_state = IntRet ret at.po_state /\
    ret.iret_adopt_fmp = NONE /\
    a.po_stack <> [] /\ at.po_stack <> [] /\ saved <> [] /\
    HD saved = (PTc,TGc) /\ outs = (HD a.po_stack).cf_inst.inst_outputs /\
    bind_outputs outs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state (HD a.po_stack).cf_state a.po_state)) = SOME sr /\
    bind_outputs (HD at.po_stack).cf_inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state (HD at.po_stack).cf_state at.po_state)) = SOME tr /\
    b.po_state = (sr with vs_inst_idx := SUC (HD a.po_stack).cf_state.vs_inst_idx) /\
    b.po_stack = TL a.po_stack /\
    ptr_tagged_chrono_step C (HD tokens) a b PT TG saved PTc
      (DRESTRICT TGc (COMPL (set outs))) (TL saved) /\
    ptr_history_content b.po_taint b.po_state zt.po_state /\ ptr_paired_cursor lp b zt /\
    ptr_mixed_vars births positions (DRESTRICT TGc (COMPL (set outs)))
      b.po_taint b.po_fn zt.po_fn b.po_state zt.po_state /\
    B' = ptr_birth_overlay (HD (TL tokens)) b.po_state.vs_allocas births /\
    ptr_structural_transcript R vs C C'
      (h ++ [b]) b (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      (TL tokens) registry B' PTc (DRESTRICT TGc (COMPL (set outs)))
      (TL saved) entries
      (H ++ [(TL tokens,registry,B',PTc,DRESTRICT TGc (COMPL (set outs)),TL saved,entries)])
Proof
  strip_tac >> drule_all ptr_paired_ret_restored_vars >> strip_tac >>
  drule ptr_paired_prefix_callers >>
  simp[concretizePtrPairedFieldsTheory.ptr_paired_callers_def] >> strip_tac >>
  `0 < LENGTH calls` by (Cases_on `calls` >> Cases_on `a.po_stack` >> gvs[]) >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >>
  Cases_on `HD calls` >>
  simp[concretizePtrPairedFieldsTheory.ptr_paired_call_def,
    concretizePtrPairedFieldsTheory.ptr_paired_saved_tags_def] >> strip_tac >>
  drule ptr_paired_prefix_alignment >>
  disch_then (qspec_then `r` mp_tac) >>
  `r < LENGTH ht` by
    (drule ptr_paired_prefix_samples >> simp[ptr_paired_samples_def, ptr_sample_list_def] >> decide_tac) >>
  simp[EL_APPEND_EQN] >> strip_tac >>
  suspend "target_control"
QED

Resume ptr_paired_ret_successor[target_control]:
  `at.po_inst = a.po_inst` by gvs[concretize_positions_unchanged] >>
  `zt.po_fn = (HD at.po_stack).cf_fn /\ 
   zt.po_stack = TL at.po_stack /\
   zt.po_state = (tr with vs_inst_idx := SUC (HD at.po_stack).cf_state.vs_inst_idx) /\
   active_inst zt.po_fn zt.po_inst zt.po_state` by
    (qpat_x_assum `ptr_chrono_step C' at zt` mp_tac >>
     simp[Once ptr_chrono_step_cases, ptr_observe_def] >>
     rpt strip_tac >> gvs[is_terminator_def] >>
     `!fuel. step_inst fuel C' a.po_inst s = step_inst 0 C' a.po_inst s` by
       (irule ptrSafeRunTheory.step_inst_non_invoke_fuel >> simp[]) >>
     gvs[]) >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (drule ptr_paired_prefix_endpoint >> strip_tac >>
     drule ptr_ret_cursor_active >> simp[]) >>
  `MEM (EL r ht).po_fn C'.ctx_functions /\
   MEM (EL (EL r done) h).po_fn C.ctx_functions` by
    (drule ptr_paired_prefix_transcript >> strip_tac >>
     drule ptr_structural_transcript_erasure >> strip_tac >>
     drule ptr_structural_trace_source >> strip_tac >>
     drule ptr_structural_trace_target >> strip_tac >>
     imp_res_tac ptr_chrono_history_reachable >>
     `ptr_observation_reachable vs C' (EL r ht) /\
      ptr_observation_reachable vs C (EL (EL r done) h)` by
       (drule ptr_paired_prefix_samples >> simp[ptr_paired_samples_def, ptr_sample_list_def] >>
        strip_tac >> fs[EVERY_MEM] >> metis_tac[EL_MEM]) >>
     fs[ptr_observation_reachable_def] >>
     imp_res_tac ptr_frame_context_membership >> simp[]) >>
  `ALL_DISTINCT (fn_labels (EL r ht).po_fn) /\
   (!i. MEM i (fn_insts (EL (EL r done) h).po_fn) /\ i.inst_opcode = ALLOCA ==>
     ?p. FLOOKUP (lp (EL (EL r done) h).po_fn) (Allocation i.inst_id) = SOME p)` by
    (fs[EVERY_MEM, optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
  suspend "caller_cursor"
QED

Resume ptr_paired_ret_successor[caller_cursor]:
  `sr.vs_current_bb = (HD a.po_stack).cf_state.vs_current_bb /\
   tr.vs_current_bb = (HD at.po_stack).cf_state.vs_current_bb /\
   sr.vs_prev_bb = (HD a.po_stack).cf_state.vs_prev_bb /\
   tr.vs_prev_bb = (HD at.po_stack).cf_state.vs_prev_bb` by
    (imp_res_tac ptr_ret_bind_control >> gvs[adopt_return_fmp_def, merge_callee_state_def]) >>
  qabbrev_tac `b0 = ptr_observe (TL a.po_stack) (HD a.po_stack).cf_params
    (DRESTRICT (HD a.po_stack).cf_prov (COMPL (set outs)))
    (a.po_taint with t_var := DRESTRICT (HD a.po_stack).cf_tvar (COMPL (set outs)))
    (HD a.po_stack).cf_fn a.po_inst
    (sr with vs_inst_idx := SUC (HD a.po_stack).cf_state.vs_inst_idx)` >>
  `?i. active_inst b0.po_fn i b0.po_state /\
       ptr_paired_cursor lp (b0 with po_inst := i) zt` by
    (irule ptr_ret_caller_cursor >> conj_tac >- simp[] >>
     qexistsl_tac [`EL (EL r done) h`, `EL r ht`] >>
     gvs[Abbr `b0`, ptr_observe_def,
       concretizePtrPairedFieldsTheory.ptr_paired_frame_def]) >>
  qabbrev_tac `b = b0 with po_inst := i` >>
  `active_inst b.po_fn b.po_inst b.po_state /\ ptr_paired_cursor lp b zt` by
    (gvs[Abbr `b`]) >>
  suspend "tagged_return"
QED

Resume ptr_paired_ret_successor[tagged_return]:
  `b = ptr_observe (TL a.po_stack) (HD a.po_stack).cf_params
    (DRESTRICT (HD a.po_stack).cf_prov (COMPL (set outs)))
    (a.po_taint with t_var := DRESTRICT (HD a.po_stack).cf_tvar (COMPL (set outs)))
    (HD a.po_stack).cf_fn i
    (sr with vs_inst_idx := SUC (HD a.po_stack).cf_state.vs_inst_idx)` by
      simp[NoAsms, Abbr `b`, Abbr `b0`, ptr_observe_def] >>
  `ptr_observe a.po_stack a.po_params a.po_prov a.po_taint
     a.po_fn a.po_inst a.po_state = a` by
    simp[NoAsms, ptr_observe_def, ptr_observation_component_equality] >>
  `ptr_tagged_chrono_step C (HD tokens)
    (ptr_observe a.po_stack a.po_params a.po_prov a.po_taint
      a.po_fn a.po_inst a.po_state) b PT TG saved PTc
      (DRESTRICT TGc (COMPL (set outs))) (TL saved)` by
    (qpat_x_assum `ptr_observe _ _ _ _ _ _ _ = a` kall_tac >>
     qpat_x_assum `b = ptr_observe _ _ _ _ _ _ _` (fn th => pure_rewrite_tac[th]) >>
     Cases_on `a.po_stack` >> gvs[] >> Cases_on `saved` >> gvs[] >>
     qpat_assum `_.cf_inst.inst_outputs = _` (fn th => once_rewrite_tac[GSYM th]) >>
     irule (cj 4 ptr_tagged_chrono_step_rules) >>
     simp[ptr_observe_def] >>
     conj_tac >- (qexistsl_tac [`0`, `ret`, `a.po_state`] >> simp[]) >>
     gvs[Abbr `b0`, ptr_observe_def]) >>
  `ptr_tagged_chrono_step C (HD tokens) a b PT TG saved PTc
     (DRESTRICT TGc (COMPL (set outs))) (TL saved)` by metis_tac[] >>
  suspend "restored_fields"
QED

Resume ptr_paired_ret_successor[restored_fields]:
  `ptr_history_content a.po_taint a.po_state at.po_state` by
    (drule ptr_paired_prefix_endpoint >> simp[ptr_paired_sample_def]) >>
  `ptr_taint_control
     ((HD a.po_stack).cf_state with vs_requests := (HD at.po_stack).cf_state.vs_requests)
     (HD at.po_stack).cf_state` by
    (drule ptr_paired_prefix_samples >>
     simp[ptr_paired_samples_def, ptr_sample_list_def] >> strip_tac >>
     first_x_assum (qspec_then `r` mp_tac) >>
     simp[EL_APPEND_EQN] >> strip_tac >>
     qmatch_asmsub_abbrev_tac `ptr_paired_sample positions _ _ snap` >>
     PairCases_on `snap` >> fs[ptr_paired_sample_def] >>
     qpat_x_assum `ptr_history_content _ (EL _ h).po_state _`
       (mp_then Any mp_tac concretizePtrRequestHistoryTheory.ptr_history_content_control) >>
     gvs[concretizePtrPairedFieldsTheory.ptr_paired_frame_def]) >>
  `ptr_observation_reachable vs C a /\ ptr_observation_reachable vs C' at` by
    (drule ptr_paired_prefix_transcript >> strip_tac >>
     drule ptr_structural_transcript_erasure >> strip_tac >>
     drule ptr_structural_trace_source >>
     drule ptr_structural_trace_target >> rpt strip_tac >>
     imp_res_tac ptr_chrono_history_reachable >> simp[]) >>
  `a.po_state.vs_call_ctx.cc_address = (HD a.po_stack).cf_state.vs_call_ctx.cc_address /\
   at.po_state.vs_call_ctx.cc_address = (HD at.po_stack).cf_state.vs_call_ctx.cc_address` by
    metis_tac[ptr_ret_reachable_caller_address] >>
  `ptr_history_content b.po_taint b.po_state zt.po_state` by
    (simp[Abbr `b`, Abbr `b0`, ptr_observe_def,
       Excl "ptr_history_content_cursor", Excl "ptr_history_content_tvar"] >>
     irule concretizePtrRequestHistoryTheory.ptr_history_content_return >>
     rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]) >>
  `ptr_mixed_vars births positions (DRESTRICT TGc (COMPL (set outs)))
     b.po_taint b.po_fn zt.po_fn b.po_state zt.po_state` by
    (qpat_x_assum `ptr_mixed_vars births positions _ _ _ _ sr tr` mp_tac >>
     simp[Abbr `b`, Abbr `b0`, ptr_observe_def, ptr_mixed_vars_def,
       ptr_opaque_env_def, lookup_var_def, op_taint_def] >>
     metis_tac[]) >>
  suspend "transcript"
QED

Resume ptr_paired_ret_successor[transcript]:
  `LENGTH a.po_stack = SUC (LENGTH b.po_stack) /\
   LENGTH at.po_stack = SUC (LENGTH zt.po_stack)` by
    (gvs[Abbr `b`, Abbr `b0`, ptr_observe_def] >>
     Cases_on `a.po_stack` >> Cases_on `at.po_stack` >> gvs[]) >>
  `ptr_structural_transcript R vs C C'
      (h ++ [b]) b (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      (TL tokens) registry (ptr_birth_overlay (HD (TL tokens)) b.po_state.vs_allocas births)
      PTc (DRESTRICT TGc (COMPL (set outs))) (TL saved) entries
      (H ++ [(TL tokens,registry,ptr_birth_overlay (HD (TL tokens)) b.po_state.vs_allocas births,
        PTc,DRESTRICT TGc (COMPL (set outs)),TL saved,entries)])` by
    (drule ptr_paired_prefix_transcript >> strip_tac >>
     drule (cj 3 ptr_structural_transcript_rules) >>
     disch_then drule >> disch_then drule >>
     qpat_assum `LENGTH a.po_stack = SUC (LENGTH b.po_stack)` (fn th =>
       simp[NoAsms, th, concretizePtrActivationChronologyTheory.ptr_activation_tokens_def,
         concretizePtrActivationChronologyTheory.ptr_activation_registry_def]) >>
     disch_then irule >> asm_rewrite_tac[]) >>
  qexistsl_tac [`b`, `sr`] >>
  qpat_assum `outs = _` (fn th =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> pure_rewrite_tac[th]) >>
  qpat_assum `(HD a.po_stack).cf_inst.inst_outputs = (HD at.po_stack).cf_inst.inst_outputs` (fn th =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> pure_rewrite_tac[th]) >>
  qpat_x_assum `at.po_inst = concretize_inst_with_positions _ _` kall_tac >>
  rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC,
    simp[NoAsms, Abbr `b`, Abbr `b0`, ptr_observe_def]]
QED

Finalise ptr_paired_ret_successor

Theorem ptr_paired_ret_successor_births:
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
  ?b ret sr tr PTc TGc outs B'.
    step_inst 0 C a.po_inst a.po_state = IntRet ret a.po_state /\
    step_inst 0 C' at.po_inst at.po_state = IntRet ret at.po_state /\
    ret.iret_adopt_fmp = NONE /\
    a.po_stack <> [] /\ at.po_stack <> [] /\ saved <> [] /\
    HD saved = (PTc,TGc) /\ outs = (HD a.po_stack).cf_inst.inst_outputs /\
    bind_outputs outs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state (HD a.po_stack).cf_state a.po_state)) = SOME sr /\
    bind_outputs (HD at.po_stack).cf_inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state (HD at.po_stack).cf_state at.po_state)) = SOME tr /\
    b.po_state = (sr with vs_inst_idx := SUC (HD a.po_stack).cf_state.vs_inst_idx) /\
    b.po_stack = TL a.po_stack /\
    ptr_tagged_chrono_step C (HD tokens) a b PT TG saved PTc
      (DRESTRICT TGc (COMPL (set outs))) (TL saved) /\
    ptr_history_content b.po_taint b.po_state zt.po_state /\ ptr_paired_cursor lp b zt /\
    ptr_mixed_vars B' positions (DRESTRICT TGc (COMPL (set outs)))
      b.po_taint b.po_fn zt.po_fn b.po_state zt.po_state /\
    B' = ptr_birth_overlay (HD (TL tokens)) b.po_state.vs_allocas births /\
    ptr_structural_transcript R vs C C'
      (h ++ [b]) b (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      (TL tokens) registry B' PTc (DRESTRICT TGc (COMPL (set outs)))
      (TL saved) entries
      (H ++ [(TL tokens,registry,B',PTc,DRESTRICT TGc (COMPL (set outs)),TL saved,entries)])
Proof
  strip_tac >> drule_all ptr_paired_ret_successor >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  drule ptr_source_ownership_caches >> strip_tac >>
  drule ptr_tagged_chrono_step_projection >> strip_tac >>
  `EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions` by
    (fs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `!key site. FLOOKUP births key = SOME site ==> FLOOKUP B' key = SOME site` by
    (`ptr_activation_tokens h a b tokens = TL tokens` by
       (Cases_on `a.po_stack` >>
        gvs[concretizePtrActivationChronologyTheory.ptr_activation_tokens_def]) >>
     drule concretizePtrActivationBirthsTheory.ptr_source_birth_caches_snoc_retained >>
     disch_then (qspec_then `b` mp_tac) >> simp[]) >>
  `ptr_mixed_vars B' positions (DRESTRICT TGc (COMPL (set outs)))
    b.po_taint b.po_fn zt.po_fn b.po_state zt.po_state` by
    (irule ptr_mixed_vars_retained_births_tvar >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  qexistsl_tac [`b`, `ret`, `sr`, `tr`, `PTc`, `TGc`, `outs`, `B'`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
