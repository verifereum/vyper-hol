Theory gasFocusConcretizeCutFmpOps
Ancestors
  gasFocusConcretizeTaggedSupport concretizePtrDallocaProducer
  concretizePtrOpaqueRetpc concretizePtrValueTransport concretizePtrOrdinaryNext
  concretizePtrPairedPrefix concretizePtrPairedFields concretizePtrStructuralTranscript
  concretizePtrSourceOwnership concretizePtrStructuralTrace
  concretizePtrChronologicalHistory concretizePtrDeletedGapHistory
  concretizePtrRequestHistory concretizePtrTaintContent concretizePtrLedgerProbe
  concretizePtrParamSupport concretizePtrSharedFields concretizePtrReturnTransport
  concretizeStepStructure concretizePtrOperationalOpcodes
  o1PassContract o1ScheduleDecomp ptrDiscipline pointerConfinedDefs
  contextCodegenRel codegenRel frameViewFacts unitLabelMapIdentity
  unitShapeDefs venomWf venomState venomInst venomExecSemantics venomInstProofs1
  opcodeClass memLocDefs finite_map list pred_set words
  o1FrameLockstep ptrTaintClean lowerDloadPtrScalar

(* These instructions do not accept a displaced fixed-allocation pointer. *)
Theorem cut_fmp_scalar_operands[local]:
  fn_ptr_ok P f /\ opaque_use_ok f /\ MEM inst (fn_insts f) /\
  taint_ok f tn inst s /\ ptr_static_support P f TG /\
  MEM inst.inst_opcode [INITIAL_FMP; BUMP; DALLOCA] ==>
  EVERY (\op. ptr_nonopaque_operand f op /\ op_prov TG op = NONE /\
              op_taint tn op = {}) inst.inst_operands
Proof
  strip_tac >>
  `EVERY (ptr_nonopaque_operand f) inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> fs[MEM]) >>
  `!v. MEM (Var v) inst.inst_operands ==> v NOTIN fn_pv P f` by
    (qpat_x_assum `fn_ptr_ok P f` mp_tac >> simp[fn_ptr_ok_def] >> strip_tac >>
     qpat_x_assum `!i. MEM i (fn_insts f) ==> _` (qspec_then `inst` mp_tac) >>
     simp[] >> fs[MEM] >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def,
          mem_write_ops_def, mem_read_ops_def] >> metis_tac[]) >>
  simp[EVERY_MEM] >> gen_tac >> strip_tac >>
  `ptr_nonopaque_operand f op` by fs[EVERY_MEM] >> simp[] >> conj_tac
  >- (Cases_on `op` >> simp[op_prov_def] >>
      Cases_on `FLOOKUP TG s'` >> gvs[ptr_static_support_def] >> metis_tac[]) >>
  qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
  simp[taint_ok_def] >> fs[MEM] >> metis_tac[]
QED

(* BUMP binds two words but does not move the frame field. DALLOCA binds
   the old FMP and advances the field by its rounded size. *)
Theorem cut_fmp_op_execution[local]:
  MEM inst.inst_opcode [INITIAL_FMP; BUMP; DALLOCA] /\
  s.vs_initial_fmp = t.vs_initial_fmp /\ s.vs_fmp = t.vs_fmp /\
  eval_operands inst.inst_operands s = eval_operands inst.inst_operands t /\
  step_inst fuel Ct inst t = OK t' ==>
  ?s' w vals. step_inst 0 C inst s = OK s' /\
    bind_outputs inst.inst_outputs vals (s with vs_fmp := w) = SOME s' /\
    bind_outputs inst.inst_outputs vals (t with vs_fmp := w) = SOME t'
Proof
  strip_tac >> fs[MEM]
  >- (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
      simp[step_inst_non_invoke] >> pure_rewrite_tac[step_inst_base_def] >>
      asm_rewrite_tac[] >> simp[Once opcode_case_def, AllCaseEqs()] >> strip_tac >>
      gvs[] >> qexistsl_tac [`t.vs_fmp`, `[t.vs_initial_fmp]`] >>
      `s with vs_fmp := t.vs_fmp = s` by simp[venom_state_component_equality] >>
      simp[bind_outputs_def])
  >- (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
      simp[step_inst_non_invoke] >> pure_rewrite_tac[step_inst_base_def] >>
      asm_rewrite_tac[] >> simp[Once opcode_case_def, AllCaseEqs()] >> strip_tac >>
      gvs[eval_operands_def, AllCaseEqs()] >>
      qmatch_goalsub_rename_tac `update_var n (b + sz) (update_var p b t)` >>
      qexistsl_tac [`t.vs_fmp`, `[b;b+sz]`] >>
      `s with vs_fmp := t.vs_fmp = s` by simp[venom_state_component_equality] >>
      simp[bind_outputs_def]) >>
  drule_all ptr_dalloca_execution >> disch_then (qspec_then `C` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `s with vs_fmp := next_fmp` >>
  qexistsl_tac [`update_var out s.vs_fmp (s with vs_fmp := next_fmp)`,
                `next_fmp`, `[s.vs_fmp]`] >>
  simp[bind_outputs_def]
QED

Theorem cut_fmp_bind_fields[local]:
  bind_outputs outs vals (s with vs_fmp := w) = SOME s' ==>
  s'.vs_params = s.vs_params /\ s'.vs_allocas = s.vs_allocas /\
  s'.vs_current_bb = s.vs_current_bb /\ s'.vs_prev_bb = s.vs_prev_bb
Proof
  strip_tac >>
  qspec_then `(\u. u.vs_params = s.vs_params /\ u.vs_allocas = s.vs_allocas /\
                   u.vs_current_bb = s.vs_current_bb /\ u.vs_prev_bb = s.vs_prev_bb)`
    mp_tac bind_outputs_preserves >> simp[update_var_def] >>
  disch_then drule >> simp[]
QED

Theorem cut_fmp_bind_mixed[local]:
  ptr_mixed_vars births positions TG tn f g s t /\
  MEM inst.inst_opcode [INITIAL_FMP; BUMP; DALLOCA] /\
  (!out. MEM out inst.inst_outputs ==> ~retpc_var f out) /\
  bind_outputs inst.inst_outputs vals (s with vs_fmp := w) = SOME s' /\
  bind_outputs inst.inst_outputs vals (t with vs_fmp := w) = SOME t' ==>
  ptr_mixed_vars births positions (set_prov TG inst.inst_outputs NONE)
    (step_taint inst s s' tn) f g s' t'
Proof
  strip_tac >>
  `ptr_mixed_vars births positions TG tn f g (s with vs_fmp := w)
     (t with vs_fmp := w)` by
    (irule ptr_mixed_vars_fields >> goal_assum (drule_at Any) >> simp[]) >>
  `LENGTH inst.inst_outputs = LENGTH vals` by fs[bind_outputs_def, AllCaseEqs()] >>
  irule ptr_mixed_bind_outputs >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  suspend "tags"
QED

Resume cut_fmp_bind_mixed[tags]:
  conj_tac
  >- (rpt strip_tac >>
      simp[FLOOKUP_set_prov, step_taint_def, op_taint_def, set_var_taint_lookup] >>
      fs[ptr_mixed_vars_def, op_taint_def]) >>
  `out_taint tn inst s = {}` by (fs[MEM] >> simp[out_taint_opcode_exclusion]) >>
  simp[LIST_REL_EL_EQN, LENGTH_ZIP, EL_ZIP] >> rpt strip_tac >>
  `MEM (EL n inst.inst_outputs) inst.inst_outputs` by metis_tac[MEM_EL] >>
  `~retpc_var f (EL n inst.inst_outputs)` by metis_tac[] >>
  simp[step_prov_def, FLOOKUP_set_prov, step_taint_def,
       op_taint_def, ptr_value_transport_scalar_empty] >>
  Cases_on `inst.inst_outputs` >> gvs[set_var_taint_def, FLOOKUP_DRESTRICT] >>
  Cases_on `t''` >> gvs[set_var_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
                       ptr_value_transport_scalar_empty]
QED

Finalise cut_fmp_bind_mixed[local]

Theorem ptr_focus_fmp_op_step:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  EVERY ssa_form C.ctx_functions /\
  (?P. EVERY (fn_ptr_ok P) C.ctx_functions) /\
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  MEM a.po_inst.inst_opcode [INITIAL_FMP; BUMP; DALLOCA] /\
  ptr_chrono_step C' at zt ==>
  ?z TG'.
    TG' = set_prov TG a.po_inst.inst_outputs NONE /\
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
  `active_inst a.po_fn a.po_inst a.po_state` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def] >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >>
     metis_tac[]) >>
  drule_all ptr_focus_source_tagged_support >> strip_tac >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
  `a.po_inst.inst_opcode <> ALLOCA /\ a.po_inst.inst_opcode <> NOP /\
   a.po_inst.inst_opcode <> INVOKE /\ a.po_inst.inst_opcode <> ASSIGN /\
   a.po_inst.inst_opcode <> PHI /\ a.po_inst.inst_opcode <> RETPC_PARAM /\
   ~is_terminator a.po_inst.inst_opcode` by (fs[MEM] >> simp[is_terminator_def]) >>
  `!out. MEM out a.po_inst.inst_outputs ==> ~retpc_var a.po_fn out` by
    (gen_tac >> disch_tac >> irule noncopy_output_not_retpc >>
     conj_tac >- fs[EVERY_MEM] >> qexists_tac `a.po_inst` >> simp[]) >>
  `EVERY (\op. ptr_nonopaque_operand a.po_fn op /\ op_prov TG op = NONE /\
              op_taint a.po_taint op = {}) a.po_inst.inst_operands` by
    (`opaque_use_ok a.po_fn /\ fn_ptr_ok P a.po_fn` by
       (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM] >> metis_tac[]) >>
     drule_all cut_fmp_scalar_operands >> simp[]) >>
  `at.po_inst = a.po_inst` by gvs[concretize_positions_unchanged] >>
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[Excl "MEM"]
  >>~- ([`step_inst _ _ _ _ = IntRet _ _`],
    qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
    simp[step_inst_non_invoke] >> strip_tac >>
    drule step_inst_base_intret_opcodes >> fs[MEM]) >>
  suspend "execute"
QED

Resume ptr_focus_fmp_op_step[execute]:
  markerLib.RESUME_TAC >>
  `a.po_state.vs_initial_fmp = at.po_state.vs_initial_fmp /\
   a.po_state.vs_fmp = at.po_state.vs_fmp /\
   a.po_state.vs_labels = at.po_state.vs_labels` by
    (fs[ptr_paired_sample_def] >> drule ptr_history_content_control >>
     simp[ptr_taint_control_def, ptr_core_shared_def, ptr_shared_fields_def]) >>
  `eval_operands a.po_inst.inst_operands a.po_state =
   eval_operands a.po_inst.inst_operands at.po_state` by
    (fs[ptr_paired_sample_def] >> drule_all ptr_mixed_scalar_operands_equal >> simp[]) >>
  `?post w vals. step_inst 0 C a.po_inst a.po_state = OK post /\
     bind_outputs a.po_inst.inst_outputs vals (a.po_state with vs_fmp := w) = SOME post /\
     bind_outputs a.po_inst.inst_outputs vals (at.po_state with vs_fmp := w) = SOME s'` by
    (irule cut_fmp_op_execution >> rpt (goal_assum (drule_at Any)) >> simp[MEM] >>
     goal_assum (drule_at Any)) >>
  every_drule_then strip_assume_tac cut_fmp_bind_fields >>
  `?i. active_inst a.po_fn i (post with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (`EVERY bb_well_formed a.po_fn.fn_blocks` by
       (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
     qpat_assum `active_inst a.po_fn a.po_inst a.po_state`
       (mp_then Any mp_tac ptr_ordinary_next_active) >>
     disch_then irule >> simp[]) >>
  qabbrev_tac `z = ptr_ledger_next a i post` >>
  qexists_tac `z` >> simp[] >>
  `ALL_DISTINCT (fn_labels a.po_fn)` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  `ALL_DISTINCT (fn_labels at.po_fn)` by
    (fs[ptr_paired_code_def] >> metis_tac[fn_labels_def, concretize_positions_labels]) >>
  drule ptr_paired_stage_local_allocas >>
  disch_then (qspecl_then [`o1_walk_view rpolicy 2`,`rpolicy`] mp_tac) >>
  simp[] >> strip_tac >>
  suspend "attach"
QED

Resume ptr_focus_fmp_op_step[attach]:
  markerLib.RESUME_TAC >>
  `ptr_mixed_vars births positions (set_prov TG a.po_inst.inst_outputs NONE)
    (step_taint a.po_inst a.po_state post a.po_taint) a.po_fn at.po_fn post s'` by
    (fs[ptr_paired_sample_def] >> irule cut_fmp_bind_mixed >> simp[MEM] >>
     qexistsl_tac [`at.po_state`, `vals`, `w`] >> simp[]) >>
  `ptr_paired_sample positions z zt
     (tokens,registry,births,PT,set_prov TG a.po_inst.inst_outputs NONE,saved,entries)` by
    (simp[ptr_paired_sample_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
     (reverse conj_tac
      >- (fs[ptr_paired_sample_def] >> irule ptr_history_content_masks >>
          qexists_tac `a.po_taint` >>
          `ptr_history_content a.po_taint post s'` by
            (irule ptr_history_content_bind_outputs >>
             rpt (goal_assum (drule_at Any)) >>
             irule concretizePtrDallocaProducerTheory.ptr_history_content_fmp >> simp[]) >>
          fs[MEM] >> simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def])) >>
     irule ptr_mixed_vars_fields >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `ptr_paired_params positions z zt
     (tokens,registry,births,PT,set_prov TG a.po_inst.inst_outputs NONE,saved,entries)` by
    fs[ptr_paired_params_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
  drule ptr_paired_prefix_ordinary_nonwrite >> disch_then irule >>
  simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def, ptr_tagged_step_def] >>
  fs[MEM] >> simp[step_prov_def, out_prov_def, step_writes_def,
       source_memory_write_ranges_def, fixed_source_write_range_def, range_bytes_def] >>
  qexistsl_tac [`0`, `post`] >> fs[]
QED

Finalise ptr_focus_fmp_op_step
