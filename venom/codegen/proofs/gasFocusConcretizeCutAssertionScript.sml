Theory gasFocusConcretizeCutAssertion
Ancestors
  gasFocusConcretizeEndpointCut gasFocusConcretizeTaggedSupport
  concretizePtrParamSupport concretizePtrRequestHistory concretizePtrReturnTransport
  concretizePtrValueTransport concretizePtrOpaqueRetpc concretizePtrOrdinaryNext
  concretizePtrPairedPrefix concretizePtrPairedFields concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrLedgerProbe concretizeStepStructure
  concretizePtrChronologicalHistory concretizePtrOperationalOpcodes
  concretizePtrTaintContent concretizePtrSharedFields concretizePtrSourceOwnership
  o1ContractSimplifyCfgSrcFrame[qualified] opcodeClass
  o1SafeUpto o1PassContract o1ScheduleDecomp unitLabelMapIdentity
  venomWf cfgWf unitShapeDefs contextCodegenRel codegenRel frameViewFacts
  ptrDiscipline pointerConfinedDefs venomExecSemantics memLocDefs venomState venomInst
  finite_map list pred_set

Theorem focus_assertion_execution[local]:
  MEM inst.inst_opcode [ASSERT; ASSERT_UNREACHABLE] /\
  eval_operands inst.inst_operands s = eval_operands inst.inst_operands t /\
  step_inst fuel Ct inst t = OK t' ==>
  step_inst 0 C inst s = OK s /\ t' = t
Proof
  strip_tac >> fs[MEM] >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke] >> pure_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[] >> simp[Once opcode_case_def] >> simp[AllCaseEqs()] >>
  strip_tac >> gvs[eval_operands_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem focus_assertion_operand_discipline[local]:
  fn_ptr_ok P fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\ ptr_static_support P fn TG /\
  MEM inst.inst_opcode [ASSERT; ASSERT_UNREACHABLE] ==>
  EVERY (\op. ptr_nonopaque_operand fn op /\ op_prov TG op = NONE /\
              op_taint tn op = {}) inst.inst_operands
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
  simp[EVERY_MEM] >> gen_tac >> strip_tac >>
  `ptr_nonopaque_operand fn op` by fs[EVERY_MEM] >> simp[] >> conj_tac
  >- (Cases_on `op` >> simp[op_prov_def] >>
      Cases_on `FLOOKUP TG s'` >> simp[] >> metis_tac[ptr_static_support_def]) >>
  qpat_x_assum `taint_ok _ _ _ _` mp_tac >> fs[MEM] >>
  simp[taint_ok_def] >> metis_tac[]
QED

Theorem ptr_focus_assertion_step:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  ptr_discipline_upto lo n C vs /\ gas_cut n vs at.po_state /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  MEM a.po_inst.inst_opcode [ASSERT; ASSERT_UNREACHABLE] /\
  ptr_chrono_step C' at zt ==>
  ?z TG'. TG' = step_prov PT TG a.po_inst z.po_state /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens registry births PT TG' saved entries
      (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) calls ws
Proof
  strip_tac >>
  drule_all ptr_paired_endpoint_cut_safety >> strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  drule ptr_frame_context_membership >> strip_tac >>
  drule o1ContractSimplifyCfgSrcFrameTheory.scfg_frame_reachable_active >> strip_tac >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def,
        EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >> metis_tac[]) >>
  `inst_wf a.po_inst` by
    (qpat_assum `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions`
       (mp_tac o REWRITE_RULE [EVERY_MEM]) >> metis_tac[]) >>
  `opaque_use_ok a.po_fn /\ EVERY bb_well_formed a.po_fn.fn_blocks /\
   ALL_DISTINCT (fn_labels a.po_fn)` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, wf_function_def,
        EVERY_MEM] >> metis_tac[]) >>
  `a.po_inst.inst_outputs = []` by (fs[MEM] >> gvs[inst_wf_def, LENGTH_NIL]) >>
  `a.po_inst.inst_opcode <> ALLOCA /\ a.po_inst.inst_opcode <> NOP /\
   a.po_inst.inst_opcode <> INVOKE /\ ~is_terminator a.po_inst.inst_opcode` by
    (fs[MEM] >> simp[is_terminator_def]) >>
  `at.po_inst = a.po_inst` by gvs[concretize_positions_unchanged] >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[ptr_discipline_upto_def, EVERY_MEM] >> metis_tac[]) >>
  `ptr_static_support P a.po_fn TG` by
    (drule_all ptr_focus_source_tagged_support >> simp[]) >>
  `fn_ptr_ok P a.po_fn` by fs[EVERY_MEM] >>
  drule_all focus_assertion_operand_discipline >> strip_tac >>
  `eval_operands a.po_inst.inst_operands a.po_state =
   eval_operands a.po_inst.inst_operands at.po_state` by
    (fs[ptr_paired_sample_def] >>
     `a.po_state.vs_labels = at.po_state.vs_labels` by metis_tac[ptr_history_content_labels] >>
     drule_all ptr_mixed_scalar_operands_equal >> simp[]) >>
  qpat_x_assum `MEM a.po_inst.inst_opcode _` (mk_asm "assertion") >>
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[Excl "MEM"]
  >>~- ([`step_inst _ _ _ _ = IntRet _ _`],
    qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
    simp[step_inst_non_invoke] >> strip_tac >>
    drule step_inst_base_intret_opcodes >> asm_x "assertion" assume_tac >> fs[MEM]) >>
  asm "assertion" assume_tac >>
  `step_inst 0 C a.po_inst a.po_state = OK a.po_state /\ s' = at.po_state` by
    (drule_all focus_assertion_execution >> simp[]) >>
  qpat_x_assum `MEM a.po_inst.inst_opcode _` kall_tac >>
  suspend "attach"
QED

Resume ptr_focus_assertion_step[attach]:
  gvs[] >>
  `?i. active_inst a.po_fn i
     (a.po_state with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (qpat_assum `active_inst a.po_fn a.po_inst a.po_state`
       (mp_then Any mp_tac ptr_ordinary_next_active) >>
     disch_then irule >> simp[]) >>
  qabbrev_tac `z = ptr_ledger_next a i a.po_state` >> qexists_tac `z` >>
  `ALL_DISTINCT (fn_labels at.po_fn)` by
    (fs[ptr_paired_code_def] >> metis_tac[fn_labels_def, concretize_positions_labels]) >>
  drule ptr_paired_stage_local_allocas >>
  disch_then (qspecl_then [`o1_walk_view rpolicy 2`, `rpolicy`] mp_tac) >>
  simp[] >> strip_tac >>
  asm_x "assertion" assume_tac >> fs[MEM] >>
  `ptr_paired_sample positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    (simp[ptr_paired_sample_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def,
          step_prov_def, set_prov_def, step_taint_def, set_var_taint_def,
          DRESTRICT_UNIV] >>
     reverse conj_tac
     >- (fs[ptr_paired_sample_def] >> irule ptr_history_content_masks >>
         qexists_tac `a.po_taint` >>
         fs[MEM, adopt_reset_def, store_taint_def, imm_taint_def]) >>
     irule ptr_mixed_vars_fields >> fs[ptr_paired_sample_def] >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `ptr_paired_params positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    fs[ptr_paired_params_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
  drule ptr_paired_prefix_ordinary_nonwrite >> disch_then irule >>
  simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def, ptr_tagged_step_def] >>
  fs[MEM] >> simp[step_prov_def, out_prov_def, step_writes_def,
       source_memory_write_ranges_def, fixed_source_write_range_def, range_bytes_def] >>
  qexistsl_tac [`0`, `a.po_state`] >> simp[]
QED

Finalise ptr_focus_assertion_step
