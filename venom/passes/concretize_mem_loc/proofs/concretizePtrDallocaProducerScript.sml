(*
 * The DALLOCA step producer for the paired prefix. DALLOCA pointers are
 * untagged: the output gets no tag in TG, and both sides return the same
 * free-memory pointer word and bump it by the same amount.
 *)
Theory concretizePtrDallocaProducer
Ancestors concretizePtrRequestHistory concretizePtrReturnTransport
  concretizePtrTaggedSupport concretizePtrSourceOwnership concretizePtrValueTransport
  concretizePtrPairedNextAttach concretizePtrPairedPrefixProbe
  concretizePtrOpaqueRetpc concretizeStepStructure concretizeStepShape
  concretizeStepRetpc concretizeStageShape
  concretizePtrOperationalOpcodes opcodeClass concretizePtrOrdinaryNext
  concretizePtrPairedPrefix concretizePtrPairedFields concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrChronologicalHistory concretizePtrAllocationSize
  concretizePtrDeletedGapHistory concretizePtrLedgerProbe concretizePtrLedgerAlignment
  concretizePtrPrefixLedger concretizePtrSharedFields concretizePtrStagePlacements
  concretizePtrDeletedGaps concretizePtrExecutedCoverage concretizePtrTaintContent
  o1PassContract o1ScheduleDecomp
  venomWf cfgWf unitLabelMapIdentity contextCodegenRel codegenRel frameViewFacts
  ptrDiscipline pointerConfinedDefs unitShapeDefs venomExecSemantics memLocDefs
  venomState venomInst finite_map list pred_set

Theorem ptr_history_content_fmp[local]:
  ptr_history_content tn s t ==>
  ptr_history_content tn (s with vs_fmp := v) (t with vs_fmp := v)
Proof
  simp[ptr_history_content_def, ptr_taint_content_def, ptr_taint_control_def,
       ptr_core_shared_def, ptr_shared_fields_def,
       contract_storage_def, contract_transient_def]
QED

Theorem ptr_dalloca_execution[local]:
  inst.inst_opcode = DALLOCA /\ s.vs_fmp = t.vs_fmp /\
  eval_operands inst.inst_operands s = eval_operands inst.inst_operands t /\
  step_inst fuel Ct inst t = OK t' ==>
  ?sz_op out sz. inst.inst_operands = [sz_op] /\ inst.inst_outputs = [out] /\
    eval_operand sz_op s = SOME sz /\
    step_inst 0 C inst s =
      OK (update_var out s.vs_fmp
            (s with vs_fmp := s.vs_fmp + n2w (ceil32 (w2n sz)))) /\
    t' = update_var out s.vs_fmp
           (t with vs_fmp := s.vs_fmp + n2w (ceil32 (w2n sz)))
Proof
  strip_tac >> qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke] >> PURE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[] >> simp[Once opcode_case_def] >>
  simp[AllCaseEqs()] >> strip_tac >>
  gvs[eval_operands_def, AllCaseEqs()]
QED

Theorem ptr_mixed_dalloca_update[local]:
  ptr_mixed_vars births positions TG tn f g s t /\
  inst.inst_opcode = DALLOCA /\ inst.inst_operands = [sz_op] /\
  inst.inst_outputs = [out] /\ eval_operand sz_op s = SOME sz /\
  ~retpc_var f out ==>
  ptr_mixed_vars births positions (set_prov TG [out] NONE)
    (step_taint inst s (update_var out v (s with vs_fmp := w)) tn)
    f g (update_var out v (s with vs_fmp := w))
        (update_var out v (t with vs_fmp := w))
Proof
  strip_tac >>
  `ptr_mixed_vars births positions TG tn f g (s with vs_fmp := w)
     (t with vs_fmp := w)` by
    (irule ptr_mixed_vars_fields >> goal_assum (drule_at Any) >> simp[]) >>
  drule ptr_mixed_vars_update >> disch_then irule >> simp[] >>
  simp[set_prov_def, step_taint_def, out_taint_def, set_var_taint_def,
       op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, ptr_value_transport_refl] >>
  rpt strip_tac >> fs[ptr_mixed_vars_def, op_taint_def]
QED

Theorem ptr_paired_prefix_dalloca:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ptr_discipline lo C vs /\ EVERY ssa_form C.ctx_functions /\
  a.po_inst.inst_opcode = DALLOCA /\ ptr_chrono_step C' at zt ==>
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
  `a.po_inst.inst_opcode <> ALLOCA /\ a.po_inst.inst_opcode <> NOP /\
   a.po_inst.inst_opcode <> INVOKE /\ a.po_inst.inst_opcode <> ASSIGN /\
   a.po_inst.inst_opcode <> PHI /\ a.po_inst.inst_opcode <> RETPC_PARAM /\
   ~is_terminator a.po_inst.inst_opcode` by simp[is_terminator_def] >>
  `EVERY (\op. ptr_nonopaque_operand a.po_fn op /\ op_prov TG op = NONE /\
     op_taint a.po_taint op = {}) a.po_inst.inst_operands` by suspend "operands" >>
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
    (qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
     simp[step_inst_non_invoke] >> strip_tac >>
     drule step_inst_base_intret_opcodes >> fs[MEM]) >>
  `a.po_state.vs_fmp = at.po_state.vs_fmp /\
   a.po_state.vs_labels = at.po_state.vs_labels` by
    (fs[ptr_paired_sample_def] >> drule ptr_history_content_control >>
     simp[ptr_taint_control_def, ptr_core_shared_def, ptr_shared_fields_def]) >>
  `eval_operands a.po_inst.inst_operands a.po_state =
   eval_operands a.po_inst.inst_operands at.po_state` by
    (fs[ptr_paired_sample_def] >> drule_all ptr_mixed_scalar_operands_equal >> simp[]) >>
  `?sz_op out sz. a.po_inst.inst_operands = [sz_op] /\ a.po_inst.inst_outputs = [out] /\
    eval_operand sz_op a.po_state = SOME sz /\
    step_inst 0 C a.po_inst a.po_state =
      OK (update_var out a.po_state.vs_fmp
            (a.po_state with vs_fmp := a.po_state.vs_fmp + n2w (ceil32 (w2n sz)))) /\
    s' = update_var out a.po_state.vs_fmp
           (at.po_state with vs_fmp := a.po_state.vs_fmp + n2w (ceil32 (w2n sz)))` by
    (drule_all ptr_dalloca_execution >> disch_then (qspec_then `C` mp_tac) >> simp[]) >>
  qabbrev_tac `post = update_var out a.po_state.vs_fmp
    (a.po_state with vs_fmp := a.po_state.vs_fmp + n2w (ceil32 (w2n sz)))` >>
  `~retpc_var a.po_fn out` by
    (irule noncopy_output_not_retpc >>
     conj_tac >- fs[EVERY_MEM] >> qexists_tac `a.po_inst` >> simp[]) >>
  `ptr_mixed_vars births positions (set_prov TG [out] NONE)
    (step_taint a.po_inst a.po_state post a.po_taint)
    a.po_fn at.po_fn post s'` by
    (fs[ptr_paired_sample_def, Abbr `post`] >>
     irule ptr_mixed_dalloca_update >> simp[]) >>
  `?i. active_inst a.po_fn i (post with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (`EVERY bb_well_formed a.po_fn.fn_blocks` by
       (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
     qpat_assum `active_inst a.po_fn a.po_inst a.po_state`
       (mp_then Any mp_tac ptr_ordinary_next_active) >>
     disch_then irule >> simp[Abbr `post`, update_var_def]) >>
  qabbrev_tac `z = ptr_ledger_next a i post` >>
  qexists_tac `z` >>
  `ALL_DISTINCT (fn_labels a.po_fn)` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  `ALL_DISTINCT (fn_labels at.po_fn)` by
    (fs[ptr_paired_code_def] >> metis_tac[fn_labels_def, concretize_positions_labels]) >>
  drule ptr_paired_stage_local_allocas >>
  disch_then (qspecl_then [`o1_walk_view rpolicy 2`,`rpolicy`] mp_tac) >>
  simp[] >> strip_tac >>
  `ptr_paired_sample positions z zt
     (tokens,registry,births,PT,set_prov TG [out] NONE,saved,entries)` by
    (simp[ptr_paired_sample_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
     (reverse conj_tac
      >- (fs[ptr_paired_sample_def] >> irule ptr_history_content_masks >>
          qexists_tac `a.po_taint` >>
          simp[Abbr `post`, step_taint_def, set_var_taint_def, store_taint_def,
               adopt_reset_def, imm_taint_def] >>
          irule ptr_history_content_fmp >> simp[]) >>
      irule ptr_mixed_vars_fields >> rpt (goal_assum (drule_at Any)) >>
      simp[])) >>
  `ptr_paired_params positions z zt
     (tokens,registry,births,PT,set_prov TG [out] NONE,saved,entries)` by
    (fs[ptr_paired_params_def, Abbr `z`, Abbr `post`, ptr_ledger_next_def,
        ptr_observe_def, update_var_def]) >>
  drule ptr_paired_prefix_ordinary_nonwrite >> disch_then irule >>
  simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def,
       ptr_tagged_step_def, step_writes_def,
       source_memory_write_ranges_def, fixed_source_write_range_def, range_bytes_def] >>
  (reverse conj_tac >- fs[Abbr `post`, update_var_def] >>
   qexistsl_tac [`0`, `post`] >> fs[Abbr `post`, update_var_def])
QED

Resume ptr_paired_prefix_dalloca[operands]:
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def,
        EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >> metis_tac[]) >>
  `!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P a.po_fn` by
    (rpt strip_tac >> irule ptr_source_tagged_var_support >>
     rpt (goal_assum (drule_at Any))) >>
  `taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `fn_ptr_ok P a.po_fn /\ opaque_use_ok a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM] >> metis_tac[]) >>
  `EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> simp[]) >>
  `!v. MEM (Var v) a.po_inst.inst_operands ==> v NOTIN fn_pv P a.po_fn` by
    (qpat_x_assum `fn_ptr_ok P a.po_fn` mp_tac >>
     simp[fn_ptr_ok_def] >> strip_tac >>
     qpat_x_assum `!inst. MEM inst (fn_insts a.po_fn) ==> _`
       (qspec_then `a.po_inst` mp_tac) >> simp[] >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def,
          mem_write_ops_def, mem_read_ops_def] >> metis_tac[]) >>
  simp[EVERY_MEM] >> gen_tac >> strip_tac >>
  `ptr_nonopaque_operand a.po_fn op` by fs[EVERY_MEM] >> simp[] >> conj_tac
  >- (Cases_on `op` >> simp[op_prov_def] >>
      Cases_on `FLOOKUP TG s` >> simp[] >> metis_tac[]) >>
  qpat_x_assum `taint_ok _ _ _ _` mp_tac >>
  simp[taint_ok_def] >> metis_tac[]
QED
Finalise ptr_paired_prefix_dalloca
