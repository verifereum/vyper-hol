Theory gasFocusConcretizeCutScalar
Ancestors
  gasFocusConcretizeTaggedSupport concretizePtrScalarCoreProducer
  concretizePtrShiftProducer concretizePtrReturnTransport concretizePtrOpaqueRetpc
  concretizePtrPairedPrefix concretizePtrPairedFields concretizePtrOrdinaryNext
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrSourceOwnership concretizePtrChronologicalHistory
  concretizePtrLedgerProbe concretizePtrRequestHistory concretizePtrValueTransport
  concretizePtrParamSupport concretizePtrDeletedGapHistory concretizePtrTaintContent
  concretizeStepStructure concretizePtrOperationalOpcodes frameRelocationGuardedValues
  o1PassContract o1ScheduleDecomp ptrDiscipline pointerConfinedDefs
  contextCodegenRel codegenRel frameViewFacts unitLabelMapIdentity
  unitShapeDefs venomWf
  venomExecSemantics venomState venomInst opcodeClass finite_map list pred_set words

Theorem focus_scalar_equal_execution[local]:
  MEM i.inst_opcode
    [Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD; SLT; SGT;
     ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET] /\
  eval_operands i.inst_operands s = eval_operands i.inst_operands t /\
  i.inst_outputs = [out] /\ step_inst fuel Ct i t = OK post ==>
  ?v. step_inst 0 C i s = OK (update_var out v s) /\ post = update_var out v t
Proof
  strip_tac >> fs[MEM] >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke] >>
  pure_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[] >>
  simp[Once opcode_case_def] >>
  simp[exec_pure1_def, exec_pure2_def, exec_pure3_def, AllCaseEqs()] >>
  strip_tac >> gvs[eval_operands_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem focus_scalar_mul_execution[local]:
  ptr_mixed_vars births positions TG tn f g s t /\
  s.vs_labels = t.vs_labels /\ taint_ok f tn i s /\
  EVERY (\op. ptr_nonopaque_operand f op /\ op_prov TG op = NONE) i.inst_operands /\
  i.inst_opcode = MUL /\ i.inst_outputs = [out] /\ step_inst fuel Ct i t = OK post ==>
  ?v w. step_inst 0 C i s = OK (update_var out v s) /\
    post = update_var out w t /\
    ptr_value_transport births positions NONE (out_taint tn i s) v w
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  `ptr_lookup_transport births positions NONE (op_taint tn op1)
     (eval_operand op1 s) (SOME v1)` by metis_tac[ptr_mixed_vars_eval] >>
  `ptr_lookup_transport births positions NONE (op_taint tn op2)
     (eval_operand op2 s) (SOME v2)` by metis_tac[ptr_mixed_vars_eval] >>
  gvs[ptr_lookup_transport_some_right, ptr_value_transport_def] >>
  rename1 `eval_operand op1 s = SOME x1` >>
  rename1 `eval_operand op2 s = SOME x2` >>
  `op_taint tn op1 = {} \/
    (op_taint tn op2 = {} /\ (x2 = 0w \/ x2 = 1w))` by
    (Cases_on `op_taint tn op1 = {}` >- simp[] >>
     qpat_x_assum `taint_ok _ _ _ _` mp_tac >> simp[taint_ok_def] >>
     strip_tac >> first_x_assum (qspec_then `op1` mp_tac) >>
     simp[] >> strip_tac >> gvs[]) >>
  `op_taint tn op2 = {} \/
    (op_taint tn op1 = {} /\ (x1 = 0w \/ x1 = 1w))` by
    (Cases_on `op_taint tn op2 = {}` >- simp[] >>
     qpat_x_assum `taint_ok _ _ _ _` mp_tac >> simp[taint_ok_def] >>
     strip_tac >> first_x_assum (qspec_then `op2` mp_tac) >>
     simp[] >> strip_tac >> gvs[]) >>
  `word_agree_except (out_taint tn i s) (x1 * x2) (v1 * v2)` by
    (mp_tac (Q.INST [`m` |-> `op_taint tn op1`, `n` |-> `op_taint tn op2`,
       `x` |-> `x1`, `y` |-> `x2`, `x'` |-> `v1`, `y'` |-> `v2`]
       word_agree_except_selector_mul) >> simp[out_taint_def]) >>
  qexistsl_tac [`x1 * x2`, `v1 * v2`] >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_pure2_def,
       ptr_value_transport_def]
QED

(* All of these outputs lose provenance, but their byte mask need not be empty. *)
Theorem focus_scalar_update[local]:
  ptr_mixed_vars births positions TG tn f g s t /\ ~retpc_var f out /\
  i.inst_outputs = [out] /\
  MEM i.inst_opcode
    [MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD; SLT; SGT;
     ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET; SHL; SHR; SAR] /\
  ptr_value_transport births positions NONE (out_taint tn i s) v w ==>
  ptr_mixed_vars births positions (step_prov PT TG i (update_var out v s))
    (step_taint i s (update_var out v s) tn) f g
    (update_var out v s) (update_var out w t)
Proof
  strip_tac >> drule ptr_mixed_vars_update >> disch_then irule >> simp[] >>
  fs[MEM] >>
  simp[step_prov_def, out_prov_def, set_prov_def, step_taint_def,
       set_var_taint_def, op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> fs[ptr_mixed_vars_def, op_taint_def] >> gvs[FLOOKUP_UPDATE]
QED

Theorem focus_scalar_core_transport[local]:
  fn_ptr_ok P f /\ opaque_use_ok f /\ MEM i (fn_insts f) /\
  taint_ok f tn i s /\ ptr_static_support P f (TG : string |-> num # num) /\
  ptr_mixed_vars births positions TG tn f g s t /\ s.vs_labels = t.vs_labels /\
  MEM i.inst_opcode
    [MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD; SLT; SGT;
     ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET] /\
  i.inst_outputs = [out] /\ step_inst fuel Ct i t = OK post ==>
  ?v w. step_inst 0 C i s = OK (update_var out v s) /\ post = update_var out w t /\
    ptr_value_transport births positions NONE (out_taint tn i s) v w
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EVERY (\op. ptr_nonopaque_operand f op /\ op_prov TG op = NONE /\
          (i.inst_opcode <> MUL ==> op_taint tn op = {})) i.inst_operands` by
    (irule ptr_scalar_core_operand_discipline >> simp[] >> conj_tac
     >- (qexists_tac `P` >> fs[ptr_static_support_def]) >>
     qexists_tac `s` >> simp[]) >>
  Cases_on `i.inst_opcode = MUL`
  >- (`EVERY (\op. ptr_nonopaque_operand f op /\ op_prov TG op = NONE)
          i.inst_operands` by fs[EVERY_MEM] >>
      drule_all focus_scalar_mul_execution >> simp[]) >>
  `eval_operands i.inst_operands s = eval_operands i.inst_operands t` by
    (irule ptr_mixed_scalar_operands_equal >>
     rpt (goal_assum (drule_at Any)) >> fs[EVERY_MEM]) >>
  `MEM i.inst_opcode
     [Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD; SLT; SGT;
      ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET]` by fs[MEM] >>
  drule_all focus_scalar_equal_execution >>
  disch_then (qspec_then `C` strip_assume_tac) >> qexistsl_tac [`v`,`v`] >>
  simp[ptr_value_transport_refl]
QED

Theorem focus_scalar_transport[local]:
  fn_ptr_ok P f /\ opaque_use_ok f /\ MEM i (fn_insts f) /\ inst_wf i /\
  taint_ok f tn i s /\ ptr_static_support P f (TG : string |-> num # num) /\
  ptr_mixed_vars births positions TG tn f g s t /\ s.vs_labels = t.vs_labels /\
  MEM i.inst_opcode
    [MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD; SLT; SGT;
     ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET; SHL; SHR; SAR] /\
  i.inst_outputs = [out] /\ step_inst fuel Ct i t = OK post ==>
  ?v w. step_inst 0 C i s = OK (update_var out v s) /\ post = update_var out w t /\
    ptr_value_transport births positions NONE (out_taint tn i s) v w
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `MEM i.inst_opcode [SHL; SHR; SAR]`
  >- (`?n a. i.inst_operands = [n; a]` by
        (qpat_x_assum `MEM i.inst_opcode [SHL; SHR; SAR]` mp_tac >>
         simp[MEM] >> strip_tac >> gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute]) >>
      qpat_assum `ptr_static_support _ _ _`
        (assume_tac o REWRITE_RULE [ptr_static_support_def]) >>
      drule_all ptr_shift_operand_discipline >> strip_tac >>
      drule_all concretizePtrShiftProducerTheory.ptr_shift_execution >> simp[]) >>
  `MEM i.inst_opcode
     [MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD; SLT; SGT;
      ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET]` by fs[MEM] >>
  drule_all focus_scalar_core_transport >> simp[]
QED

Theorem ptr_focus_scalar_step:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  EVERY ssa_form C.ctx_functions /\
  (?P. EVERY (fn_ptr_ok P) C.ctx_functions) /\
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  MEM a.po_inst.inst_opcode
    [MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD; SLT; SGT;
     ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET; SHL; SHR; SAR] /\
  ptr_chrono_step C' at zt ==>
  ?z TG'.
    TG' = step_prov PT TG a.po_inst z.po_state /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens registry births PT TG' saved entries
      (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) calls ws
Proof
  disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  qpat_x_assum `MEM a.po_inst.inst_opcode _` (mk_asm "scalar") >>
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
  `inst_wf a.po_inst` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `?out. a.po_inst.inst_outputs = [out]` by
    (asm "scalar" mp_tac >> simp[MEM] >> strip_tac >>
     gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute]) >>
  `a.po_inst.inst_opcode <> ALLOCA /\ a.po_inst.inst_opcode <> NOP /\
   a.po_inst.inst_opcode <> INVOKE /\ a.po_inst.inst_opcode <> ASSIGN /\
   a.po_inst.inst_opcode <> PHI /\ a.po_inst.inst_opcode <> RETPC_PARAM /\
   ~is_terminator a.po_inst.inst_opcode` by
    (asm "scalar" mp_tac >> simp[MEM] >> strip_tac >> simp[is_terminator_def]) >>
  `~retpc_var a.po_fn out` by
    (irule noncopy_output_not_retpc >>
     conj_tac >- fs[EVERY_MEM] >> qexists_tac `a.po_inst` >> simp[]) >>
  `fn_ptr_ok P a.po_fn /\ opaque_use_ok a.po_fn /\
   EVERY bb_well_formed a.po_fn.fn_blocks /\ ALL_DISTINCT (fn_labels a.po_fn)` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, wf_function_def,
        EVERY_MEM] >> metis_tac[]) >>
  `at.po_inst = a.po_inst` by gvs[concretize_positions_unchanged] >>
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[Excl "MEM"]
  >>~- ([`step_inst _ _ _ _ = IntRet _ _`],
    qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
    simp[step_inst_non_invoke] >> strip_tac >>
    drule step_inst_base_intret_opcodes >>
    asm "scalar" mp_tac >> simp[MEM] >> strip_tac >> strip_tac >> gvs[]) >>
  suspend "attach"
QED

Resume ptr_focus_scalar_step[attach]:
  markerLib.RESUME_TAC >>
  `?v w. step_inst 0 C a.po_inst a.po_state = OK (update_var out v a.po_state) /\
     s' = update_var out w at.po_state /\
     ptr_mixed_vars births positions
       (step_prov PT TG a.po_inst (update_var out v a.po_state))
       (step_taint a.po_inst a.po_state (update_var out v a.po_state) a.po_taint)
       a.po_fn at.po_fn (update_var out v a.po_state) s'` by
    (qpat_assum `ptr_paired_sample _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ptr_paired_sample_def]) >>
     drule_then assume_tac ptr_history_content_labels >>
     asm "scalar" assume_tac >> drule_all focus_scalar_transport >>
     disch_then (qspec_then `C` strip_assume_tac) >>
     qexistsl_tac [`v`,`w`] >> simp[] >> irule focus_scalar_update >> simp[] >>
     metis_tac[]) >>
  `?i. active_inst a.po_fn i
     ((update_var out v a.po_state) with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (qpat_assum `active_inst a.po_fn a.po_inst a.po_state`
       (mp_then Any mp_tac ptr_ordinary_next_active) >>
     disch_then irule >> simp[update_var_def]) >>
  qabbrev_tac `z = ptr_ledger_next a i (update_var out v a.po_state)` >>
  qexists_tac `z` >>
  `ALL_DISTINCT (fn_labels at.po_fn)` by
    (fs[ptr_paired_code_def] >> metis_tac[fn_labels_def, concretize_positions_labels]) >>
  drule ptr_paired_stage_local_allocas >>
  disch_then (qspecl_then [`o1_walk_view rpolicy 2`, `rpolicy`] mp_tac) >>
  simp[] >> strip_tac >>
  `ptr_paired_sample positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    (simp[ptr_paired_sample_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
     (reverse conj_tac
      >- (fs[ptr_paired_sample_def] >>
          irule ptr_history_content_masks >> goal_assum (drule_at Any) >>
          asm "scalar" mp_tac >> simp[MEM] >> strip_tac >>
          simp[step_taint_def, mem_taint_def, set_var_taint_def, adopt_reset_def,
               store_taint_def, imm_taint_def])) >>
     asm "scalar" mp_tac >> simp[MEM] >> strip_tac >>
     gvs[step_prov_def, out_prov_def] >>
     irule ptr_mixed_vars_fields >> rpt (goal_assum (drule_at Any)) >>
     simp[update_var_def]) >>
  `ptr_paired_params positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    (fs[ptr_paired_params_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def, update_var_def]) >>
  drule ptr_paired_prefix_ordinary_nonwrite >> disch_then irule >>
  simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def, update_var_def,
       ptr_tagged_step_def] >>
  asm "scalar" mp_tac >> simp[MEM] >> strip_tac >>
  simp[step_prov_def, out_prov_def, step_writes_def,
       source_memory_write_ranges_def, fixed_source_write_range_def, range_bytes_def] >>
  (reverse conj_tac >- fs[update_var_def] >>
   qexistsl_tac [`0`, `update_var out v a.po_state`] >> fs[update_var_def])
QED

Finalise ptr_focus_scalar_step
