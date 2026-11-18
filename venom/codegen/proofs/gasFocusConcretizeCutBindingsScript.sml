Theory gasFocusConcretizeCutBindings
Ancestors
  concretizePtrOpaqueRetpc concretizePtrValueTransport concretizePtrValueSelection
  concretizePtrOrdinaryNext concretizeStepStructure concretizePtrOperationalOpcodes
  concretizePtrPairedPrefix concretizePtrPairedFields concretizePtrStructuralTranscript
  concretizePtrSourceOwnership concretizePtrStructuralTrace concretizePtrChronologicalHistory
  concretizePtrDeletedGapHistory concretizePtrRequestHistory concretizePtrLedgerProbe
  o1PassContract o1ScheduleDecomp ptrDiscipline pointerConfinedDefs
  contextCodegenRel codegenRel frameViewFacts unitLabelMapIdentity
  unitShapeDefs venomWf venomState venomInst venomExecSemantics opcodeClass
  finite_map list rich_list pred_set words

Theorem focus_assign_execution[local]:
  ptr_mixed_vars births positions TG tn f g s t /\ s.vs_labels = t.vs_labels /\
  retpc_shape_ok f /\ MEM inst (fn_insts f) /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  inst.inst_outputs = [out] /\ step_inst fuel Ct inst t = OK post ==>
  ?sv tv. step_inst 0 C inst s = OK (update_var out sv s) /\
    post = update_var out tv t /\
    ptr_mixed_vars births positions (step_prov PT TG inst (update_var out sv s))
      (step_taint inst s (update_var out sv s) tn) f g (update_var out sv s) post
Proof
  strip_tac >>
  `MEM out inst.inst_outputs` by simp[] >>
  drule_all ptr_mixed_assign_eval >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  strip_tac >> gvs[optionTheory.OPTREL_def, AllCaseEqs()] >>
  qexistsl_tac [`sv`, `v`] >> simp[] >>
  drule ptr_mixed_vars_update >> disch_then irule >> simp[] >>
  simp[step_prov_def, out_prov_def, first_prov_def, set_prov_def,
       step_taint_def, out_taint_def, set_var_taint_def, op_taint_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  Cases_on `op_prov TG op` >>
  gvs[op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> fs[ptr_mixed_vars_def, op_taint_def] >> metis_tac[]
QED

Theorem focus_param_execution[local]:
  ptr_mixed_vars births positions TG tn f g s t /\
  ((PT = [] /\ s.vs_params = t.vs_params) \/
   ptr_args_transport births positions PT
     (REPLICATE (LENGTH s.vs_params) {}) s.vs_params t.vs_params) /\
  inst.inst_opcode = PARAM /\ inst.inst_operands = [Lit idx] /\
  inst.inst_outputs = [out] /\ ~retpc_var f out /\
  step_inst fuel Ct inst t = OK post ==>
  ?sv tv. step_inst 0 C inst s = OK (update_var out sv s) /\
    post = update_var out tv t /\
    ptr_mixed_vars births positions (step_prov PT TG inst (update_var out sv s))
      (step_taint inst s (update_var out sv s) tn) f g (update_var out sv s) post
Proof
  strip_tac >>
  `w2n idx < LENGTH s.vs_params /\ w2n idx < LENGTH t.vs_params` by
    (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     drule_all ptr_param_step >> disch_then (fn th => rewrite_tac[th]) >>
     IF_CASES_TAC >> gvs[] >> drule ptr_args_transport_lengths >> simp[]) >>
  `ptr_value_transport births positions
     (if w2n idx < LENGTH PT then EL (w2n idx) PT else NONE) {}
     (EL (w2n idx) s.vs_params) (EL (w2n idx) t.vs_params)` by
    (gvs[ptr_value_transport_refl] >>
     drule ptr_args_transport_lengths >> strip_tac >> simp[] >>
     drule_all ptr_args_transport_el >> simp[EL_REPLICATE]) >>
  `post = update_var out (EL (w2n idx) t.vs_params) t` by
    (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     drule_all ptr_param_step >> disch_then (fn th => rewrite_tac[th]) >> simp[]) >>
  qexistsl_tac [`EL (w2n idx) s.vs_params`, `EL (w2n idx) t.vs_params`] >>
  asm_rewrite_tac[] >>
  (conj_tac >- (drule_all ptr_param_step >> disch_then (fn th => simp[th]))) >>
  drule ptr_mixed_vars_update >> disch_then irule >> simp[] >>
  simp[step_prov_def, out_prov_def, set_prov_def,
       step_taint_def, out_taint_def, set_var_taint_def, op_taint_def, eval_operand_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  Cases_on `if w2n idx < LENGTH PT then EL (w2n idx) PT else NONE` >>
  gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> fs[ptr_mixed_vars_def, op_taint_def]
QED

Theorem focus_retpc_execution[local]:
  inst.inst_opcode = RETPC_PARAM /\ MEM inst (fn_insts f) /\
  ptr_mixed_vars births positions TG tn f g s t /\
  step_inst fuel Ct inst t = OK post ==>
  ?out sv tv. step_inst 0 C inst s = OK (update_var out sv s) /\
    post = update_var out tv t /\
    ptr_mixed_vars births positions (step_prov PT TG inst (update_var out sv s))
      (step_taint inst s (update_var out sv s) tn) f g (update_var out sv s) post
Proof
  strip_tac >>
  `?idx out. inst = mk_inst inst.inst_id RETPC_PARAM [Lit idx] [out] /\
    step_inst 0 C inst s = OK (update_var out s.vs_return_pc_token s) /\
    post = update_var out t.vs_return_pc_token t` by
    (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     simp[step_inst_non_invoke] >> PURE_REWRITE_TAC[step_inst_base_def] >>
     ASM_REWRITE_TAC[] >> simp[Once opcode_case_def] >>
     simp[AllCaseEqs()] >> strip_tac >>
     simp[mk_inst_def, instruction_component_equality] >> metis_tac[]) >>
  `retpc_var f out` by
    (simp[retpc_var_def] >> irule (cj 1 copy_phi_var_rules) >>
     qexists_tac `inst` >> simp[] >>
     qpat_assum `inst = mk_inst _ _ _ _` (fn th => once_rewrite_tac[th]) >>
     simp[mk_inst_def]) >>
  qexistsl_tac [`out`, `s.vs_return_pc_token`, `t.vs_return_pc_token`] >> simp[] >>
  qpat_assum `inst = mk_inst _ _ _ _` SUBST1_TAC >>
  irule ptr_mixed_vars_retpc_step_transport >> simp[]
QED

Theorem focus_binding_execution[local]:
  ptr_mixed_vars births positions TG tn f g s t /\ s.vs_labels = t.vs_labels /\
  ((PT = [] /\ s.vs_params = t.vs_params) \/
   ptr_args_transport births positions PT
     (REPLICATE (LENGTH s.vs_params) {}) s.vs_params t.vs_params) /\
  retpc_shape_ok f /\ ssa_form f /\ MEM inst (fn_insts f) /\ inst_wf inst /\
  MEM inst.inst_opcode [ASSIGN; PARAM; RETPC_PARAM] /\
  step_inst fuel Ct inst t = OK post ==>
  ?out sv tv. step_inst 0 C inst s = OK (update_var out sv s) /\
    post = update_var out tv t /\
    ptr_mixed_vars births positions (step_prov PT TG inst (update_var out sv s))
      (step_taint inst s (update_var out sv s) tn) f g (update_var out sv s) post
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `MEM inst.inst_opcode [ASSIGN; PARAM; RETPC_PARAM]` mp_tac >>
  simp[] >> strip_tac
  >- (`?op out. inst.inst_operands = [op] /\ inst.inst_outputs = [out]` by
        (gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
      qexists_tac `out` >> drule_all focus_assign_execution >> simp[])
  >- (`?idx out. inst.inst_operands = [Lit idx] /\ inst.inst_outputs = [out]` by
        (gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute, AllCaseEqs()] >> metis_tac[]) >>
      `~retpc_var f out` by
        (irule noncopy_output_not_retpc >> simp[] >> qexists_tac `inst` >> simp[]) >>
      qexists_tac `out` >> drule_all focus_param_execution >> simp[]) >>
  drule_all focus_retpc_execution >> simp[]
QED

Theorem ptr_focus_binding_step:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  EVERY ssa_form C.ctx_functions /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  MEM a.po_inst.inst_opcode [ASSIGN; PARAM; RETPC_PARAM] /\ ptr_chrono_step C' at zt ==>
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
  drule ptr_frame_context_membership >> strip_tac >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
  `retpc_shape_ok a.po_fn /\ inst_wf a.po_inst /\ ssa_form a.po_fn /\
   EVERY bb_well_formed a.po_fn.fn_blocks /\ ALL_DISTINCT (fn_labels a.po_fn)` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, wf_function_def,
        fn_inst_wf_def, EVERY_MEM, fn_insts_MEM] >> metis_tac[]) >>
  `a.po_inst.inst_opcode <> ALLOCA /\ a.po_inst.inst_opcode <> NOP /\
   a.po_inst.inst_opcode <> INVOKE /\ ~is_terminator a.po_inst.inst_opcode` by
    (fs[MEM] >> simp[is_terminator_def]) >>
  `at.po_inst = a.po_inst` by gvs[concretize_positions_unchanged] >>
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[Excl "MEM"]
  >>~- ([`step_inst _ _ _ _ = IntRet _ _`],
    qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
    simp[step_inst_non_invoke] >> strip_tac >>
    drule step_inst_base_intret_opcodes >> fs[MEM]) >>
  suspend "attach"
QED

Resume ptr_focus_binding_step[attach]:
  markerLib.RESUME_TAC >>
  `?out sv tv. step_inst 0 C a.po_inst a.po_state = OK (update_var out sv a.po_state) /\
     s' = update_var out tv at.po_state /\
     ptr_mixed_vars births positions
       (step_prov PT TG a.po_inst (update_var out sv a.po_state))
       (step_taint a.po_inst a.po_state (update_var out sv a.po_state) a.po_taint)
       a.po_fn at.po_fn (update_var out sv a.po_state) s'` by
    (fs[ptr_paired_sample_def] >>
     `a.po_state.vs_labels = at.po_state.vs_labels` by metis_tac[ptr_history_content_labels] >>
     irule focus_binding_execution >> rpt (goal_assum (drule_at Any)) >>
     (reverse conj_tac
      >- (simp[MEM] >> qpat_assum `ptr_paired_params _ _ _ _`
            (ACCEPT_TAC o REWRITE_RULE [ptr_paired_params_def]))) >>
     qexistsl_tac [`C'`, `fuel`] >> simp[]) >>
  `?i. active_inst a.po_fn i
     ((update_var out sv a.po_state) with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (qpat_assum `active_inst a.po_fn a.po_inst a.po_state`
       (mp_then Any mp_tac ptr_ordinary_next_active) >>
     disch_then irule >> simp[update_var_def]) >>
  qabbrev_tac `z = ptr_ledger_next a i (update_var out sv a.po_state)` >>
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
      >- (fs[ptr_paired_sample_def] >> irule ptr_history_content_masks >>
          goal_assum (drule_at Any) >> fs[MEM] >>
          simp[step_taint_def, set_var_taint_def, store_taint_def, adopt_reset_def,
               imm_taint_def, update_var_def])) >>
     fs[MEM] >> gvs[step_prov_def, out_prov_def, lookup_var_def] >>
     irule ptr_mixed_vars_fields >> rpt (goal_assum (drule_at Any)) >> simp[update_var_def]) >>
  `ptr_paired_params positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    (fs[ptr_paired_params_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def, update_var_def]) >>
  drule ptr_paired_prefix_ordinary_nonwrite >> disch_then irule >>
  simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def, update_var_def, ptr_tagged_step_def] >>
  fs[MEM] >> simp[step_prov_def, out_prov_def, lookup_var_def, step_writes_def,
       source_memory_write_ranges_def, fixed_source_write_range_def, range_bytes_def] >>
  (reverse conj_tac >- fs[update_var_def] >>
   qexistsl_tac [`0`, `update_var out sv a.po_state`] >> fs[update_var_def])
QED
Finalise ptr_focus_binding_step
