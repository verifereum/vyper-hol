Theory concretizePtrEnvironmentReadProducer
Ancestors concretizePtrRequestHistory concretizePtrTaintContent concretizePtrOperationalOpcodes concretizePtrPairedPrefixProbe concretizePtrParamProducer concretizePtrAssignProducer concretizePtrValueTransport
  concretizePtrOrdinaryNext concretizePtrOpaqueRetpc concretizePtrPairedNextAttach
  concretizePtrPairedPrefix concretizePtrPairedFields concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrSourceOwnership concretizePtrChronologicalHistory
  concretizePtrAllocationSize concretizePtrDeletedGapHistory concretizePtrTaggedSupport
  concretizePtrLedgerProbe concretizePtrLedgerAlignment concretizePtrPrefixLedger
  concretizePtrSharedFields concretizePtrStagePlacements concretizePtrDeletedGaps
  concretizePtrExecutedCoverage concretizeStepStructure concretizeStepShape
  concretizeStepRetpc concretizeStageShape
  o1PassContract o1ScheduleDecomp unitShapeDefs venomWf cfgWf unitLabelMapIdentity
  contextCodegenRel codegenRel frameViewFacts ptrDiscipline venomExecSemantics
  venomState venomInst finite_map words list rich_list arithmetic

(* Shared by the nullary and unary account-reading producers. Storage is
   deliberately absent: history content preserves only nonstorage fields. *)
Theorem ptr_environment_account_observations:
  ptr_history_content tn s t ==>
  !a. (s.vs_accounts a).balance = (t.vs_accounts a).balance /\
      (s.vs_accounts a).code = (t.vs_accounts a).code /\
      (s.vs_accounts a).nonce = (t.vs_accounts a).nonce
Proof
  strip_tac >> gen_tac >>
  drule ptr_history_content_current >>
  strip_tac >> drule ptr_taint_content_account >>
  disch_then (qspec_then `a` mp_tac) >>
  simp[] >> strip_tac >>
  first_assum (mp_tac o AP_TERM ``\a:account_state. a.balance``) >>
  first_assum (mp_tac o AP_TERM ``\a:account_state. a.code``) >>
  first_x_assum (mp_tac o AP_TERM ``\a:account_state. a.nonce``) >> simp[]
QED

Theorem ptr_environment_read_execution[local]:
  ptr_history_content tn s t /\
  MEM inst.inst_opcode [CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID;
    COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
    CALLDATASIZE; RETURNDATASIZE; BLOBBASEFEE; CODESIZE; SELFBALANCE] /\
  inst.inst_outputs = [out] /\ step_inst fuel Ct inst t = OK t' ==>
  ?v. step_inst 0 C inst s = OK (update_var out v s) /\
      t' = update_var out v t
Proof
  strip_tac >>
  drule ptr_history_content_call_ctx >> strip_tac >>
  drule ptr_history_content_tx_ctx >> strip_tac >>
  drule ptr_history_content_block_ctx >> strip_tac >>
  drule ptr_history_content_returndata >> strip_tac >>
  drule ptr_history_content_code >> strip_tac >>
  drule ptr_environment_account_observations >> strip_tac >>
  fs[MEM] >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke] >>
  PURE_REWRITE_TAC [step_inst_base_def] >>
  ASM_REWRITE_TAC [] >>
  simp[exec_read0_def] >>
  strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `update_var out value s` >>
  qexists_tac `value` >> simp[Abbr `value`, vfmStateTheory.lookup_account_def]
QED

Theorem ptr_mixed_environment_read_execution[local]:
  ptr_mixed_vars births positions TG tn f g s t /\ ptr_history_content tn s t /\
  MEM inst.inst_opcode [CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID;
    COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
    CALLDATASIZE; RETURNDATASIZE; BLOBBASEFEE; CODESIZE; SELFBALANCE] /\
  inst.inst_outputs = [out] /\ ~retpc_var f out /\
  step_inst fuel Ct inst t = OK t' ==>
  ?v. step_inst 0 C inst s = OK (update_var out v s) /\
    t' = update_var out v t /\
    ptr_mixed_vars births positions
      (step_prov PT TG inst (update_var out v s))
      (step_taint inst s (update_var out v s) tn)
      f g (update_var out v s) t'
Proof
  strip_tac >>
  drule_all ptr_environment_read_execution >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  qexists_tac `v` >> simp[] >> gvs[] >>
  drule ptr_mixed_vars_update >> disch_then irule >> simp[] >>
  fs[MEM] >>
  simp[step_prov_def, out_prov_def, set_prov_def,
       step_taint_def, out_taint_def, set_var_taint_def, op_taint_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, ptr_value_transport_refl] >>
  rpt strip_tac >> fs[ptr_mixed_vars_def, op_taint_def]
QED

Theorem ptr_paired_prefix_environment_read:
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
  MEM a.po_inst.inst_opcode [CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID;
    COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
    CALLDATASIZE; RETURNDATASIZE; BLOBBASEFEE; CODESIZE; SELFBALANCE] /\ ptr_chrono_step C' at zt ==>
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
  `?out. a.po_inst.inst_outputs = [out]` by
    (fs[MEM] >> gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute]) >>
  `a.po_inst.inst_opcode <> ALLOCA /\ a.po_inst.inst_opcode <> NOP /\
   a.po_inst.inst_opcode <> INVOKE /\ a.po_inst.inst_opcode <> ASSIGN /\
   a.po_inst.inst_opcode <> PHI /\ a.po_inst.inst_opcode <> RETPC_PARAM /\
   ~is_terminator a.po_inst.inst_opcode` by (fs[MEM] >> simp[is_terminator_def]) >>
  `~retpc_var a.po_fn out` by
    (irule noncopy_output_not_retpc >>
     conj_tac >- fs[EVERY_MEM] >> qexists_tac `a.po_inst` >> simp[]) >>
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
     simp[exec_read0_def, AllCaseEqs()]) >>
  `?v. step_inst 0 C a.po_inst a.po_state = OK (update_var out v a.po_state) /\
     s' = update_var out v at.po_state /\
     ptr_mixed_vars births positions
       (step_prov PT TG a.po_inst (update_var out v a.po_state))
       (step_taint a.po_inst a.po_state (update_var out v a.po_state) a.po_taint)
       a.po_fn at.po_fn (update_var out v a.po_state) s'` by
    (fs[ptr_paired_sample_def] >>
     `MEM a.po_inst.inst_opcode [CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID;
       COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
       CALLDATASIZE; RETURNDATASIZE; BLOBBASEFEE; CODESIZE; SELFBALANCE]` by simp[] >>
     drule_all ptr_mixed_environment_read_execution >>
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
          irule ptr_history_content_masks >>
          qexists_tac `a.po_taint` >>
          fs[MEM] >> simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def]) >>
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
Resume ptr_paired_prefix_environment_read[shape]:
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
  fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def,
     wf_function_def, fn_inst_wf_def, EVERY_MEM, fn_insts_MEM] >> metis_tac[]
QED
Finalise ptr_paired_prefix_environment_read

Theorem ptr_paired_environment_read_prefix_normalize:
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
  MEM a.po_inst.inst_opcode [CALLER; ADDRESS; CALLVALUE; ORIGIN; GASPRICE; CHAINID;
    COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE;
    CALLDATASIZE; RETURNDATASIZE; BLOBBASEFEE; CODESIZE; SELFBALANCE] ==>
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
  drule_all ptr_paired_prefix_environment_read >> strip_tac >>
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

Theorem ptr_history_content_common_gas_readings[local]:
  ptr_history_content tn s t ==>
  ptr_history_content tn (s with vs_gas_readings := readings)
    (t with vs_gas_readings := readings)
Proof
  simp[ptr_history_content_def, ptr_taint_content_def,
       ptr_taint_control_def, ptr_core_shared_def, ptr_shared_fields_def,
       contract_storage_def, contract_transient_def] >> strip_tac >> gvs[]
QED

Theorem ptr_gas_execution[local]:
  ptr_history_content tn s t /\ inst.inst_opcode = GAS /\
  inst.inst_outputs = [out] /\ step_inst fuel Ct inst t = OK t' ==>
  ?v readings.
    step_inst 0 C inst s = OK (update_var out v (s with vs_gas_readings := readings)) /\
    t' = update_var out v (t with vs_gas_readings := readings)
Proof
  strip_tac >>
  `s.vs_gas_readings = t.vs_gas_readings` by
    (drule ptr_history_content_control >>
     simp[ptr_taint_control_def, ptr_core_shared_def, ptr_shared_fields_def]) >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke] >> PURE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[] >> simp[exec_gas_def] >>
  Cases_on `t.vs_gas_readings`
  >- (simp[] >> strip_tac >> qexistsl_tac [`0w`, `[]`] >>
      gvs[update_var_def, venom_state_component_equality]) >>
  simp[] >> strip_tac >> rename1 `s.vs_gas_readings = r::rest` >>
  qexistsl_tac [`r`, `rest`] >> simp[]
QED

Theorem ptr_gas_update_var[local]:
  (update_var out v s) with vs_gas_readings := readings =
  update_var out v (s with vs_gas_readings := readings)
Proof
  simp[update_var_def]
QED

Theorem ptr_mixed_gas_execution[local]:
  ptr_mixed_vars births positions TG tn f g s t /\ ptr_history_content tn s t /\
  inst.inst_opcode = GAS /\ inst.inst_outputs = [out] /\ ~retpc_var f out /\
  step_inst fuel Ct inst t = OK t' ==>
  ?v readings.
    step_inst 0 C inst s = OK (update_var out v (s with vs_gas_readings := readings)) /\
    t' = update_var out v (t with vs_gas_readings := readings) /\
    ptr_mixed_vars births positions
      (step_prov PT TG inst (update_var out v (s with vs_gas_readings := readings)))
      (step_taint inst s (update_var out v (s with vs_gas_readings := readings)) tn)
      f g (update_var out v (s with vs_gas_readings := readings)) t'
Proof
  strip_tac >> drule_all ptr_gas_execution >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  qexistsl_tac [`v`, `readings`] >> simp[] >> gvs[] >>
  `ptr_mixed_vars births positions TG tn f g
     (s with vs_gas_readings := readings) (t with vs_gas_readings := readings)` by
    (irule ptr_mixed_vars_fields >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  pure_rewrite_tac[ptr_gas_update_var] >>
  drule ptr_mixed_vars_update >> disch_then irule >> simp[] >>
  simp[step_prov_def, out_prov_def, set_prov_def,
       step_taint_def, out_taint_def, set_var_taint_def, op_taint_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, ptr_value_transport_refl] >>
  rpt strip_tac >> fs[ptr_mixed_vars_def, op_taint_def]
QED

Theorem ptr_paired_prefix_gas:
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
  a.po_inst.inst_opcode = GAS /\ ptr_chrono_step C' at zt ==>
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
  `?out. a.po_inst.inst_outputs = [out]` by
    gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute] >>
  `a.po_inst.inst_opcode <> ALLOCA /\ a.po_inst.inst_opcode <> NOP /\
   a.po_inst.inst_opcode <> INVOKE /\ a.po_inst.inst_opcode <> ASSIGN /\
   a.po_inst.inst_opcode <> PHI /\ a.po_inst.inst_opcode <> RETPC_PARAM /\
   ~is_terminator a.po_inst.inst_opcode` by simp[is_terminator_def] >>
  `~retpc_var a.po_fn out` by
    (irule noncopy_output_not_retpc >>
     conj_tac >- fs[EVERY_MEM] >> qexists_tac `a.po_inst` >> simp[]) >>
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
     simp[step_inst_non_invoke] >> PURE_REWRITE_TAC[step_inst_base_def] >>
     ASM_REWRITE_TAC[] >> simp[]) >>
  `?v readings.
     step_inst 0 C a.po_inst a.po_state =
       OK (update_var out v (a.po_state with vs_gas_readings := readings)) /\
     s' = update_var out v (at.po_state with vs_gas_readings := readings) /\
     ptr_mixed_vars births positions
       (step_prov PT TG a.po_inst (update_var out v (a.po_state with vs_gas_readings := readings)))
       (step_taint a.po_inst a.po_state
         (update_var out v (a.po_state with vs_gas_readings := readings)) a.po_taint)
       a.po_fn at.po_fn (update_var out v (a.po_state with vs_gas_readings := readings)) s'` by
    (fs[ptr_paired_sample_def] >> drule_all ptr_mixed_gas_execution >>
     disch_then (qspecl_then [`PT`,`C`] mp_tac) >> simp[]) >>
  `?i. active_inst a.po_fn i
     ((update_var out v (a.po_state with vs_gas_readings := readings))
       with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (`EVERY bb_well_formed a.po_fn.fn_blocks` by
       (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
     qpat_assum `active_inst a.po_fn a.po_inst a.po_state`
       (mp_then Any mp_tac ptr_ordinary_next_active) >>
     disch_then irule >> simp[update_var_def]) >>
  qabbrev_tac `z = ptr_ledger_next a i
    (update_var out v (a.po_state with vs_gas_readings := readings))` >>
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
          irule ptr_history_content_masks >>
          qexists_tac `a.po_taint` >>
          fs[MEM] >> simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def] >>
          rewrite_tac[ptr_gas_update_var] >>
          simp[] >> irule ptr_history_content_common_gas_readings >> simp[]) >>
      gvs[step_prov_def, out_prov_def] >>
      irule ptr_mixed_vars_fields >> rpt (goal_assum (drule_at Any)) >>
      simp[update_var_def])) >>
  `ptr_paired_params positions z zt
     (tokens,registry,births,PT,step_prov PT TG a.po_inst z.po_state,saved,entries)` by
    (fs[ptr_paired_params_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def, update_var_def]) >>
  drule ptr_paired_prefix_ordinary_nonwrite >> disch_then irule >>
  simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def, update_var_def,
       ptr_tagged_step_def] >>
  simp[step_prov_def, out_prov_def, step_writes_def,
       source_memory_write_ranges_def, fixed_source_write_range_def, range_bytes_def] >>
  (reverse conj_tac >- fs[update_var_def] >>
   qexistsl_tac [`0`, `update_var out v (a.po_state with vs_gas_readings := readings)`] >>
   fs[update_var_def])
QED
Resume ptr_paired_prefix_gas[shape]:
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
  fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def,
     wf_function_def, fn_inst_wf_def, EVERY_MEM, fn_insts_MEM] >> metis_tac[]
QED
Finalise ptr_paired_prefix_gas

Theorem ptr_paired_gas_prefix_normalize:
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
  ptr_chrono_step C' at zt /\ a.po_inst.inst_opcode = GAS ==>
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
  drule_all ptr_paired_prefix_gas >> strip_tac >>
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
