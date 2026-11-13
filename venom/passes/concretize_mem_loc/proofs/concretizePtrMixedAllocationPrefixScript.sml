Theory concretizePtrMixedAllocationPrefix
Ancestors venomWfProps concretizePtrRequestHistory
  concretizePtrMixedAllocationTransport concretizePtrAllocationTransport concretizePtrPairedPrefix
  concretizePtrPairedFields concretizePtrSharedFields venomState
  unitLabelMapIdentity venomExecProofs concretizePtrLedgerAlignment concretizePtrDeletedGaps
  concretizePtrStagePlacements concretizePtrAllocationSize
  concretizePtrExecutedCoverage concretizePtrLedgerProbe concretizePtrActivationBirths
  concretizePtrSourceOwnership concretizePtrActivationChronology concretizePtrOpaqueRetpc
  concretizePtrStructuralTranscript concretizePtrChronologicalHistory
  concretizePtrStructuralTrace concretizePtrDeletedGapHistory removeUnusedSsaProofs
  concretizePtrEventEmbedding codegenRel
  concretizeStepStructure concretizeStepShape concretizeStepCallChecks
  concretizeStepRetpc concretizeStageShape
  o1PassContract stackPlanGen ptrDiscipline unitMemInv venomWf cfgWf
  o1ScheduleDecomp venomExecSemantics venomInst unitShapeDefs
  list finite_map words contextCodegenRel arithmetic rich_list concretizeMemLocDefs

Theorem ptr_paired_prefix_alloca_inputs:
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
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode = ALLOCA /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  fn_inst_wf a.po_fn /\ retpc_shape_ok a.po_fn /\
  ptr_chrono_step C' at zt ==>
  ?sz out pos.
    a.po_inst.inst_operands = [Lit sz] /\
    a.po_inst.inst_outputs = [out] /\ ~retpc_var a.po_fn out /\
    FLOOKUP (lp a.po_fn) (Allocation a.po_inst.inst_id) = SOME pos /\
    FLOOKUP positions (Allocation a.po_inst.inst_id) = SOME (pos,w2n sz) /\
    (!base size. FLOOKUP a.po_state.vs_allocas a.po_inst.inst_id = SOME (base,size)
      ==> size = w2n sz)
Proof
  strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_placements >> strip_tac >>
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
    (qpat_x_assum `active_inst _ _ _` mp_tac >>
     simp[active_inst_def] >> strip_tac >>
     simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     qexists_tac `bb.bb_instructions` >> conj_tac
     >- (qexists_tac `bb` >> simp[]) >>
     qpat_x_assum `EL _ _ = a.po_inst` (SUBST1_TAC o SYM) >>
     irule EL_MEM >> simp[]) >>
  `inst_wf a.po_inst` by
    (qpat_x_assum `fn_inst_wf _` mp_tac >>
     qpat_x_assum `MEM a.po_inst (fn_insts _)` mp_tac >>
     simp[fn_inst_wf_def, fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[]) >>
  qpat_x_assum `inst_wf a.po_inst` mp_tac >>
  simp[inst_wf_def] >> strip_tac >>
  `?out. a.po_inst.inst_outputs = [out]` by
    (Cases_on `a.po_inst.inst_outputs` >> gvs[] >>
     Cases_on `t` >> gvs[]) >>
  `~retpc_var a.po_fn out` by
    (strip_tac >> qpat_x_assum `retpc_shape_ok _` mp_tac >>
     pure_rewrite_tac[retpc_shape_ok_def] >>
     disch_then (mp_tac o cj 3) >>
     disch_then (qspecl_then [`a.po_inst`,`out`] mp_tac) >> simp[]) >>
  `fn_inst_ids_distinct a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  `get_alloca_size a.po_fn (Allocation a.po_inst.inst_id) = w2n sz` by
    (irule ptr_alloca_inst_size >> simp[]) >>
  drule_all ptr_stage_alloca_mems >> strip_tac >>
  `FLOOKUP positions (Allocation a.po_inst.inst_id) = SOME (p,w2n sz)` by
    (fs[ptr_stage_placements_def] >> metis_tac[lookup_function_MEM]) >>
  `FLOOKUP (lp a.po_fn) (Allocation a.po_inst.inst_id) = SOME p` by
    (qpat_x_assum `ptr_paired_code _ _ _ _ _` mp_tac >>
     qpat_x_assum `MEM a.po_inst (fn_insts _)` mp_tac >>
     simp[ptr_paired_code_def, fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     rpt strip_tac >> gvs[] >>
     first_x_assum (qspecl_then [`bb`,`a.po_inst`] mp_tac) >> simp[]) >>
  qexistsl_tac [`sz`,`out`,`p`] >> simp[] >>
  rpt strip_tac >> drule_all ptr_frame_current_allocation_size >> simp[]
QED

(* This is only the selected semantic schema, not a full prefix certificate. *)
Theorem ptr_paired_prefix_alloca_success:
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
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode = ALLOCA /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  fn_inst_wf a.po_fn /\ retpc_shape_ok a.po_fn /\
  ptr_chrono_step C' at zt ==>
  ?s' b B TG'.
    step_inst 0 C a.po_inst a.po_state = OK s' /\
    b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\ b.po_params = a.po_params /\
    b.po_state = (s' with vs_inst_idx := SUC a.po_state.vs_inst_idx) /\
    ptr_tagged_chrono_step C (HD tokens) a b PT TG saved PT TG' saved /\
    TG' = ptr_tagged_step (HD tokens) PT TG a.po_inst s' /\
    B = ptr_birth_overlay (HD tokens) b.po_state.vs_allocas births /\
    (!owner site. FLOOKUP births owner = SOME site ==> FLOOKUP B owner = SOME site) /\
    ptr_mixed_vars B positions TG' b.po_taint b.po_fn zt.po_fn b.po_state zt.po_state /\
    ptr_history_content b.po_taint b.po_state zt.po_state /\ ptr_paired_cursor lp b zt
Proof
  strip_tac >> drule_all ptr_paired_prefix_alloca_inputs >> strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
     a.po_state at.po_state` by fs[ptr_paired_sample_def] >>
  drule_all ptr_mixed_alloca_transport >>
  disch_then (qspecl_then [`HD tokens`,`0`,`PT`,`C'`,`C`] strip_assume_tac) >>
  `?i. active_inst a.po_fn i (s' with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    suspend "source_cursor" >>
  qabbrev_tac `b = ptr_ledger_next a i s'` >>
  qabbrev_tac `B = ptr_birth_overlay (HD tokens) b.po_state.vs_allocas births` >>
  qabbrev_tac `TG' = ptr_tagged_step (HD tokens) PT TG a.po_inst s'` >>
  `ptr_tagged_chrono_step C (HD tokens) a b PT TG saved PT TG' saved` by
    suspend "tagged" >>
  `(!owner site. FLOOKUP births owner = SOME site ==> FLOOKUP B owner = SOME site) /\
   (!base size. FLOOKUP s'.vs_allocas a.po_inst.inst_id = SOME (base,size) ==>
       FLOOKUP B (HD tokens,a.po_inst.inst_id) = SOME (base,size))` by
    suspend "births" >>
  qexistsl_tac [`s'`,`b`,`B`,`TG'`] >>
  simp[Abbr `b`, ptr_ledger_next_def, ptr_observe_def] >>
  suspend "post"
QED

Resume ptr_paired_prefix_alloca_success[source_cursor]:
  qpat_x_assum `active_inst a.po_fn a.po_inst a.po_state` mp_tac >>
  simp[active_inst_def] >> strip_tac >>
  `bb_well_formed bb` by
    (drule_all ptr_frame_sizes >> strip_tac >>
     fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, wf_function_def] >> metis_tac[]) >>
  `SUC a.po_state.vs_inst_idx < LENGTH bb.bb_instructions` by
    (spose_not_then assume_tac >>
     `a.po_state.vs_inst_idx = LENGTH bb.bb_instructions - 1` by decide_tac >>
     `LAST bb.bb_instructions = a.po_inst` by
       (fs[bb_well_formed_def] >> metis_tac[LAST_EL, PRE_SUB1]) >>
     gvs[bb_well_formed_def, is_terminator_def]) >>
  qexists_tac `bb` >> simp[]
QED

Resume ptr_paired_prefix_alloca_success[tagged]:
  simp[Abbr `b`, Abbr `TG'`, ptr_ledger_next_def] >>
  `~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE` by
    simp[is_terminator_def] >>
  `ptr_observe a.po_stack a.po_params a.po_prov a.po_taint
     a.po_fn a.po_inst a.po_state = a` by
    simp[NoAsms, ptr_observe_def, ptr_observation_component_equality] >>
  drule_all (cj 1 ptr_tagged_chrono_step_rules) >> simp[] >> metis_tac[]
QED

Resume ptr_paired_prefix_alloca_success[births]:
  `EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions` by
    (gvs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `ptr_activation_tokens h a b tokens = tokens /\
   ptr_activation_registry h a b registry = registry` by
    simp[Abbr `b`, ptr_ledger_next_def, ptr_observe_def,
      ptr_activation_tokens_def, ptr_activation_registry_def] >>
  drule_all (cj 2 ptr_source_ownership_rules) >> simp[] >> strip_tac >>
  `ptr_source_birth_caches vs C h a tokens registry births` by
    metis_tac[ptr_source_ownership_caches] >>
  `ptr_chrono_step C a b` by metis_tac[ptr_tagged_chrono_step_projection] >>
  drule ptr_source_birth_caches_snoc_retained >>
  simp[] >> disch_then (drule_at Any) >> strip_tac >>
  `ptr_source_birth_caches vs C (h ++ [b]) b tokens registry B` by
    (simp[Abbr `B`] >> metis_tac[ptr_source_ownership_caches]) >>
  drule_all ptr_source_birth_caches_active_lookup >> strip_tac >>
  simp[Abbr `B`] >> conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  `b.po_state.vs_allocas = s'.vs_allocas` by
    simp[Abbr `b`, ptr_ledger_next_def, ptr_observe_def] >>
  metis_tac[]
QED

Resume ptr_paired_prefix_alloca_success[post]:
  `at.po_inst.inst_opcode = ASSIGN` by
    simp[concretize_inst_with_positions_def, passSharedDefsTheory.mk_assign_inst_def] >>
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[is_terminator_def]
  >- suspend "post_next"
  >> qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac
  >> simp[step_inst_non_invoke]
  >> pure_once_rewrite_tac[step_inst_base_def]
  >> pure_asm_rewrite_tac[]
  >> pure_rewrite_tac[venomInstTheory.opcode_case_def]
  >> simp[AllCaseEqs()]

QED
Resume ptr_paired_prefix_alloca_success[post_next]:
  `step_inst 0 C' (concretize_inst_with_positions (lp a.po_fn) a.po_inst)
     at.po_state = OK s''` by
    (qpat_x_assum `step_inst fuel C' _ _ = OK _` mp_tac >>
     simp[step_inst_non_invoke]) >>
  `ptr_mixed_vars B positions TG' (step_taint a.po_inst a.po_state s' a.po_taint)
     a.po_fn at.po_fn s' s''` by
    (first_x_assum (qspecl_then [`B`,`s''`] mp_tac) >> simp[]) >>
  conj_tac
  >- (irule ptr_mixed_vars_fields >> goal_assum (drule_at Any) >> simp[]) >>
  suspend "core_cursor"
QED
Resume ptr_paired_prefix_alloca_success[core_cursor]:
  qpat_x_assum `step_inst 0 C a.po_inst a.po_state = OK s'` mp_tac >>
  qpat_x_assum `step_inst 0 C' _ _ = OK s''` mp_tac >>
  simp[step_inst_non_invoke, concretize_inst_with_positions_def,
       passSharedDefsTheory.mk_assign_inst_def] >>
  pure_once_rewrite_tac[step_inst_base_def] >> pure_asm_rewrite_tac[] >>
  pure_rewrite_tac[instruction_accfupds, combinTheory.K_THM, venomInstTheory.opcode_case_def] >>
  simp[AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
  >- (qpat_x_assum `exec_alloca _ _ _ = OK _` mp_tac >>
      qpat_x_assum `ptr_paired_sample _ _ _ _` mp_tac >>
      qpat_x_assum `a.po_inst.inst_outputs = _` mp_tac >>
      qpat_x_assum `a.po_inst.inst_operands = _` mp_tac >>
      qpat_x_assum `a.po_inst.inst_opcode = ALLOCA` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      qpat_x_assum `exec_alloca _ _ _ = OK _` mp_tac >>
      simp[exec_alloca_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
      fs[ptr_paired_sample_def] >>
      simp[step_taint_def, mem_taint_def, store_taint_def, adopt_reset_def,
           imm_taint_def, set_var_taint_def, GSYM update_var_def] >>
      irule ptr_history_content_masks >>
      qexists_tac `a.po_taint` >> simp[]) >>
  suspend "cursor"
QED
Resume ptr_paired_prefix_alloca_success[cursor]:
  `MEM a.po_fn C.ctx_functions` by (drule_all ptr_frame_sizes >> simp[]) >>
  `ALL_DISTINCT (fn_labels a.po_fn)` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  `ALL_DISTINCT (fn_labels at.po_fn)` by
    (fs[ptr_paired_code_def] >> metis_tac[fn_labels_def, concretize_positions_labels]) >>
  `!ai. MEM ai (fn_insts a.po_fn) /\ ai.inst_opcode = ALLOCA ==>
       ?p. FLOOKUP (lp a.po_fn) (Allocation ai.inst_id) = SOME p` by
    (rpt strip_tac >> drule_all ptr_stage_alloca_mems >> strip_tac >>
     `MEM g C'.ctx_functions` by metis_tac[lookup_function_MEM] >>
     `FLOOKUP positions (Allocation ai.inst_id) =
       SOME (p,get_alloca_size a.po_fn (Allocation ai.inst_id))` by
       (fs[ptr_paired_prefix_def, ptr_stage_placements_def] >> metis_tac[]) >>
     fs[ptr_paired_code_def, fn_insts_MEM] >>
     qpat_x_assum `!bb inst. _` (qspecl_then [`bb`,`ai`] mp_tac) >> simp[]) >>
  qpat_x_assum `!ai. MEM ai (fn_insts a.po_fn) /\ _ ==> _` mp_tac >>
  qpat_x_assum `ALL_DISTINCT (fn_labels a.po_fn)` mp_tac >>
  qpat_x_assum `ALL_DISTINCT (fn_labels at.po_fn)` mp_tac >>
  qpat_x_assum `active_inst a.po_fn i _` mp_tac >>
  qpat_x_assum `active_inst at.po_fn zt.po_inst _` mp_tac >>
  qpat_x_assum `ptr_paired_cursor _ _ _` mp_tac >>
  qpat_x_assum `exec_alloca _ _ _ = OK _` mp_tac >>
  qpat_x_assum `a.po_inst.inst_outputs = _` mp_tac >>
  qpat_x_assum `a.po_inst.inst_opcode = _` mp_tac >>
  qpat_x_assum `ptr_paired_code _ _ _ _ _` mp_tac >>
  qpat_x_assum `s'.vs_current_bb = _` mp_tac >>
  qpat_x_assum `zt.po_state = _` mp_tac >>
  qpat_x_assum `zt.po_fn = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  gvs[ptr_paired_cursor_def, ptr_ledger_next_def, ptr_observe_def, update_var_def] >>
  `s'.vs_prev_bb = a.po_state.vs_prev_bb` by
    (qpat_x_assum `exec_alloca _ _ _ = OK _` mp_tac >>
     simp[exec_alloca_def, AllCaseEqs()] >> strip_tac >> gvs[update_var_def]) >>
  simp[] >>
  `SUC a.po_state.vs_inst_idx < LENGTH bb.bb_instructions /\
   i = EL (SUC a.po_state.vs_inst_idx) bb.bb_instructions` by
    (qpat_assum `active_inst _ i _` mp_tac >>
     qpat_assum `lookup_block _ a.po_fn.fn_blocks = SOME bb` mp_tac >>
     qpat_assum `s'.vs_current_bb = _` mp_tac >>
     qpat_assum `ALL_DISTINCT (fn_labels a.po_fn)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[active_inst_def, fn_labels_def] >>
     rpt strip_tac >> rename1 `MEM nextbb a.po_fn.fn_blocks` >>
     `lookup_block at.po_state.vs_current_bb a.po_fn.fn_blocks = SOME nextbb` by
       (irule MEM_lookup_block >> simp[]) >> gvs[]) >>
  `SUC at.po_state.vs_inst_idx < LENGTH bbt.bb_instructions /\
   zt.po_inst = EL (SUC at.po_state.vs_inst_idx) bbt.bb_instructions` by
    (qpat_assum `active_inst _ zt.po_inst _` mp_tac >>
     qpat_assum `lookup_block _ at.po_fn.fn_blocks = SOME bbt` mp_tac >>
     qpat_assum `ALL_DISTINCT (fn_labels at.po_fn)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[active_inst_def, fn_labels_def] >>
     rpt strip_tac >> rename1 `MEM nextbb at.po_fn.fn_blocks` >>
     `lookup_block at.po_state.vs_current_bb at.po_fn.fn_blocks = SOME nextbb` by
       (irule MEM_lookup_block >> simp[]) >> gvs[]) >>
  suspend "cursor_order"
QED
Resume ptr_paired_prefix_alloca_success[cursor_order]:
  `a.po_state.vs_inst_idx = EL at.po_state.vs_inst_idx indices` by
    (spose_not_then assume_tac >>
     `a.po_state.vs_inst_idx < EL at.po_state.vs_inst_idx indices` by decide_tac >>
     qpat_x_assum `!k. _ ==> _.inst_opcode = NOP`
       (qspec_then `a.po_state.vs_inst_idx` mp_tac) >> simp[]) >>
  `LENGTH bbt.bb_instructions = LENGTH indices` by
    (drule ptr_ledger_alignment_cursor >> simp[]) >>
  `SUC at.po_state.vs_inst_idx < LENGTH indices` by decide_tac >>
  `EL at.po_state.vs_inst_idx indices < EL (SUC at.po_state.vs_inst_idx) indices` by
    (qpat_assum `ptr_ledger_block_alignment _ _ _ indices` mp_tac >>
     qpat_assum `SUC at.po_state.vs_inst_idx < LENGTH indices` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     irule ptr_ledger_alignment_order >> simp[] >>
     qexistsl_tac [`lp a.po_fn`,`bb.bb_instructions`,`bbt.bb_instructions`] >> simp[]) >>
  qexists_tac `indices` >> simp[] >> rpt strip_tac >>
  `(concretize_inst_with_positions (lp a.po_fn)
      (EL k bb.bb_instructions)).inst_opcode = NOP` by
    (irule ptr_ledger_alignment_gap >>
     qexistsl_tac [`indices`,`SUC at.po_state.vs_inst_idx`,`bbt.bb_instructions`] >>
     simp[] >> decide_tac) >>
  `k < LENGTH bb.bb_instructions` by
    (drule ptr_ledger_alignment_cursor >> strip_tac >>
     `EL (SUC at.po_state.vs_inst_idx) indices < LENGTH bb.bb_instructions` by
       (qpat_x_assum `!j. j < LENGTH bbt.bb_instructions ==> _`
          (qspec_then `SUC at.po_state.vs_inst_idx` mp_tac) >> simp[]) >> decide_tac) >>
  drule_all ptr_positioned_block_nop_iff >> simp[]
QED
Finalise ptr_paired_prefix_alloca_success

Theorem ptr_paired_prefix_alloca_immediate:
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
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode = ALLOCA /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  fn_inst_wf a.po_fn /\ retpc_shape_ok a.po_fn /\
  ptr_chrono_step C' at zt ==>
  ?s' b B TG'.
    step_inst 0 C a.po_inst a.po_state = OK s' /\
    b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\ b.po_params = a.po_params /\
    b.po_state = (s' with vs_inst_idx := SUC a.po_state.vs_inst_idx) /\
    ptr_tagged_chrono_step C (HD tokens) a b PT TG saved PT TG' saved /\
    TG' = ptr_tagged_step (HD tokens) PT TG a.po_inst s' /\
    B = ptr_birth_overlay (HD tokens) b.po_state.vs_allocas births /\
    (!owner site. FLOOKUP births owner = SOME site ==> FLOOKUP B owner = SOME site) /\
    ptr_mixed_vars B positions TG' b.po_taint b.po_fn zt.po_fn b.po_state zt.po_state /\
    ptr_history_content b.po_taint b.po_state zt.po_state /\ ptr_paired_cursor lp b zt /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ [b]) b (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens registry B PT TG' saved entries
      (H ++ [(tokens,registry,B,PT,TG',saved,entries)]) calls ws
Proof
  strip_tac >> drule_all ptr_paired_prefix_alloca_success >>
  disch_then (qx_choose_then `s'` (qx_choose_then `b`
    (qx_choose_then `B` (qx_choose_then `TG'` strip_assume_tac)))) >>
  qexistsl_tac [`s'`,`b`,`B`,`TG'`] >>
  simp[] >> suspend "certificate"
QED
Resume ptr_paired_prefix_alloca_immediate[certificate]:
  drule_all ptr_paired_prefix_alloca_inputs >> strip_tac >>
  `zt.po_fn = at.po_fn /\ zt.po_stack = at.po_stack /\
   zt.po_state.vs_params = at.po_state.vs_params /\
   s'.vs_params = a.po_state.vs_params` by suspend "fields" >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_chrono_history_end >> strip_tac >>
  gvs[] >>
  rewrite_tac[ptr_paired_prefix_def] >> rpt conj_tac
  >- suspend "transcript"
  >- fs[ptr_paired_prefix_def]
  >- (irule ptr_paired_samples_pair >>
      fs[ptr_paired_prefix_def, ptr_paired_sample_def])
  >- suspend "alignment"
  >- (irule ptr_paired_callers_retained >>
      fs[ptr_paired_prefix_def, ptr_paired_samples_def, ptr_sample_list_def] >>
      qexistsl_tac [`LAST h`, `at`] >> simp[])
  >> suspend "writes"
QED
Resume ptr_paired_prefix_alloca_immediate[fields]:
  `at.po_inst.inst_opcode = ASSIGN` by
    simp[concretize_inst_with_positions_def, passSharedDefsTheory.mk_assign_inst_def] >>
  `zt.po_fn = at.po_fn /\ zt.po_stack = at.po_stack /\
   zt.po_state.vs_params = at.po_state.vs_params` by
     (qpat_x_assum `ptr_chrono_step C' at zt` mp_tac >>
      once_rewrite_tac[ptr_chrono_step_cases] >>
      simp[ptr_observe_def, ptr_observation_component_equality] >>
      strip_tac >> gvs[is_terminator_def]
      >- (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
          simp[step_inst_non_invoke] >>
          pure_once_rewrite_tac[step_inst_base_def] >> pure_asm_rewrite_tac[] >>
          pure_rewrite_tac[venomInstTheory.opcode_case_def] >>
          simp[AllCaseEqs(), update_var_def] >> strip_tac >> gvs[]) >>
      qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
      simp[step_inst_non_invoke] >>
      pure_once_rewrite_tac[step_inst_base_def] >> pure_asm_rewrite_tac[] >>
      pure_rewrite_tac[venomInstTheory.opcode_case_def] >> simp[AllCaseEqs()]) >>
  simp[] >>
  qpat_x_assum `step_inst 0 C a.po_inst a.po_state = OK s'` mp_tac >>
  qpat_x_assum `a.po_inst.inst_opcode = ALLOCA` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> strip_tac >>
  simp[step_inst_non_invoke] >>
  pure_once_rewrite_tac[step_inst_base_def] >> pure_asm_rewrite_tac[] >>
  pure_rewrite_tac[venomInstTheory.opcode_case_def] >>
  simp[exec_alloca_def, AllCaseEqs()] >> strip_tac >> gvs[update_var_def]
QED
Resume ptr_paired_prefix_alloca_immediate[transcript]:
  drule (cj 3 ptr_structural_transcript_rules) >>
  disch_then drule >> disch_then drule >>
  simp[ptr_activation_tokens_def, ptr_activation_registry_def,
       concretize_positions_inst_id]
QED
Resume ptr_paired_prefix_alloca_immediate[alignment]:
  `ptr_paired_params positions b zt
    (tokens,registry,ptr_birth_overlay (HD tokens) s'.vs_allocas births,PT,
     ptr_tagged_step (HD tokens) PT TG (LAST h).po_inst s',saved,entries)` by
    (qpat_x_assum `ptr_paired_params _ _ _ _` mp_tac >>
     simp[ptr_paired_params_def] >> strip_tac
     >- simp[] >>
     disj2_tac >> irule ptr_args_transport_birth_extension >>
     goal_assum (drule_at Any) >> simp[]) >>
  irule ptr_paired_alignment_pair >> fs[ptr_paired_prefix_def]
QED
Resume ptr_paired_prefix_alloca_immediate[writes]:
  `EVERY (\n. SUC n < LENGTH h) done` by
    (qpat_x_assum `ptr_event_embedding _ _ _` mp_tac >>
     simp[ptr_event_embedding_def, EVERY_EL] >> strip_tac >>
     gen_tac >> strip_tac >>
     qpat_x_assum `!i j. _` (qspecl_then [`n`,`LENGTH done`] mp_tac) >>
     simp[EL_APPEND_EQN] >> decide_tac) >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM listTheory.APPEND_NIL))) >>
  irule ptr_paired_writes_pair >>
  simp[step_writes_def, source_memory_write_ranges_def, fixed_source_write_range_def,
       range_bytes_def] >>
  fs[ptr_paired_prefix_def, ptr_paired_samples_def, ptr_sample_list_def]
QED
Finalise ptr_paired_prefix_alloca_immediate
