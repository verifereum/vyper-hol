(*
 * Paired-prefix extension for the N1 opcode family (ADD; SUB).
 *)
Theory concretizePtrAffineFamily
Ancestors
  concretizePtrStorageReadProducer concretizePtrAffineTransport
  concretizePtrOpaqueRetpc concretizePtrValueTransport ptrDiscipline
  venomExecSemantics finite_map list words
  concretizePtrOwnedAffinePrefix concretizePtrReturnTransport concretizePtrTaggedSupport
  concretizePtrPairedNextAttach concretizePtrPairedPrefixProbe
  concretizePtrRequestHistory concretizePtrTaintContent concretizePtrSourceOwnership
  concretizeStepStructure concretizeStepShape concretizeStepCallChecks
  concretizeStepRetpc concretizeStageShape concretizePtrOperationalOpcodes opcodeClass
  concretizePtrOrdinaryNext concretizePtrPairedPrefix concretizePtrPairedFields
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrChronologicalHistory concretizePtrAllocationSize concretizePtrDeletedGapHistory
  concretizePtrLedgerProbe concretizePtrLedgerAlignment concretizePtrPrefixLedger
  concretizePtrSharedFields concretizePtrStagePlacements concretizePtrDeletedGaps
  concretizePtrExecutedCoverage o1PassContract o1ScheduleDecomp venomWf cfgWf
  unitLabelMapIdentity contextCodegenRel codegenRel frameViewFacts
  pointerConfinedDefs unitShapeDefs memLocDefs venomState venomInst pred_set

Theorem ptr_mixed_affine_execution_back[local]:
  ptr_mixed_vars births positions TG tn f g s t /\
  s.vs_labels = t.vs_labels /\
  ptr_nonopaque_operand f x /\ ptr_nonopaque_operand f y /\
  inst.inst_operands = [x;y] /\ inst.inst_outputs = [out] /\
  MEM inst.inst_opcode [ADD;SUB] /\
  (inst.inst_opcode = ADD ==> op_prov TG x = NONE \/ op_prov TG y = NONE) /\
  (inst.inst_opcode = SUB ==> op_prov TG y = NONE) /\
  op_taint tn x = {} /\ op_taint tn y = {} /\ ~retpc_var f out /\
  step_inst fuel Ct inst t = OK t' ==>
  ?sv tv. step_inst 0 C inst s = OK (update_var out sv s) /\
    t' = update_var out tv t /\
    ptr_mixed_vars births positions
      (step_prov PT TG inst (update_var out sv s))
      (step_taint inst s (update_var out sv s) tn)
      f g (update_var out sv s) t'
Proof
  strip_tac >>
  `ptr_lookup_transport births positions (op_prov TG x) {}
     (eval_operand x s) (eval_operand x t)` by
    (metis_tac[ptr_mixed_vars_eval]) >>
  `ptr_lookup_transport births positions (op_prov TG y) {}
     (eval_operand y s) (eval_operand y t)` by
    (metis_tac[ptr_mixed_vars_eval]) >>
  gvs[MEM] >>
  gvs[ptr_affine_step, exec_pure2_def, AllCaseEqs()] >>
  gvs[ptr_lookup_transport_some_right] >>
  qmatch_goalsub_abbrev_tac `update_var out sv s` >>
  qmatch_goalsub_abbrev_tac `update_var out tv t` >>
  qexistsl_tac [`sv`, `tv`] >> simp[] >>
  drule ptr_mixed_vars_update >> disch_then irule >> simp[] >>
  simp[step_prov_def, out_prov_def, first_prov_def, set_prov_def,
       step_taint_def, out_taint_def, set_var_taint_def, op_taint_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  Cases_on `op_prov TG x` >> Cases_on `op_prov TG y` >>
  gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, ptr_value_transport_scalar_empty,
      Abbr `sv`, Abbr `tv`] >>
  rpt conj_tac >> rpt strip_tac >>
  fs[ptr_mixed_vars_def, op_taint_def] >>
  metis_tac[ptr_value_transport_add_left, ptr_value_transport_add_right,
            ptr_value_transport_sub_right, WORD_ADD_COMM]
QED

Theorem ptr_paired_prefix_affine:
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
  MEM a.po_inst.inst_opcode [ADD; SUB] /\ ptr_chrono_step C' at zt ==>
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
  `?x y out. a.po_inst.inst_operands = [x;y] /\ a.po_inst.inst_outputs = [out]` by
    (fs[MEM] >> gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute]) >>
  `a.po_inst.inst_opcode <> ALLOCA /\ a.po_inst.inst_opcode <> NOP /\
   a.po_inst.inst_opcode <> INVOKE /\ a.po_inst.inst_opcode <> ASSIGN /\
   a.po_inst.inst_opcode <> PHI /\ a.po_inst.inst_opcode <> RETPC_PARAM /\
   ~is_terminator a.po_inst.inst_opcode` by (fs[MEM] >> simp[is_terminator_def]) >>
  `~retpc_var a.po_fn out` by
    (irule noncopy_output_not_retpc >>
     conj_tac >- fs[EVERY_MEM] >> qexists_tac `a.po_inst` >> simp[]) >>
  `ptr_nonopaque_operand a.po_fn x /\ ptr_nonopaque_operand a.po_fn y /\
   op_taint a.po_taint x = {} /\ op_taint a.po_taint y = {} /\
   (a.po_inst.inst_opcode = ADD ==> op_prov TG x = NONE \/ op_prov TG y = NONE) /\
   (a.po_inst.inst_opcode = SUB ==> op_prov TG y = NONE)` by suspend "operands" >>
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
  `?v tv. step_inst 0 C a.po_inst a.po_state = OK (update_var out v a.po_state) /\
     s' = update_var out tv at.po_state /\
     ptr_mixed_vars births positions
       (step_prov PT TG a.po_inst (update_var out v a.po_state))
       (step_taint a.po_inst a.po_state (update_var out v a.po_state) a.po_taint)
       a.po_fn at.po_fn (update_var out v a.po_state) s'` by
    (fs[ptr_paired_sample_def] >>
     `MEM a.po_inst.inst_opcode [ADD; SUB]` by simp[] >>
     `a.po_state.vs_labels = at.po_state.vs_labels` by
       metis_tac[ptr_history_content_labels] >>
     drule ptr_mixed_affine_execution_back >> simp[] >>
     disch_then irule >> simp[] >> metis_tac[]) >>
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
          goal_assum (drule_at Any) >>
          fs[MEM] >>
          simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def])) >>
     gvs[step_prov_def, out_prov_def] >>
     irule ptr_mixed_vars_fields >> rpt (goal_assum (drule_at Any)) >>
     simp[update_var_def]) >>
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

Resume ptr_paired_prefix_affine[shape]:
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
  fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def,
     wf_function_def, fn_inst_wf_def, EVERY_MEM, fn_insts_MEM] >> metis_tac[]
QED

Resume ptr_paired_prefix_affine[operands]:
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def,
        EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >> metis_tac[]) >>
  `!stk PG G tn fn inst s. frame_reachable vs C stk PG G tn fn inst s ==>
     taint_ok fn tn inst s` by (fs[ptr_discipline_def] >> metis_tac[]) >>
  `op_taint a.po_taint x = {} /\ op_taint a.po_taint y = {} /\
   (a.po_inst.inst_opcode = ADD ==> op_prov TG x = NONE \/ op_prov TG y = NONE) /\
   (a.po_inst.inst_opcode = SUB ==> op_prov TG y = NONE)` by
    (irule ptr_owned_affine_conditions >> simp[] >>
     conj_tac >- fs[MEM] >>
     goal_assum (drule_at (Pos last)) >> simp[] >>
     qexists_tac `P` >> simp[] >> metis_tac[]) >> simp[] >>
  `opaque_use_ok a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM] >> metis_tac[]) >>
  `EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> simp[] >> fs[MEM]) >>
  qpat_x_assum `EVERY (ptr_nonopaque_operand _) _` mp_tac >> simp[]
QED
Finalise ptr_paired_prefix_affine

Theorem ptr_paired_affine_prefix_normalize:
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
  ptr_chrono_step C' at zt /\ MEM a.po_inst.inst_opcode [ADD; SUB] ==>
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
  drule_all ptr_paired_prefix_affine >> strip_tac >>
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

