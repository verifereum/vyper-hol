Theory concretizePtrFixedWriteReflection
Ancestors concretizePtrHistoricalWriteExclusion concretizePtrStageReserved
  concretizePtrExactWriteTransport concretizePtrHistoricalWriteClassification
  concretizePtrWritePurity concretizePtrValueTransport
  concretizePtrSourceOwnership concretizePtrOwnershipErasure concretizePtrComparisonTransport
  concretizePtrPairedPrefix concretizePtrPairedFields
  concretizeStepStructure concretizeStepShape concretizeStepCallChecks
  concretizeStepRetpc concretizeStageShape
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrChronologicalHistory concretizePtrHistoricalSupport
  concretizePtrOwnerPath contextCodegenRel unitShapeDefs venomWf
  concretizePtrOperationalOpcodes o1PassContract
  concretizePtrOpaqueRetpc concretizePtrOwnerSeeds concretizePtrSharedFields
  venomExecSemantics venomInst concretizeMemLocDefs memLocDefs words
  passSharedDefs codegenRel concretizePtrWriteClassification
  ptrDiscipline list pred_set arithmetic finite_map

Theorem ptr_paired_fixed_actual_write_reflection:
  ptr_paired_prefix R lp positions lo vs C C'
    h endpoint ht at done tokens registry births PT TG saved entries H calls ws /\
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
  max_live_eom C' = SOME eom /\ x < lo /\ q < LENGTH done /\
  x IN range_bytes (step_writes (EL q ht).po_inst
    (EL q ht).po_state (EL (SUC q) ht).po_state) ==>
  x IN range_bytes (step_writes (EL (EL q done) h).po_inst
    (EL (EL q done) h).po_state (EL (SUC (EL q done)) h).po_state) \/
  in_revert_forward (EL (EL q done) h).po_fn
    (EL (EL q done) h).po_state
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `in_revert_forward (EL (EL q done) h).po_fn
    (EL (EL q done) h).po_state` >- simp[] >>
  simp[] >>
  drule_all ptr_paired_historical_event >> strip_tac >>
  qmatch_asmsub_abbrev_tac `ptr_mixed_vars bj positions TGj aa.po_taint
    aa.po_fn (EL q ht).po_fn aa.po_state (EL q ht).po_state` >>
  `MEM aa.po_fn C.ctx_functions` by
    (fs[ptr_observation_reachable_def] >>
     drule ptr_frame_context_membership >> simp[]) >>
  `opaque_use_ok aa.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM] >> metis_tac[]) >>
  `active_inst aa.po_fn aa.po_inst aa.po_state` by
    (drule (cj 1 ptr_owner_view_active) >>
     disch_then (qspec_then `LENGTH aa.po_stack` mp_tac) >> simp[ptr_owner_view_def]) >>
  `MEM aa.po_inst (fn_insts aa.po_fn)` by
    (fs[active_inst_def, fn_insts_def, MEM_fn_insts_blocks_iff, lookup_block_def] >>
     metis_tac[MEM_EL]) >>
  `aa.po_inst.inst_opcode <> DRET` by
    (drule_all ptr_discipline_no_dret >> simp[]) >>
  `aa.po_state.vs_labels = (EL q ht).po_state.vs_labels` by
    fs[ptr_core_shared_def, ptr_shared_fields_def] >>
  `(EL (SUC (EL q done)) h).po_state.vs_returndata =
      (EL (SUC q) ht).po_state.vs_returndata` by
    (drule ptr_paired_prefix_samples >> strip_tac >>
     drule ptr_structural_transcript_erasure >> strip_tac >>
     drule_all ptr_paired_samples_post_returndata >> simp[]) >>
  Cases_on `aa.po_inst.inst_opcode = ALLOCA`
  >- (qpat_x_assum `(EL q ht).po_inst = _` mp_tac >>
      simp[concretize_inst_with_positions_def] >>
      rpt BasicProvers.TOP_CASE_TAC >> strip_tac >>
      gvs[mk_assign_inst_def, mk_nop_inst_def, instruction_component_equality] >>
      fs[ptr_step_write_range, source_memory_write_ranges_def]) >>
  `(EL q ht).po_inst = aa.po_inst` by metis_tac[concretize_positions_unchanged] >>
  qpat_x_assum `(EL q ht).po_inst = concretize_inst_with_positions _ _` kall_tac >>
  gvs[] >>
  `label_positions_ok aa.po_inst` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM,
        inst_shape_ok_def] >> metis_tac[]) >>
  qpat_assum `ptr_discipline _ _ _` mp_tac >>
  pure_rewrite_tac[ptr_discipline_def] >> strip_tac >>
  `EVERY (fn_ptr_ok P) C.ctx_functions` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions` by
    (pure_once_rewrite_tac[EVERY_MEM] >> qx_gen_tac `f` >> strip_tac >>
     BETA_TAC >> irule ptr_fn_inst_wf_flat >>
     fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
     first_x_assum drule >> simp[]) >>
  `EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions` by
    (qpat_x_assum `~ctx_has_dalloca C` mp_tac >>
     simp[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `EL q done < LENGTH h` by decide_tac >>
  `fn_ptr_ok P aa.po_fn` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `!u. u IN FDOM TGj ==> u IN fn_pv P aa.po_fn` by
    (rpt strip_tac >> simp[Abbr `aa`] >>
     irule ptr_transcript_tagged_domain_support >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  drule_all ptr_ordinary_write_operand_transport >>
  disch_then (qx_choose_then `ops` (qx_choose_then `sizeop`
    (qx_choose_then `dest` (qx_choose_then `z` (qx_choose_then `destt`
      (map_every assume_tac o CONJUNCTS)))))) >>
  unabbrev_all_tac >>
  drule_all ptr_historical_write_classification >>
  strip_tac
  >- (`MEM (EL (EL q done) h).po_inst.inst_opcode [CALL;STATICCALL;DELEGATECALL] ==>
        LENGTH (EL (SUC (EL q done)) h).po_state.vs_returndata =
        LENGTH (EL (SUC q) ht).po_state.vs_returndata` by simp[] >>
      drule_all ptr_write_transport_fixed_exact >> simp[]) >>
  drule ptr_structural_transcript_ownership >>
  disch_then (qspec_then `EL q done` mp_tac) >>
  simp[ptr_snapshot_ownership_def] >> strip_tac >>
  drule_all ptr_source_ownership_prov_erases >>
  simp[concretizePtrPrefixLedgerTheory.ptr_ledger_erases_def] >> strip_tac >>
  `FLOOKUP bj (token,bid) = SOME (db,sb)` by
    (qpat_x_assum `!v. FLOOKUP (EL (EL q done) h).po_prov v = _`
       (qspec_then `dv` mp_tac) >>
     simp[ptr_owner_project_def]) >>
  `op_prov TGj ops.iao_ofst = SOME (token,bid)` by simp[op_prov_def] >>
  `destt = dest - n2w db + n2w pb` by
    (gvs[ptr_lookup_transport_some, ptr_value_transport_def]) >>
  `w2n destt = pb + (w2n dest - db)` by
    (irule ptr_closed_relocation_value >> simp[] >>
     qexists `sb` >> simp[] >> decide_tac) >>
  `w2n destt <= x /\ x < w2n destt + w2n z` by
    (drule_all ptr_step_write_max_containment >> simp[]) >>
  `pb <= x /\ x - pb < sb` by decide_tac >>
  `lo <= pb + (x-pb)` by
    (irule ptr_stage_placements_reserved_prefix >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  decide_tac
QED
