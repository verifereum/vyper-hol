Theory gasFocusConcretizeCutFrameAccess
Ancestors
  gasFocusConcretizeCutCoverage gasFocusChronologicalCut
  gasFocusConcretizeGhostCutHistory gasFocusConcretizeCutActualWrite
  gasFocusConcretizeHistoricalCut gasFocusConcretizeTaggedSupport
  concretizePtrPairedPrefix concretizePtrStructuralTranscript
  concretizePtrDallocaDisciplineTransport concretizePtrDallocaEndpointDemands
  frameAllocationOwnership passSharedDefs concretizeStepStructure
  concretizePtrForwardingTaintHistory concretizePtrStructuralTrace
  concretizePtrChronologicalHistory concretizePtrOperationalOpcodes
  concretizePtrOwnerPath lowerDloadPtrRawReachable lowerDloadPtrForward
  contextCodegenRel codegenRel ptrDiscipline memSafeRun venomWf venomInst
  list arithmetic finite_map pred_set words

Theorem focus_concretize_window_opcode[local]:
  ptr_chrono_history vs C h at /\ EVERY wf_function C.ctx_functions /\
  lookup_block at.po_state.vs_current_bb at.po_fn.fn_blocks = SOME bb /\
  revert_forward_pair bb i j /\
  i < at.po_state.vs_inst_idx /\ at.po_state.vs_inst_idx <= j ==>
  at.po_inst.inst_opcode = ASSIGN \/
  (at.po_inst.inst_opcode = REVERT /\ at.po_state.vs_inst_idx = j /\
   in_revert_forward at.po_fn at.po_state)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_chrono_history_reachable >>
  simp[ptr_observation_reachable_def] >> strip_tac >>
  drule ptr_frame_context_membership >> strip_tac >>
  `ALL_DISTINCT (fn_labels at.po_fn)` by fs[EVERY_MEM,wf_function_def] >>
  drule ptr_owner_frame_active >> strip_tac >>
  drule_all active_inst_block_lookup >> strip_tac >>
  `bb' = bb` by metis_tac[optionTheory.SOME_11] >>
  `get_instruction bb at.po_state.vs_inst_idx = SOME at.po_inst` by gvs[] >>
  `i <= at.po_state.vs_inst_idx` by decide_tac >>
  drule_all revert_forward_pair_interval_opcode >> strip_tac
  >- (qsuff_tac `F` >- simp[] >> decide_tac)
  >- simp[] >>
  simp[in_revert_forward_def, revert_forward_at_def] >>
  qexists `i` >> gvs[]
QED

Theorem focus_concretize_window_frame_access[local]:
  ptr_chrono_history vs C h at /\
  EVERY wf_function C.ctx_functions /\
  EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions /\
  (!b op. MEM b h /\ b.po_inst.inst_opcode = RETURNDATACOPY /\
    MEM op b.po_inst.inst_operands ==> op_taint b.po_taint op = {}) /\
  lookup_block at.po_state.vs_current_bb at.po_fn.fn_blocks = SOME bb /\
  revert_forward_pair bb i j /\
  i < at.po_state.vs_inst_idx /\ at.po_state.vs_inst_idx <= j ==>
  access_ok eom at.po_prov at.po_fn at.po_inst at.po_state /\
  taint_ok at.po_fn at.po_taint at.po_inst at.po_state
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all focus_concretize_window_opcode >> strip_tac
  >- simp[access_ok_def, taint_ok_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def] >>
  `!op. MEM op at.po_inst.inst_operands ==> op_taint at.po_taint op = {}` by
    metis_tac[ptr_chrono_forward_revert_operands_clean] >>
  simp[access_ok_def, taint_ok_def, about_to_revert_def] >> metis_tac[]
QED

Theorem focus_concretize_paired_frame_access_ptr_safe:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_initial_state_ok vs /\
  vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  o1_ptr_safe_upto D lo n C vs /\ alloca_frontier_upto n C vs /\
  EVERY ssa_form C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  max_live_eom C' = SOME eom /\ ptr_stage_placements C' positions /\
  (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  gas_cut n vs at.po_state /\
  EVERY (\i. ~in_revert_forward (EL i h).po_fn (EL i h).po_state) done /\
  a.po_inst.inst_opcode <> NOP /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state /\
  gas_cut n vs a.po_state /\
  access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state ==>
  access_ok eom at.po_prov at.po_fn at.po_inst at.po_state /\
  taint_ok at.po_fn at.po_taint at.po_inst at.po_state
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\ fixed_region_reserved lo C /\
   ptr_discipline_upto lo n C vs` by fs[o1SafeUptoTheory.o1_ptr_safe_upto_def] >>
  drule concretizePtrChronologicalDemandTheory.ptr_frame_operand_instructions >> strip_tac >>
  drule frame_reachable_functions_member >> strip_tac >>
  `inst_wf a.po_inst /\ wf_function a.po_fn /\ fn_shape_ok a.po_fn /\
   EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions` by
    (fs[o1PassContractTheory.o1_ctx_shape_def,o1PassContractTheory.o1_fn_shape_def,
        EVERY_MEM] >> metis_tac[concretizePtrHistoricalWriteExclusionTheory.ptr_fn_inst_wf_flat,
                              EVERY_MEM]) >>
  Cases_on `a.po_inst.inst_opcode = ALLOCA`
  >- (qpat_assum `at.po_inst = concretize_inst_with_positions _ _` mp_tac >>
      `LENGTH a.po_inst.inst_outputs = 1` by fs[inst_wf_def] >>
      fs[LENGTH_EQ_NUM_compute] >>
      Cases_on `FLOOKUP (lp a.po_fn) (Allocation a.po_inst.inst_id)` >>
      simp[concretizeMemLocDefsTheory.concretize_inst_with_positions_def, AllCaseEqs()] >>
      rpt strip_tac >>
      fs[mk_assign_inst_def, mk_nop_inst_def, access_ok_def, taint_ok_def,
         source_memory_read_ranges_def, source_memory_write_ranges_def, op_taint_def]) >>
  `at.po_inst = a.po_inst` by simp[concretize_positions_unchanged] >>
  drule_all focus_concretize_cut_ghost_endpoint_ptr_safe >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `ptr_dalloca_ghost_sample _ _ _ _ _ a at`
    (strip_assume_tac o SIMP_RULE (srw_ss())
      [concretizePtrDallocaGhostInterfaceTheory.ptr_dalloca_ghost_sample_def,
       concretizePtrDallocaGhostInterfaceTheory.ptr_dalloca_ghost_compare_def]) >>
  `!op. op_taint at.po_taint op SUBSET op_taint a.po_taint op` by
    (gen_tac >> Cases_on `op` >>
     fs[concretizePtrDallocaGhostInterfaceTheory.ptr_dalloca_ghost_vars_def,
        op_taint_def, entry_taint_def] >> metis_tac[]) >>
  Cases_on `in_revert_forward a.po_fn a.po_state`
  >- (`in_revert_forward at.po_fn at.po_state` by
        (drule_all concretizePtrForwardingTransportTheory.ptr_paired_prefix_forwarding_static >> simp[]) >>
      `a.po_inst.inst_opcode = RETURNDATACOPY \/ a.po_inst.inst_opcode = REVERT` by
        (drule ptr_owner_frame_active >> strip_tac >>
         `ALL_DISTINCT (fn_labels a.po_fn)` by fs[wf_function_def] >>
         drule_all active_inst_block_lookup >> strip_tac >>
         fs[in_revert_forward_def] >> drule_all revert_forward_at_opcode >> simp[]) >>
      `!op. MEM op a.po_inst.inst_operands ==> op_taint a.po_taint op = {}` by
        (fs[taint_ok_def] >> metis_tac[]) >>
      `!op. MEM op a.po_inst.inst_operands ==> op_taint at.po_taint op = {}` by
        metis_tac[SUBSET_EMPTY] >>
      fs[access_ok_def,taint_ok_def,about_to_revert_def,
         source_memory_read_ranges_def] >> metis_tac[]) >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  drule_all ptr_source_ownership_erases_upto >> strip_tac >>
  drule (Q.INST [`rpolicy` |-> `rpolicy`, `n` |-> `n`,
                 `eom` |-> `eom`, `names` |-> `names`] focus_cut_paired_access_ranges) >>
  simp[] >> disch_then (mk_asm "ranges") >>
  conj_tac >- suspend "access" >>
  suspend "taint"
QED

Resume focus_concretize_paired_frame_access_ptr_safe[access]:
  markerLib.RESUME_TAC >> rpt disch_tac >>
  `lo <= eom` by
    (drule_all concretizePtrStageBoundsTheory.ptr_stage_fixed_region_bound >> simp[]) >>
  `!v b sz. FLOOKUP at.po_prov v = SOME (b,sz) ==> dyn_floor C vs <= b` by
    (rpt strip_tac >>
     `FLOOKUP TG v = NONE` by metis_tac[] >>
     `FLOOKUP a.po_prov v = SOME (b,sz)` by
       (fs[concretizePtrDallocaGhostInterfaceTheory.ptr_dalloca_ghost_vars_def] >>
        metis_tac[]) >>
     qpat_assum `ptr_ledger_erases _ _ _ _`
       (mp_tac o Q.SPEC `v` o CONJUNCT1 o REWRITE_RULE
         [concretizePtrPrefixLedgerTheory.ptr_ledger_erases_def]) >>
     simp[concretizePtrPrefixLedgerTheory.ptr_owner_erases_def]) >>
  drule ptr_structural_transcript_endpoint >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_chrono_history_end >> strip_tac >>
  `LENGTH h - 1 < LENGTH h` by decide_tac >>
  `h <> [] /\ H <> []` by (Cases_on `H` >> gvs[]) >>
  `EL (LENGTH h - 1) h = a /\
   EL (LENGTH h - 1) H = (tokens,registry,births,PT,TG,saved,entries)` by
    metis_tac[REWRITE_RULE [PRE_SUB1] LAST_EL] >>
  `ptr_observation_reachable vs C a` by
    (drule ptr_chrono_history_reachable >> simp[]) >>
  `vs.vs_allocas = FEMPTY` by fs[unitTransformDefsTheory.o1_initial_state_ok_def] >>
  `!v b sz. FLOOKUP a.po_prov v = SOME (b,sz) /\
     dyn_floor C vs <= b /\ 0 < sz ==> FLOOKUP at.po_prov v = SOME (b,sz)` by
    (rpt strip_tac >> Cases_on `FLOOKUP TG v` >- metis_tac[] >>
     rename1 `FLOOKUP TG v = SOME tag` >> PairCases_on `tag` >>
     `?d. d <= LENGTH a.po_stack /\
          FLOOKUP (ptr_owner_view d a).cf_state.vs_allocas tag1 = SOME (b,sz)` by
       (drule_at (Pat `ptr_structural_transcript _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
          (Q.SPECL [`LENGTH (h:ptr_observation list) - 1`, `LENGTH (h:ptr_observation list) - 1`]
            (GENL [``i:num``,``j:num``] ptr_transcript_historical_placement_upto)) >>
        simp[] >> disch_then drule_all >> simp[] >> metis_tac[]) >>
     `b + sz <= dyn_floor C vs` by (drule_all ptr_cut_owner_below_floor >> simp[]) >>
     qsuff_tac `F` >- simp[] >> decide_tac) >>
  qpat_x_assum `EL (LENGTH h - 1) h = a` kall_tac >>
  `!op. op_prov TG op = NONE ==>
     op_prov a.po_prov op = op_prov at.po_prov op` by
    (gen_tac >> Cases_on `op` >> simp[op_prov_def] >> disch_tac >>
     rename1 `FLOOKUP TG v = NONE` >>
     qpat_assum `ptr_dalloca_ghost_vars _ _ _ _ _ _`
       (mp_tac o Q.SPEC `v` o CONJUNCT2 o REWRITE_RULE
         [concretizePtrDallocaGhostInterfaceTheory.ptr_dalloca_ghost_vars_def]) >>
     qpat_assum `!v site. FLOOKUP TG v = NONE /\ _ ==> FLOOKUP at.po_prov v = SOME site`
       (mp_tac o Q.SPEC `v`) >>
     Cases_on `FLOOKUP at.po_prov v` >> Cases_on `FLOOKUP a.po_prov v` >> simp[]) >>
  `!op. op_prov TG op <> NONE ==> op_prov at.po_prov op = NONE` by
    (gen_tac >> Cases_on `op` >> simp[op_prov_def] >> disch_tac >>
     rename1 `FLOOKUP TG v <> NONE` >>
     qpat_assum `!v site. FLOOKUP at.po_prov v = SOME site ==> FLOOKUP TG v = NONE`
       (mp_tac o Q.SPEC `v`) >> Cases_on `FLOOKUP at.po_prov v` >> simp[]) >>
  `!mops rs rt off len.
     ((mops = mem_read_ops a.po_inst /\ rs = source_memory_read_ranges a.po_inst a.po_state /\
       rt = source_memory_read_ranges a.po_inst at.po_state) \/
      (mops = mem_write_ops a.po_inst /\ rs = source_memory_write_ranges a.po_inst a.po_state /\
       rt = source_memory_write_ranges a.po_inst at.po_state)) /\
     MEM (off,len) rt /\ 0 < len ==>
     ?off_s. MEM (off_s,len) rs /\
       ((off = off_s /\ (!ops. mops = SOME ops ==>
          op_prov a.po_prov ops.iao_ofst = op_prov at.po_prov ops.iao_ofst)) \/
        (off + len <= eom /\ (!ops. mops = SOME ops ==>
          op_prov at.po_prov ops.iao_ofst = NONE)))` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     asm "ranges" drule_all >>
     disch_then (qx_choose_then `off_s` (CONJUNCTS_THEN2 assume_tac
       (DISJ_CASES_THEN2 strip_assume_tac (qx_choose_then `ops`
         (qx_choose_then `x` (qx_choose_then `y` (fn th =>
           let val (facts,kind) = front_last (CONJUNCTS th)
           in map_every assume_tac facts >>
              DISJ_CASES_THEN2 (map_every assume_tac o CONJUNCTS) strip_assume_tac kind
           end))))))) >>
     qexists `off_s` >> (conj_tac >- simp[])
     >- (disj1_tac >> (conj_tac >- simp[]) >> rpt strip_tac >>
         qpat_assum `!ops. mops = SOME ops ==> _ /\ _` drule >> strip_tac >>
         qpat_assum `!op. op_prov TG op = NONE ==> _` drule >> simp[])
     >- (disj1_tac >> simp[] >> qpat_assum `!op. op_prov TG op = NONE ==> _` drule >> simp[]) >>
     disj2_tac >> (conj_tac >- decide_tac) >>
     simp[] >> qpat_assum `!op. op_prov TG op <> NONE ==> _` irule >>
     simp[op_prov_def]) >>
  irule ptr_dalloca_access_transport_positive >>
  qpat_assum `ptr_dalloca_ghost_vars _ _ _ _ _ _` (irule_at Any) >>
  qexistsl [`lo`,`a.po_fn`,`dyn_floor C vs`] >>
  asm_rewrite_tac[] >> simp[]
QED

Resume focus_concretize_paired_frame_access_ptr_safe[taint]:
  markerLib.RESUME_TAC >> rpt disch_tac >>
  Cases_on `a.po_inst.inst_opcode = RETURNDATACOPY \/ a.po_inst.inst_opcode = REVERT`
  >- (`!op. MEM op a.po_inst.inst_operands ==> op_taint a.po_taint op = {}` by
        (qpat_assum `taint_ok a.po_fn a.po_taint a.po_inst a.po_state`
           (mp_tac o CONJUNCT1 o REWRITE_RULE[taint_ok_def]) >>
         qpat_assum `a.po_inst.inst_opcode = RETURNDATACOPY \/ a.po_inst.inst_opcode = REVERT` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
         qpat_x_assum `!operand. _` (qspec_then `op` mp_tac) >>
         qpat_x_assum `a.po_inst.inst_opcode = _` SUBST1_TAC >> simp[]) >>
      `!op. MEM op a.po_inst.inst_operands ==> op_taint at.po_taint op = {}` by
        metis_tac[SUBSET_EMPTY] >>
      fs[taint_ok_def,about_to_revert_def,source_memory_read_ranges_def] >> metis_tac[]) >>
  `!off len i.
     MEM (off,len) (source_memory_read_ranges a.po_inst at.po_state) /\
     off <= i /\ i < off + len /\ i IN at.po_taint.t_mem ==>
     ?off_s j. MEM (off_s,len) (source_memory_read_ranges a.po_inst a.po_state) /\
       off_s <= j /\ j < off_s + len /\ j IN a.po_taint.t_mem` by
    (rpt gen_tac >> strip_tac >> `0 < len` by decide_tac >>
     qabbrev_tac `mops = mem_read_ops a.po_inst` >>
     qabbrev_tac `rs = source_memory_read_ranges a.po_inst a.po_state` >>
     qabbrev_tac `rt = source_memory_read_ranges a.po_inst at.po_state` >>
     Q.SUBGOAL_THEN
       `(mops = mops /\ rs = rs /\ rt = rt) \/
        (mops = mem_write_ops a.po_inst /\ rs = source_memory_write_ranges a.po_inst a.po_state /\
         rt = source_memory_write_ranges a.po_inst at.po_state)` assume_tac
     >- simp[] >>
     asm "ranges" drule_all >>
     disch_then (qx_choose_then `off_s` (CONJUNCTS_THEN2 assume_tac
       (DISJ_CASES_THEN2 strip_assume_tac (qx_choose_then `ops`
         (qx_choose_then `x` (qx_choose_then `y` (fn th =>
           let val (facts,kind) = front_last (CONJUNCTS th)
           in map_every assume_tac facts >>
              DISJ_CASES_THEN2 (map_every assume_tac o CONJUNCTS) strip_assume_tac kind
           end)))))))
     >- (`i < lo` by decide_tac >> qexistsl [`off_s`,`i`] >>
         simp[] >> first_assum irule >> simp[])
     >- (`i < lo \/ dyn_floor C vs <= i` by gvs[] >>
         qexistsl [`off_s`,`i`] >> simp[] >> first_assum irule >> simp[]) >>
     `mem_read_ops a.po_inst = SOME ops` by fs[Abbr `mops`] >>
     `inst_read_op a.po_inst = SOME (Var v)` by
       simp[concretizeMemLocDefsTheory.inst_read_op_def] >>
     drule concretizePtrReadOriginTheory.ptr_read_op_operand >> strip_tac >>
     `a.po_inst.inst_opcode <> ASSIGN` by (strip_tac >> fs[memLocDefsTheory.mem_read_ops_def]) >>
     qabbrev_tac `ix = (w2n x - b) + (i - w2n y)` >>
     `ix < sz /\ pa + ix = i /\ off_s <= b + ix /\ b + ix < off_s + len` by
       (simp[Abbr `ix`] >> decide_tac) >>
     `b + ix IN a.po_taint.t_mem` by
       (qpat_assum `!v token aid b sz pos ix. _ ==> _ ==> _`
          (qspecl_then [`v`,`EL (LENGTH a.po_stack - d) tokens`,`aid`,`b`,`sz`,`pa`,`ix`] mp_tac) >>
        simp[]) >>
     qexistsl [`off_s`,`b + ix`] >> simp[]) >>
  irule ptr_dalloca_taint_transport >>
  qexistsl [`a.po_fn`,`a.po_state`,`a.po_taint`] >>
  asm_rewrite_tac[] >> simp[about_to_revert_def] >> conj_tac
  >- (strip_tac >>
      drule o1LowerDloadPtrDisciplineTheory.ptr_discipline_upto_fn_ptr_ok >> strip_tac >>
      drule_all ptr_focus_source_tagged_support >> strip_tac >>
      `fn_ptr_ok P a.po_fn` by fs[EVERY_MEM] >>
      `opaque_use_ok a.po_fn` by fs[unitShapeDefsTheory.fn_shape_ok_def] >>
      drule ptr_paired_prefix_endpoint >> strip_tac >>
      `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
          a.po_state at.po_state /\ a.po_state.vs_labels = at.po_state.vs_labels` by
        (fs[ptr_paired_sample_def] >> metis_tac[concretizePtrRequestHistoryTheory.ptr_history_content_labels]) >>
      fs[concretizePtrParamSupportTheory.ptr_static_support_def] >>
      metis_tac[ptr_dalloca_mul_clean_demands]) >>
  gvs[]
QED

Finalise focus_concretize_paired_frame_access_ptr_safe[local]

(* Preserve the previous export: its [local] attribute on the suspended
   declaration was ignored, so the old Finalise exported this name. *)
Theorem focus_concretize_paired_frame_access:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_initial_state_ok vs /\
  vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  o1_safe_upto D lo n C vs /\ alloca_frontier_upto n C vs /\
  EVERY ssa_form C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  max_live_eom C' = SOME eom /\ ptr_stage_placements C' positions /\
  (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\
  gas_cut n vs at.po_state /\
  EVERY (\i. ~in_revert_forward (EL i h).po_fn (EL i h).po_state) done /\
  a.po_inst.inst_opcode <> NOP /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state /\
  gas_cut n vs a.po_state /\
  access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state ==>
  access_ok eom at.po_prov at.po_fn at.po_inst at.po_state /\
  taint_ok at.po_fn at.po_taint at.po_inst at.po_state
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  fs[o1SafeUptoTheory.o1_safe_upto_def] >>
  drule_all focus_concretize_paired_frame_access_ptr_safe >> simp[]
QED

Theorem focus_concretize_cut_frame_access:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_ctx_shape C' /\ o1_initial_state_ok vs /\
  vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  o1_ptr_safe_upto D lo n C vs /\
  mem_inv (\ctx fn inst s. gas_cut n vs s ==> dload_headroom_ok ctx fn inst s) C vs /\
  (!fn inst s. raw_reachable vs C fn inst s /\ gas_cut n vs s ==>
    raw_mem_ok C fn inst s /\ dload_offset_ok C fn inst s) /\
  alloca_frontier_upto n C vs /\
  EVERY ssa_form C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  max_live_eom C' = SOME eom /\
  (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) ==>
  !stk PG G tn fn inst s. frame_reachable vs C' stk PG G tn fn inst s /\
    gas_cut n vs s ==> access_ok eom G fn inst s /\ taint_ok fn tn inst s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all focus_concretize_cut_fields_cut_headroom >> strip_tac >>
  `EVERY wf_function C'.ctx_functions /\
   EVERY (\fn. EVERY inst_wf (fn_insts fn)) C'.ctx_functions` by
    (fs[o1PassContractTheory.o1_ctx_shape_def,o1PassContractTheory.o1_fn_shape_def,
        EVERY_MEM] >> metis_tac[concretizePtrHistoricalWriteExclusionTheory.ptr_fn_inst_wf_flat,
                              EVERY_MEM]) >>
  `!ht at. ptr_chrono_history vs C' ht at /\ gas_cut n vs at.po_state ==>
     (access_ok eom at.po_prov at.po_fn at.po_inst at.po_state /\
      taint_ok at.po_fn at.po_taint at.po_inst at.po_state) \/
     ?bb i j. lookup_block at.po_state.vs_current_bb at.po_fn.fn_blocks = SOME bb /\
       revert_forward_pair bb i j /\ i < at.po_state.vs_inst_idx /\
       at.po_state.vs_inst_idx <= j` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!ht at. ptr_chrono_history _ _ ht at /\ _ ==> _ <= _ /\ _`
       (qspecl_then [`ht`,`at`] mp_tac) >> (impl_tac >- simp[]) >> strip_tac
     >- (disj1_tac >> drule_at
           (Pat `ptr_paired_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
           focus_concretize_paired_frame_access_ptr_safe >>
         metis_tac[]) >>
     disj2_tac >> metis_tac[]) >>
  `!ht at. ptr_chrono_history vs C' ht at /\ gas_cut n vs at.po_state /\
     at.po_inst.inst_opcode = RETURNDATACOPY ==>
     !op. MEM op at.po_inst.inst_operands ==> op_taint at.po_taint op = {}` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!ht at. _ ==> (_ /\ taint_ok _ _ _ _) \/ _`
       (qspecl_then [`ht`,`at`] mp_tac) >> (impl_tac >- simp[]) >> strip_tac
     >- (qpat_x_assum `taint_ok _ _ _ _` mp_tac >> simp[taint_ok_def] >> metis_tac[]) >>
     drule_all focus_concretize_window_opcode >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_then (qx_choose_then `ht` assume_tac) ptr_reachable_has_chrono_history >>
  qabbrev_tac `at = ptr_observe stk PG G tn fn inst s` >>
  `gas_cut n vs at.po_state` by simp[Abbr `at`,ptr_observe_def] >>
  `access_ok eom at.po_prov at.po_fn at.po_inst at.po_state /\
   taint_ok at.po_fn at.po_taint at.po_inst at.po_state` suffices_by
    simp[Abbr `at`,ptr_observe_def] >>
  qpat_assum `!ht at. _ ==> (_ /\ taint_ok _ _ _ _) \/ _`
    (qspecl_then [`ht`,`at`] mp_tac) >> (impl_tac >- simp[]) >> strip_tac
  >- simp[] >>
  `!b op. MEM b ht /\ b.po_inst.inst_opcode = RETURNDATACOPY /\
      MEM op b.po_inst.inst_operands ==> op_taint b.po_taint op = {}` by
    (rpt gen_tac >> strip_tac >>
     drule_all ptr_chrono_history_cut >> simp[EVERY_MEM] >> strip_tac >>
     qpat_x_assum `MEM b ht` (strip_assume_tac o REWRITE_RULE[MEM_EL]) >>
     drule ptr_chrono_history_prefix >> disch_then drule >>
     disch_then assume_tac >>
     `MEM b ht` by metis_tac[MEM_EL] >>
     `gas_cut n vs b.po_state` by simp[] >>
     qpat_assum `!ht at. _ ==> !op. _`
       (qspecl_then [`TAKE (SUC n') ht`,`b`] mp_tac) >>
     gvs[] >> metis_tac[]) >>
  irule focus_concretize_window_frame_access >>
  (metis_tac[])
QED
