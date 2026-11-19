Theory gasFocusConcretizeCutTaintWithin
Ancestors
  gasFocusConcretizeCutCoverage o1SafeUpto concretizeLayoutCutSafe
  lowerDloadPtrRawReachable lowerDloadRevertSuffix lowerDloadReachability
  frameAllocationOwnership concretizePtrChronologicalHistory
  gasFocusConcretizeGhostCutHistory gasFocusConcretizeGhostCutHalt
  concretizePtrDallocaPairedObservation concretizePtrDallocaGhostInterface
  concretizePtrPairedPrefix concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrHistoricalWriteExclusion concretizePtrParamSupport concretizePtrOwnerPath
  o1LowerDloadPtrDiscipline gasFocusConcretizeHistoricalCut gasFocusConcretizeTaggedSupport
  o1PassContract unitShapeDefs list finite_map ptrDiscipline
  lowerDloadRequestObservation concretizeLayoutLocalReturn opcodeClass
  concretizeStepShape concretizePtrOpaqueRetpc pred_set
  concretizeMemLocDefs concretizePtrPrefixLedger concretizePtrValueTransport
  venomState venomInst venomExecSemantics

Theorem ptr_cut_window_taint_steps[local]:
  ALL_DISTINCT (fn_labels fn) /\ active_inst fn inst s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  revert_forward_pair bb i j /\ i < s.vs_inst_idx /\ s.vs_inst_idx <= j ==>
  step_inst fuel ctx inst s <> Halt post /\
  (step_inst fuel ctx inst s = OK post ==> post.vs_requests = s.vs_requests)
Proof
  strip_tac >>
  drule_all active_inst_block_lookup >> strip_tac >> gvs[] >>
  drule_all ld_revert_pair_suffix_step >> simp[next_inst_def] >> metis_tac[]
QED

Theorem focus_concretize_cut_taint_within:
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
  (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) /\ dead_wf D ==>
  taint_within_upto D n C' vs
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all focus_concretize_cut_fields_cut_headroom >> strip_tac >>
  `taint_within_upto D n C vs /\ ptr_discipline_upto lo n C vs /\
   fixed_region_reserved lo C /\ EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions` by
     fs[o1_ptr_safe_upto_def] >>
  rewrite_tac[taint_within_upto_def] >> conj_tac >>
  map_every qx_gen_tac [`stk`,`PG`,`G`,`tn`,`fn`,`inst`,`s`,`fuel`,`post`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM fn C'.ctx_functions` by (drule frame_reachable_functions_member >> simp[]) >>
  `ALL_DISTINCT (fn_labels fn)` by
    (drule lowerDloadReachabilityTheory.o1_ctx_shape_distinct_block_labels >>
     simp[listTheory.EVERY_MEM, fn_labels_def]) >>
  drule ptr_reachable_has_chrono_history >> strip_tac >>
  qmatch_asmsub_abbrev_tac `ptr_chrono_history vs C' ht at` >>
  `gas_cut n vs at.po_state` by simp[Abbr `at`, ptr_observe_def] >>
  `active_inst at.po_fn at.po_inst at.po_state` by simp[Abbr `at`, ptr_observe_def] >>
  (reverse (qpat_assum `!ht at. ptr_chrono_history vs C' ht at /\ _ ==> _`
    (drule_all_then strip_assume_tac))
   >- (fs[Abbr `at`, ptr_observe_def] >> drule_all ptr_cut_window_taint_steps >>
       metis_tac[prim_recTheory.LESS_REFL])) >>
  drule_all focus_concretize_cut_ghost_endpoint_ptr_safe >> strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
     metis_tac[ptr_fn_inst_wf_flat, EVERY_MEM]) >>
  drule_all ptr_source_ownership_erases_upto >> strip_tac >>
  drule ptr_discipline_upto_fn_ptr_ok >> strip_tac >>
  drule_all ptr_frame_current_static >> strip_tac >>
  drule_all ptr_focus_source_tagged_support >> strip_tac >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (drule concretizePtrChronologicalDemandTheory.ptr_frame_operand_instructions >> simp[]) >>
  rename1 `ptr_static_support P a.po_fn TG` >>
  `fn_ptr_ok P a.po_fn /\ inst_wf a.po_inst /\ opaque_use_ok a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, inst_shape_ok_def, EVERY_MEM] >>
     metis_tac[]) >>
  `ALL_DISTINCT (fn_labels a.po_fn)` by
    (qpat_assum `o1_ctx_shape C` (mp_tac o MATCH_MP
       lowerDloadReachabilityTheory.o1_ctx_shape_distinct_block_labels) >>
     simp[listTheory.EVERY_MEM, fn_labels_def]) >>
  `ptr_observation_reachable vs C a` by simp[ptr_observation_reachable_def] >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (drule ptr_owner_frame_active >> simp[]) >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn a.po_state at.po_state /\
   ptr_history_content a.po_taint a.po_state at.po_state` by fs[ptr_paired_sample_def] >>
  qpat_x_assum `ptr_dalloca_ghost_sample _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o
     REWRITE_RULE [ptr_dalloca_ghost_sample_def, ptr_dalloca_ghost_compare_def])
  >- suspend "request" >> suspend "halt"
QED

Resume focus_concretize_cut_taint_within[request]:
  `at.po_inst.inst_opcode <> INVOKE /\ step_inst fuel C' at.po_inst at.po_state = OK post /\
   LENGTH at.po_state.vs_requests < LENGTH post.vs_requests` by
    (qpat_x_assum `at.po_inst = concretize_inst_with_positions _ _` kall_tac >>
     simp[Abbr `at`, ptr_observe_def]) >>
  drule_all ld_request_growth_external >> strip_tac >>
  `at.po_inst = a.po_inst` by
    (qpat_assum `at.po_inst = concretize_inst_with_positions _ _`
       (fn th => once_rewrite_tac[th] >> irule concretize_positions_other_opcode >>
         rewrite_tac[GSYM th] >> fs[MEM])) >>
  `~in_revert_forward a.po_fn a.po_state` by
    (irule active_inst_not_revert_forward >>
     qpat_assum `active_inst a.po_fn a.po_inst a.po_state` (irule_at Any) >>
     simp[] >> (gvs[MEM])) >>
  `EVERY bb_well_formed at.po_fn.fn_blocks` by
    (`wf_function fn` by (irule o1_ctx_shape_function_wf >> simp[] >> qexists `C'` >> simp[]) >>
     pop_assum mp_tac >>
     simp[Abbr `at`, ptr_observe_def, venomWfTheory.wf_function_def, EVERY_MEM]) >>
  `!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P a.po_fn` by
    fs[ptr_static_support_def] >>
  `!srcpost. a.po_inst.inst_opcode <> INVOKE /\
    step_inst 0 C a.po_inst a.po_state = OK srcpost /\
    LENGTH a.po_state.vs_requests < LENGTH srcpost.vs_requests ==>
      a.po_taint.t_stor SUBSET D.d_stor a.po_state.vs_call_ctx.cc_address
        (a.po_state.vs_accounts a.po_state.vs_call_ctx.cc_address).storage /\
      a.po_taint.t_trans SUBSET D.d_trans a.po_state.vs_call_ctx.cc_address
        (a.po_state.vs_transient a.po_state.vs_call_ctx.cc_address)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `taint_within_upto D n C vs`
       (drule_all_then ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [taint_within_upto_def])) >>
  `!ops x y len j.
    mem_read_ops a.po_inst = SOME ops /\ eval_operand ops.iao_ofst a.po_state = SOME x /\
    eval_operand ops.iao_ofst at.po_state = SOME y /\
    MEM (w2n x,len) (source_memory_read_ranges a.po_inst a.po_state) /\
    ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {} (SOME x) (SOME y) /\
    j < len /\ w2n x + j NOTIN a.po_taint.t_mem ==>
    read_byte (w2n x+j) a.po_state.vs_memory = read_byte (w2n y+j) at.po_state.vs_memory` by
    (rpt gen_tac >> strip_tac >> drule_all focus_cut_paired_read_bytes_ptr_safe >> simp[]) >>
  drule_all focus_cut_paired_request_observation >>
  qpat_x_assum `at.po_inst = concretize_inst_with_positions _ _` kall_tac >>
  simp[Abbr `at`, ptr_observe_def]
QED

Resume focus_concretize_cut_taint_within[halt]:
  `at.po_inst.inst_opcode <> INVOKE /\ step_inst fuel C' at.po_inst at.po_state = Halt post` by
    (qpat_x_assum `at.po_inst = concretize_inst_with_positions _ _` kall_tac >>
     simp[Abbr `at`, ptr_observe_def]) >>
  `MEM at.po_inst.inst_opcode [STOP;RETURN;SINK;SELFDESTRUCT]` by
    (drule step_inst_halt_opcodes >> simp[MEM]) >>
  `at.po_inst = a.po_inst` by
    (qpat_assum `at.po_inst = concretize_inst_with_positions _ _`
       (fn th => once_rewrite_tac[th] >> irule concretize_positions_other_opcode >>
         rewrite_tac[GSYM th] >> gvs[MEM])) >>
  `MEM a.po_inst.inst_opcode [STOP;RETURN;SINK;SELFDESTRUCT]` by
    (qpat_assum `at.po_inst = a.po_inst` (fn th => rewrite_tac[GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  `~in_revert_forward a.po_fn a.po_state` by
    (irule active_inst_not_revert_forward >>
     qpat_assum `active_inst a.po_fn a.po_inst a.po_state` (irule_at Any) >>
     qpat_assum `MEM a.po_inst.inst_opcode _`
       (strip_assume_tac o REWRITE_RULE [MEM]) >> simp[]) >>
  `EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands` by
    ((simp[EVERY_MEM] >> Cases >> simp[ptr_nonopaque_operand_def] >>
     qpat_assum `opaque_use_ok a.po_fn`
       (mp_tac o REWRITE_RULE [opaque_use_ok_def]) >>
     disch_then drule >>
     qpat_assum `MEM a.po_inst.inst_opcode _`
       (strip_assume_tac o REWRITE_RULE [MEM]) >> simp[retpc_use_ok_def] >> (metis_tac[EVERY_MEM, ptr_nonopaque_operand_def, retpc_use_ok_def]))) >>
  `ptr_use_ok P (fn_pv P a.po_fn) a.po_inst` by
    (drule_all (cj 9 o1ContractMakeSsaPtrOkTheory.mssa_ok_inst) >> simp[]) >>
  `FDOM a.po_prov SUBSET fn_pv P a.po_fn` by
    (simp[SUBSET_DEF, venomExecProofsTheory.FDOM_FLOOKUP] >> rpt strip_tac >>
     qpat_assum `ptr_static_support P a.po_fn a.po_prov`
       (drule_all_then ACCEPT_TAC o REWRITE_RULE [ptr_static_support_def])) >>
  `!addr x y len.
    a.po_inst.inst_opcode = RETURN /\ inst_read_op a.po_inst = SOME addr /\
    eval_operand addr a.po_state = SOME x /\ eval_operand addr at.po_state = SOME y /\
    MEM (w2n x,len) (source_memory_read_ranges a.po_inst a.po_state) /\
    ptr_lookup_transport births positions (op_prov TG addr) {} (SOME x) (SOME y) ==>
    (0 < len ==>
      (x = y /\ (w2n x + len <= lo \/ dyn_floor C vs <= w2n x)) \/
      (?v token aid b sz p.
        addr = Var v /\ FLOOKUP TG v = SOME (token,aid) /\
        FLOOKUP a.po_prov v = SOME (b,sz) /\ FLOOKUP births (token,aid) = SOME (b,sz) /\
        FLOOKUP positions (Allocation aid) = SOME (p,sz) /\
        b <= w2n x /\ w2n x + len <= b + sz /\ w2n y = p + (w2n x - b))) /\
    (!k. k < len /\ w2n x + k NOTIN a.po_taint.t_mem ==>
      read_byte (w2n x + k) a.po_state.vs_memory = read_byte (w2n y + k) at.po_state.vs_memory)` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     `?ops. mem_read_ops a.po_inst = SOME ops /\ ops.iao_ofst = addr` by
       (qpat_x_assum `inst_read_op a.po_inst = _` mp_tac >>
        Cases_on `mem_read_ops a.po_inst` >> simp[inst_read_op_def]) >>
     `eval_operand ops.iao_ofst a.po_state = SOME x /\
      eval_operand ops.iao_ofst at.po_state = SOME y /\
      ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {} (SOME x) (SOME y)` by simp[] >>
     reverse conj_tac
     >- (gen_tac >> strip_tac >> drule_all focus_cut_paired_read_bytes_ptr_safe >> simp[]) >>
     strip_tac >>
     drule concretizePtrOwnershipErasureTheory.ptr_owner_op_projection >>
     disch_then (qspec_then `addr` strip_assume_tac) >>
     `w2n x + len <= lo /\ op_prov a.po_prov addr = NONE \/
      (?v b sz. addr = Var v /\ FLOOKUP a.po_prov v = SOME (b,sz) /\
                b <= w2n x /\ w2n x + len <= b + sz)` by
       (drule_all (SIMP_RULE (srw_ss()) [] (Q.INST
          [`ranges` |-> `source_memory_read_ranges inst s`, `mops` |-> `mem_read_ops inst`]
          concretizePtrObservationInterfaceTheory.ptr_access_range_classification)) >>
        simp[])
     >- (`op_prov TG addr = NONE` by
          (Cases_on `op_prov TG addr` >> gvs[ptr_owner_erases_def, FLOOKUP_DEF]) >>
         disj1_tac >> gvs[ptr_lookup_transport_def, ptr_value_transport_scalar_empty]) >>
     Cases_on `op_prov TG addr` >> gvs[op_prov_def, ptr_owner_erases_def]
     >- gvs[ptr_lookup_transport_def, ptr_value_transport_scalar_empty] >>
     rename1 `FLOOKUP TG v = SOME tag` >> PairCases_on `tag` >>
     `?p. FLOOKUP positions (Allocation tag1) = SOME (p,sz) /\ y = x - n2w b + n2w p` by
       gvs[ptr_lookup_transport_def, ptr_value_transport_def, op_prov_def] >>
     `p + sz < dimword (:256)` by
       (drule_all concretizePtrPlacementBoundsTheory.ptr_stage_placements_strict_bound >> simp[]) >>
     `w2n y = p + (w2n x - b)` by
       (irule concretizePtrComparisonTransportTheory.ptr_closed_relocation_value >>
        simp[] >> qexists `sz` >> simp[] >> decide_tac) >>
     disj2_tac >> qexistsl [`tag0`,`tag1`,`b`,`sz`,`p`] >> simp[]) >>
  `!sh. step_inst 0 C a.po_inst a.po_state = Halt sh ==>
    (step_taint a.po_inst a.po_state sh a.po_taint).t_stor SUBSET
      D.d_stor sh.vs_call_ctx.cc_address (sh.vs_accounts sh.vs_call_ctx.cc_address).storage /\
    (step_taint a.po_inst a.po_state sh a.po_taint).t_trans SUBSET
      D.d_trans sh.vs_call_ctx.cc_address (sh.vs_transient sh.vs_call_ctx.cc_address) /\
    (step_taint a.po_inst a.po_state sh a.po_taint).t_imm SUBSET D.d_imm sh.vs_immutables /\
    ret_taint a.po_taint a.po_inst a.po_state SUBSET D.d_ret sh.vs_returndata` by
    (gen_tac >> disch_tac >>
     `a.po_inst.inst_opcode <> INVOKE` by
       (qpat_assum `MEM a.po_inst.inst_opcode _`
          (strip_assume_tac o REWRITE_RULE [MEM]) >> simp[]) >>
     qpat_assum `taint_within_upto D n C vs`
       (drule_all_then ACCEPT_TAC o CONJUNCT2 o REWRITE_RULE [taint_within_upto_def])) >>
  `!v token aid b sz p j.
    inst_read_op a.po_inst = SOME (Var v) /\
    FLOOKUP TG v = SOME (token,aid) /\ FLOOKUP a.po_prov v = SOME (b,sz) /\
    FLOOKUP births (token,aid) = SOME (b,sz) /\
    FLOOKUP positions (Allocation aid) = SOME (p,sz) /\ j < sz /\
    p + j IN at.po_taint.t_mem ==> b + j IN a.po_taint.t_mem` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     drule_then assume_tac concretizePtrReadOriginTheory.ptr_read_op_operand >>
     `a.po_inst.inst_opcode <> ASSIGN` by fs[MEM] >>
     qpat_assum `!v token aid base size pos ix. _ /\ _ /\ MEM (Var v) _ /\ _ ==> _`
       (qspecl_then [`v`,`token`,`aid`,`b`,`sz`,`p`,`j`] mp_tac) >> simp[]) >>
  drule_all focus_cut_paired_halt_observation >>
  qpat_x_assum `at.po_inst = concretize_inst_with_positions _ _` kall_tac >>
  qpat_x_assum `at.po_inst = a.po_inst` kall_tac >>
  simp[Abbr `at`, ptr_observe_def]
QED

Finalise focus_concretize_cut_taint_within
