(*
 * Paired-prefix extension for every continuing target step: the universal
 * premise of ptr_paired_history_coverage, under the stage premises.
 *)
Theory concretizePtrUniversalExtension
Ancestors
  concretizePtrAffineFamily concretizePtrComparisonFamily concretizePtrIloadFamily concretizePtrByteStoreFamily concretizePtrBufferCopyFamily concretizePtrExtcodecopyFamily concretizePtrStorageWriteFamily concretizePtrHashLogFamily concretizePtrCallFamily concretizePtrCreateFamily
  concretizePtrStorageReadProducer concretizePtrPairedJump
  concretizePtrOperationalOpcodes concretizePtrPairedPrefix
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrChronologicalHistory ptrDiscipline unitShapeDefs venomWf
  pointerConfinedDefs venomInst list o1PassContract unitLabelMapIdentity
  concretizeStepStructure venomExecSemantics concretizePtrDeletedGapHistory
  contextCodegenRel concretizePtrPairedJumpEntry concretizePtrPairedCallSchema

Theorem current_retpc_parse[local]:
  retpc_shape_ok = frameRel$retpc_shape_ok
Proof
  simp[]
QED

Theorem ptr_paired_universal_jump_extension[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_discipline lo C vs /\ o1_ctx_shape C /\ ~ctx_has_dalloca C /\
  EVERY (\f. fn_inst_wf f /\ retpc_shape_ok f /\ opaque_use_ok f /\
    EVERY bb_well_formed f.fn_blocks /\ ALL_DISTINCT (fn_labels f) /\
    (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions /\
  EVERY (\g. ALL_DISTINCT (fn_labels g)) C'.ctx_functions /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt /\ MEM a.po_inst.inst_opcode [JMP; JNZ; DJMP] ==>
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
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `MEM a.po_fn C.ctx_functions` by
    (drule ptr_structural_trace_source >> strip_tac >>
     drule ptr_chrono_history_reachable >>
     simp[ptr_observation_reachable_def] >> strip_tac >>
     drule ptr_frame_context_membership >> simp[]) >>
  `MEM at.po_fn C'.ctx_functions` by
    (drule ptr_structural_trace_target >> strip_tac >>
     drule ptr_chrono_history_reachable >>
     simp[ptr_observation_reachable_def] >> strip_tac >>
     drule ptr_frame_context_membership >> simp[]) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def,
        EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >> metis_tac[]) >>
  `EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions` by
    (fs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `unitShapeDefs$retpc_shape_ok a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def,
        EVERY_MEM] >> metis_tac[]) >>
  `at.po_inst = a.po_inst` by
    (fs[MEM] >> gvs[concretize_positions_unchanged]) >>
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[is_terminator_def, MEM]
  >>~- ([`step_inst _ _ _ _ = IntRet _ _`],
    qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
    simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()])
  >~ [`a.po_inst.inst_opcode = JMP`] >- suspend "jmp"
  >~ [`a.po_inst.inst_opcode = JNZ`] >- suspend "jnz"
  >> suspend "djmp"
QED

Resume ptr_paired_universal_jump_extension[jmp]:
  `fn_inst_wf a.po_fn /\ retpc_shape_ok a.po_fn /\
   EVERY bb_well_formed a.po_fn.fn_blocks /\
   ALL_DISTINCT (fn_labels a.po_fn) /\ ALL_DISTINCT (fn_labels at.po_fn) /\
   (!i. MEM i (fn_insts a.po_fn) /\ i.inst_opcode = ALLOCA ==>
     IS_SOME (FLOOKUP (lp a.po_fn) (Allocation i.inst_id)))` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `zt = ptr_observe at.po_stack at.po_params
    (entry_prov at.po_fn s' at.po_prov)
    (entry_taint_vars at.po_fn s' at.po_taint) at.po_fn zt.po_inst zt.po_state` by
    simp[ptr_observation_component_equality, ptr_observe_def] >>
  drule ptr_paired_jump_prefix_normalize >>
  simp[is_terminator_def] >>
  disch_then (qspecl_then [`s'`, `zt.po_state`, `zt.po_inst`, `fuel`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_x_assum `zt = ptr_observe _ _ _ _ _ _ _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th])) >>
  qexistsl_tac [`[b] ++ delta`, `ptr_gap_scan bb (LENGTH delta) b`,
    `tokens`, `registry`, `ptr_birth_overlay (HD tokens) b.po_state.vs_allocas births`,
    `PT`, `entry_prov a.po_fn s_jump TG`, `saved`, `entries`,
    `[(tokens,registry,ptr_birth_overlay (HD tokens) b.po_state.vs_allocas births,
       PT,entry_prov a.po_fn s_jump TG,saved,entries)] ++ snapshots`, `calls`, `ws`] >>
  gvs[APPEND_ASSOC, ptr_gap_scan_fields, ptr_observe_def,
      ptr_observation_component_equality]
QED
Resume ptr_paired_universal_jump_extension[jnz]:
  `?cond yes no. a.po_inst.inst_operands = [cond; Label yes; Label no]` by
    (`active_inst a.po_fn a.po_inst a.po_state` by
       (drule ptr_structural_trace_source >> strip_tac >>
        drule ptr_chrono_history_reachable >>
        simp[ptr_observation_reachable_def] >> strip_tac >>
        qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
        simp[Once frame_reachable_cases] >> rpt strip_tac >> gvs[]) >>
     `MEM a.po_inst (fn_insts a.po_fn)` by
       (fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
     `inst_wf a.po_inst` by (fs[EVERY_MEM] >> metis_tac[]) >>
     gvs[inst_wf_def] >> metis_tac[]) >>
  `opaque_use_ok a.po_fn` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `MEM a.po_inst.inst_opcode [JNZ; DJMP] /\ MEM cond a.po_inst.inst_operands` by simp[] >>
  drule_all ptr_owned_jnz_scalar >> strip_tac >>
  `fn_inst_wf a.po_fn /\ EVERY bb_well_formed a.po_fn.fn_blocks /\
   ALL_DISTINCT (fn_labels a.po_fn) /\ ALL_DISTINCT (fn_labels at.po_fn) /\
   (!i. MEM i (fn_insts a.po_fn) /\ i.inst_opcode = ALLOCA ==>
     IS_SOME (FLOOKUP (lp a.po_fn) (Allocation i.inst_id)))` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `zt = ptr_observe at.po_stack at.po_params
    (entry_prov at.po_fn s' at.po_prov)
    (entry_taint_vars at.po_fn s' at.po_taint) at.po_fn zt.po_inst zt.po_state` by
    simp[ptr_observation_component_equality, ptr_observe_def] >>
  drule ptr_paired_jnz_prefix_normalize >> simp[is_terminator_def] >>
  disch_then (qspecl_then [`s'`, `zt.po_state`, `zt.po_inst`, `fuel`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_x_assum `zt = ptr_observe _ _ _ _ _ _ _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th])) >>
  qexistsl_tac [`[b] ++ delta`, `ptr_gap_scan bb (LENGTH delta) b`,
    `tokens`, `registry`, `ptr_birth_overlay (HD tokens) b.po_state.vs_allocas births`,
    `PT`, `entry_prov a.po_fn s_jump TG`, `saved`, `entries`,
    `[(tokens,registry,ptr_birth_overlay (HD tokens) b.po_state.vs_allocas births,
       PT,entry_prov a.po_fn s_jump TG,saved,entries)] ++ snapshots`, `calls`, `ws`] >>
  simp[APPEND_ASSOC, ptr_gap_scan_fields]
QED
Resume ptr_paired_universal_jump_extension[djmp]:
  `fn_inst_wf a.po_fn /\ opaque_use_ok a.po_fn /\
   EVERY bb_well_formed a.po_fn.fn_blocks /\
   ALL_DISTINCT (fn_labels a.po_fn) /\ ALL_DISTINCT (fn_labels at.po_fn) /\
   (!i. MEM i (fn_insts a.po_fn) /\ i.inst_opcode = ALLOCA ==>
     IS_SOME (FLOOKUP (lp a.po_fn) (Allocation i.inst_id)))` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `zt = ptr_observe at.po_stack at.po_params
    (entry_prov at.po_fn s' at.po_prov)
    (entry_taint_vars at.po_fn s' at.po_taint) at.po_fn zt.po_inst zt.po_state` by
    simp[ptr_observation_component_equality, ptr_observe_def] >>
  drule ptr_paired_djmp_prefix_normalize >> simp[is_terminator_def] >>
  disch_then (qspecl_then [`s'`, `zt.po_state`, `zt.po_inst`, `fuel`] mp_tac) >>
  disch_then (qspec_then `P` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_x_assum `zt = ptr_observe _ _ _ _ _ _ _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th])) >>
  qexistsl_tac [`[b] ++ delta`, `ptr_gap_scan bb (LENGTH delta) b`,
    `tokens`, `registry`, `ptr_birth_overlay (HD tokens) b.po_state.vs_allocas births`,
    `PT`, `entry_prov a.po_fn s_jump TG`, `saved`, `entries`,
    `[(tokens,registry,ptr_birth_overlay (HD tokens) b.po_state.vs_allocas births,
       PT,entry_prov a.po_fn s_jump TG,saved,entries)] ++ snapshots`, `calls`, `ws`] >>
  simp[APPEND_ASSOC, ptr_gap_scan_fields]
QED
Finalise ptr_paired_universal_jump_extension

Theorem ptr_paired_universal_invoke_extension[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_discipline lo C vs /\
  LIST_REL (ptr_paired_code R lp positions) C.ctx_functions C'.ctx_functions /\
  (!f g. ptr_paired_code R lp positions f g ==> g.fn_name = f.fn_name) /\
  EVERY (\f. first_block_no_phi f /\ fn_inst_wf f /\ opaque_use_ok f /\
    EVERY bb_well_formed f.fn_blocks /\ ALL_DISTINCT (fn_labels f) /\
    (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions /\
  EVERY (\g. ALL_DISTINCT (fn_labels g)) C'.ctx_functions /\
  a.po_inst.inst_opcode = INVOKE /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt ==>
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
  `opaque_use_ok a.po_fn` by
    (drule ptr_paired_prefix_transcript >> strip_tac >>
     drule ptr_structural_transcript_erasure >> strip_tac >>
     drule ptr_structural_trace_source >> strip_tac >>
     drule ptr_chrono_history_reachable >>
     simp[ptr_observation_reachable_def] >> strip_tac >>
     drule ptr_frame_context_membership >> strip_tac >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\f. first_block_no_phi f /\ fn_inst_wf f /\
    EVERY bb_well_formed f.fn_blocks /\ ALL_DISTINCT (fn_labels f) /\
    (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `at.po_inst = a.po_inst` by simp[concretize_positions_unchanged] >>
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[is_terminator_def]
  >>~- ([`step_inst _ _ _ _ = IntRet _ _`],
    qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
    simp[step_inst_def, AllCaseEqs()]) >>
  `zt = ptr_observe
    (<|cf_fn := at.po_fn; cf_inst := at.po_inst; cf_state := at.po_state;
       cf_params := at.po_params; cf_prov := at.po_prov;
       cf_tvar := at.po_taint.t_var|> :: at.po_stack)
    (MAP (op_prov at.po_prov) ops) FEMPTY
    (at.po_taint with t_var := FEMPTY) zt.po_fn zt.po_inst zt.po_state` by
    simp[ptr_observe_def, ptr_observation_component_equality] >>
  `decode_invoke at.po_inst = SOME (nm,ops) /\
   active_inst at.po_fn at.po_inst at.po_state /\
   at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst` by
    (qpat_x_assum `zt = ptr_observe _ _ _ _ _ _ _` kall_tac >> simp[]) >>
  drule ptr_paired_invoke_prefix_normalize >>
  disch_then (qspecl_then [`ops`, `nm`, `zt.po_inst`, `zt.po_fn`,
    `zt.po_state`, `cs`, `zt`, `args`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  qexistsl_tac [`[b] ++ delta`, `ptr_gap_scan bb n b`,
    `LENGTH h :: tokens`, `registry |+ (LENGTH h,f)`, `B`,
    `MAP (op_prov TG) ops`, `FEMPTY`, `(PT,TG)::saved`,
    `entries |+ (LENGTH h,LENGTH ht)`,
    `[(LENGTH h :: tokens,registry |+ (LENGTH h,f),B,
       MAP (op_prov TG) ops,FEMPTY,(PT,TG)::saved,
       entries |+ (LENGTH h,LENGTH ht))] ++ snapshots`,
    `(LENGTH h - 1,LENGTH ht - 1)::calls`, `ws`] >>
  qpat_x_assum `zt = ptr_observe _ _ _ _ _ _ _` kall_tac >>
  gvs[APPEND_ASSOC, ptr_gap_scan_fields, ptr_observe_def]
QED

Theorem ptr_paired_universal_extension:
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
  ptr_chrono_step C' at zt ==>
  ?delta z tokens' registry' births' PT' TG' saved' entries' snapshots calls' ws'.
    delta <> [] /\ LENGTH snapshots = LENGTH delta /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ delta) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens' registry' births' PT' TG' saved' entries'
      (H ++ snapshots) calls' ws' /\
    z.po_inst.inst_opcode <> NOP /\
    zt.po_inst = concretize_inst_with_positions (lp z.po_fn) z.po_inst
Proof
  cheat
QED

