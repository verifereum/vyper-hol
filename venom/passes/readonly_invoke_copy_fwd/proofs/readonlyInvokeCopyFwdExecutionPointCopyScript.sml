(* Actual MCOPY steps preserve the runner's history and support channels. *)
Theory readonlyInvokeCopyFwdExecutionPointCopy
Ancestors
  readonlyInvokeCopyFwdExecutionSteps readonlyInvokeCopyFwdExecutionCopy
  readonlyInvokeCopyFwdExecutionRetainedCopy readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdExecutionCoverage readonlyInvokeCopyFwdExecutionHistory
  readonlyInvokeCopyFwdExecutionHistoryLifecycle readonlyInvokeCopyFwdExecutionMapCoverage
  readonlyInvokeCopyFwdAnalyzedOrigins readonlyInvokeCopyFwdAnalyzedLifecycle
  readonlyInvokeCopyFwdHeterogeneousLedger readonlyInvokeCopyFwdHistoryPhase
  readonlyInvokeCopyFwdHistoryEventUniqueness readonlyInvokeCopyFwdExecutionCallSites
  readonlyInvokeCopyFwdHistory readonlyInvokeCopyFwdPlan readonlyInvokeCopyFwdMapCoverage
  readonlyInvokeCopyFwdHistoryOrigin readonlyInvokeCopyFwdProtectionOrigin
  readonlyInvokeCopyFwdExecutionCopyShape
  invokeCopyFwdCommonDefs readonlyMemoryArgsDefs o1PassContract
  o1LowerDloadOccurrence o1LowerDloadGhost o1LowerDloadRawBridge
  occurrenceGeometry ptrDiscipline unitMemInv
  contextCodegenRel venomWf venomWfProps venomInstProofs venomExecSemantics
  venomExecProofs venomState venomInst finite_map list pred_set arithmetic words

Theorem ricf_copy_coverage_zero[local]:
  ricf_copy_coverage ctx0 fn log a ledger s /\ wf_function fn /\
  active_inst fn inst s /\ inst.inst_operands = [dop;rop;Lit 0w] /\
  u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = SUC s.vs_inst_idx ==>
  ricf_copy_coverage ctx0 fn log a ledger u
Proof
  strip_tac >> irule ricf_copy_coverage_next >> qexists_tac `s` >> simp[] >>
  rpt strip_tac >>
  `?bb. MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    EL s.vs_inst_idx bb.bb_instructions = inst` by
    (fs[active_inst_def] >> metis_tac[]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL b fn.fn_blocks)` by
    (conj_tac >> irule MEM_lookup_block >>
     fs[wf_function_def, fn_labels_def] >> simp[EL_MEM]) >>
  `bb = EL b fn.fn_blocks` by metis_tac[optionTheory.SOME_11] >>
  gvs[ricf_event_copy_def]
QED


Theorem ricf_copy_coverage_retained[local]:
  ricf_copy_coverage ctx0 fn log a ledger s /\ wf_function fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_logged_function_trace ctx0 fn log mid /\ b < LENGTH fn.fn_blocks /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL b fn.fn_blocks) /\
  (EL s.vs_inst_idx (EL b mid.fn_blocks).bb_instructions).inst_opcode = MCOPY /\
  u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = SUC s.vs_inst_idx ==>
  ricf_copy_coverage ctx0 fn log a ledger u
Proof
  strip_tac >> irule ricf_copy_coverage_next >> qexists_tac `s` >> simp[] >>
  qx_genl_tac [`round`,`cb`,`es`,`prefix`,`e`,`current`,`dst`,`sv`,`z`] >>
  strip_tac >> strip_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL cb fn.fn_blocks)` by
    (irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def] >> simp[EL_MEM]) >>
  `ALL_DISTINCT fn.fn_blocks` by
    (irule (ISPEC ``\bb:basic_block. bb.bb_label`` ALL_DISTINCT_MAP) >>
     fs[wf_function_def, fn_labels_def]) >>
  `cb = b` by metis_tac[ALL_DISTINCT_EL_IMP, optionTheory.SOME_11] >>
  drule_all ricf_call_located_event_erased_at_end >> gvs[ricf_event_copy_def]
QED

Theorem ricf_execution_point_copy_preserve[local]:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates
    sites maps targets stk PG G tn fn inst s t /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ wf_function fn /\
  active_inst fn inst s /\ inst.inst_opcode = MCOPY /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) /\
  (!history:(ricf_protection_event # call_frame list) list. ricf_copy_coverage
    (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions (readonly_mem_analyze C) fn)
    fn (log_of fn) a history s ==>
    ricf_copy_coverage
    (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions (readonly_mem_analyze C) fn)
    fn (log_of fn) a history (u with vs_inst_idx := SUC s.vs_inst_idx)) /\
  (!n B HP H certificates E.
    ricf_execution_invariant vs C D stk PG G tn fn inst s t
      n a U B HP H certificates E sites maps targets tn /\
    ricf_analyzed_origins vs C stk PG G tn fn inst s a U B certificates sites maps /\
    ricf_certificate_readonly vs C log_of stk PG G tn fn inst s U B certificates /\
    ricf_mapped_support a B E PG G sites ==>
    ?v. step_inst fuel Ct target t = OK v /\
      ricf_execution_invariant vs C D stk PG (step_prov PG G inst u)
        (step_taint inst s u tn) fn next
        (u with vs_inst_idx := SUC s.vs_inst_idx)
        (v with vs_inst_idx := SUC s.vs_inst_idx)
        n a U (occurrence_sites_step a B inst u) HP
        (occurrence_step a HP H inst u) certificates E sites maps targets
        (step_taint inst s u tn)) ==>
  ?v. step_inst fuel Ct target t = OK v /\
    ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates
      sites maps targets stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  qpat_x_assum `ricf_execution_point _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ricf_execution_point_def]) >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
  `ricf_analyzed_origins vs C stk PG G tn fn inst s a U B certificates sites maps /\
   ricf_certificate_readonly vs C log_of stk PG G tn fn inst s U B certificates` by
    (drule ricf_history_certificates_analyzed >>
     fs[ricf_analyzed_origins_def, ricf_history_certificates_def]) >>
  qpat_x_assum `!n B HP H certificates E. _`
    (qspecl_then [`n`,`B`,`HP`,`H`,`certificates`,`E`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `occurrence_sites_step a B inst u = B` by simp[occurrence_sites_step_def] >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    simp[is_terminator_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
    fs[wf_function_def, fn_inst_ids_distinct_def, fn_insts_def,
      fn_insts_blocks_flat, MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF] >>
  `ricf_history_certificates vs C log_of stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
    a U B history certificates` by
    (drule_all ricf_history_certificates_next >> simp[]) >>
  `ricf_analyzed_origins vs C stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
    a U B history sites maps` by
    (mp_tac (Q.INST [`ledger` |-> `history`] ricf_analyzed_origins_next) >>
     impl_tac >- simp[] >> simp[]) >>
  `ricf_mapped_support a B E PG (step_prov PG G inst u) sites` by
    (irule ricf_execution_mapped_support_ordinary >> simp[]) >>
  qexists_tac `v` >> simp[] >> pure_rewrite_tac[ricf_execution_point_def] >>
  qexistsl_tac [`n`,`B`,`HP`,`occurrence_step a HP H inst u`,
    `history`,`certificates`,`E`] >> fs[] >> first_x_assum irule >> simp[]
QED

Theorem ricf_execution_point_zero_copy:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates
    sites maps targets stk PG G tn fn inst s t /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ wf_function fn /\
  active_inst fn inst s /\ inst.inst_opcode = MCOPY /\
  inst.inst_operands = [dop;rop;Lit 0w] /\ inst.inst_outputs = [] /\
  step_inst fuel C inst s = OK u /\
  nop.inst_opcode = NOP /\ nop.inst_operands = [] /\ nop.inst_outputs = [] /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  step_inst fuel Ct nop t = OK t /\
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates
    sites maps targets stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next
    (u with vs_inst_idx := SUC s.vs_inst_idx)
    (t with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `u.vs_current_bb = s.vs_current_bb` by
    (drule step_preserves_control_flow >> simp[is_terminator_def]) >>
  `step_inst fuel Ct nop t = OK t` by
    simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  mp_tac (Q.INST [`target` |-> `nop`] ricf_execution_point_copy_preserve) >>
  (impl_tac >-
    (simp[] >> conj_tac
     >- (rpt strip_tac >> irule ricf_copy_coverage_zero >>
         simp[] >> qexistsl_tac [`dop`,`inst`,`rop`,`s`] >> simp[]) >>
     rpt gen_tac >> strip_tac >>
     mp_tac (Q.INST [`ledger` |-> `certificates`, `rt` |-> `tn`]
       ricf_execution_zero_copy_next) >> simp[])) >>
  simp[]
QED

Theorem ricf_execution_point_retained_copy:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates
    sites maps targets stk PG G tn fn inst s t /\
  o1_ctx_shape C /\ o1_fn_shape C fn /\ wf_ssa fn /\
  ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions) /\
  EVERY wf_ssa C.ctx_functions /\ EVERY ricf_param_order_ok C.ctx_functions /\
  EVERY wf_function C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = MCOPY /\ step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) /\
  ricf_logged_function_trace
    (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions (readonly_mem_analyze C) fn)
    fn (log_of fn) mid /\ b < LENGTH fn.fn_blocks /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL b fn.fn_blocks) /\
  (EL s.vs_inst_idx (EL b mid.fn_blocks).bb_instructions).inst_opcode = MCOPY ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates
      sites maps targets stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `wf_function fn` by fs[o1_fn_shape_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
    fs[wf_function_def, fn_inst_ids_distinct_def, fn_insts_def,
      fn_insts_blocks_flat, MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF] >>
  `u.vs_current_bb = s.vs_current_bb` by
    (drule step_preserves_control_flow >> simp[is_terminator_def]) >>
  irule ricf_execution_point_copy_preserve >> simp[] >> conj_tac
  >- (rpt strip_tac >> irule ricf_copy_coverage_retained >>
      simp[] >> qexistsl_tac [`b`,`mid`,`s`] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `MEM inst.inst_opcode [MCOPY]` by simp[] >>
  drule_all ricf_execution_retained_copy_next >>
  disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]
QED

Theorem ricf_execution_point_positive_copy:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates
    sites maps targets stk PG G tn fn inst s t /\
  o1_fn_shape C fn /\ wf_ssa fn /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ mem_inv raw_mem_ok C vs /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ptr_discipline lo C vs /\ ~in_revert_forward fn s /\
  ricf_located_event
    (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions (readonly_mem_analyze C) fn)
    fn (log_of fn) round b es prefix e current /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL b fn.fn_blocks) /\
  s.vs_inst_idx = e.rfe_index /\ inst = ricf_event_copy e (EL b fn.fn_blocks) /\
  inst.inst_operands = [Var dst;Var sv;Lit z] /\ 0 < w2n z /\
  active_inst fn inst s /\ step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) /\
  nop.inst_opcode = NOP /\ nop.inst_operands = [] /\ nop.inst_outputs = [] ==>
  step_inst fuel Ct nop t = OK t /\
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates
    sites maps targets stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next
    (u with vs_inst_idx := SUC s.vs_inst_idx)
    (t with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  qpat_x_assum `ricf_execution_point _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ricf_execution_point_def]) >>
  `wf_function fn /\ ssa_form fn /\ fn_inst_wf fn` by
    fs[o1_fn_shape_def, wf_ssa_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
    fs[wf_function_def, fn_inst_ids_distinct_def, fn_insts_def,
      fn_insts_blocks_flat, MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF] >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[occ_frame_reachable_projection] >>
  `lo <= vs.vs_alloca_next /\ access_ok lo G fn inst s` by
    (qpat_assum `ptr_discipline lo C vs` mp_tac >>
     qpat_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[ptr_discipline_def] >> metis_tac[]) >>
  `occurrence_natural_geometry lo a U B stk s` by
    (drule occ_frame_reachable_geometry >> simp[]) >>
  `raw_reachable vs C fn inst s` by
    (irule ld_frame_raw_reachable >> simp[] >>
     fs[EVERY_MEM] >> metis_tac[lookup_function_MEM]) >>
  `s.vs_alloca_next <= dimword (:256)` by
    (qpat_assum `mem_inv raw_mem_ok C vs` mp_tac >>
     qpat_assum `raw_reachable vs C fn inst s` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[mem_inv_raw_reachable, raw_mem_ok_def] >> metis_tac[LESS_IMP_LESS_OR_EQ]) >>
  `b < LENGTH fn.fn_blocks /\ inst.inst_opcode = MCOPY` by
    (drule_all ricf_located_event_source_block >> strip_tac >>
     drule ricf_located_event_validation >> strip_tac >>
     drule ricf_event_copy_shape >> strip_tac >>
     fs[ricf_event_copy_def, ricf_block_edit_def, LIST_REL_EL_EQN] >>
     metis_tac[ricf_inst_edit_def]) >>
  `occurrence_sites_step a B inst u = B` by simp[occurrence_sites_step_def] >>
  mp_tac (Q.INST [`ledger` |-> `certificates`, `rt` |-> `tn`,
    `ctx0` |-> `icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
      (readonly_mem_analyze C) fn`, `log` |-> `log_of (fn:ir_function)`]
    ricf_execution_positive_copy_next) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  qpat_x_assum `ledger' = _` SUBST_ALL_TAC >>
  `0 < p.rpe_size /\
   FLOOKUP B p.rpe_dst = SOME (p.rpe_db,p.rpe_size) /\
   FLOOKUP B p.rpe_src = SOME (p.rpe_sb,p.rpe_size)` by
    (qpat_assum `ricf_execution_invariant _ _ _ _ _ _ _ _ next _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       mp_tac >> qpat_assum `occurrence_sites_step _ _ _ _ = _` mp_tac >>
     qpat_assum `inst = ricf_event_copy e (EL b fn.fn_blocks)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def,
       ricf_phase_entry_def] >> metis_tac[]) >>
  `FST p.rpe_dst = a` by
    (qpat_assum `ricf_history_origin _ _ _ _ _ _ _ _ _`
       (mp_tac o PURE_REWRITE_RULE [ricf_history_origin_def, ricf_source_copy_payload_def]) >>
     qpat_assum `p.rpe_owner = a` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     rpt strip_tac >> gvs[]) >>
  `ricf_history_certificates vs C log_of stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
    a U B ((p,[])::history) ((p,[])::certificates)` by
    (mp_tac (Q.INST [`p` |-> `p`] ricf_history_certificates_activate) >>
     impl_tac >- gvs[] >> gvs[]) >>
  `ricf_chosen_support vs C log_of a fn B (E UNION {p.rpe_dst})` by
    (mp_tac (Q.INST [`p` |-> `p`] ricf_chosen_support_activate) >>
     (impl_tac >- gvs[]) >> qpat_assum `p.rpe_fn = fn` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `p.rpe_dst INSERT E = E UNION {p.rpe_dst}` by SET_TAC[] >> metis_tac[]) >>
  `ricf_analyzed_origins vs C stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
    a U B history sites maps` by
    (mp_tac (Q.INST [`ledger` |-> `history`] ricf_analyzed_origins_next) >>
     impl_tac >- simp[is_terminator_def] >> simp[]) >>
  `ricf_analyzed_origins vs C stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
    a U B ((p,[])::history) sites maps` by
    (fs[ricf_analyzed_origins_def] >> irule ricf_chosen_ledger_analyzed >>
     qexists_tac `log_of` >>
     gvs[ricf_history_certificates_def]) >>
  `ricf_mapped_support a B (E UNION {p.rpe_dst}) PG
    (step_prov PG G inst u) sites` by
    (irule ricf_execution_mapped_support_ordinary >> simp[] >>
     Cases_on `p.rpe_dst` >> fs[] >>
     irule ricf_mapped_support_activate >> simp[]) >>
  `u.vs_current_bb = s.vs_current_bb` by metis_tac[step_preserves_control_flow, is_terminator_def] >>
  `ricf_copy_coverage
    (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions (readonly_mem_analyze C) fn)
    fn (log_of fn) a ((p,[])::history) (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (mp_tac (Q.INST [
       `ctx0` |-> `icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
         (readonly_mem_analyze C) fn`, `log` |-> `log_of (fn:ir_function)`,
       `ledger` |-> `history`, `bb` |-> `EL b fn.fn_blocks`,
       `u` |-> `u with vs_inst_idx := SUC s.vs_inst_idx`]
       (INST_TYPE [alpha |-> ``:call_frame``] ricf_copy_coverage_activate)) >>
     (impl_tac >-
     (simp[] >> qx_genl_tac [`round'`,`cb`,`es'`,`prefix'`,`other`,`current'`] >>
     strip_tac >>
     `lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL cb fn.fn_blocks)` by
       (irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def] >> simp[EL_MEM]) >>
     `ALL_DISTINCT fn.fn_blocks` by
       (irule (ISPEC ``\bb:basic_block. bb.bb_label`` ALL_DISTINCT_MAP) >>
        fs[wf_function_def, fn_labels_def]) >>
     `cb = b` by metis_tac[ALL_DISTINCT_EL_IMP, optionTheory.SOME_11] >>
     fs[] >> irule ricf_located_event_position_unique >> metis_tac[])) >> simp[]) >>
  `{id | id IN E UNION {p.rpe_dst} /\ FST id <> a} = E0` by
    (qpat_assum `{id | id IN E /\ FST id <> a} = E0` mp_tac >>
     qpat_assum `FST p.rpe_dst = a` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[EXTENSION] >> metis_tac[]) >>
  simp[] >> pure_rewrite_tac[ricf_execution_point_def] >>
  qexistsl_tac [`n`,`B`,`HP`,`occurrence_step a HP H inst u`,
    `(p,[])::history`,`(p,[])::certificates`,`E UNION {p.rpe_dst}`] >>
  gvs[]
QED

Theorem ricf_execution_point_copy:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates
    sites maps targets stk PG G tn fn inst s t /\
  o1_ctx_shape C /\ o1_fn_shape C fn /\ wf_ssa fn /\
  ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions) /\
  EVERY wf_ssa C.ctx_functions /\ EVERY ricf_param_order_ok C.ctx_functions /\
  EVERY wf_function C.ctx_functions /\ EVERY fn_inst_wf C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = MCOPY /\ step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) /\
  ricf_logged_function_trace
    (icf_build_ctx (icf_fn_meta_of C) C.ctx_functions (readonly_mem_analyze C) fn)
    fn (log_of fn) mid /\ b < LENGTH fn.fn_blocks /\
  s.vs_inst_idx < LENGTH (EL b fn.fn_blocks).bb_instructions /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL b fn.fn_blocks) /\
  inst = EL s.vs_inst_idx (EL b fn.fn_blocks).bb_instructions /\
  target = EL s.vs_inst_idx (EL b mid.fn_blocks).bb_instructions ==>
  ?v. step_inst fuel Ct target t = OK v /\
    ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates
      sites maps targets stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `wf_function fn /\ fn_inst_wf fn /\ ssa_form fn` by
    fs[o1_fn_shape_def, wf_ssa_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
    fs[wf_function_def, fn_inst_ids_distinct_def, fn_insts_def,
      fn_insts_blocks_flat, MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF] >>
  Cases_on `target.inst_opcode = MCOPY`
  >- (`ricf_function_edit fn mid` by
        metis_tac[ricf_logged_function_trace_erases, ricf_function_trace_edit] >>
      `target = inst` by
        (fs[ricf_function_edit_def, ricf_block_edit_def, LIST_REL_EL_EQN] >>
         metis_tac[ricf_inst_edit_def]) >>
      qpat_x_assum `target = inst` SUBST_ALL_TAC >>
      mp_tac (Q.INST [`lo` |-> `lo`, `mid` |-> `mid`, `b` |-> `b`]
        ricf_execution_point_retained_copy) >>
      (impl_tac >- gvs[]) >> simp[]) >>
  mp_tac (Q.INST [`ctx0` |-> `icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
    (readonly_mem_analyze C) fn`, `log` |-> `log_of (fn:ir_function)`,
    `i` |-> `s.vs_inst_idx`] ricf_execution_logged_erased_copy) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `inst_wf inst` by
    (fs[fn_inst_wf_def, active_inst_def] >> metis_tac[MEM_EL]) >>
  `inst.inst_outputs = []` by gvs[inst_wf_def] >>
  Cases_on `w2n z = 0`
  >- (`z = 0w` by metis_tac[w2n_eq_0] >>
      qexists_tac `t` >>
      mp_tac (Q.INST [`nop` |-> `target`, `dop` |-> `Var dst`,
        `rop` |-> `Var sv`] ricf_execution_point_zero_copy) >>
      (impl_tac >- simp[]) >> simp[]) >>
  `0 < w2n z` by decide_tac >> qexists_tac `t` >>
  mp_tac (Q.INST [`nop` |-> `target`] ricf_execution_point_positive_copy) >>
  (impl_tac >- gvs[]) >> simp[]
QED
