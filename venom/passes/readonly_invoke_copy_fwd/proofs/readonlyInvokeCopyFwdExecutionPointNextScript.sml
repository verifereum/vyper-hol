(* Ordinary opcode kernels supply the relational state transition; this joins
   their actual source step with every retained history and coverage channel. *)
Theory readonlyInvokeCopyFwdExecutionPointNext
Ancestors
  readonlyInvokeCopyFwdExecutionSteps readonlyInvokeCopyFwdExecutionEffects
  readonlyInvokeCopyFwdExecutionAssertions
  readonlyInvokeCopyFwdExecutionCoverage readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdExecutionHistory readonlyInvokeCopyFwdExecutionHistoryLifecycle
  readonlyInvokeCopyFwdExecutionMapCoverage readonlyInvokeCopyFwdAnalyzedOrigins
  readonlyInvokeCopyFwdAnalyzedLifecycle readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdHistoryPhase readonlyInvokeCopyFwdMapCoverage
  invokeCopyFwdCommonDefs readonlyMemoryArgsDefs o1PassContract
  o1LowerDloadOccurrence o1LowerDloadGhost ptrDiscipline
  contextCodegenRel venomWf venomWfProps venomInstProofs venomExecSemantics
  venomState venomInst finite_map list pred_set arithmetic

Theorem ricf_execution_point_ordinary:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates
    sites maps targets stk PG G tn fn inst s t /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ wf_function fn /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> ALLOCA /\
  inst.inst_opcode <> DALLOCA /\ inst.inst_opcode <> MCOPY /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) /\
  (!n B HP H certificates E.
    ricf_execution_invariant vs C D stk PG G tn fn inst s t
      n a U B HP H certificates E sites maps targets tn /\
    ricf_analyzed_origins vs C stk PG G tn fn inst s a U B certificates sites maps /\
    ricf_certificate_readonly vs C log_of stk PG G tn fn inst s U B certificates /\
    ricf_mapped_support a B E PG G sites ==>
    ?v. step_inst fuel Ct inst t = OK v /\
      ricf_execution_invariant vs C D stk PG (step_prov PG G inst u)
        (step_taint inst s u tn) fn next
        (u with vs_inst_idx := SUC s.vs_inst_idx)
        (v with vs_inst_idx := SUC s.vs_inst_idx)
        n a U (occurrence_sites_step a B inst u) HP
        (occurrence_step a HP H inst u) certificates E sites maps targets
        (step_taint inst s u tn)) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
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
  `u.vs_current_bb = s.vs_current_bb` by metis_tac[step_preserves_control_flow] >>
  qexists_tac `v` >> simp[] >>
  pure_rewrite_tac[ricf_execution_point_def] >>
  qexistsl_tac [`n`,`B`,`HP`,`occurrence_step a HP H inst u`,
    `history`,`certificates`,`E`] >>
  fs[] >>
  mp_tac (Q.INST [`ctx0` |-> `icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
      (readonly_mem_analyze C) fn`, `log` |-> `log_of fn`, `ledger` |-> `history`,
    `u` |-> `u with vs_inst_idx := SUC s.vs_inst_idx`]
    (INST_TYPE [alpha |-> ``:call_frame``] ricf_copy_coverage_ordinary)) >> simp[]
QED

Theorem ricf_execution_point_storage_store:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates
    sites maps targets stk PG G tn fn inst s t /\
  o1_fn_shape C fn /\ wf_ssa fn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\
  MEM inst.inst_opcode [SSTORE;TSTORE] /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates
      sites maps targets stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `wf_function fn /\ ~is_terminator inst.inst_opcode /\
   inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> ALLOCA /\
   inst.inst_opcode <> DALLOCA /\ inst.inst_opcode <> MCOPY` by
    fs[o1_fn_shape_def, MEM, is_terminator_def] >>
  irule ricf_execution_point_ordinary >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_all ricf_execution_storage_store_next >>
  disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]
QED

Theorem ricf_execution_point_assert:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates
    sites maps targets stk PG G tn fn inst s t /\
  o1_fn_shape C fn /\ wf_ssa fn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\
  MEM inst.inst_opcode [ASSERT;ASSERT_UNREACHABLE] /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates
      sites maps targets stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `wf_function fn /\ ~is_terminator inst.inst_opcode /\
   inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> ALLOCA /\
   inst.inst_opcode <> DALLOCA /\ inst.inst_opcode <> MCOPY` by
    fs[o1_fn_shape_def, MEM, is_terminator_def] >>
  irule ricf_execution_point_ordinary >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_all ricf_execution_assert_next >>
  disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]
QED
