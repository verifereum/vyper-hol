(* Concrete local and terminal adapters for the runner's point relation. *)
Theory readonlyInvokeCopyFwdExecutionPointLocal
Ancestors
  readonlyInvokeCopyFwdExecutionSteps readonlyInvokeCopyFwdExecutionPointNext
  readonlyInvokeCopyFwdExecutionReturnBridge readonlyInvokeCopyFwdExecutionCoverage
  readonlyInvokeCopyFwdExecutionLocal readonlyInvokeCopyFwdExecutionControl
  readonlyInvokeCopyFwdExecutionAllocation
  readonlyInvokeCopyFwdExecutionOrdinary
  readonlyInvokeCopyFwdExecutionBlock
  readonlyInvokeCopyFwdExecutionBoundary readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdOpaque readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdPlan
  readonlyInvokeCopyFwdMapCoverage readonlyInvokeCopyFwdAnalyzedOrigins
  readonlyInvokeCopyFwdAnalyzedLifecycle
  readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdExecutionHistoryLifecycle
  readonlyInvokeCopyFwdExecutionMapCoverage
  readonlyInvokeCopyFwdHistoryPhase readonlyInvokeCopyFwdExecutionHistory
  invokeCopyFwdCommonDefs readonlyMemoryArgsDefs o1PassContract
  reachableFnSim taintAgree contextCodegenRel venomInstProofs
  o1LowerDloadOccurrence o1LowerDloadGhost occurrenceGeometry ptrDiscipline codegenRel
  venomExecProps venomExecProofs venomExecSemantics venomWf venomWfProps venomInst venomState
  passSimulationDefs list rich_list finite_map arithmetic

Theorem ricf_execution_point_ret:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
    stk PG G tn fn inst s t /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\ active_inst (mid_of fn) inst t /\
  inst.inst_opcode = RET /\ step_inst fuel C inst s = IntRet ret se ==>
  step_inst fuel Ct inst t = IntRet ret t /\
  ricf_execution_return vs C Ct mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets
    stk PG G tn fn ret se t
Proof
  rw[ricf_execution_point_def] >>
  drule_all ricf_execution_ret_result >>
  disch_then (qspec_then `Ct` strip_assume_tac) >> gvs[]
QED

Theorem ricf_execution_point_nop:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
    stk PG G tn fn inst s t /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ wf_function fn /\
  active_inst fn inst s /\ inst.inst_opcode = NOP /\ inst.inst_outputs = [] /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
      stk PG (step_prov PG G inst u) (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> irule ricf_execution_point_ordinary >>
  simp[is_terminator_def] >> rpt gen_tac >> strip_tac >>
  drule_all ricf_execution_nop_next >>
  disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]
QED

Theorem ricf_execution_point_param:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
    stk PG G tn fn inst s t /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ wf_function fn /\ ssa_form fn /\
  active_inst fn inst s /\ MEM inst.inst_opcode [PARAM; RETPC_PARAM] /\
  inst.inst_operands = [Lit idx] /\ inst.inst_outputs = [out] /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
      stk PG (step_prov PG G inst u) (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
   inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> DALLOCA /\
   inst.inst_opcode <> MCOPY` by fs[MEM, is_terminator_def] >>
  irule ricf_execution_point_ordinary >> simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = PARAM`
  >- (drule_all ricf_execution_param_next >>
      disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  `inst.inst_opcode = RETPC_PARAM` by fs[MEM] >>
  drule_all ricf_execution_retpc_next >>
  disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]
QED

Theorem ricf_execution_point_scalar:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
    stk PG G tn fn inst s t /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ wf_function fn /\
  ssa_form fn /\ opaque_use_ok fn /\ ptr_discipline lo C vs /\
  active_inst fn inst s /\
  MEM inst.inst_opcode [ISZERO;NOT;MUL;Div;Mod;SDIV;SMOD;Exp;
    SLT;SGT;AND;OR;XOR;ADDMOD;MULMOD] /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
      stk PG (step_prov PG G inst u) (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
   inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> DALLOCA /\
   inst.inst_opcode <> MCOPY` by fs[MEM, is_terminator_def] >>
  irule ricf_execution_point_ordinary >> simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `MEM inst.inst_opcode [ISZERO;NOT]`
  >- (drule_all ricf_execution_unary_next >>
      disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  Cases_on `MEM inst.inst_opcode [ADDMOD;MULMOD]`
  >- (drule_all ricf_execution_ternary_next >>
      disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  `MEM inst.inst_opcode [MUL;Div;Mod;SDIV;SMOD;Exp;SLT;SGT;AND;OR;XOR]` by fs[MEM] >>
  drule_all ricf_execution_binary_next >>
  disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]
QED

Theorem ricf_execution_point_alloca:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
    stk PG G tn fn inst s t /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ wf_function fn /\
  active_inst fn inst s /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit amount] /\ inst.inst_outputs = [out] /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
      stk PG (step_prov PG G inst u) (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  qpat_x_assum `ricf_execution_point _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ricf_execution_point_def]) >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
  `occurrence_natural_geometry 0 a U B stk s` by
    (drule occ_frame_reachable_geometry >>
     disch_then (qspec_then `0` mp_tac) >> simp[]) >>
  `occurrence_allocas_ok B a s` by
    (drule occ_frame_reachable_annotation >> simp[occurrence_annotation_ok_def]) >>
  `?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C D stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B inst u) HP
      (occurrence_step a HP H inst u) certificates E sites maps targets
      (step_taint inst s u tn)` by
    (Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
     >- (drule_all ricf_execution_fresh_alloca_next >>
         disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
     rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME pair` >>
     Cases_on `pair` >> drule_all ricf_execution_cached_alloca_next >>
     disch_then (qspec_then `Ct` strip_assume_tac) >> metis_tac[]) >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    simp[is_terminator_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
    fs[wf_function_def, fn_inst_ids_distinct_def, fn_insts_def,
       fn_insts_blocks_flat, MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF] >>
  `ricf_history_certificates vs C log_of stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
    a U (occurrence_sites_step a B inst u) history certificates` by
    (drule_all ricf_history_certificates_next >> simp[]) >>
  `ricf_analyzed_origins vs C stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
    a U (occurrence_sites_step a B inst u) history sites maps` by
    (drule_all ricf_analyzed_origins_next >> simp[]) >>
  `ricf_mapped_support a (occurrence_sites_step a B inst u) E PG
    (step_prov PG G inst u) sites` by
    (irule ricf_execution_mapped_support_alloca >> metis_tac[]) >>
  `ricf_chosen_support vs C log_of a fn (occurrence_sites_step a B inst u) E` by
    (irule ricf_chosen_support_sites_step >> metis_tac[]) >>
  `DRESTRICT (occurrence_sites_step a B inst u) {id | FST id <> a} = B0` by
    (qpat_x_assum `DRESTRICT B _ = B0` (SUBST1_TAC o SYM) >>
     simp[fmap_eq_flookup, FLOOKUP_DRESTRICT] >> Cases >>
     simp[occurrence_sites_step_other_owner]) >>
  `u.vs_current_bb = s.vs_current_bb` by metis_tac[step_preserves_control_flow] >>
  qexists_tac `v` >> simp[] >> pure_rewrite_tac[ricf_execution_point_def] >>
  qexistsl_tac [`n`,`occurrence_sites_step a B inst u`,`HP`,
    `occurrence_step a HP H inst u`,`history`,`certificates`,`E`] >>
  simp[] >>
  mp_tac (Q.INST [`ctx0` |-> `icf_build_ctx (icf_fn_meta_of C) C.ctx_functions
      (readonly_mem_analyze C) fn`, `fn` |-> `fn`, `log` |-> `log_of (fn : ir_function)`,
    `ledger` |-> `history`, `s` |-> `s`, `inst` |-> `inst`,
    `u` |-> `u with vs_inst_idx := SUC s.vs_inst_idx`]
    (INST_TYPE [alpha |-> ``:call_frame``] ricf_copy_coverage_ordinary)) >> simp[]
QED

Theorem ricf_execution_point_jmp:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
    stk PG G tn fn inst s t /\
  o1_fn_shape C fn /\ ricf_function_edit fn (mid_of fn) /\
  inst.inst_opcode = JMP /\ inst.inst_operands = [Label lbl] /\
  active_inst fn inst s /\ step_inst fuel C inst s = OK u /\ ~u.vs_halted ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    block_step_rel D vs C
      (ricf_execution_boundary vs C mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
      (ricf_execution_return vs C Ct mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
      stk PG fn (step_inst fuel C inst s) (step_inst fuel Ct inst t)
Proof
  strip_tac >>
  qpat_x_assum `ricf_execution_point _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ricf_execution_point_def]) >>
  `retpc_shape_ok fn /\ fn_inst_wf fn` by
    fs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def] >>
  `u = jump_to lbl s /\ step_inst fuel Ct inst t = OK (jump_to lbl t)` by
    gvs[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  `s.vs_halted = t.vs_halted` by
    (fs[ricf_execution_invariant_def, ricf_opaque_frame_agree_def,
        ricf_frame_agree_def] >> drule taint_agree_frame >>
     disch_then (mp_tac o Q.AP_TERM `\st. st.vs_halted`) >>
     simp[ricf_opaque_view_def]) >>
  `~(jump_to lbl t).vs_halted` by fs[jump_to_def] >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
  `block_reach vs C stk PG (entry_prov fn u G) (entry_taint_vars fn u tn) fn u` by
    metis_tac[frame_reachable_block_reach] >>
  `ricf_execution_boundary vs C mid_of log_of D a U B0 E0 outer_history outer_certificates
    sites maps targets stk PG (entry_prov fn u G) (entry_taint_vars fn u tn)
    fn u (jump_to lbl t)` by
    (rewrite_tac[ricf_execution_boundary_def] >>
     qx_gen_tac `s1` >> qx_gen_tac `next` >> strip_tac >>
     `ricf_history_certificates vs C log_of stk PG (entry_prov fn u G)
       (entry_taint_vars fn u tn) fn next s1 a U B
       (FILTER (\entry. SND entry <> []) history)
       (FILTER (\entry. SND entry <> []) certificates)` by
       (drule_all ricf_history_certificates_block >> simp[]) >>
     `ricf_analyzed_origins vs C stk PG (entry_prov fn u G)
       (entry_taint_vars fn u tn) fn next s1 a U B
       (FILTER (\entry. SND entry <> []) history) sites maps` by
       (simp[ricf_analyzed_origins_def] >> rpt conj_tac
        >- (mp_tac (Q.INST [`ledger` |-> `history`, `u` |-> `u`,
              `s1` |-> `s1`, `inst` |-> `inst`, `fuel` |-> `fuel`]
              ricf_analyzed_ledger_block) >>
            impl_tac >- (fs[ricf_analyzed_origins_def] >> metis_tac[]) >> simp[])
        >- (irule ricf_analyzed_map_origins_block >>
            fs[ricf_analyzed_origins_def] >> metis_tac[]) >>
        irule ricf_analyzed_saved_map_origins_block >>
        fs[ricf_analyzed_origins_def] >> metis_tac[]) >>
     `ricf_mapped_support a B E PG (entry_prov fn u G) sites` by
       metis_tac[ricf_execution_mapped_support_entry] >>
     drule_all ricf_execution_jump_block >>
     disch_then (qspec_then `Ct` strip_assume_tac) >>
     qexistsl_tac [`t1`,`n`,`B`,`HP`,`entry_prov fn u H`,
       `FILTER (\entry. SND entry <> []) history`,
       `FILTER (\entry. SND entry <> []) certificates`,`E`] >>
     simp[rich_listTheory.FILTER_FILTER] >> gvs[] >>
     irule ricf_function_edit_enters_block >> qexists_tac `fn` >> simp[]) >>
  `~s.vs_halted /\ ~t.vs_halted` by fs[jump_to_def] >>
  qexists_tac `jump_to lbl t` >> simp[block_step_rel_def] >>
  qexistsl_tac [`entry_prov fn u G`,`entry_taint_vars fn u tn`] >> gvs[]
QED

Theorem ricf_execution_point_jnz:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
    stk PG G tn fn inst s t /\
  ptr_discipline lo C vs /\ o1_fn_shape C fn /\
  ricf_function_edit fn (mid_of fn) /\
  inst.inst_opcode = JNZ /\
  inst.inst_operands = [cond; Label if_nonzero; Label if_zero] /\
  active_inst fn inst s /\ step_inst fuel C inst s = OK u /\ ~u.vs_halted ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    block_step_rel D vs C
      (ricf_execution_boundary vs C mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
      (ricf_execution_return vs C Ct mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
      stk PG fn (step_inst fuel C inst s) (step_inst fuel Ct inst t)
Proof
  strip_tac >>
  qpat_x_assum `ricf_execution_point _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ricf_execution_point_def]) >>
  `opaque_use_ok fn` by fs[o1_fn_shape_def, unitShapeDefsTheory.fn_shape_ok_def] >>
  Cases_on `eval_operand cond s`
  >- gvs[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  rename1 `eval_operand cond s = SOME value` >>
  `eval_operand cond t = SOME value` by
    (irule ricf_execution_jnz_condition >> metis_tac[MEM]) >>
  qabbrev_tac `lbl = if value <> 0w then if_nonzero else if_zero` >>
  `u = jump_to lbl s /\ step_inst fuel Ct inst t = OK (jump_to lbl t)` by
    (Cases_on `value = 0w` >>
     gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, Abbr `lbl`]) >>
  `s.vs_halted = t.vs_halted` by
    (fs[ricf_execution_invariant_def, ricf_opaque_frame_agree_def,
        ricf_frame_agree_def] >> drule taint_agree_frame >>
     disch_then (mp_tac o Q.AP_TERM `\st. st.vs_halted`) >>
     simp[ricf_opaque_view_def]) >>
  `~(jump_to lbl t).vs_halted` by fs[jump_to_def] >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
  `block_reach vs C stk PG (entry_prov fn u G) (entry_taint_vars fn u tn) fn u` by
    metis_tac[frame_reachable_block_reach] >>
  `ricf_execution_boundary vs C mid_of log_of D a U B0 E0 outer_history outer_certificates
    sites maps targets stk PG (entry_prov fn u G) (entry_taint_vars fn u tn)
    fn u (jump_to lbl t)` by
    (rewrite_tac[ricf_execution_boundary_def] >>
     qx_gen_tac `s1` >> qx_gen_tac `next` >> strip_tac >>
     `ricf_history_certificates vs C log_of stk PG (entry_prov fn u G)
       (entry_taint_vars fn u tn) fn next s1 a U B
       (FILTER (\entry. SND entry <> []) history)
       (FILTER (\entry. SND entry <> []) certificates)` by
       (drule_all ricf_history_certificates_block >> simp[]) >>
     `ricf_analyzed_origins vs C stk PG (entry_prov fn u G)
       (entry_taint_vars fn u tn) fn next s1 a U B
       (FILTER (\entry. SND entry <> []) history) sites maps` by
       (simp[ricf_analyzed_origins_def] >> rpt conj_tac
        >- (mp_tac (Q.INST [`ledger` |-> `history`, `u` |-> `u`,
              `s1` |-> `s1`, `inst` |-> `inst`, `fuel` |-> `fuel`]
              ricf_analyzed_ledger_block) >>
            impl_tac >- (fs[ricf_analyzed_origins_def] >> metis_tac[]) >> simp[])
        >- (irule ricf_analyzed_map_origins_block >>
            fs[ricf_analyzed_origins_def] >> metis_tac[]) >>
        irule ricf_analyzed_saved_map_origins_block >>
        fs[ricf_analyzed_origins_def] >> metis_tac[]) >>
     `ricf_mapped_support a B E PG (entry_prov fn u G) sites` by
       metis_tac[ricf_execution_mapped_support_entry] >>
     drule_all ricf_execution_jnz_block >>
     disch_then (qspec_then `Ct` strip_assume_tac) >>
     qexistsl_tac [`t1`,`n`,`B`,`HP`,`entry_prov fn u H`,
       `FILTER (\entry. SND entry <> []) history`,
       `FILTER (\entry. SND entry <> []) certificates`,`E`] >>
     simp[rich_listTheory.FILTER_FILTER] >> gvs[] >>
     irule ricf_function_edit_enters_block >> qexists_tac `fn` >> simp[]) >>
  `~s.vs_halted /\ ~t.vs_halted` by fs[jump_to_def] >>
  qexists_tac `jump_to lbl t` >> simp[block_step_rel_def] >>
  qexistsl_tac [`entry_prov fn u G`,`entry_taint_vars fn u tn`] >> gvs[]
QED

Theorem ricf_execution_point_ret_step:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
    stk PG G tn fn inst s t /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\ active_inst (mid_of fn) inst t /\
  inst.inst_opcode = RET /\ step_inst fuel C inst s = IntRet ret se ==>
  block_step_rel D vs C
    (ricf_execution_boundary vs C mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
    (ricf_execution_return vs C Ct mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
    stk PG fn (step_inst fuel C inst s) (step_inst fuel Ct inst t)
Proof
  strip_tac >> drule_all ricf_execution_point_ret >>
  disch_then (qspec_then `Ct` strip_assume_tac) >>
  simp[block_step_rel_def, fn_run_rel_def] >> metis_tac[]
QED

Theorem ricf_execution_point_stop_sink:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
    stk PG G tn fn inst s t /\
  taint_within D C vs /\ active_inst fn inst s /\
  MEM inst.inst_opcode [STOP; SINK] /\ step_inst fuel C inst s = Halt se ==>
  block_step_rel D vs C R Rret stk PG fn
    (step_inst fuel C inst s) (step_inst fuel Ct inst t)
Proof
  strip_tac >>
  qpat_x_assum `ricf_execution_point _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ricf_execution_point_def]) >>
  drule_all ricf_execution_stop_sink >>
  disch_then (qspec_then `Ct` strip_assume_tac) >>
  simp[block_step_rel_def, fn_run_rel_def]
QED

Theorem ricf_execution_point_revert:
  ricf_execution_point vs C log_of D a U B0 E0 outer_history outer_certificates sites maps targets
    stk PG G tn fn inst s t /\
  inst.inst_opcode = REVERT /\ inst.inst_operands = [addr;sz] /\
  step_inst fuel C inst s = Abort Revert_abort se ==>
  block_step_rel D vs C R Rret stk PG fn
    (step_inst fuel C inst s) (step_inst fuel Ct inst t)
Proof
  rw[ricf_execution_point_def] >> drule_all ricf_execution_revert >>
  disch_then (qspec_then `Ct` strip_assume_tac) >>
  simp[block_step_rel_def, fn_run_rel_def]
QED

