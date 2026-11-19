Theory callGuardGasLinkProof
Ancestors
  e2eRequestCutDefs e2eDefs e2eEntry e2eProducers e2eCorrectness
  callRawVariant lowerDloadDefs loweringShapeSource vyperLoweringCorrect
  asmOptimizer o1PassContract o1PipelineCorrect venomState venomLayout
  o1PipelineCompose unitMemInv unitTransformDefs ptrDiscipline contextRawReachable
  e2eComposition sourceUnitExecution vyperInterpreter runtimeLabelReadiness
  gasMaskProjection gasSummary gasEvents gasExplicitSites o1SafeUpto
  codegenSymRel asmFrameRel oracleExecProps venomExecSemantics venomInst
  words arithmetic list sorting
Libs
  stepInstBaseLib

Theorem guard_runtime_phases:
  fin IN accepted_finalizers /\
  compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) ==>
  ?rpolicy unit out prog prog' cp.
    resolve_o1_policy policy = SOME rpolicy /\
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    fin rpolicy prog = SOME prog' /\ runtime_bc = assemble prog'
Proof
  simp[accepted_finalizers_def] >> strip_tac >> gvs[]
  >- (drule compile_vyper_runtime_phases >>
      disch_then (qx_choosel_then [`rp`, `cu`, `po`, `p`, `plan`] strip_assume_tac) >>
      qexistsl_tac [`rp`, `cu`, `po`, `p`, `plan`] >> simp[]) >>
  drule compile_vyper_runtime_phases_asm_opt >>
  disch_then (qx_choosel_then [`rp`, `cu`, `po`, `p`, `p'`, `plan`] strip_assume_tac) >>
  qexistsl_tac [`rp`, `cu`, `po`, `p`, `p'`, `plan`] >> simp[]
QED

Theorem guard_selected_raw_inputs[local]:
  vyper_call_staging fin policy tops (assemble prog') am tx ret es /\
  vs0 = opt_entry_state prog prog' cplan es /\ txp = tx with code := vs0.vs_code /\
  code_layout_valid vs0 /\ raw_variant fmp vs vs0 ==>
  source_typing_ok tops am txp /\ source_deployment_rel tops am txp /\
  dispatched_vyper_call tops txp vs.vs_call_ctx.cc_calldata ret /\
  LENGTH vs.vs_call_ctx.cc_calldata < 2 ** 64 /\
  initial_venom_state_rel tops am txp vs /\ code_layout_valid vs /\
  EVERY (\oc. LENGTH oc.co_returnData < dimword(:256) /\
              accounts_runtime_well_typed oc.co_accounts) vs.vs_outcomes /\
  LENGTH vs.vs_outcomes < 2 ** 64 /\
  vs.vs_fmp = fmp /\ vs.vs_initial_fmp = fmp
Proof
  simp[vyper_call_staging_def, vyper_frame_staging_def] >> strip_tac >> gvs[] >>
  rename1 `raw_variant fmp vs (opt_entry_state prog prog' cplan es)` >>
  qabbrev_tac `vs0 = opt_entry_state prog prog' cplan es` >>
  `LENGTH vs0.vs_code < 2 ** 256` by
    (qpat_assum `code_layout_valid vs0`
       (mp_tac o REWRITE_RULE [code_layout_valid_def]) >>
     simp[dimword_def, dimindex_256] >> strip_tac >>
     irule LESS_EQ_LESS_TRANS >> qexists_tac `2 ** 255` >> fs[]) >>
  `source_deployment_rel tops am tx` by
    fs[call_state_rel_def] >>
  `vs.vs_outcomes = MAP SND (call_trace es) /\
   vs.vs_call_ctx.cc_calldata = buffer_to_list (FST (HD es.contexts)).msgParams.data` by
    (drule raw_variant_outcomes >> drule raw_variant_call_ctx >>
     simp[Abbr `vs0`, opt_entry_state_def, entry_venom_state_def]) >>
  `wf_state es /\ balance_bounded (2 ** 256 - 1) es /\ returndata_bounded es` by
    fs[call_state_rel_def, evm_state_ok_def] >>
  drule_all call_trace_outcomes_bounded >> strip_tac >>
  `LENGTH vs.vs_call_ctx.cc_calldata < 2 ** 64` by
    metis_tac[Abbr `vs0`, raw_variant_opt_entry_calldata_bound] >>
  `initial_venom_state_rel tops am (tx with code := vs0.vs_code) vs` by
    metis_tac[Abbr `vs0`, opt_entry_initial_venom_state_rel,
              raw_variant_initial_venom_state_rel] >>
  `code_layout_valid vs /\ vs.vs_fmp = fmp /\ vs.vs_initial_fmp = fmp` by
    (qpat_assum `raw_variant _ _ _`
       (mp_tac o REWRITE_RULE [raw_variant_def, gas_variant_def]) >>
     disch_then (mp_tac o Q.AP_TERM
       `\st:venom_state. (st.vs_fmp, st.vs_initial_fmp, st.vs_code,
                         st.vs_data_section, st.vs_labels)`) >>
     simp[] >> strip_tac >> fs[code_layout_valid_def]) >>
  fs[source_typing_ok_code_update, source_deployment_rel_def, layouts_agree_def,
     dispatched_vyper_call_code_update]
QED

Theorem guard_source_marks:
  s1_request_prefix tops /\ supported_program tops /\
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  vyper_call_staging fin policy tops (assemble prog') am tx ret es /\
  vs0 = opt_entry_state prog prog' cplan es /\ txp = tx with code := vs0.vs_code /\
  code_layout_valid vs0 /\ w2n fmp < 2 ** 254 /\
  unit_alloca_budget unit.cu_context +
    32 * ctx_dload_count unit.cu_context <= w2n fmp ==>
  ?shadow_ctx. !vs. raw_variant fmp vs vs0 ==>
    ?marks.
      source_unit_execution_correct_with shadow_ctx marks tops ret am txp unit vs /\
      !tail res am' rqs obs obs_pre rq outcome sfx H.
        call_external_trace (SOME vs.vs_outcomes)
          (gas_explicit marks vs.vs_gas_readings ++ tail) am txp =
          (res,am',rqs,obs) /\
        ~source_exempt tops (res,am',rqs) /\
        obs = obs_pre ++ StorageOutcome rq outcome :: sfx /\
        valid_horizon
          (initial_evaluation_context am.sources am.layouts txp NONE)
          (initial_state am []) H obs_pre ==>
        (computed_precompile rq ==>
           outcome.co_accounts = rq.cr_accounts /\
           outcome.co_tStorage = rq.cr_tStorage) /\
        (~computed_precompile rq ==>
           recorded_outcomes_count obs_pre < LENGTH rqs /\
           EL (recorded_outcomes_count obs_pre) rqs = rq /\
           raw_safe_rq_upto
             (cx_dead H (initial_evaluation_context am.sources am.layouts txp NONE))
             0 (recorded_outcomes_count obs_pre) unit.cu_context vs /\
           ?fn inst s fuel s'.
             raw_reachable vs unit.cu_context fn inst s /\
             inst.inst_opcode <> INVOKE /\
             LENGTH s.vs_requests = recorded_outcomes_count obs_pre /\
             step_inst fuel unit.cu_context inst s = OK s' /\
             recorded_outcomes_count obs_pre < LENGTH s'.vs_requests /\
             request_agree H txp.target rq (EL (recorded_outcomes_count obs_pre) s'.vs_requests) /\
             outcome = (if s.vs_outcomes = [] then failed_outcome rq else HD s.vs_outcomes))
Proof
  strip_tac >>
  qpat_x_assum `s1_request_prefix tops`
    (mp_tac o Q.SPECL [`rpolicy`, `unit`] o REWRITE_RULE [s1_request_prefix_def]) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `shadow_ctx` assume_tac) >>
  qexists_tac `shadow_ctx` >> rpt strip_tac >>
  qpat_x_assum `!am tx ret vs. _`
    (qspecl_then [`am`, `txp`, `ret`, `vs`] mp_tac) >>
  impl_tac >- (drule_all guard_selected_raw_inputs >> strip_tac >> fs[]) >>
  simp[]
QED

Theorem request_step_has_outcome[local]:
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK t /\
  LENGTH s.vs_requests < LENGTH t.vs_requests ==>
  s.vs_outcomes <> []
Proof
  strip_tac >> gvs[step_inst_non_invoke] >>
  Cases_on `MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]`
  >- (gvs[] >> with_opcode_clause gvs >>
      gvs[exec_ext_call_def, exec_delegatecall_def, exec_create_def, AllCaseEqs()]) >>
  gvs[] >> drule_all step_inst_base_oracle >> strip_tac >> gvs[]
QED

Theorem guard_request_cut_pair[local]:
  raw_safe_rq_upto D 0 k C vs /\
  (?fn inst s fuel s'.
     raw_reachable vs C fn inst s /\ inst.inst_opcode <> INVOKE /\
     LENGTH s.vs_requests = k /\ step_inst fuel C inst s = OK s' /\
     k < LENGTH s'.vs_requests /\ request_agree H addr rq (EL k s'.vs_requests) /\
     outcome = (if s.vs_outcomes = [] then failed_outcome rq else HD s.vs_outcomes)) /\
  (!fn inst s fuel s'.
     raw_safe_rq_upto D 0 k C vs /\
     raw_reachable vs C fn inst s /\ inst.inst_opcode <> INVOKE /\
     LENGTH s.vs_requests = k /\ step_inst fuel C inst s = OK s' /\
     k < LENGTH s'.vs_requests /\ s.vs_outcomes <> [] ==>
     (?fn' inst' t fuel' t'.
        raw_reachable vs0 C' fn' inst' t /\ inst'.inst_opcode <> INVOKE /\
        LENGTH t.vs_requests = k /\ step_inst fuel' C' inst' t = OK t' /\
        k < LENGTH t'.vs_requests /\
        request_agree_except D (EL k s'.vs_requests) (EL k t'.vs_requests) /\
        t.vs_outcomes = s.vs_outcomes) /\
     ctx_rq_upto D k C C' vs vs0 /\
     (?eom. max_live_eom C' = SOME eom /\
        mem_inv (\ctx fn inst t. (request_cut k t /\ ~in_static_abort_prefix fn t) ==>
          lowered_mem_ok eom (w2n t.vs_initial_fmp) ctx fn inst t) C' vs0) /\
     (fin = asm_opt_finalizer ==>
        code_end_offset_ok (\ctx fn inst t. raw_reachable vs0 ctx fn inst t /\
          request_cut k t /\ ~in_static_abort_prefix fn t) C')) ==>
  (?fn inst s fuel s' fn' inst' t fuel' t'.
     raw_reachable vs C fn inst s /\ inst.inst_opcode <> INVOKE /\
     LENGTH s.vs_requests = k /\ step_inst fuel C inst s = OK s' /\
     k < LENGTH s'.vs_requests /\ request_agree H addr rq (EL k s'.vs_requests) /\
     outcome = (if s.vs_outcomes = [] then failed_outcome rq else HD s.vs_outcomes) /\
     raw_reachable vs0 C' fn' inst' t /\ inst'.inst_opcode <> INVOKE /\
     LENGTH t.vs_requests = k /\ step_inst fuel' C' inst' t = OK t' /\
     k < LENGTH t'.vs_requests /\
     request_agree_except D (EL k s'.vs_requests) (EL k t'.vs_requests) /\
     t.vs_outcomes = s.vs_outcomes) /\
  ctx_rq_upto D k C C' vs vs0 /\
  (?eom. max_live_eom C' = SOME eom /\
     mem_inv (\ctx fn inst t. (request_cut k t /\ ~in_static_abort_prefix fn t) ==>
       lowered_mem_ok eom (w2n t.vs_initial_fmp) ctx fn inst t) C' vs0) /\
  (fin = asm_opt_finalizer ==>
     code_end_offset_ok (\ctx fn inst t. raw_reachable vs0 ctx fn inst t /\
       request_cut k t /\ ~in_static_abort_prefix fn t) C')
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2
      (qx_choosel_then [`fn`, `inst`, `s`, `fuel`, `s'`] strip_assume_tac)
      (qspecl_then [`fn`, `inst`, `s`, `fuel`, `s'`] mp_tac))) >>
  impl_tac
  >- (asm_rewrite_tac[] >> irule request_step_has_outcome >> metis_tac[]) >>
  disch_then (CONJUNCTS_THEN2
    (qx_choosel_then [`fn'`, `inst'`, `t`, `fuel'`, `t'`] strip_assume_tac)
    strip_assume_tac) >>
  conj_tac >- (qexistsl_tac [`fn`, `inst`, `s`, `fuel`, `s'`,
                             `fn'`, `inst'`, `t`, `fuel'`, `t'`] >>
               asm_rewrite_tac[]) >>
  asm_rewrite_tac[] >>
  qexists_tac `eom` >> asm_rewrite_tac[]
QED

Theorem guard_selected_request_replay:
  (!tail res am' rqs obs obs_pre rq outcome sfx H.
  call_external_trace (SOME vs.vs_outcomes)
    (gas_explicit marks vs.vs_gas_readings ++ tail) am tx =
    (res,am',rqs,obs) /\
  ~source_exempt tops (res,am',rqs) /\
  obs = obs_pre ++ StorageOutcome rq outcome :: sfx /\
  valid_horizon
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am []) H obs_pre ==>
  (computed_precompile rq ==>
     outcome.co_accounts = rq.cr_accounts /\
     outcome.co_tStorage = rq.cr_tStorage) /\
  (~computed_precompile rq ==>
     recorded_outcomes_count obs_pre < LENGTH rqs /\
     EL (recorded_outcomes_count obs_pre) rqs = rq /\
     raw_safe_rq_upto
       (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
       0 (recorded_outcomes_count obs_pre) C vs /\
     ?fn inst s fuel s'.
       raw_reachable vs C fn inst s /\
       inst.inst_opcode <> INVOKE /\
       LENGTH s.vs_requests = recorded_outcomes_count obs_pre /\
       step_inst fuel C inst s = OK s' /\
       recorded_outcomes_count obs_pre < LENGTH s'.vs_requests /\
       request_agree H tx.target rq (EL (recorded_outcomes_count obs_pre) s'.vs_requests) /\
       outcome = (if s.vs_outcomes = [] then failed_outcome rq else HD s.vs_outcomes))) /\
  (!H:(bool # bytes32 # type_value) list # num list. !k fn inst s fuel s'.
     raw_safe_rq_upto (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE)) 0 k C vs /\
     raw_reachable vs C fn inst s /\ inst.inst_opcode <> INVOKE /\
     LENGTH s.vs_requests = k /\ step_inst fuel C inst s = OK s' /\
     k < LENGTH s'.vs_requests /\ s.vs_outcomes <> [] ==>
     (?fn' inst' t fuel' t'.
        raw_reachable vs0 C' fn' inst' t /\ inst'.inst_opcode <> INVOKE /\
        LENGTH t.vs_requests = k /\ step_inst fuel' C' inst' t = OK t' /\
        k < LENGTH t'.vs_requests /\
        request_agree_except (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE)) (EL k s'.vs_requests) (EL k t'.vs_requests) /\
        t.vs_outcomes = s.vs_outcomes) /\
     ctx_rq_upto (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE)) k C C' vs vs0 /\
     (?eom. max_live_eom C' = SOME eom /\
        mem_inv (\ctx fn inst t. (request_cut k t /\ ~in_static_abort_prefix fn t) ==>
          lowered_mem_ok eom (w2n t.vs_initial_fmp) ctx fn inst t) C' vs0) /\
     (fin = asm_opt_finalizer ==>
        code_end_offset_ok (\ctx fn inst t. raw_reachable vs0 ctx fn inst t /\
          request_cut k t /\ ~in_static_abort_prefix fn t) C')) ==>
  !tail res am' rqs obs obs_pre rq outcome sfx H.
  call_external_trace (SOME vs.vs_outcomes)
    (gas_explicit marks vs.vs_gas_readings ++ tail) am tx =
    (res,am',rqs,obs) /\
  ~source_exempt tops (res,am',rqs) /\
  obs = obs_pre ++ StorageOutcome rq outcome :: sfx /\
  valid_horizon
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am []) H obs_pre ==>
  (computed_precompile rq ==>
     outcome.co_accounts = rq.cr_accounts /\
     outcome.co_tStorage = rq.cr_tStorage) /\
  (~computed_precompile rq ==>
     recorded_outcomes_count obs_pre < LENGTH rqs /\
     EL (recorded_outcomes_count obs_pre) rqs = rq /\
     raw_safe_rq_upto
       (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
       0 (recorded_outcomes_count obs_pre) C vs /\
     (?fn inst s fuel s' fn' inst' t fuel' t'.
        raw_reachable vs C fn inst s /\
        inst.inst_opcode <> INVOKE /\
        LENGTH s.vs_requests = recorded_outcomes_count obs_pre /\
        step_inst fuel C inst s = OK s' /\
        recorded_outcomes_count obs_pre < LENGTH s'.vs_requests /\
        request_agree H tx.target
          rq (EL (recorded_outcomes_count obs_pre) s'.vs_requests) /\
        outcome =
          (if s.vs_outcomes = [] then failed_outcome rq
           else HD s.vs_outcomes) /\
        raw_reachable vs0
          C' fn' inst' t /\
        inst'.inst_opcode <> INVOKE /\
        LENGTH t.vs_requests = recorded_outcomes_count obs_pre /\
        step_inst fuel' C' inst' t = OK t' /\
        recorded_outcomes_count obs_pre < LENGTH t'.vs_requests /\
        request_agree_except
          (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
          (EL (recorded_outcomes_count obs_pre) s'.vs_requests)
          (EL (recorded_outcomes_count obs_pre) t'.vs_requests) /\
        t.vs_outcomes = s.vs_outcomes) /\
     ctx_rq_upto
       (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
       (recorded_outcomes_count obs_pre)
       C C'
       vs vs0 /\
     (?eom. max_live_eom C' = SOME eom /\
       mem_inv (\ctx fn inst s. (request_cut (recorded_outcomes_count obs_pre) s /\ ~in_static_abort_prefix fn s) ==>
         lowered_mem_ok eom (w2n s.vs_initial_fmp) ctx fn inst s) C' vs0) /\
     (fin = asm_opt_finalizer ==>
       code_end_offset_ok (\ctx fn inst s. raw_reachable vs0 ctx fn inst s /\
         request_cut (recorded_outcomes_count obs_pre) s /\ ~in_static_abort_prefix fn s) C'))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!tail res am' rqs obs obs_pre rq outcome sfx H. _`
    (qspecl_then [`tail`, `res`, `am'`, `rqs`, `obs`, `obs_pre`, `rq`,
                  `outcome`, `sfx`, `H`] mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  strip_tac >>
  qpat_x_assum `~computed_precompile rq ==> _`
    (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac assume_tac)) o UNDISCH) >>
  asm_rewrite_tac[] >>
  irule guard_request_cut_pair >>
  asm_rewrite_tac[] >>
  qpat_x_assum `!H k fn inst s fuel s'. _`
    (qspecl_then [`H`, `recorded_outcomes_count obs_pre`] ACCEPT_TAC)
QED
