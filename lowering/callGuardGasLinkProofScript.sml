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

Theorem guard_opt_entry_layout:
  supported_program tops /\ source_typing_ok tops am tx /\
  call_state_rel tops (assemble prog') am tx es /\
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  codegen_assembly rpolicy out.po_unit = SOME prog ==>
  code_layout_valid (opt_entry_state prog prog' cplan es)
Proof
  strip_tac >>
  drule supported_program_raw_shape_free_program >> strip_tac >>
  `?art. vyperTypeContract$check_contract F am.layouts tx.target [(NONE,tops)] = SOME art` by
    metis_tac[source_typing_ok_def] >>
  drule_all lower_vyper_runtime_unit_source_unit_ok >> strip_tac >>
  drule_all lower_vyper_runtime_unit_o1_shape_extras >> strip_tac >>
  drule_all lower_vyper_runtime_unit_defs_reach_uses >> strip_tac >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  metis_tac[opt_entry_code_layout_valid]
QED

Theorem guard_selected_raw_inputs:
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

Theorem guard_focus_callback_inputs:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ o1_source_unit_ok unit /\
  raw_unit_memory_ok unit.cu_context vs /\ ptr_discipline 0 unit.cu_context vs /\
  taint_within (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
    unit.cu_context vs /\
  mem_inv dload_offset_ok unit.cu_context vs /\
  mem_inv dload_headroom_ok unit.cu_context vs ==>
  dead_wf (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE)) /\
  o1_pre_walk_inv (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
    unit.cu_context vs
Proof
  strip_tac >> conj_tac
  >- (simp[cx_dead_def, initial_evaluation_context_def] >>
      MATCH_ACCEPT_TAC
        (SIMP_RULE (srw_ss()) [external_call_dead_def]
          (Q.INST [`src` |-> `(INL NoneV, am, [])`] external_call_dead_wf))) >>
  `mem_inv raw_mem_ok unit.cu_context vs` by
    (simp[raw_unit_memory_ok_mem_inv] >> rpt strip_tac >>
     fs[raw_unit_memory_ok_def] >> metis_tac[raw_reachable_least]) >>
  drule lower_vyper_runtime_unit_raw_defaults >> strip_tac >>
  drule lower_vyper_runtime_unit_global_reserved >> strip_tac >>
  drule lower_vyper_runtime_unit_defs_reach_uses >> strip_tac >>
  irule o1_source_pre_walk_inv >>
  simp[o1_src_inv_def, source_fmp_free, fixed_region_reserved_def,
       staticLayoutDefsTheory.reserved_intervals_wf_def] >>
  qexists_tac `0` >> simp[fixed_region_reserved_def]
QED

Theorem gas_readings_rel_selected_marks:
  LENGTH raw_slots = LENGTH sites /\
  PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) readings /\
  (!raw. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw ==>
     (?rest. MAP project sites = markf (raw ++ pad) ++ rest) /\
     !tail. P (raw ++ pad) tail) ==>
  gas_readings_rel readings
    (\gs. ?raw tail. gs = gas_explicit (markf raw) raw ++ tail /\ P raw tail)
Proof
  strip_tac >> rewrite_tac[gas_readings_rel_def] >>
  qspecl_then [`MAP project sites`, `raw_slots`, `unused`, `readings`,
    `\gs. ?raw tail. gs = gas_explicit (markf raw) raw ++ tail /\ P raw tail`]
    mp_tac gas_mask_projection >>
  impl_tac
  >- (simp[] >> rpt gen_tac >> strip_tac >>
      rename1 `LIST_REL _ raw_slots raw` >>
      qpat_assum `!raw. LIST_REL _ raw_slots raw ==> _`
        (qspec_then `raw` (fn replay =>
          qpat_assum `LIST_REL _ raw_slots raw`
            (CONJUNCTS_THEN2 (qx_choose_then `rest` assume_tac) assume_tac o
             MATCH_MP replay))) >>
      qexistsl_tac [`raw ++ pad`,
        `gas_explicit rest (DROP (LENGTH (markf (raw ++ pad))) (raw ++ pad)) ++ tail`] >>
      asm_rewrite_tac[] >>
      irule gas_mask_padded_split >>
      `LENGTH (MAP project sites) = LENGTH raw` by
        (simp[] >> metis_tac[LIST_REL_LENGTH]) >>
      metis_tac[]) >>
  simp[]
QED

Theorem guard_marked_focus_family:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  o1_source_unit_ok unit /\ ~ctx_has_dalloca unit.cu_context /\
  initial_venom_state_rel tops am tx vs0 /\ code_layout_valid vs0 /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
  (!vs. raw_variant fmp vs vs0 ==>
     ?marks. source_unit_execution_correct_with shadow_ctx marks tops ret am tx unit vs /\
             prefix_ok vs marks) ==>
  ?markf. !gs.
    source_unit_execution_correct_with shadow_ctx (markf gs) tops ret am tx unit
      (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
    prefix_ok (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>)
      (markf gs) /\
    ?D fuel extra.
      dead_wf D /\
      (!fn inst s.
         raw_reachable
           (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>)
           unit.cu_context fn inst s /\
         gas_cut (MIN (LENGTH (markf gs)) (LENGTH gs))
           (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>) s ==>
         inst_dload_in_section inst s) /\
      o1_safe_upto D 0 (MIN (LENGTH (markf gs)) (LENGTH gs)) unit.cu_context
        (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
      MAP (\key. key IN gas_explicit_sites unit.cu_context shadow_ctx)
        (gas_events_blocks fuel unit.cu_context func
          (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp;
                      vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>)) =
        markf gs ++ extra
Proof
  strip_tac >>
  `!gs. ?marks. source_unit_execution_correct_with shadow_ctx marks tops ret am tx unit
       (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
       prefix_ok (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>)
         marks` by
    (gen_tac >> qpat_x_assum `!vs. raw_variant _ _ _ ==> _` irule >>
     simp[raw_variant_def, gas_variant_def, venom_state_component_equality]) >>
  pop_assum mp_tac >> CONV_TAC (LAND_CONV SKOLEM_CONV) >>
  disch_then (qx_choose_then `markf` assume_tac) >>
  qexists_tac `markf` >> gen_tac >>
  first_x_assum (qspec_then `gs` strip_assume_tac) >>
  `initial_venom_state_rel tops am tx
     (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>)` by
    (irule raw_variant_initial_venom_state_rel >> qexistsl_tac [`fmp`, `vs0`] >>
     simp[raw_variant_def, gas_variant_def, venom_state_component_equality]) >>
  asm_rewrite_tac[] >>
  drule_at (Pat `source_unit_execution_correct_with _ _ _ _ _ _ _ _`)
    call_certificate_raw_entry_boundary >>
  simp[code_layout_valid_def] >> disch_then irule >>
  fs[code_layout_valid_def] >> metis_tac[]
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

Theorem guard_request_cut_pair:
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

Theorem guard_whole_focus_callback:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  o1_source_unit_ok unit /\ raw_variant fmp vs vs0 /\
  (!D. (?fr. terminates (run_context fr unit.cu_context vs)) /\
       dead_wf D /\ o1_pre_walk_inv D unit.cu_context vs /\
       (fin = asm_opt_finalizer ==>
         mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
           s.vs_code = vs0.vs_code /\ s.vs_data_section = vs0.vs_data_section)
           unit.cu_context vs) ==> P D) ==>
  !H:(bool # bytes32 # type_value) list # num list.
    (?fr. terminates (run_context fr unit.cu_context vs)) /\
    raw_unit_memory_ok unit.cu_context vs /\ ptr_discipline 0 unit.cu_context vs /\
    taint_within (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
      unit.cu_context vs /\
    mem_inv dload_offset_ok unit.cu_context vs /\
    mem_inv dload_headroom_ok unit.cu_context vs /\
    mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
      s.vs_code = vs.vs_code /\ s.vs_data_section = vs.vs_data_section)
      unit.cu_context vs ==>
    P (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
Proof
  strip_tac >> gen_tac >> strip_tac >>
  qpat_x_assum `!D. _ ==> P D` irule >>
  drule_all guard_focus_callback_inputs >> strip_tac >>
  `vs.vs_code = vs0.vs_code /\ vs.vs_data_section = vs0.vs_data_section` by
    (qpat_assum `raw_variant _ _ _`
       (mp_tac o REWRITE_RULE [raw_variant_def, gas_variant_def]) >>
     disch_then (mp_tac o Q.AP_TERM
       `\st:venom_state. (st.vs_code, st.vs_data_section)`) >>
     simp[]) >>
  asm_rewrite_tac[] >>
  conj_tac >- metis_tac[] >>
  strip_tac >>
  qpat_x_assum `mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\ _) _ _`
    mp_tac >> simp[]
QED

Theorem guard_selected_witness:
  LENGTH raw_slots = LENGTH sites /\
  PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) readings /\
  (!raw. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw ==>
    (?rest. MAP project sites = markf (raw ++ [0w]) ++ rest) /\
    P (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp;
                  vs_initial_fmp := fmp|>) (markf (raw ++ [0w]))) ==>
  gas_readings_rel readings
    (\gs. ?vs marks tail. gs = gas_explicit marks vs.vs_gas_readings ++ tail /\
      raw_variant fmp vs vs0 /\ P vs marks)
Proof
  strip_tac >>
  qspecl_then [ `raw_slots`, `sites`, `unused`, `readings`, `project`, `markf`, `[0w]`,
    `\raw (tail:bytes32 list).
       P (vs0 with <|vs_gas_readings := raw; vs_fmp := fmp; vs_initial_fmp := fmp|>)
         (markf raw)` ] mp_tac (Q.GENL
       [`raw_slots`, `sites`, `unused`, `readings`, `project`, `markf`, `pad`, `P`]
       gas_readings_rel_selected_marks) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  disch_then (fn th => irule (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
    gas_readings_rel_mono) th)) >>
  BETA_TAC >> gen_tac >>
  disch_then (qx_choosel_then [`raw`, `tail`] strip_assume_tac) >>
  qexistsl_tac
    [`vs0 with <|vs_gas_readings := raw; vs_fmp := fmp; vs_initial_fmp := fmp|>`,
     `markf raw`, `tail`] >>
  simp[raw_variant_def, gas_variant_def, venom_state_component_equality]
QED

Theorem guard_source_focus_setup:
  supported_program tops /\ source_typing_ok tops am tx /\
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out ==>
  o1_source_unit_ok unit /\ ~ctx_has_dalloca unit.cu_context /\
  unit_entry_no_params unit /\ unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  unit_shape_ok out.po_unit /\
  (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
     ~MEM (Label "runtime_begin") inst.inst_operands) /\
  unit.cu_context.ctx_entry = SOME "__entry" /\
  ?func. lookup_function "__entry" unit.cu_context.ctx_functions = SOME func
Proof
  strip_tac >>
  drule supported_program_raw_shape_free_program >> strip_tac >>
  `?art. vyperTypeContract$check_contract F am.layouts tx.target [(NONE,tops)] = SOME art` by
    metis_tac[source_typing_ok_def] >>
  drule_all lower_vyper_runtime_unit_source_unit_ok >> strip_tac >>
  `~ctx_has_dalloca unit.cu_context` by
    (irule every_no_dalloca >>
     drule_all lower_vyper_runtime_unit_no_dalloca_checked >> simp[]) >>
  drule_all lower_vyper_runtime_unit_o1_shape_extras >> strip_tac >>
  drule lower_vyper_runtime_unit_defs_reach_uses >> strip_tac >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  simp[] >> metis_tac[lower_vyper_runtime_unit_no_runtime_begin]
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

Theorem call_pipeline_gas_link_from_static_focus:
  (!rpolicy unit out vs0 cpl prog fin prog' es0 nm entryfn lbl fmp markf
    lo (project : (string # num) -> bool) result final.
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    o1_source_unit_ok unit /\ unit_entry_no_params unit /\
    unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
    o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp /\
    code_layout_valid vs0 /\
    (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
       ~MEM (Label "runtime_begin") inst.inst_operands) /\
    unit_shape_ok out.po_unit /\
    generate_context_plan out.po_unit.cu_context = SOME cpl /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
    (fin = asm_opt_finalizer ==>
       label_flow_ok unit.cu_context /\
       (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
                  ~MEM (Label "code_end") inst.inst_operands) /\
       EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                         ds.ds_items) unit.cu_data_segment /\
       ((?fn inst. MEM fn unit.cu_context.ctx_functions /\
                   MEM inst (fn_insts fn) /\
                   MEM (Label "runtime_begin") inst.inst_operands) ==>
        EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment) /\
       LENGTH vs0.vs_data_section < dimword (:256) DIV 2) /\
    vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
    codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
    asm_frame_rel_tail [] prog' vs0.vs_data_section es0
      (entry_asm_state vs0 es0 with
        as_code := assemble prog' ++ vs0.vs_data_section) es0 /\
    unit.cu_context.ctx_entry = SOME nm /\
    lookup_function nm unit.cu_context.ctx_functions = SOME entryfn /\
    fn_entry_label entryfn = SOME lbl /\
    w2n vs0.vs_initial_fmp <= w2n fmp /\ w2n fmp < 2 ** 254 /\
    unit_alloca_budget unit.cu_context +
      32 * ctx_dload_count unit.cu_context <= w2n fmp /\
    (!gs. ?D f extra.
      dead_wf D /\
      (fin = asm_opt_finalizer ==>
         !fn inst s.
           raw_reachable (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>)
             unit.cu_context fn inst s /\
           gas_cut (MIN (LENGTH (markf gs)) (LENGTH gs))
             (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>) s ==>
           inst_dload_in_section inst s) /\
      o1_safe_upto D lo (MIN (LENGTH (markf gs)) (LENGTH gs))
        unit.cu_context (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
      MAP project
        (gas_events_blocks f unit.cu_context entryfn
          (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp;
                      vs_prev_bb := NONE;
                      vs_current_bb := lbl; vs_inst_idx := 0|>)) =
        markf gs ++ extra) /\
    run_call es0 = SOME (result,final) /\
    ~frame_resource_starved es0 result final ==>
    ?raw_slots sites unused.
      LENGTH raw_slots = LENGTH sites /\
      PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es0) /\
      !raw.
        LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw ==>
        (?rest. MAP project sites = markf (raw ++ [0w]) ++ rest) /\
        !D.
          (?fr. terminates (run_context fr unit.cu_context
             (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>))) /\
          dead_wf D /\
          o1_pre_walk_inv D unit.cu_context
            (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
          (fin = asm_opt_finalizer ==>
             mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                       s.vs_code = vs0.vs_code /\ s.vs_data_section = vs0.vs_data_section)
               unit.cu_context (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>)) ==>
          ctx_sim D unit.cu_context out.po_unit.cu_context
            (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) vs0 /\
          ctx_abort_rq D unit.cu_context out.po_unit.cu_context
            (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) vs0 /\
          (fin = asm_opt_finalizer ==>
             code_end_offset_ok
               (\ctx fn inst s. raw_reachable vs0 ctx fn inst s /\
                 ~in_static_abort_prefix fn s) out.po_unit.cu_context) /\
          ((o1_lowered_inv out.po_unit.cu_context vs0 /\
            (fin = asm_opt_finalizer ==>
               code_end_offset_ok (raw_reachable vs0) out.po_unit.cu_context)) \/
           ((?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
              mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
                        lowered_mem_ok eom (w2n s.vs_initial_fmp) ctx fn inst s)
                out.po_unit.cu_context vs0) /\
            !fuel. terminates (run_context fuel unit.cu_context
                      (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>)) ==>
                   ?u. run_context fuel unit.cu_context
                         (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) =
                       Abort ExHalt_abort u))) /\
  (!tops rpolicy unit.
  supported_program tops /\ ~program_reads_self_code tops /\
  lower_vyper_runtime_unit tops rpolicy = SOME unit ==>
  label_flow_ok unit.cu_context /\
  (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
             ~MEM (Label "code_end") inst.inst_operands) /\
  EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                    ds.ds_items) unit.cu_data_segment /\
  ((?fn inst. MEM fn unit.cu_context.ctx_functions /\
              MEM inst (fn_insts fn) /\
              MEM (Label "runtime_begin") inst.inst_operands) ==>
   EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment)) ==>
  !fin policy tops deploy_bc runtime_bc rpolicy unit out prog prog' cp
   am tx txp ret es vs0 fmp r es'.
    fin IN accepted_finalizers /\
    (fin = asm_opt_finalizer ==> ~program_reads_self_code tops) /\
    compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\
    source_typing_ok tops am txp /\
    call_state_rel tops (assemble prog') am tx es /\
    LENGTH (call_trace es) < 2 ** 64 /\
    resolve_o1_policy policy = SOME rpolicy /\
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    fin rpolicy prog = SOME prog' /\
    vs0 = opt_entry_state prog prog' cp es /\
    txp = tx with code := vs0.vs_code /\
    w2n vs0.vs_initial_fmp <= w2n fmp /\
    w2n fmp < 2 ** 254 /\
    unit_alloca_budget unit.cu_context +
      32 * ctx_dload_count unit.cu_context <= w2n fmp /\
    (?shadow_ctx. !vs.
       raw_variant fmp vs vs0 ==>
       ?marks.
         source_unit_execution_correct_with shadow_ctx marks
           tops ret am txp unit vs) /\
    run_call es = SOME (r, es') /\
    ~frame_resource_starved es r es' ==>
    gas_readings_rel (gas_readings es)
      (\gs. call_storage_ok am txp (MAP SND (call_trace es)) gs ==>
         ?vs marks tail.
           gs = gas_explicit marks vs.vs_gas_readings ++ tail /\
           raw_variant fmp vs vs0 /\
           (!H:(bool # bytes32 # type_value) list # num list.
              (?fr. terminates (run_context fr unit.cu_context vs)) /\
              raw_unit_memory_ok unit.cu_context vs /\
              ptr_discipline 0 unit.cu_context vs /\
              taint_within
                (cx_dead H (initial_evaluation_context am.sources am.layouts txp NONE))
                unit.cu_context vs /\
              mem_inv dload_offset_ok unit.cu_context vs /\
              mem_inv dload_headroom_ok unit.cu_context vs /\
              mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                s.vs_code = vs.vs_code /\ s.vs_data_section = vs.vs_data_section)
                unit.cu_context vs ==>
              ctx_sim
                (cx_dead H (initial_evaluation_context am.sources am.layouts txp NONE))
                unit.cu_context out.po_unit.cu_context vs
                vs0 /\
              (fin = asm_opt_finalizer ==>
                 code_end_offset_ok (\ctx fn inst s. raw_reachable vs0 ctx fn inst s /\
                                     ~in_static_abort_prefix fn s) out.po_unit.cu_context) /\
              ((o1_lowered_inv out.po_unit.cu_context vs0 /\
                (fin = asm_opt_finalizer ==>
                   code_end_offset_ok (raw_reachable vs0) out.po_unit.cu_context)) \/
               ((?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
                  mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
                            lowered_mem_ok eom (w2n s.vs_initial_fmp) ctx fn inst s)
                    out.po_unit.cu_context vs0) /\
                !fuel. terminates (run_context fuel unit.cu_context vs) ==>
                       ?u. run_context fuel unit.cu_context vs = Abort ExHalt_abort u))) /\
           source_unit_execution_correct_at marks tops ret am txp unit vs)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all guard_source_focus_setup >> strip_tac >>
  rename1 `lookup_function "__entry" unit.cu_context.ctx_functions = SOME func` >>
  rename1 `generate_context_plan out.po_unit.cu_context = SOME cplan` >>
  drule_all opt_entry_focus_setup >> strip_tac >>
  `initial_venom_state_rel tops am txp vs0` by
    metis_tac[opt_entry_initial_venom_state_rel] >>
  drule_all
    (SIMP_RULE (srw_ss()) []
      (Q.INST [ `prefix_ok` |-> `\(s:venom_state) (m:bool list). T` ]
        guard_marked_focus_family)) >>
  disch_then (qx_choose_then `markf` assume_tac) >>
  `fn_entry_label func = SOME "__entry"` by
    (qpat_assum `!gs. source_unit_execution_correct_with _ _ _ _ _ _ _ _ /\ _`
       (mp_tac o REWRITE_RULE [source_unit_execution_correct_with_def] o
        CONJUNCT1 o Q.SPEC `[]`) >>
     disch_then (qx_choosel_then [ `cf`, `shadow_cf` ] strip_assume_tac) >>
     `cf = func` by fs[] >> fs[]) >>
  `fin = asm_opt_finalizer ==>
    label_flow_ok unit.cu_context /\
    (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
               ~MEM (Label "code_end") inst.inst_operands) /\
    EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                      ds.ds_items) unit.cu_data_segment /\
    ((?fn inst. MEM fn unit.cu_context.ctx_functions /\
                MEM inst (fn_insts fn) /\
                MEM (Label "runtime_begin") inst.inst_operands) ==>
     EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment) /\
    LENGTH vs0.vs_data_section < dimword (:256) DIV 2` by
    (disch_tac >>
     qpat_x_assum `!tops rpolicy unit. _`
       (qspecl_then [ `tops`, `rpolicy`, `unit` ] mp_tac) >>
     impl_tac >- fs[] >> strip_tac >> asm_rewrite_tac[]) >>
  qpat_x_assum `!rp cu pout v cpl p finalizer p' es0 nm entryfn lbl fm mf lo project result last. _`
    mp_tac >>
  disch_then (mp_tac o Q.SPECL
    [ `rpolicy`, `unit`, `out`, `vs0`, `cplan`, `prog`, `fin`, `prog'`,
      `es`, `"__entry"`, `func`, `"__entry"`, `fmp`, `markf`, `0`,
      `\key. key IN gas_explicit_sites unit.cu_context shadow_ctx`, `r`, `es'` ]) >>
  impl_tac
  >- (BETA_TAC >> asm_rewrite_tac[] >> gen_tac >>
      qpat_assum `!gs. source_unit_execution_correct_with _ _ _ _ _ _ _ _ /\ _`
        (qx_choosel_then [`D`, `fuel`, `extra`] strip_assume_tac o
         CONJUNCT2 o Q.SPEC `gs`) >>
      qexistsl_tac [`D`, `fuel`, `extra`] >>
      qpat_x_assum `vs0 = opt_entry_state _ _ _ _` SUBST_ALL_TAC >>
      pure_rewrite_tac[venom_state_fupdcanon] >>
      qpat_assum `MAP _ (gas_events_blocks _ _ _ _) = _`
        (fn th => asm_rewrite_tac [REWRITE_RULE [venom_state_fupdcanon] th])) >>
  disch_then (qx_choosel_then [ `raw_slots`, `sites`, `unused` ] strip_assume_tac) >>
  qabbrev_tac `project = MAP (\key. key IN gas_explicit_sites unit.cu_context shadow_ctx) sites` >>
  rewrite_tac[gas_readings_rel_def] >>
  irule gas_mask_projection >>
  qexistsl_tac [ `project`, `raw_slots`, `unused` ] >>
  `LENGTH project = LENGTH raw_slots` by simp[Abbr `project`] >>
  qpat_assum `LENGTH project = LENGTH raw_slots` (fn lengths =>
    qpat_assum `PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es)`
      (fn readings => rewrite_tac [lengths, readings])) >>
  qx_genl_tac [`raw`, `tail`] >> strip_tac >> BETA_TAC >>
  qpat_x_assum `!raw. LIST_REL _ raw_slots raw ==> _` (qspec_then `raw` mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `rest` assume_tac) assume_tac) >>
  qabbrev_tac `vs = vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>` >>
  qabbrev_tac `marks = markf (raw ++ [0w])` >>
  qabbrev_tac `suffix = gas_explicit rest (DROP (LENGTH marks) (raw ++ [0w])) ++ tail` >>
  `gas_explicit project raw ++ tail = gas_explicit marks vs.vs_gas_readings ++ suffix` by
    (qpat_assum `project = marks ++ rest` (fn th => once_rewrite_tac [th]) >>
     simp[Abbr `suffix`, Abbr `vs`] >>
     irule (SIMP_RULE (srw_ss()) []
       (Q.INST [`tail` |-> `[]:bytes32 list`] gas_mask_padded_split)) >>
     `LENGTH raw_slots = LENGTH raw` by metis_tac[LIST_REL_LENGTH] >> fs[]) >>
  `raw_variant fmp vs vs0` by
    simp[Abbr `vs`, raw_variant_def, gas_variant_def, venom_state_component_equality] >>
  `source_unit_execution_correct_at marks tops ret am txp unit vs` by
    (rewrite_tac[source_unit_execution_correct_at_with] >>
     qexists_tac `shadow_ctx` >>
     qunabbrev_tac `marks` >> qunabbrev_tac `vs` >>
     qpat_assum `!gs. source_unit_execution_correct_with _ _ _ _ _ _ _ _ /\ _`
       (ACCEPT_TAC o CONJUNCT1 o Q.SPEC `raw ++ [0w]`)) >>
  disch_tac >> qexistsl_tac [ `vs`, `marks`, `suffix` ] >>
  qpat_assum `raw_variant fmp vs vs0` (fn raw_variant_thm =>
    qpat_assum `source_unit_execution_correct_at marks _ _ _ _ unit vs` (fn cert =>
      qpat_assum `gas_explicit project raw ++ tail = _`
        (fn readings => rewrite_tac [raw_variant_thm, cert, readings]))) >>
  qx_gen_tac `H` >> strip_tac >>
  drule_all guard_focus_callback_inputs >> strip_tac >>
  qpat_x_assum `!D. (?fr. terminates _) /\ _ ==> _`
    (qspec_then `cx_dead H (initial_evaluation_context am.sources am.layouts txp NONE)` mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rename1 `terminates (run_context fuel unit.cu_context vs)` >>
          qexists_tac `fuel` >> first_assum ACCEPT_TAC) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      disch_tac >>
      `vs.vs_code = vs0.vs_code /\ vs.vs_data_section = vs0.vs_data_section` by
        simp[Abbr `vs`] >>
      qpat_assum `vs.vs_code = _` (fn code =>
        qpat_assum `vs.vs_data_section = _` (fn data =>
          qpat_assum `mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\ _) _ vs`
            (ACCEPT_TAC o REWRITE_RULE [code, data])))) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 assume_tac assume_tac))) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
