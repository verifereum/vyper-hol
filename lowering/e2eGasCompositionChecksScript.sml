(* Exercise the frozen focus contracts against the exact gas links and
   optimized correctness statements. The focus suppliers are hypotheses. *)
Theory e2eGasCompositionChecks
Ancestors
  e2eCorrectness e2eDeployCorrectness e2eDeployAtMarks e2eDeployRawFmp
  e2eDefs e2eDeployDefs e2eEntry e2eProducers callRawVariant
  asmOptimizer ctorDeployDefs compilePhasesProps compileVyper
  loweringCalldataCorrect loweringShapeSource loweringShapeProps
  vyperLoweringCorrect o1PipelineCorrect o1PassContract lowerDloadDefs
  sourceUnitExecution vfmExecution callTrace frameOutcome vyperAST list
  e2eComposition venomState codegen vyperCompiler contextCodegenRel unitMemInv
  unitTransformDefs ptrDiscipline contextRawReachable vyperInterpreter
  runtimeLabelReadiness gasSummary gasEvents gasExplicitSites o1SafeUpto
  o1PipelineCompose codegenSymRel asmFrameRel codegenEntryRel runtimeSymSrcUnit
  fragGasOriginEvents fragGasOriginPtrSafeUpto acceptedContextPhi memSafeRun
  loweringMemCorrect asmOptNonemptyFinalizer fragGasOrigin e2eRequestCutDefs
  venomLayout arithmetic sorting words pair codegenCorrectness o1StaticPipelineCorrect
  o1PipelineMemoryLoweredAbort venomExecSemantics venomWf
  ctorDeployInitcode ctorDeployEntry ctorDeployShape ctorDeployDefsReach
  deployUnitExecution ctorDeployBodyJoint ctorDeployDead ctorDeployFrame
  passSimulationDefs deployUnitExitSafe ctorDeployMemoryFrontier
  deployUnitProducers ctorDeployRawEntryFacts asmOptNonemptyWitness
  deployFrameReplay deploySymSrcUnit frameRel codegenRel
  contextPlanLayoutProps asmDataSuffixProps venomInst vyperArith
  vyperStorageFootprint loweringStateRelDefs

  e2eOutcomesGuard e2eOptEntry o1ComposeSupport o1LabelFlowStaticContracts o1FnScheduleDecompHelpers oracleExecProps
  venomPipelineRunner extCallOracle dftGasOracleDefs fcgDefs irSupply venomPassSchedule
  codegenStaticAbort codegenAsmOpt codegenAsmStaticWf contextStaticAbortRel asmSymSem asmOptFinalizerCorrect
Libs
  stepInstBaseLib

val _ = Parse.hide "tops";

val call_pipeline_gas_link_contract = concl e2eCorrectnessTheory.call_pipeline_gas_link;

Theorem vyper_call_correct_asm_opt_from_link:
  ^call_pipeline_gas_link_contract ==>
(
  !policy tops deploy_bc runtime_bc am tx ret es.
    compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) /\
    ~program_reads_self_code tops /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    dispatched_vyper_call tops tx
      (buffer_to_list (FST (HD es.contexts)).msgParams.data) ret /\
    LENGTH (call_trace es) < 2 ** 64
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       call_result_rel tops am tx es r es')
)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule compile_vyper_runtime_phases_asm_opt >> strip_tac >>
  rename1 `generate_context_plan out.po_unit.cu_context = SOME cplan` >>
  qpat_x_assum `prog = _ ++ _` kall_tac >>
  `asm_opt_finalizer IN accepted_finalizers` by simp[accepted_finalizers_def] >>
  `call_state_rel tops (assemble prog') am tx es` by fs[] >>
  qspec_then `es` strip_assume_tac run_call_total >>
  qexistsl_tac [`r`, `es'`] >> simp[] >>
  Cases_on `frame_resource_starved es r es'` >> simp[] >>
  `ALOOKUP am.sources tx.target = SOME [(NONE,tops)] /\
   source_deployment_rel tops am tx` by
    fs[call_state_rel_def, world_rel_def, source_deployment_rel_def] >>
  `external_return_type tops tx.function_name = ret` by
    (fs[dispatched_vyper_call_def] >> simp[external_return_type_def]) >>
  `outcomes_accounts_typed (SOME (MAP SND (call_trace es)))` by
    (`wf_state es /\ balance_bounded (2 ** 256 - 1) es /\ returndata_bounded es` by
       fs[call_state_rel_def, evm_state_ok_def] >>
     drule_all call_trace_outcomes_bounded >>
     simp[exprSimHypsDefsTheory.outcomes_accounts_typed_def, listTheory.EVERY_MEM]) >>
  qabbrev_tac `vs0 = opt_entry_state prog prog' cplan es` >>
  qabbrev_tac `txp = tx with code := vs0.vs_code` >>
  drule supported_program_raw_shape_free_program >> strip_tac >>
  `?art. vyperTypeContract$check_contract F am.layouts tx.target [(NONE,tops)] = SOME art` by
    metis_tac[source_typing_ok_def] >>
  drule_all lower_vyper_runtime_unit_source_unit_ok >> strip_tac >>
  drule_all lower_vyper_runtime_unit_o1_shape_extras >> strip_tac >>
  drule_all lower_vyper_runtime_unit_defs_reach_uses >> strip_tac >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  `code_layout_valid vs0` by
    metis_tac[Abbr `vs0`, opt_entry_code_layout_valid] >>
  `source_typing_ok tops am txp` by
    (simp[Abbr `txp`] >> irule source_typing_ok_code_update >>
     qpat_assum `code_layout_valid vs0`
       (mp_tac o REWRITE_RULE [code_layout_valid_def]) >>
     simp[wordsTheory.dimword_def, venomLayoutTheory.dimindex_256] >>
     strip_tac >> irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
     qexists_tac `2 ** 255` >> fs[]) >>
  `initial_venom_state_rel tops am txp vs0` by
    metis_tac[Abbr `vs0`, Abbr `txp`, opt_entry_initial_venom_state_rel] >>
  `source_deployment_rel tops am txp` by
    fs[Abbr `txp`, source_deployment_rel_def, layouts_agree_def] >>
  qabbrev_tac `fmp = (n2w (MAX cplan.cp_initial_fmp
    (unit_alloca_budget unit.cu_context +
     32 * ctx_dload_count unit.cu_context)) : bytes32)` >>
  qspecl_then [`tops`, `rpolicy`, `unit`, `out`, `cplan`, `prog`, `prog'`, `es`,
               `fmp`] mp_tac raw_fmp_choice >>
  impl_tac >- simp[Abbr `fmp`] >>
  strip_tac >>
  `w2n vs0.vs_initial_fmp <= w2n fmp` by fs[Abbr `vs0`] >>
  drule_all lower_vyper_runtime_unit_correct_dispatched_with >> strip_tac >>
  `?shadow_ctx. !vs. raw_variant fmp vs vs0 ==>
     ?marks. source_unit_execution_correct_with shadow_ctx marks
       tops ret am txp unit vs` by
    (qexists_tac `shadow_ctx` >> rpt strip_tac >>
     `vs.vs_outcomes = MAP SND (call_trace es) /\
      vs.vs_call_ctx.cc_calldata =
        buffer_to_list (FST (HD es.contexts)).msgParams.data /\
      vs.vs_fmp = fmp /\ vs.vs_initial_fmp = fmp` by
       (qpat_assum `raw_variant _ _ _`
          (mp_tac o PURE_REWRITE_RULE [raw_variant_def, gas_variant_def]) >>
        disch_then (mp_tac o Q.AP_TERM
          `\s:venom_state. (s.vs_outcomes, s.vs_call_ctx.cc_calldata,
             s.vs_fmp, s.vs_initial_fmp)`) >>
        simp[Abbr `vs0`, opt_entry_state_def, entry_venom_state_def] >> metis_tac[]) >>
     `LENGTH vs.vs_call_ctx.cc_calldata < 2 ** 64` by
       metis_tac[Abbr `vs0`, raw_variant_opt_entry_calldata_bound] >>
     `initial_venom_state_rel tops am txp vs` by
       metis_tac[raw_variant_initial_venom_state_rel] >>
     qpat_x_assum `!am tx ret vs. _` (qspecl_then [`am`, `txp`, `ret`, `vs`] mp_tac) >>
     gvs[Abbr `txp`, dispatched_vyper_call_code_update]) >>
  qpat_x_assum `!fin policy tops deploy_bc runtime_bc rpolicy unit out prog prog' cp
    am tx txp ret es vs0 fmp r es'. _`
    (qspecl_then [`asm_opt_finalizer`, `policy`, `tops`, `deploy_bc`, `runtime_bc`,
      `rpolicy`, `unit`, `out`, `prog`, `prog'`, `cplan`, `am`, `tx`, `txp`, `ret`,
      `es`, `vs0`, `fmp`, `r`, `es'`] mp_tac) >>
  impl_tac >- (asm_simp_tac bool_ss [Abbr `vs0`, Abbr `txp`] >> metis_tac[]) >>
  strip_tac >>
  qspecl_then [`asm_opt_finalizer`, `policy`, `tops`, `deploy_bc`, `runtime_bc`,
      `rpolicy`, `unit`, `out`, `prog`, `prog'`, `cplan`, `am`, `tx`, `txp`, `ret`,
      `es`, `vs0`, `fmp`, `r`, `es'`] mp_tac vyper_call_correct_from_gas_link >>
  impl_tac >- asm_simp_tac bool_ss [Abbr `vs0`, Abbr `txp`] >>
  asm_simp_tac bool_ss [Abbr `txp`, call_result_rel_code_update]
QED

Theorem optimized_deploy_phases[local]:
  compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc,runtime_bc) ==>
  ?rpolicy dunit dout prog prog' cplan.
    deploy_phases policy tops (assemble prog,runtime_bc)
      (rpolicy,dunit,dout,prog,cplan) /\
    asm_opt_finalizer rpolicy prog = SOME prog' /\ deploy_bc = assemble prog'
Proof
  simp[compile_vyper_def] >> strip_tac >>
  drule compile_vyper_with_success_phases >> strip_tac >>
  gvs[finalize_codegen_def, AllCaseEqs()] >>
  qpat_assum `codegen_assembly rpolicy deploy_out.po_unit = SOME _`
    (strip_assume_tac o MATCH_MP codegen_assembly_success_shape) >>
  rename1 `generate_context_plan deploy_out.po_unit.cu_context = SOME cplan` >>
  rename1 `asm_opt_finalizer rpolicy prog = SOME prog'` >>
  qexistsl_tac [`rpolicy`, `deploy_unit`, `deploy_out`, `prog`, `prog'`, `cplan`] >>
  asm_simp_tac bool_ss [deploy_phases_def, o1PipelineCorrectTheory.o1_pipeline_def]
QED

val deploy_pipeline_gas_link_contract = concl e2eDeployCorrectnessTheory.deploy_pipeline_gas_link;

Theorem e2e_deploy_correctness_asm_opt_from_link:
  ^deploy_pipeline_gas_link_contract ==>
(
  !policy tops deploy_bc runtime_bc am tx es.
    compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) /\
    ~program_reads_self_code tops /\
    supported_program tops /\ supported_program_deploy tops /\
    constructor_call_free tops /\
    deploy_typing_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (creation_resource_starved es r es' \/
       deploy_call_result_rel tops runtime_bc am tx es r es')
)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule optimized_deploy_phases >> strip_tac >>
  rename1 `deploy_phases policy tops _ (_,dunit,dout,prog,cplan)` >>
  `asm_opt_finalizer IN accepted_finalizers` by simp[accepted_finalizers_def] >>
  drule_all compile_vyper_runtime_not_ef >> strip_tac >>
  qspec_then `es` strip_assume_tac run_call_total >>
  qexistsl_tac [`r`, `es'`] >> simp[] >>
  Cases_on `creation_resource_starved es r es'` >> simp[] >>
  `deploy_state_rel tops (assemble prog') am tx es` by fs[] >>
  `deploy_source_ok tops am tx` by simp[deploy_source_ok_def] >>
  drule_all deploy_source_ok_opt_code >> strip_tac >>
  drule deploy_raw_fmp_exists >>
  disch_then (qspecl_then [`prog'`, `es`] strip_assume_tac) >>
  qspecl_then [`asm_opt_finalizer`, `policy`, `tops`, `runtime_bc`, `rpolicy`,
    `dunit`, `dout`, `prog`, `prog'`, `cplan`, `am`, `tx`, `es`, `fmp`] mp_tac
    deploy_unit_execution_correct_raw_fmp >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qabbrev_tac `vs_out = opt_deploy_entry_state prog prog' cplan tops es` >>
  qpat_x_assum `!fin policy tops runtime_bc rpolicy dunit dout prog prog' cplan
    am tx es vs_out fmp r es'. _`
    (qspecl_then [`asm_opt_finalizer`, `policy`, `tops`, `runtime_bc`, `rpolicy`,
      `dunit`, `dout`, `prog`, `prog'`, `cplan`, `am`, `tx`, `es`, `vs_out`, `fmp`,
      `r`, `es'`] mp_tac) >>
  impl_tac >- (asm_simp_tac bool_ss [Abbr `vs_out`] >>
                qexists_tac `shadow_ctx` >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  qspecl_then [`asm_opt_finalizer`, `policy`, `tops`, `deploy_bc`, `runtime_bc`,
    `rpolicy`, `dunit`, `dout`, `prog`, `prog'`, `cplan`, `am`, `tx`,
    `tx with code := vs_out.vs_code`, `es`, `vs_out`, `fmp`, `r`, `es'`] mp_tac
    e2e_deploy_correct_from_gas_link >>
  impl_tac >- (asm_simp_tac bool_ss [Abbr `vs_out`] >>
                qpat_assum `~(?t. runtime_bc = _::t)` mp_tac >> simp[]) >>
  asm_simp_tac bool_ss [deploy_call_result_rel_code_update]
QED

Theorem opt_entry_codegen_asm_entry_rel[local]:
  !tops prog prog' am tx es cplan u.
  call_state_rel tops (assemble prog') am tx es /\ unit_shape_ok u ==>
  codegen_asm_entry_rel cplan prog (opt_entry_state prog prog' cplan es)
    (entry_asm_state (opt_entry_state prog prog' cplan es) es)
Proof
  rpt strip_tac >>
  simp[codegenEntrySimTheory.codegen_asm_entry_rel_def,
       entry_asm_state_def, shared_state_rel_def,
       venom_asm_terminal_rel_def, opt_entry_state_def,
       entry_venom_state_frame_fields, entry_venom_state_fresh] >>
  gvs[call_state_rel_def, frame_fresh_def, frame_tx_rel_def, world_rel_def,
      entry_venom_state_def, venomStateTheory.init_venom_state_def,
      context_memory_rel_def]
QED

Theorem opt_entry_asm_frame_rel[local]:
  !tops prog prog' am tx es cplan u.
  call_state_rel tops (assemble prog') am tx es /\ unit_shape_ok u /\
  assemble prog' <> [] ==>
  asm_frame_rel prog' (opt_entry_state prog prog' cplan es).vs_data_section es
    (entry_asm_state (opt_entry_state prog prog' cplan es) es with
       as_code := assemble prog' ++
         (opt_entry_state prog prog' cplan es).vs_data_section) es
Proof
  rpt strip_tac >>
  drule_then (qspecl_then [`u`, `cplan`] assume_tac)
    entry_venom_state_initial_ctx_rel >>
  drule_then (qspec_then `cplan` strip_assume_tac)
    entry_venom_state_installed_section >>
  fs[entry_venom_state_frame_fields] >>
  `account_already_created
     (lookup_account (FST (HD es.contexts)).msgParams.callee
        es.rollback.accounts)` by
    (`(FST (HD es.contexts)).msgParams.code <> []` by
       (strip_tac >> fs[]) >>
     gvs[call_state_rel_def, frame_fresh_def, frame_tx_rel_def, world_rel_def,
         vfmExecutionTheory.account_already_created_def,
         listTheory.NULL_EQ]) >>
  `asm_frame_rel prog' (entry_venom_state prog' cplan es).vs_data_section es
     (entry_asm_state (entry_venom_state prog' cplan es) es) es` by
    metis_tac[asm_frame_rel_entry] >>
  `entry_asm_state (opt_entry_state prog prog' cplan es) es with
     as_code := assemble prog' ++
       (opt_entry_state prog prog' cplan es).vs_data_section =
   entry_asm_state (entry_venom_state prog' cplan es) es` by
    (qpat_assum `_ = assemble prog' ++ _` (fn th => REWRITE_TAC [GSYM th]) >>
     simp[opt_entry_state_def, entry_asm_state_def] >>
     simp[entry_venom_state_def] >>
     qpat_x_assum `_ = assemble prog' ++ _` (ACCEPT_TAC o SYM)) >>
  qpat_x_assum `entry_asm_state _ _ with as_code := _ = _` SUBST1_TAC >>
  fs[opt_entry_state_def, entry_venom_state_frame_fields]
QED

Theorem opt_entry_fields[local]:
  !tops prog prog' am tx es cplan vs.
    call_state_rel tops (assemble prog') am tx es /\
    vs = opt_entry_state prog prog' cplan es ==>
    vs.vs_initial_fmp = n2w cplan.cp_initial_fmp /\
    vs.vs_call_ctx.cc_calldata =
      buffer_to_list (FST (HD es.contexts)).msgParams.data /\
    vs.vs_fmp = vs.vs_initial_fmp /\
    vs.vs_call_ctx.cc_static = tx.is_static /\
    o1_initial_state_ok vs /\
    vs.vs_code = assemble prog ++ vs.vs_data_section
Proof
  rpt strip_tac >> gvs[] >>
  simp[opt_entry_state_def, entry_venom_state_frame_fields,
       entry_venom_state_fresh, o1_initial_state_ok_def] >>
  gvs[call_state_rel_def, frame_fresh_def, frame_tx_rel_def, world_rel_def,
      entry_venom_state_def, opt_entry_state_def]
QED

Theorem opt_entry_data_section_bound[local]:
  !tops prog prog' am tx es cplan policy unit.
    call_state_rel tops (assemble prog') am tx es /\
    codegen_assembly policy unit = SOME prog /\ unit_shape_ok unit /\
    assemble prog <> [] ==>
    LENGTH (opt_entry_state prog prog' cplan es).vs_data_section <
      dimword (:256) DIV 2
Proof
  rpt strip_tac >>
  drule_all opt_entry_code_layout_valid >>
  disch_then (qspec_then `cplan` assume_tac) >>
  qabbrev_tac `vs = opt_entry_state prog prog' cplan es` >>
  `vs.vs_code = assemble prog ++ vs.vs_data_section` by
    simp[Abbr `vs`, opt_entry_state_def, entry_venom_state_frame_fields] >>
  `0 < LENGTH (assemble prog)` by
    (Cases_on `assemble prog` >> fs[]) >>
  fs[code_layout_valid_def] >> decide_tac
QED

Theorem selected_raw_memory[local]:
  lower_vyper_runtime_unit tops rp = SOME unit /\
  o1_source_unit_ok unit /\ ~ctx_has_dalloca unit.cu_context /\
  w2n vs.vs_initial_fmp <= w2n vs.vs_fmp /\
  initial_venom_state_rel tops am tx vs /\ code_layout_valid vs /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME "__entry" /\
  (!n. mem_safe_blocks n unit.cu_context fn
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>)) /\
  (!n. ptr_safe_blocks D 0 n unit.cu_context fn [] FEMPTY entry_taint
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>)) ==>
  raw_unit_memory_ok unit.cu_context vs /\
  ptr_discipline 0 unit.cu_context vs /\ taint_within D unit.cu_context vs /\
  mem_inv dload_offset_ok unit.cu_context vs /\
  mem_inv dload_headroom_ok unit.cu_context vs /\
  mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
    s.vs_code = vs.vs_code /\ s.vs_data_section = vs.vs_data_section)
    unit.cu_context vs
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`tops`, `rp`, `unit`, `am`, `tx`, `vs`, `fn`, `"__entry"`, `D`]
            lower_vyper_runtime_unit_memory_ok) >>
  impl_tac >- fs[] >> strip_tac >> simp[] >>
  conj_tac
  >- metis_tac[lower_vyper_runtime_unit_dload_offset_ok] >>
  conj_tac
  >- metis_tac[lower_vyper_runtime_unit_dload_headroom_ok] >>
  metis_tac[lower_vyper_runtime_unit_dload_in_section]
QED

Theorem opt_entry_focus_setup[local]:
  fin IN accepted_finalizers /\
  fin rpolicy prog = SOME prog' /\
  call_state_rel tops (assemble prog') am tx es /\
  codegen_assembly rpolicy unit = SOME prog /\ unit_shape_ok unit /\
  vs0 = opt_entry_state prog prog' cplan es ==>
  code_layout_valid vs0 /\ o1_initial_state_ok vs0 /\
  vs0.vs_fmp = vs0.vs_initial_fmp /\
  vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
  LENGTH vs0.vs_data_section < dimword (:256) DIV 2 /\
  codegen_asm_entry_rel cplan prog vs0 (entry_asm_state vs0 es) /\
  asm_frame_rel_tail [] prog' vs0.vs_data_section es
    (entry_asm_state vs0 es with as_code := assemble prog' ++ vs0.vs_data_section)
    es
Proof
  strip_tac >>
  drule codegenAsmProgOkTheory.codegen_assembly_nonempty >> strip_tac >>
  `assemble prog' <> []` by
    (qpat_x_assum `fin IN accepted_finalizers` mp_tac >>
     simp[accepted_finalizers_def] >> strip_tac >> gvs[] >>
     metis_tac[codegen_assembly_finalizer_nonempty]) >>
  drule_all opt_entry_fields >> strip_tac >>
  rpt conj_tac >> gvs[asm_frame_rel_tail_nil] >>
  metis_tac[opt_entry_code_layout_valid, opt_entry_data_section_bound,
            opt_entry_codegen_asm_entry_rel, opt_entry_asm_frame_rel]
QED

Theorem call_certificate_raw_entry_boundary[local]:
  lower_vyper_runtime_unit tops rp = SOME unit /\
  o1_source_unit_ok unit /\ ~ctx_has_dalloca unit.cu_context /\
  initial_venom_state_rel tops am tx vs /\ code_layout_valid vs /\
  w2n vs.vs_initial_fmp <= w2n vs.vs_fmp /\
  source_unit_execution_correct_with shadow_ctx marks tops ret am tx unit vs /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME func ==>
  ?D fuel extra.
    dead_wf D /\
    (!fn inst s. raw_reachable vs unit.cu_context fn inst s /\
       gas_cut (MIN (LENGTH marks) (LENGTH vs.vs_gas_readings)) vs s ==>
       inst_dload_in_section inst s) /\
    o1_safe_upto D 0 (MIN (LENGTH marks) (LENGTH vs.vs_gas_readings))
      unit.cu_context vs /\
    MAP (\key. key IN gas_explicit_sites unit.cu_context shadow_ctx)
      (gas_events_blocks fuel unit.cu_context func
        (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                  vs_inst_idx := 0|>)) = marks ++ extra
Proof
  strip_tac >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  drule vyperCompilerTheory.lowering_context_ok_bridge >> strip_tac >>
  drule lower_vyper_runtime_unit_raw_defaults >> strip_tac >>
  `EVERY (\f. ALL_DISTINCT (fn_labels f)) unit.cu_context.ctx_functions` by
    fs[EVERY_MEM] >>
  `?P. EVERY (\f. fn_ptr_ok P f /\ fn_ptr_ok P (reachable_fn f))
       unit.cu_context.ctx_functions` by
    (drule lower_vyper_runtime_unit_fn_ptr_ok >> simp[EVERY_MEM] >>
     strip_tac >> qexists_tac `P` >> simp[]) >>
  `reserved_intervals_wf unit.cu_context.ctx_global_reserved` by
    (drule lower_vyper_runtime_unit_global_reserved >>
     simp[staticLayoutDefsTheory.reserved_intervals_wf_def]) >>
  `fixed_region_reserved 0 unit.cu_context /\
   fmp_free_ctx unit.cu_context` by
    simp[fixed_region_reserved_def, source_fmp_free] >>
  `mem_inv dload_headroom_ok unit.cu_context vs` by
    (irule lower_vyper_runtime_unit_dload_headroom_ok >> simp[] >>
     metis_tac[]) >>
  `!H:(bool # bytes32 # type_value) list # num list.
     dead_wf (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))` by
    (gen_tac >> simp[cx_dead_def, initial_evaluation_context_def] >>
     MATCH_ACCEPT_TAC
       (SIMP_RULE (srw_ss()) [external_call_dead_def]
         (Q.INST [`src` |-> `(INL NoneV, am, [])`] external_call_dead_wf))) >>
  qpat_x_assum `source_unit_execution_correct_with _ _ _ _ _ _ _ _` mp_tac >>
  simp[source_unit_execution_correct_with_def] >> strip_tac >> gvs[] >>
  rename1 `lookup_function "__entry" unit.cu_context.ctx_functions = SOME func` >>
  `?bb. lookup_block "__entry" func.fn_blocks = SOME bb` by
    (gvs[fn_entry_label_def, entry_block_def, AllCaseEqs()] >>
     Cases_on `func.fn_blocks` >> gvs[lookup_block_def, FIND_thm]) >>
  `phi_prefix_length bb.bb_instructions = 0` by
    (irule lower_vyper_runtime_unit_block_phi >> metis_tac[]) >>
  all_tac
  >~ [`gas_origin_ptr_focus _ _ _ _`]
  >- suspend "focus"
  >~ [`gas_origin_ptr_focus _ _ _ _`]
  >- suspend "focus"
  >> suspend "exit"
QED

Resume call_certificate_raw_entry_boundary[focus]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  qabbrev_tac `D = cx_dead H
    (initial_evaluation_context am.sources am.layouts tx NONE)` >>
  `dead_wf D` by
    (simp[Abbr `D`] >>
     first_assum (fn th => ACCEPT_TAC (Q.SPEC `H` th))) >>
  `o1_safe_upto D 0 (MIN (LENGTH marks) (LENGTH vs.vs_gas_readings))
     unit.cu_context vs` by
    (irule gas_origin_ptr_focus_o1_safe_upto >> simp[] >> metis_tac[]) >>
  `!fn inst s. raw_reachable vs unit.cu_context fn inst s /\
     gas_cut (MIN (LENGTH marks) (LENGTH vs.vs_gas_readings)) vs s ==>
     inst_dload_in_section inst s` by
    (drule gas_origin_ptr_focus_dload_upto >> simp[] >> metis_tac[]) >>
  drule fragGasOriginPtrTheory.gas_origin_ptr_focus_origin >> strip_tac >>
  drule_at (Pat `gas_origin_focus _ _ _ _ _ _`)
    gas_origin_focus_entry_events_prefix >> simp[] >> strip_tac >>
  qexistsl_tac [`D`, `fuel`, `extra`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume call_certificate_raw_entry_boundary[exit]:
  rpt strip_tac >>
  drule_all selected_run >> strip_tac >>
  `valid_horizon (initial_evaluation_context am.sources am.layouts tx NONE)
     (initial_state am []) (storage_trace_horizon obs) obs` by
    metis_tac[storage_trace_domain_def] >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon obs` mp_tac) >>
  simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `ptr_safe_blocks D` >>
  `raw_unit_memory_ok unit.cu_context vs /\
   ptr_discipline 0 unit.cu_context vs /\ taint_within D unit.cu_context vs /\
   mem_inv dload_offset_ok unit.cu_context vs /\
   mem_inv dload_headroom_ok unit.cu_context vs /\
   mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
     s.vs_code = vs.vs_code /\ s.vs_data_section = vs.vs_data_section)
     unit.cu_context vs` by
    (irule selected_raw_memory >> metis_tac[]) >>
  `mem_inv raw_mem_ok unit.cu_context vs` by
    (qpat_x_assum `raw_unit_memory_ok _ _` mp_tac >>
     simp[unitTransformDefsTheory.raw_unit_memory_ok_def, mem_inv_def,
          raw_mem_ok_def]) >>
  `o1_src_inv D unit.cu_context vs` by
    (simp[o1_src_inv_def] >> metis_tac[]) >>
  drule_all o1_src_inv_ptr_safe_upto >> strip_tac >>
  `!fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
     inst_dload_in_section inst s` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\ _) _ _`
       (drule o CONJUNCT2 o REWRITE_RULE [mem_inv_raw_reachable]) >>
     simp[]) >>
  drule_at (Pat `gas_origin_path _ _ _ _ _ _ _`)
    gas_origin_path_entry_events >> simp[] >> strip_tac >>
  qexistsl_tac [`D`, `fuel'`, `[]`] >> simp[Abbr `D`] >>
  rpt strip_tac >> first_x_assum irule >> goal_assum (drule_at Any)
QED

Finalise call_certificate_raw_entry_boundary

Theorem guard_source_focus_setup[local]:
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

Theorem guard_marked_focus_family[local]:
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

Theorem guard_focus_callback_inputs[local]:
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

Theorem gas_mask_recorded_partition[local]:
  LENGTH marks = LENGTH slots ==>
  PERM
    (MAP THE (FILTER IS_SOME (MAP SND (FILTER FST (ZIP (marks, slots))))) ++
     MAP THE (FILTER IS_SOME
       (MAP SND (FILTER ($~ o FST) (ZIP (marks, slots))))))
    (MAP THE (FILTER IS_SOME slots))
Proof
  strip_tac >>
  rewrite_tac[GSYM MAP_APPEND] >> irule PERM_MAP >>
  rewrite_tac[GSYM FILTER_APPEND_DISTRIB] >> irule PERM_FILTER >>
  rewrite_tac[GSYM MAP_APPEND] >>
  irule PERM_TRANS >> qexists_tac `MAP SND (ZIP (marks, slots))` >>
  conj_tac
  >- (irule PERM_MAP >> simp[PERM_SYM, PERM_SPLIT]) >>
  simp[MAP_ZIP]
QED

Theorem gas_mask_filling_extension[local]:
  LENGTH marks = LENGTH slots /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w)
    (MAP SND (FILTER FST (ZIP (marks, slots)))) gobs ==>
  ?raw.
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) slots raw /\
    !tail. gas_explicit marks (raw ++ tail) = gobs
Proof
  qid_spec_tac `gobs` >> qid_spec_tac `slots` >>
  Induct_on `marks`
  >- simp[ZIP] >>
  rpt gen_tac >> rename1 `gas_explicit (mark :: marks) _` >>
  Cases_on `slots` >- simp[] >>
  rename1 `ZIP (_, slot :: slots)` >> Cases_on `mark`
  >- (Cases_on `gobs` >> simp[ZIP] >>
      rename1 `gas_explicit _ _ = w :: gs` >> strip_tac >>
      first_x_assum drule_all >> strip_tac >>
      rename1 `LIST_REL _ slots raw` >>
      qexists_tac `w :: raw` >>
      simp[gas_explicit_cons]) >>
  simp[ZIP] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  rename1 `LIST_REL _ slots raw` >>
  qexists_tac `(case slot of NONE => 0w | SOME w => w) :: raw` >>
  Cases_on `slot` >> simp[gas_explicit_cons]
QED

Theorem gas_mask_projection[local]:
  !flags slots unused readings (P : bytes32 list -> bool).
    LENGTH flags = LENGTH slots /\
    PERM (MAP THE (FILTER IS_SOME slots) ++ unused) readings /\
    (!raw tail.
       LIST_REL (\slot w. slot = NONE \/ slot = SOME w) slots raw ==>
       P (gas_explicit flags raw ++ tail)) ==>
    ?source_slots source_unused.
      PERM (MAP THE (FILTER IS_SOME source_slots) ++ source_unused) readings /\
      !gs tail.
        LIST_REL (\slot w. slot = NONE \/ slot = SOME w) source_slots gs ==>
        P (gs ++ tail)
Proof
  rpt gen_tac >> strip_tac >>
  drule gas_mask_recorded_partition >> strip_tac >>
  qexistsl_tac
    [`MAP SND (FILTER FST (ZIP (flags, slots)))`,
     `MAP THE (FILTER IS_SOME
        (MAP SND (FILTER ($~ o FST) (ZIP (flags, slots))))) ++ unused`] >>
  conj_tac
  >- (rewrite_tac[APPEND_ASSOC] >> irule PERM_TRANS >>
      qexists_tac `MAP THE (FILTER IS_SOME slots) ++ unused` >>
      conj_tac >- simp[PERM_APPEND_IFF] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_all gas_mask_filling_extension >> strip_tac >>
  qpat_x_assum `!raw tail. LIST_REL _ slots raw ==> _`
    (qspecl_then [`raw`, `tail`] mp_tac) >>
  simp[] >>
  qpat_x_assum `!tail. gas_explicit flags (raw ++ tail) = gs`
    (qspec_then `[]` mp_tac) >> simp[]
QED

Theorem gas_mask_padded_split[local]:
  LENGTH (marks ++ rest) = LENGTH raw ==>
  gas_explicit (marks ++ rest) raw ++ tail =
    gas_explicit marks (raw ++ pad) ++
      (gas_explicit rest (DROP (LENGTH marks) (raw ++ pad)) ++ tail)
Proof
  strip_tac >>
  `gas_explicit (marks ++ rest) raw =
     gas_explicit (marks ++ rest) (raw ++ pad)` by
    (PURE_REWRITE_TAC[gas_explicit_def, gasOracleReplayTheory.gas_prefix_def] >>
     qpat_x_assum `LENGTH (marks ++ rest) = LENGTH raw` SUBST1_TAC >>
     PURE_REWRITE_TAC[GSYM APPEND_ASSOC, rich_listTheory.TAKE_LENGTH_APPEND] >>
     simp[]) >>
  pop_assum SUBST1_TAC >>
  simp[gas_explicit_append, APPEND_ASSOC]
QED

Theorem call_pipeline_gas_link_from_frozen_focus:
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
                     Abort ExHalt_abort u)))
  ==>
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
     `~program_reads_self_code tops` by
       (qpat_assum `fin = asm_opt_finalizer ==> ~program_reads_self_code tops`
          (fn exclude => qpat_assum `fin = asm_opt_finalizer`
            (ACCEPT_TAC o MP exclude))) >>
     drule_all lower_vyper_runtime_unit_sym_src_ok >>
     strip_tac >> asm_rewrite_tac[]) >>
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

(* The request cut can include the entry state even when the gas cut is empty. *)
Theorem request_cut_can_extend_past_gas_cut:
  !vs:venom_state.
    request_cut (LENGTH vs.vs_requests) vs /\
    ~gas_cut (MIN (LENGTH ([]:bool list)) (LENGTH vs.vs_gas_readings)) vs vs
Proof
  simp[request_cut_def, gas_cut_def]
QED

val frozen_call_focus_contract =
  boolSyntax.lhand (concl call_pipeline_gas_link_from_frozen_focus);

Theorem vyper_call_correct_asm_opt_from_frozen_focus:
  ^frozen_call_focus_contract ==>
(
  !policy tops deploy_bc runtime_bc am tx ret es.
    compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) /\
    ~program_reads_self_code tops /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    dispatched_vyper_call tops tx
      (buffer_to_list (FST (HD es.contexts)).msgParams.data) ret /\
    LENGTH (call_trace es) < 2 ** 64
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       call_result_rel tops am tx es r es')
)
Proof
  disch_then (ACCEPT_TAC o MP vyper_call_correct_asm_opt_from_link o
    MP call_pipeline_gas_link_from_frozen_focus)
QED

Theorem shadow_root_single[local]:
  es.contexts = [(ctxt, rb)] ==>
  (shadow_root es).contexts =
    [(ctxt with msgParams updated_by
        (\mp. mp with outputTo := Memory <| offset := 0; size := 0 |>), rb)] /\
  (shadow_root es).txParams = es.txParams /\
  (shadow_root es).rollback = es.rollback /\
  (shadow_root es).originalAccounts = es.originalAccounts /\
  (shadow_root es).msdomain = es.msdomain /\
  call_trace (shadow_root es) = call_trace es /\
  gas_readings (shadow_root es) = gas_readings es
Proof
  strip_tac >>
  `frame_obs (shadow_root es) = frame_obs es` by
    (irule shadow_root_frame_obs >> simp[]) >>
  asm_rewrite_tac[call_trace_def, gas_readings_def] >>
  simp[shadow_root_def, shadow_root_contexts_def]
QED

Theorem opt_deploy_codegen_asm_entry_rel[local]:
  !tops prog prog' am tx es cplan u.
  deploy_state_rel tops (assemble prog') am tx es /\ unit_shape_ok u ==>
  codegen_asm_entry_rel cplan prog (opt_deploy_entry_state prog prog' cplan tops es)
    (entry_asm_state (opt_deploy_entry_state prog prog' cplan tops es)
       (shadow_root es))
Proof
  rpt strip_tac >> fs[deploy_state_rel_def] >>
  drule shadow_root_single >> strip_tac >>
  simp[codegenEntrySimTheory.codegen_asm_entry_rel_def, entry_asm_state_def, shared_state_rel_def,
       venom_asm_terminal_rel_def, opt_deploy_entry_state_def,
       opt_entry_state_def, entry_venom_state_frame_fields,
       entry_venom_state_fresh] >>
  gvs[entry_venom_state_def, venomStateTheory.init_venom_state_def, contextCodegenRelTheory.context_memory_rel_def]
QED

Theorem opt_deploy_asm_frame_rel[local]:
  !tops prog prog' am tx es cplan u.
  deploy_state_rel tops (assemble prog') am tx es /\ unit_shape_ok u /\
  assemble prog' <> [] ==>
  asm_frame_rel prog'
    (opt_deploy_entry_state prog prog' cplan tops es).vs_data_section
    (shadow_root es)
    (entry_asm_state (opt_deploy_entry_state prog prog' cplan tops es)
       (shadow_root es) with
       as_code := assemble prog' ++
         (opt_deploy_entry_state prog prog' cplan tops es).vs_data_section)
    (shadow_root es)
Proof
  rpt strip_tac >>
  `wf_state (shadow_root es)` by fs[deploy_state_rel_def, shadow_root_wf_state] >>
  fs[deploy_state_rel_def] >>
  drule shadow_root_single >> strip_tac >>
  `es.txParams.blockNumber < dimword (:256)` by
    (fs[e2eDefsTheory.tx_block_fields_rel_def, tx_env_ok_def] >>
     irule lt_dimword_256 >> qexists_tac `255` >> simp[]) >>
  simp[asm_frame_rel_def, asm_evm_rel_def, entry_asm_state_def,
       opt_deploy_entry_state_def, opt_entry_state_def, data_suffix_assemble,
       asm_pc_to_offset_zero, entry_venom_state_frame_fields] >>
  gvs[entry_venom_state_def, venomStateTheory.init_venom_state_def, wordsTheory.w2n_n2w, listTheory.DROP_APPEND] >>
  rewrite_tac[GSYM CONJ_ASSOC]
QED

Theorem deploy_selected_producer_inputs[local]:
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  deploy_source_ok tops am tx /\
  deploy_unit_execution_correct_at marks tops runtime_bc am tx dunit vs /\
  deploy_storage_ok tops am tx vs.vs_outcomes
    (gas_explicit marks vs.vs_gas_readings ++ tail) /\
  ~deploy_source_exempt tops
    (load_contract (SOME vs.vs_outcomes)
      (gas_explicit marks vs.vs_gas_readings ++ tail) am tx [(NONE, tops)] []) /\
  raw_unit_memory_ok dunit.cu_context vs /\
  ptr_discipline (imm_len tops) dunit.cu_context vs /\
  taint_within D dunit.cu_context vs /\
  mem_inv dload_offset_ok dunit.cu_context vs /\
  mem_inv dload_headroom_ok dunit.cu_context vs ==>
  (?fuel. terminates (run_context fuel dunit.cu_context vs)) /\
  o1_pre_walk_inv D dunit.cu_context vs /\
  mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                            s.vs_code = vs.vs_code /\
                            s.vs_data_section = vs.vs_data_section)
    dunit.cu_context vs
Proof
  strip_tac >>
  drule_all deploy_unit_shape_ok >> strip_tac >>
  drule_all deploy_unit_defs_reach_uses >> strip_tac >>
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit` by
    fs[deploy_phases_def] >>
  drule lower_vyper_deploy_unit_context_ok >> strip_tac >>
  drule lower_vyper_deploy_unit_entry >> strip_tac >>
  drule_all deploy_unit_exit_safe_runs >> strip_tac >>
  conj_tac >- metis_tac[deploy_venom_result_rel_terminates] >>
  conj_tac
  >- (`mem_inv raw_mem_ok dunit.cu_context vs` by
        (qpat_x_assum `raw_unit_memory_ok _ _` mp_tac >>
         simp[unitTransformDefsTheory.raw_unit_memory_ok_def, mem_inv_def,
              raw_mem_ok_def]) >>
      irule o1_source_pre_walk_inv >>
      simp[o1_src_inv_def] >> metis_tac[source_fmp_free]) >>
  `!fn inst s. raw_reachable vs dunit.cu_context fn inst s ==>
     inst_dload_in_section inst s` by
    (rpt strip_tac >> irule lowered_unit_dload_in_section >> metis_tac[]) >>
  simp[mem_inv_raw_reachable] >> metis_tac[raw_reachable_code_data]
QED

Theorem deploy_focus_frame_inputs[local]:
  deploy_phases policy tops (assemble prog, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  deploy_state_rel tops (assemble prog') am tx es /\
  vs_out = opt_deploy_entry_state prog prog' cplan tops es /\
  deploy_source_ok tops am (tx with code := vs_out.vs_code) /\
  fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
  unit_shape_ok dout.po_unit /\
  run_call es = SOME (r, es') /\ ~creation_resource_starved es r es' ==>
  o1_run_state_ok vs_out /\
  vs_out.vs_code = assemble prog ++ vs_out.vs_data_section /\
  LENGTH vs_out.vs_data_section < dimword (:256) DIV 2 /\
  vs_out.vs_outcomes = MAP SND (call_trace es) /\
  codegen_asm_entry_rel cplan prog vs_out
    (entry_asm_state vs_out (shadow_root es)) /\
  asm_frame_rel_tail [] prog' vs_out.vs_data_section (shadow_root es)
    (entry_asm_state vs_out (shadow_root es) with
      as_code := assemble prog' ++ vs_out.vs_data_section) (shadow_root es) /\
  gas_readings (shadow_root es) = gas_readings es /\
  ?sr sg. run_call (shadow_root es) = SOME (sr,sg) /\
          ~frame_resource_starved (shadow_root es) sr sg
Proof
  strip_tac >>
  `codegen_assembly rpolicy dout.po_unit = SOME prog` by fs[deploy_phases_def] >>
  `assemble prog <> []` by
    metis_tac[codegen_assembly_terminal_witness, terminal_witness_assemble_nonempty] >>
  `assemble prog' <> []` by
    (Cases_on `fin = K SOME` >- gvs[] >>
     `fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
     metis_tac[codegen_assembly_finalizer_nonempty]) >>
  `?ctxt rb. es.contexts = [(ctxt,rb)] /\ ~ctxt.msgParams.static` by
    fs[deploy_state_rel_def] >>
  drule_all deploy_shadow_run_not_starved >> strip_tac >>
  `frame_obs (shadow_root es) = frame_obs es` by
    (irule shadow_root_frame_obs >> simp[]) >>
  `vs_out.vs_fmp = vs_out.vs_initial_fmp /\
   o1_initial_state_ok vs_out /\ ~vs_out.vs_call_ctx.cc_static /\
   vs_out.vs_code = assemble prog ++ vs_out.vs_data_section /\
   vs_out.vs_outcomes = MAP SND (call_trace es)` by
    simp[opt_deploy_entry_state_def, opt_entry_state_def,
         entry_venom_state_def, venomStateTheory.init_venom_state_def,
         o1_initial_state_ok_def] >>
  `code_layout_valid vs_out` by
    (Q.SUBGOAL_THEN
      `vs_out with <|vs_gas_readings := vs_out.vs_gas_readings;
          vs_fmp := vs_out.vs_fmp; vs_initial_fmp := vs_out.vs_fmp|> = vs_out`
      (fn th => ONCE_REWRITE_TAC [GSYM th])
     >- simp[venomStateTheory.venom_state_component_equality] >>
     qpat_x_assum `vs_out = _` SUBST_ALL_TAC >>
     irule deploy_raw_entry_code_layout >> metis_tac[]) >>
  `LENGTH vs_out.vs_data_section < dimword (:256) DIV 2` by
    (`0 < LENGTH (assemble prog)` by (Cases_on `assemble prog` >> fs[]) >>
     qpat_assum `code_layout_valid vs_out`
       (strip_assume_tac o REWRITE_RULE [code_layout_valid_def]) >>
     qpat_assum `LENGTH vs_out.vs_code <= _` mp_tac >>
     qpat_assum `vs_out.vs_code = assemble prog ++ _`
       (fn th => REWRITE_TAC [th, listTheory.LENGTH_APPEND]) >>
     qpat_assum `0 < LENGTH (assemble prog)` mp_tac >>
     decide_tac) >>
  simp[o1_run_state_ok_def, asm_frame_rel_tail_nil, gas_readings_def] >>
  metis_tac[opt_deploy_codegen_asm_entry_rel, opt_deploy_asm_frame_rel]
QED

Theorem deploy_pipeline_gas_link_from_frozen_focus:
  (!rpolicy unit out vs0 cpl prog fin prog' es0 nm entryfn lbl fmp markf
    lo (project : (string # num) -> bool) result final.
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  o1_run_state_ok vs0 /\ unit_shape_ok out.po_unit /\
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
           code_end_offset_ok (raw_reachable vs0) out.po_unit.cu_context) /\
        o1_lowered_inv out.po_unit.cu_context vs0) ==>
  !fin policy tops runtime_bc rpolicy dunit dout prog prog' cplan am tx es vs_out fmp r es'.
    fin IN accepted_finalizers /\
    fin rpolicy prog = SOME prog' /\
    (fin = asm_opt_finalizer ==> ~program_reads_self_code tops) /\
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_state_rel tops (assemble prog') am tx es /\
    vs_out = opt_deploy_entry_state prog prog' cplan tops es /\
    deploy_source_ok tops am (tx with code := vs_out.vs_code) /\
    w2n vs_out.vs_initial_fmp <= w2n fmp /\
    w2n fmp < 2 ** 254 /\
    unit_alloca_budget dunit.cu_context +
      32 * ctx_dload_count dunit.cu_context <= w2n fmp /\
    (?shadow_ctx. !vs.
       raw_variant fmp vs vs_out ==>
       ?marks. deploy_unit_execution_correct_with shadow_ctx marks
         tops runtime_bc am (tx with code := vs_out.vs_code) dunit vs) /\
    run_call es = SOME (r, es') /\
    ~creation_resource_starved es r es' ==>
    gas_readings_rel (gas_readings es)
      (\gs. deploy_storage_ok tops am (tx with code := vs_out.vs_code) (MAP SND (call_trace es)) gs ==>
            ?vs marks tail.
              gs = gas_explicit marks vs.vs_gas_readings ++ tail /\
              raw_variant fmp vs vs_out /\
              (~deploy_source_exempt tops
                 (load_contract (SOME vs.vs_outcomes)
                   (gas_explicit marks vs.vs_gas_readings ++ tail)
                   am (tx with code := vs_out.vs_code) [(NONE, tops)] []) ==>
               !D. dead_wf D ==>
                 raw_unit_memory_ok dunit.cu_context vs /\
                 ptr_discipline (imm_len tops) dunit.cu_context vs /\
                 taint_within D dunit.cu_context vs /\
                 mem_inv dload_offset_ok dunit.cu_context vs /\
                 mem_inv dload_headroom_ok dunit.cu_context vs ==>
                 ctx_sim D dunit.cu_context dout.po_unit.cu_context vs
                   vs_out /\
                 (fin = asm_opt_finalizer ==>
                    code_end_offset_ok (raw_reachable vs_out) dout.po_unit.cu_context) /\
                 o1_lowered_inv dout.po_unit.cu_context
                   vs_out) /\
              deploy_unit_execution_correct_at marks tops runtime_bc am (tx with code := vs_out.vs_code) dunit vs)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
   o1PipelineCorrect$o1_pipeline rpolicy dunit = SOME dout /\
   codegen_assembly rpolicy dout.po_unit = SOME prog /\
   generate_context_plan dout.po_unit.cu_context = SOME cplan` by
    fs[deploy_phases_def] >>
  drule_all deploy_unit_shape_ok >> strip_tac >>
  drule_all deploy_unit_defs_reach_uses >> strip_tac >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  drule_all deploy_focus_frame_inputs >> strip_tac >>
  rename1 `run_call (shadow_root es) = SOME (sr,sg)` >>
  drule lower_vyper_deploy_unit_entry >> strip_tac >>
  rename1 `lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME func` >>
  drule_all deploy_raw_fmp_focus_mask_entry >>
  disch_then (qx_choose_then `markf` assume_tac) >>
  `fn_entry_label func = SOME "__deploy"` by
    (qpat_assum `!gs. deploy_unit_execution_correct_with _ _ _ _ _ _ _ _ /\ _`
       (mp_tac o REWRITE_RULE [deploy_unit_execution_correct_with_def] o
        CONJUNCT1 o Q.SPEC `[]`) >>
     disch_then (qx_choosel_then [`df`, `shadow_df`] strip_assume_tac) >>
     `df = func` by fs[] >> fs[]) >>
  `fin = asm_opt_finalizer ==>
     label_flow_ok dunit.cu_context /\
     (!fn inst. MEM fn dunit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
                ~MEM (Label "code_end") inst.inst_operands) /\
     EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                       ds.ds_items) dunit.cu_data_segment /\
     ((?fn inst. MEM fn dunit.cu_context.ctx_functions /\
                 MEM inst (fn_insts fn) /\
                 MEM (Label "runtime_begin") inst.inst_operands) ==>
      EXISTS (\ds. ds.ds_label = "runtime_begin") dunit.cu_data_segment) /\
     LENGTH vs_out.vs_data_section < dimword (:256) DIV 2` by
    (disch_tac >>
     qspecl_then [`policy`, `tops`, `assemble prog`, `runtime_bc`,
                  `rpolicy`, `dunit`, `dout`, `prog`, `cplan`] mp_tac
       deploySymSrcUnitTheory.lower_vyper_deploy_unit_sym_src_ok >>
     impl_tac >- fs[deploy_source_ok_def] >>
     strip_tac >> asm_rewrite_tac[]) >>
  qpat_x_assum `!rpolicy unit out vs0 cpl prog fin prog' es0 nm entryfn lbl fmp markf
                   lo project result final. _` mp_tac >>
  disch_then (mp_tac o Q.SPECL [
    `rpolicy`, `dunit`, `dout`, `vs_out`, `cplan`, `prog`, `fin`, `prog'`,
    `shadow_root es`, `"__deploy"`, `func`, `"__deploy"`, `fmp`, `markf`,
    `imm_len tops`, `\key. key IN gas_explicit_sites dunit.cu_context shadow_ctx`,
    `sr`, `sg` ]) >>
  impl_tac
  >- (BETA_TAC >> asm_rewrite_tac[] >> gen_tac >>
      qpat_assum `!gs. deploy_unit_execution_correct_with _ _ _ _ _ _ _ _ /\ _`
        (mp_tac o CONJUNCT2 o Q.SPEC `gs`) >>
      simp[]) >>
  disch_then (qx_choosel_then [`raw_slots`, `sites`, `unused`] strip_assume_tac) >>
  qabbrev_tac `project = MAP
    (\key. key IN gas_explicit_sites dunit.cu_context shadow_ctx) sites` >>
  rewrite_tac[gas_readings_rel_def] >>
  irule gas_mask_projection >>
  qexistsl_tac [`project`, `raw_slots`, `unused`] >>
  `LENGTH project = LENGTH raw_slots` by simp[Abbr `project`] >>
  `PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es)` by
    (qpat_assum `gas_readings (shadow_root es) = gas_readings es`
       (fn th => once_rewrite_tac [GSYM th]) >> first_assum ACCEPT_TAC) >>
  qpat_assum `LENGTH project = LENGTH raw_slots` (fn lengths =>
    qpat_assum `PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es)`
      (fn readings => rewrite_tac [lengths, readings])) >>
  qx_genl_tac [`raw`, `tail`] >> strip_tac >> BETA_TAC >>
  qpat_x_assum `!raw. LIST_REL _ raw_slots raw ==> _` (qspec_then `raw` mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `rest` assume_tac) assume_tac) >>
  qabbrev_tac `vs = vs_out with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp;
                                    vs_initial_fmp := fmp|>` >>
  qabbrev_tac `marks = markf (raw ++ [0w])` >>
  qabbrev_tac `suffix = gas_explicit rest (DROP (LENGTH marks) (raw ++ [0w])) ++ tail` >>
  `gas_explicit project raw ++ tail = gas_explicit marks vs.vs_gas_readings ++ suffix` by
    (qpat_assum `project = marks ++ rest` (fn th => once_rewrite_tac [th]) >>
     simp[Abbr `suffix`, Abbr `vs`] >>
     irule (SIMP_RULE (srw_ss()) []
       (Q.INST [`tail` |-> `[]:bytes32 list`] gas_mask_padded_split)) >>
     `LENGTH raw_slots = LENGTH raw` by metis_tac[LIST_REL_LENGTH] >> fs[]) >>
  `raw_variant fmp vs vs_out /\ vs.vs_outcomes = MAP SND (call_trace es)` by
    simp[Abbr `vs`, raw_variant_def, gas_variant_def, venom_state_component_equality] >>
  `deploy_unit_execution_correct_at marks tops runtime_bc am
     (tx with code := vs_out.vs_code) dunit vs` by
    (rewrite_tac[deploy_unit_execution_correct_at_with] >>
     qexists_tac `shadow_ctx` >>
     qunabbrev_tac `marks` >> qunabbrev_tac `vs` >>
     qpat_assum `!gs. deploy_unit_execution_correct_with _ _ _ _ _ _ _ _ /\ _`
       (ACCEPT_TAC o CONJUNCT1 o Q.SPEC `raw ++ [0w]`)) >>
  disch_tac >> qexistsl_tac [`vs`, `marks`, `suffix`] >>
  qpat_assum `raw_variant fmp vs vs_out` (fn raw_variant_thm =>
    qpat_assum `deploy_unit_execution_correct_at marks _ _ _ _ dunit vs` (fn cert =>
      qpat_assum `gas_explicit project raw ++ tail = _`
        (fn readings => rewrite_tac [raw_variant_thm, cert, readings]))) >>
  disch_tac >> qx_gen_tac `D` >> disch_tac >>
  disch_then strip_assume_tac >>
  `deploy_storage_ok tops am (tx with code := vs_out.vs_code) vs.vs_outcomes
       (gas_explicit marks vs.vs_gas_readings ++ suffix)` by
    (qpat_assum `gas_explicit project raw ++ tail = _`
       (fn th => once_rewrite_tac [GSYM th]) >>
     qpat_assum `vs.vs_outcomes = _` (fn th => rewrite_tac [th]) >>
     first_assum ACCEPT_TAC) >>
  drule_all deploy_selected_producer_inputs >> strip_tac >>
  qpat_x_assum `!D. (?fr. terminates _) /\ _ ==> _` (qspec_then `D` mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rename1 `terminates (run_context fuel dunit.cu_context vs)` >>
          qexists_tac `fuel` >> first_assum ACCEPT_TAC) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      disch_tac >>
      `vs.vs_code = vs_out.vs_code /\ vs.vs_data_section = vs_out.vs_data_section` by
        simp[Abbr `vs`] >>
      qpat_assum `vs.vs_code = _` (fn code =>
        qpat_assum `vs.vs_data_section = _` (fn data =>
          qpat_assum `mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\ _) _ vs`
            (ACCEPT_TAC o REWRITE_RULE [code, data])))) >>
  strip_tac >> asm_rewrite_tac[]
QED

val frozen_deploy_focus_contract =
  boolSyntax.lhand (concl deploy_pipeline_gas_link_from_frozen_focus);

Theorem e2e_deploy_correctness_asm_opt_from_frozen_focus:
  ^frozen_deploy_focus_contract ==>
(
  !policy tops deploy_bc runtime_bc am tx es.
    compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) /\
    ~program_reads_self_code tops /\
    supported_program tops /\ supported_program_deploy tops /\
    constructor_call_free tops /\
    deploy_typing_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (creation_resource_starved es r es' \/
       deploy_call_result_rel tops runtime_bc am tx es r es')
)
Proof
  disch_then (ACCEPT_TAC o MP e2e_deploy_correctness_asm_opt_from_link o
    MP deploy_pipeline_gas_link_from_frozen_focus)
QED


(* Check term identity as well as retaining the signed text above. *)
val _ =
  List.app (fn (conditional, target) =>
    if aconv (snd (boolSyntax.dest_imp (concl conditional))) (concl target) then ()
    else raise Fail "gas composition conclusion differs from its contract")
    [(call_pipeline_gas_link_from_frozen_focus,
       e2eCorrectnessTheory.call_pipeline_gas_link),
     (deploy_pipeline_gas_link_from_frozen_focus,
       e2eDeployCorrectnessTheory.deploy_pipeline_gas_link),
     (vyper_call_correct_asm_opt_from_frozen_focus,
       e2eCorrectnessTheory.vyper_call_correct_asm_opt),
     (e2e_deploy_correctness_asm_opt_from_frozen_focus,
       e2eDeployCorrectnessTheory.e2e_deploy_correctness_asm_opt)];

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

(* Candidate shared-selector shape. The fixed-filling Exit and the request cut retain one mask. *)

val focus_finalizer_selected_request_draft : term = ``
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp /\
  code_layout_valid vs0 /\
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
  ~frame_resource_starved es0 result final /\
  run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit
    (init_ir_supply unit) = SOME (pre,t) /\
  pre.cu_context.ctx_entry = SOME nm /\
  run_callee_first rpolicy o1_fn_passes
    (fcg_postorder (fcg_analyze pre.cu_context) nm)
    (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)) t =
    SOME (out.po_unit,t') /\
  stage 0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
  stage 9 = out.po_unit.cu_context /\
  (!k. k < 9 ==> ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
    (stage k) (stage (SUC k))) /\
  (!k. k <= 9 ==> o1_ctx_shape (stage k) /\
    EVERY (o1_fn_row k) (stage k).ctx_functions) ==>
  ?raw_slots sites unused.
    LENGTH raw_slots = LENGTH sites /\
    PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es0) /\
    !raw.
      LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw ==>
      (?rest. MAP project sites = markf (raw ++ [0w]) ++ rest) /\
      (!D.
        (?fr. terminates (run_context fr unit.cu_context
           (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>))) /\
        dead_wf D /\
        o1_pre_walk_inv D unit.cu_context
          (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
        (fin = asm_opt_finalizer ==>
           mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                     s.vs_code = vs0.vs_code /\ s.vs_data_section = vs0.vs_data_section)
             unit.cu_context (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>)) ==>
        ((?orc.
          (!fuel. gas_res_rel (run_context fuel (stage 7)
            (vs0 with vs_gas_readings := raw ++ [0w]))
            (ev_context orc fuel (stage 7) vs0)) /\
          (!fuel. gas_res_rel (run_context fuel (stage 8) vs0)
            (ev_context orc fuel (stage 8) vs0)) /\
          (!p d fn inst s. ev_reachable orc vs0 (stage 7) p d fn inst s ==>
            ?ws. raw_reachable (vs0 with vs_gas_readings := raw ++ [0w])
                 (stage 7) fn inst (s with vs_gas_readings := ws)) /\
          (!fn inst s. raw_reachable vs0 (stage 8) fn inst s ==>
            ?p d. ev_reachable orc vs0 (stage 8) p d fn inst
              (s with vs_gas_readings := vs0.vs_gas_readings))) /\
        ((!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
           ~MEM (Label "runtime_begin") inst.inst_operands) ==>
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
                     Abort ExHalt_abort u))))) /\
      (!D k vs fn inst s fuel s'.
        vs = (vs0 with <|vs_gas_readings := raw ++ [0w];
                         vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
        dead_wf D /\ raw_safe_rq_upto D 0 k unit.cu_context vs /\
        raw_reachable vs unit.cu_context fn inst s /\
        inst.inst_opcode <> INVOKE /\ LENGTH s.vs_requests = k /\
        step_inst fuel unit.cu_context inst s = OK s' /\
        k < LENGTH s'.vs_requests ==>
        (?fn' inst' t fuel' t'.
          raw_reachable vs0 out.po_unit.cu_context fn' inst' t /\
          inst'.inst_opcode <> INVOKE /\ LENGTH t.vs_requests = k /\
          step_inst fuel' out.po_unit.cu_context inst' t = OK t' /\
          k < LENGTH t'.vs_requests /\
          request_agree_except D (EL k s'.vs_requests) (EL k t'.vs_requests) /\
          t.vs_outcomes = s.vs_outcomes) /\
        ctx_rq_upto D k unit.cu_context out.po_unit.cu_context vs vs0 /\
        (?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
          mem_inv (\ctx fn inst t. (request_cut k t /\ ~in_static_abort_prefix fn t) ==>
            lowered_mem_ok eom (w2n t.vs_initial_fmp) ctx fn inst t)
            out.po_unit.cu_context vs0) /\
        (fin = asm_opt_finalizer ==>
          code_end_offset_ok (\ctx fn inst t.
            raw_reachable vs0 ctx fn inst t /\ request_cut k t /\
            ~in_static_abort_prefix fn t) out.po_unit.cu_context))
``;

val supplied_request_cut =
  let
    open boolSyntax
    val selected = snd (strip_exists (snd (dest_imp focus_finalizer_selected_request_draft)))
    val fillings = List.last (strip_conj selected)
    val posts = snd (dest_imp (snd (dest_forall fillings)))
  in
    List.last (strip_conj posts)
  end;

val guard_replay_at_unit =
  Q.INST [`C` |-> `unit.cu_context`, `C'` |-> `out.po_unit.cu_context`]
    guard_selected_request_replay;

val (guard_replay_inputs, guard_replay_output) =
  boolSyntax.dest_imp (concl guard_replay_at_unit);
val s1_request_prefix_at_filling = boolSyntax.lhand guard_replay_inputs;

Theorem guard_request_cut_from_draft:
  vs = (vs0 with <|vs_gas_readings := raw ++ [0w];
                    vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
  ^supplied_request_cut /\ ^s1_request_prefix_at_filling ==>
  ^guard_replay_output
Proof
  strip_tac >> mp_tac guard_replay_at_unit >>
  impl_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >>
      rpt gen_tac >> strip_tac >>
      qabbrev_tac `D = cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE)` >>
      `dead_wf D` by
        (simp[Abbr `D`, cx_dead_def, initial_evaluation_context_def] >>
         MATCH_ACCEPT_TAC
           (SIMP_RULE (srw_ss()) [external_call_dead_def]
             (Q.INST [`src` |-> `(INL NoneV, am, [])`] external_call_dead_wf))) >>
      qspecl_then [`D`, `k`, `vs`, `fn`, `inst`, `s`, `fuel`, `s'`] mp_tac
        (ASSUME supplied_request_cut) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      simp[Abbr `D`]) >>
  disch_then ACCEPT_TAC
QED

Theorem recorded_outcomes_count_snoc:
  recorded_outcomes_count (pre ++ [StorageOutcome rq outcome]) =
    SUC (recorded_outcomes_count pre)
Proof
  simp[recorded_outcomes_count_def, FILTER_APPEND_DISTRIB]
QED

Theorem call_trace_request_outcome_index:
  k < LENGTH (call_trace es) ==>
  (EL k (call_requests es), EL k (MAP SND (call_trace es))) = EL k (call_trace es)
Proof
  simp[call_requests_def, EL_MAP]
QED

Theorem record_request_at_next_index:
  EL (LENGTH rqs) (record_request rq rqs) = rq /\
  LENGTH (record_request rq rqs) = SUC (LENGTH rqs)
Proof
  simp[record_request_def, EL_APPEND_EQN]
QED

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

Theorem guard_replay_stage_witness[local]:
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  unit.cu_context.ctx_entry = SOME nm /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit ==>
  ?pre t t' stage.
    run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit
      (init_ir_supply unit) = SOME (pre,t) /\
    pre.cu_context.ctx_entry = SOME nm /\
    run_callee_first rpolicy o1_fn_passes
      (fcg_postorder (fcg_analyze pre.cu_context) nm)
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)) t =
      SOME (out.po_unit,t') /\
    stage 0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
    stage 9 = out.po_unit.cu_context /\
    (!k. k < 9 ==> ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
      (stage k) (stage (SUC k))) /\
    (!k. k <= 9 ==> o1_ctx_shape (stage k) /\
      EVERY (o1_fn_row k) (stage k).ctx_functions)
Proof
  simp[o1_pipeline_def] >> strip_tac >>
  drule o1_driver_runs >> strip_tac >>
  `o1_ctx_shape unit.cu_context` by metis_tac[o1_source_unit_ok_ctx_shape] >>
  `ir_supply_inst_ok (init_ir_supply unit)` by simp[init_ir_supply_inst_ok] >>
  drule_all o1_pre_walk_rows >> strip_tac >>
  drule_all o1_pre_walk_sim >> strip_tac >>
  `pre.cu_context.ctx_entry = SOME nm` by metis_tac[] >>
  mp_tac (Q.INST [`unit` |-> `pre`, `fcg` |-> `fcg_analyze pre.cu_context`]
    o1_ctx_shape_prune) >> simp[unit_labels_wf_namespace] >> strip_tac >>
  mp_tac (Q.INST [`unit` |-> `pre`, `entry` |-> `nm`,
    `fcg` |-> `fcg_analyze pre.cu_context`] o1_walk_callee_first) >>
  simp[] >> strip_tac >>
  `EVERY (o1_fn_row 0) (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context.ctx_functions` by
    (irule o1_prune_every >> first_assum ACCEPT_TAC) >>
  `entry = nm` by metis_tac[optionTheory.SOME_11] >>
  qexists_tac `t'` >>
  fs[run_callee_first_def] >>
  drule_at (Pat `run_named_fn_schedules _ _ _ _ _ _ = _`)
    (Q.INST [`R` |-> `o1_fn_row`] o1_schedule_stages) >>
  impl_tac >- fs[o1_fn_passes_steps, o1_step_contracts_from_rows, unit_labels_wf_namespace] >>
  strip_tac >> qexists_tac `stage` >>
  fs[o1_fn_passes_def, o1_walk_view_def]
QED

Theorem code_layout_length_bound[local]:
  code_layout_valid vs ==> LENGTH vs.vs_code < 2 ** 256
Proof
  simp[code_layout_valid_def, dimword_def, dimindex_256] >>
  strip_tac >> irule LESS_EQ_LESS_TRANS >> qexists_tac `2 ** 255` >> simp[]
QED

val guard_replay_at_boolean_marks =
  let
    val marks = List.find (fn v => fst (dest_var v) = "markf")
      (free_vars focus_finalizer_selected_request_draft)
    val mark_type = listSyntax.dest_list_type (snd (dom_rng (type_of (valOf marks))))
  in
    inst [mark_type |-> bool] focus_finalizer_selected_request_draft
  end;

val guard_replay_selector = ``
  !rpolicy unit out vs0 cpl prog fin prog' es0 nm entryfn lbl fmp markf lo
    project result final pre t t' stage.
    ^guard_replay_at_boolean_marks
``;
val guard_result = concl e2eOutcomesGuardTheory.call_guard_gas_link;

Theorem call_guard_gas_link_from_draft:
  ^guard_replay_selector ==> ^guard_result
Proof
  strip_tac >> rewrite_tac[call_guard_gas_link_stmt_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `vyper_call_staging _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vyper_call_staging_def, vyper_frame_staging_def]) >>
  drule_all guard_runtime_phases >> strip_tac >>
  rename1 `generate_context_plan out.po_unit.cu_context = SOME cplan` >>
  `call_state_rel tops (assemble prog') am tx es` by metis_tac[] >>
  drule_all guard_source_focus_setup >> strip_tac >>
  rename1 `lookup_function "__entry" unit.cu_context.ctx_functions = SOME func` >>
  qabbrev_tac `vs0 = opt_entry_state prog prog' cplan es` >>
  qabbrev_tac `txp = tx with code := vs0.vs_code` >>
  `vs0 = opt_entry_state prog prog' cplan es` by simp[Abbr `vs0`] >>
  `txp = tx with code := vs0.vs_code` by simp[Abbr `txp`] >>
  qabbrev_tac `fmp = (n2w (MAX cplan.cp_initial_fmp
    (unit_alloca_budget unit.cu_context +
     32 * ctx_dload_count unit.cu_context)) : bytes32)` >>
  qspecl_then [`tops`, `rpolicy`, `unit`, `out`, `cplan`, `prog`, `prog'`, `es`,
    `fmp`] mp_tac raw_fmp_choice >>
  impl_tac >- simp[Abbr `fmp`] >>
  disch_then (strip_assume_tac o PURE_REWRITE_RULE
    [GSYM (ASSUME ``vs0 = opt_entry_state prog prog' cplan es``)]) >>
  drule_all opt_entry_focus_setup >> strip_tac >>
  `source_typing_ok tops am txp` by
    (qpat_assum `txp = tx with code := vs0.vs_code` (fn th => PURE_REWRITE_TAC[th]) >>
     irule source_typing_ok_code_update >>
     conj_tac >- (irule code_layout_length_bound >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  `initial_venom_state_rel tops am txp vs0` by
    (qpat_assum `txp = tx with code := vs0.vs_code` (fn txth =>
       qpat_assum `vs0 = opt_entry_state _ _ _ _` (fn st =>
         PURE_REWRITE_TAC[txth, st])) >>
     irule opt_entry_initial_venom_state_rel >> first_assum ACCEPT_TAC) >>
  `vyper_call_staging fin policy tops (assemble prog') am tx ret es` by
    (qpat_assum `runtime_bc = assemble prog'` (fn th => PURE_REWRITE_TAC[GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`txp` |-> `txp`, `fmp` |-> `fmp`, `vs0` |-> `vs0`,
    `cplan` |-> `cplan`, `unit` |-> `unit`, `rpolicy` |-> `rpolicy`]
    guard_source_marks) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `shadow_ctx` (fn source_marks =>
    let
      open boolSyntax
      val (vs, admits) = dest_forall (concl source_marks)
      val (marks, properties) = dest_exists (snd (dest_imp admits))
      val prefix = mk_abs(vs, mk_abs(marks, rand properties))
      val family = INST [mk_var("prefix_ok", type_of prefix) |-> prefix]
        (Q.INST [`tx` |-> `txp`] guard_marked_focus_family)
    in
      assume_tac source_marks >> mp_tac (BETA_RULE family)
    end)) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `markf` assume_tac) >>
  `fn_entry_label func = SOME "__entry"` by
    (qpat_assum `!gs. source_unit_execution_correct_with _ _ _ _ _ _ _ _ /\ _`
       (mp_tac o REWRITE_RULE [source_unit_execution_correct_with_def] o
        CONJUNCT1 o Q.SPEC `[]`) >>
     disch_then (qx_choosel_then [`cf`, `shadow_cf`] strip_assume_tac) >>
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
     `~program_reads_self_code tops` by metis_tac[] >>
     drule_all lower_vyper_runtime_unit_sym_src_ok >>
     strip_tac >> asm_rewrite_tac[]) >>
  drule_all guard_replay_stage_witness >>
  disch_then (qx_choosel_then [`pre`, `t`, `t'`, `stage`] strip_assume_tac) >>
  qspecl_then [`rpolicy`, `unit`, `out`, `vs0`, `cplan`, `prog`, `fin`,
    `prog'`, `es`, `"__entry"`, `func`, `"__entry"`, `fmp`, `markf`, `0`,
    `\key. key IN gas_explicit_sites unit.cu_context shadow_ctx`, `r`, `es'`,
    `pre`, `t`, `t'`, `stage`] mp_tac (ASSUME guard_replay_selector) >>
  impl_tac
  >- (BETA_TAC >> asm_rewrite_tac[] >> gen_tac >>
      qpat_assum `!gs. source_unit_execution_correct_with _ _ _ _ _ _ _ _ /\ _`
        (qx_choosel_then [`D`, `fuel`, `extra`] strip_assume_tac o
         CONJUNCT2 o CONJUNCT2 o Q.SPEC `gs`) >>
      qexistsl_tac [`D`, `fuel`, `extra`] >>
      qpat_x_assum `vs0 = opt_entry_state _ _ _ _` SUBST_ALL_TAC >>
      pure_rewrite_tac[venom_state_fupdcanon] >>
      qpat_assum `MAP _ (gas_events_blocks _ _ _ _) = _`
        (fn th => asm_rewrite_tac[REWRITE_RULE [venom_state_fupdcanon] th])) >>
  disch_then (qx_choosel_then [`raw_slots`, `sites`, `unused`] strip_assume_tac) >>
  qabbrev_tac `project = MAP (\key. key IN gas_explicit_sites unit.cu_context shadow_ctx) sites` >>
  rewrite_tac[gas_readings_rel_def] >>
  irule gas_mask_projection >>
  qexistsl_tac [`project`, `raw_slots`, `unused`] >>
  `LENGTH project = LENGTH raw_slots` by simp[Abbr `project`] >>
  qpat_assum `LENGTH project = LENGTH raw_slots` (fn lengths =>
    qpat_assum `PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es)`
      (fn readings => rewrite_tac[lengths, readings])) >>
  qx_genl_tac [`raw`, `tail`] >> strip_tac >> BETA_TAC >>
  qpat_x_assum `!raw. LIST_REL _ raw_slots raw ==> _` (qspec_then `raw` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `rest` assume_tac)
    (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  qabbrev_tac `vs = vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>` >>
  qabbrev_tac `marks = markf (raw ++ [0w])` >>
  `vs = vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp;
    vs_initial_fmp := fmp|>` by simp[Abbr `vs`] >>
  `marks = markf (raw ++ [0w])` by simp[Abbr `marks`] >>
  qabbrev_tac `suffix = gas_explicit rest (DROP (LENGTH marks) (raw ++ [0w])) ++ tail` >>
  `vs.vs_gas_readings = raw ++ [0w]` by
    (qpat_assum `vs = vs0 with <|vs_gas_readings := raw ++ [0w];
             vs_fmp := fmp; vs_initial_fmp := fmp|>`
       (ACCEPT_TAC o SIMP_RULE (srw_ss()) [] o Q.AP_TERM `\s:venom_state. s.vs_gas_readings`)) >>
  `gas_explicit project raw ++ tail = gas_explicit marks vs.vs_gas_readings ++ suffix` by
    (qpat_assum `project = marks ++ rest` (fn mask =>
       qpat_assum `vs.vs_gas_readings = raw ++ [0w]` (fn reads =>
         qpat_assum `Abbrev (suffix = _)` (fn suffix_def =>
           PURE_REWRITE_TAC[mask, reads, REWRITE_RULE [markerTheory.Abbrev_def] suffix_def]))) >>
     irule gas_mask_padded_split >>
     qpat_assum `project = marks ++ rest` (fn mask =>
       qpat_assum `LENGTH project = LENGTH raw_slots` (fn slots =>
         PURE_REWRITE_TAC[GSYM mask, slots])) >>
     drule LIST_REL_LENGTH >> disch_then ACCEPT_TAC) >>
  `raw_variant fmp vs vs0` by
    (qpat_assum `vs = vs0 with <|vs_gas_readings := raw ++ [0w];
             vs_fmp := fmp; vs_initial_fmp := fmp|>` (fn st => PURE_REWRITE_TAC[st]) >>
     simp_tac (srw_ss()) [raw_variant_def, gas_variant_def, venom_state_component_equality]) >>
  qpat_assum `!gs. source_unit_execution_correct_with _ _ _ _ _ _ _ _ /\ _`
    (fn family =>
      let val filling = Q.SPEC `raw ++ [0w]` family in
        mp_tac (CONJ (CONJUNCT1 filling) (CONJUNCT1 (CONJUNCT2 filling)))
      end) >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac o PURE_REWRITE_RULE
    [GSYM (ASSUME ``vs = vs0 with <|vs_gas_readings := raw ++ [0w];
      vs_fmp := fmp; vs_initial_fmp := fmp|>``),
     GSYM (ASSUME ``(marks:bool list) = markf (raw ++ [0w:bytes32])``)]) >>
  `source_unit_execution_correct_at marks tops ret am txp unit vs` by
    (PURE_REWRITE_TAC[source_unit_execution_correct_at_with] >>
     qexists_tac `shadow_ctx` >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`rpolicy`, `unit`, `out`, `prog`, `prog'`, `cplan`, `fmp`, `vs`,
    `marks`, `suffix`] >>
  qpat_assum `vs0 = opt_entry_state _ _ _ _` (fn st =>
    qpat_assum `txp = tx with code := vs0.vs_code`
      (fn txth => PURE_REWRITE_TAC[GSYM st, GSYM txth])) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qx_gen_tac `H` >> strip_tac >>
      drule_all (Q.INST [`tx` |-> `txp`] guard_focus_callback_inputs) >> strip_tac >>
      qpat_assum `!D. (?fr. terminates _) /\ _ ==> _`
        (qspec_then `cx_dead H (initial_evaluation_context am.sources am.layouts txp NONE)` mp_tac) >>
      impl_tac
      >- (conj_tac
          >- (rename1 `terminates (run_context fuel unit.cu_context vs)` >>
              qexists_tac `fuel` >> first_assum ACCEPT_TAC) >>
          conj_tac >- first_assum ACCEPT_TAC >>
          conj_tac >- first_assum ACCEPT_TAC >>
          strip_tac >>
          `vs.vs_code = vs0.vs_code /\ vs.vs_data_section = vs0.vs_data_section` by
            (qpat_assum `vs = vs0 with <|vs_gas_readings := raw ++ [0w];
                vs_fmp := fmp; vs_initial_fmp := fmp|>`
               (ACCEPT_TAC o SIMP_RULE (srw_ss()) [pairTheory.PAIR_EQ] o
                Q.AP_TERM `\s:venom_state. (s.vs_code,s.vs_data_section)`)) >>
          qpat_assum `vs.vs_code = _` (fn code =>
            qpat_assum `vs.vs_data_section = _` (fn data =>
              qpat_assum `mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\ _) _ vs`
                (ACCEPT_TAC o PURE_REWRITE_RULE [code, data])))) >>
      disch_then (mp_tac o CONJUNCT2) >>
      impl_tac >- first_assum ACCEPT_TAC >>
      disch_then ACCEPT_TAC)
  >- (`txp.target = tx.target` by
        (qpat_assum `txp = tx with code := vs0.vs_code`
           (ACCEPT_TAC o SIMP_RULE (srw_ss()) [] o Q.AP_TERM `\t. t.target`)) >>
      qpat_assum `vs = vs0 with <|vs_gas_readings := raw ++ [0w];
        vs_fmp := fmp; vs_initial_fmp := fmp|>` (fn st =>
        mp_tac (PURE_REWRITE_RULE [GSYM st, REFL_CLAUSE, AND_CLAUSES]
          (Q.INST [`tx` |-> `txp`] guard_request_cut_from_draft))) >>
      impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
      qpat_assum `txp.target = tx.target` (fn target =>
        disch_then (ACCEPT_TAC o PURE_REWRITE_RULE [target])))
QED

val abort_entry = concl codegenStaticAbortTheory.codegen_entry_asm_sim_abort_asm_opt;
val abort_frame = concl codegenStaticAbortTheory.asm_frame_exception_requests;
val abort_result = concl codegenStaticAbortTheory.codegen_correct_static_abort_asm_opt;

Theorem codegen_correct_static_abort_asm_opt_from_suppliers:
  ^abort_entry /\ ^abort_frame ==> ^abort_result
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `codegen_ready unit.cu_context` by fs[codegen_context_obligations_abort_def] >>
  `asm_static_wf prog` by (drule_all codegen_asm_static_wf >> simp[]) >>
  `asm_refines prog prog'` by
    metis_tac[asm_opt_finalizer_meets_contract, finalizer_correct_def] >>
  `asm_frame_prog_ok prog'` by
    (irule asm_static_wf_frame_prog_ok >> fs[asm_refines_def]) >>
  `(entry_asm_state vs es).as_code = assemble prog ++ vs.vs_data_section` by
    simp[entry_asm_state_def] >>
  rename1 `generate_context_plan unit.cu_context = SOME plan` >>
  qspecl_then [`fuel`, `rpolicy`, `unit`, `plan`, `prog`, `prog'`, `Inv`,
    `vs`, `entry_asm_state vs es`, `a`, `vs'`] mp_tac (ASSUME abort_entry) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`n`, `ast`] assume_tac) >>
  qspecl_then [`prog'`, `vs.vs_data_section`, `es`,
    `entry_asm_state vs es with as_code := assemble prog' ++ vs.vs_data_section`,
    `n`, `ast`, `vs'.vs_requests`] mp_tac (ASSUME abort_frame) >>
  impl_tac
  >- (qpat_x_assum `(_ = AsmRevert ast \/ _) /\ _`
        (map_every assume_tac o CONJUNCTS) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED
