(* Linked compiler correctness and gas sufficiency. *)
Theory e2eModsTopsDraft
Ancestors
  linkedRuntimeCertificateFocus gasFocusStaticPrefixDriver gasMaskProjection
  gasEvents gasExplicitSites linkedCallHorizonComposition requestCutLabels
  staticAbortAsmOptCorrect codegenStaticAbort contextRawReachable contextStaticAbortRel
  e2eModsDefs e2eDeployModsDefs compileUnit e2eComposition bodyInvSplit
  linkedCompilePhases linkedCallPremises runtimeUnitShapeMods ctorDeployShapeMods
  linkedCallStorage linkedDeployEntry linkedFrameGas linkedRawUnitShape linkedCallEntry
  linkedOutputLayout linkedUnitMemory lowerDloadDefs e2eProducers unitTransformDefs deployRuntimeSuffix
  linkedRuntimeLabelReadiness linkedDeployLabelReadiness sourceLabelFlow
  sourceUnitExecutionMods sourceUnitExecution vyperLoweringCorrect loweringStateRelDefs
  gasFocusReplayExit staticAbortDefs codegenSymRel abiTypeBoundProps compileEnv vyperTyping
  linkedRuntimeFuel linkedDeployFuel linkedCodegenGas linkedDeployGasTail o1StaticPipelineCorrect[qualified]
  runtimeLabelInvariant gasFocusOptLabelFlow[qualified] venomInst
  venomPipelineDriverProps venomState codegenAsmStaticWf asmSymSem
  o1PipelineCorrect[qualified] ptrDiscipline staticLayoutDefs
  asmCodePrefix asmOptNonemptyFinalizer asmOptimizer codegenAsmProgOk
  stackPlanGen e2eEntry vyperTypeContract
  e2eGasSufficient asmFrameRel codegenEntryRel codegenLabelDisciplined codegenRel frameRel
  ctorDeployFrame deployFrameReplay frameStep vfmExecutionProp venomLayout o1PassContract
  e2eCorrectness[qualified] e2eDeployCorrectness[qualified]
  e2eGasSufficientTop[qualified] e2eDefs
  vyperInterpreter frameOutcome frameGas callTrace vfmExecution vfmConstants
  vfmContext asmIR list codegenAsmOpt codegenCorrectness passSimulationDefs
  staticShadowDefs staticShadowRun staticShadowO1State o1PipelineCompose
  venomExecSemantics unitMemInv ctorDeployRunBounded unitShapeDefs
  vyperArith contextPlanLayoutProps contextCodegenRel ctorDeployMemoryFrontier
  ptrSafeRun fragGasPathMem fragExec fragGasPathPtr
  linkedRuntimeCalldataReject
  vyperTypeContractSoundness e2eDeployFrame accountsRelProps vfmState
  linkedEmptyDeploySource linkedEmptyDeployTarget o1SafeUpto[qualified]
  linkedEmptyDeployMemory linkedEmptyDeployCode vyperCompiler linkedStructFields
  o1OpcodeAbsence[qualified] venomCompilerWf[qualified] vyperTypeContractStaticMaps
  linkedDeployConstructorSource linkedDeployConstructorRun linkedDeployConstructorCode compileVyper
  linkedNonpayableDeploySource bodyFullShadowInternalRun internalBlockPackagingProps
  linkedDeployConstructorReject linkedDeployRevertSize ctorDeployLoweringPrefix
  ctorDeployMemoryRunMemEntryTaskInputs vyperTypeContractContext
  ctorDeployBodyShadow fragExecMem
  linkedConstructorBodyShadowCode linkedDeployShadowBodyInv
  ctorDeployMemoryRunPtrPrefixEntrySemanticMods
  linkedRuntimeDispatchedCertificate linkedRuntimeCertificateExit vyperStorageFootprint
  exprSimHypsDefs vfmCalldataBound vfmBuffer
  linkedRuntimeDallocaWindows runtimePeakMemoryProof runtimePeakMemoryCode
  loweringBudgetAccountCodes linkedConstructorSourceTrace linkedConstructorRegistrationMetadata
  ctorDeployLoweringEntryPrefix moduleLoweringProps callRawVariant
  createSizeExit sourceUnitCreateSizeRun entryCreateExit[qualified]
  entryCreateReject[qualified] acceptedContextPhi[qualified] venomRunBounded
  vyperTypeContractModes[qualified] e2eDeployEntry[qualified,ignore_grammar]
  vyperImportRefsProps vyperCallFiniteStorage vyperStorageBackend frameRunRaises

val linked_runtime_rejection_tac = fn tx_quote =>
  qspecl_then [`mods`,`exps`,`rpolicy`,`runtime_unit`,`am`,tx_quote,`vi`]
    mp_tac lower_vyper_runtime_unit_reverts_mods >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`reject_fn`,`reject_state`,`G'`,`tn'`,`reject_marks`]
    (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`reject_fn`,`reject_state`,`reject_marks`] >> asm_rewrite_tac[];

val linked_runtime_correct_rejection_tac = fn tx_quote =>
  `ctx_has_dalloca runtime_unit.cu_context ==>
    unit_alloca_budget runtime_unit.cu_context <= w2n vi.vs_initial_fmp /\
    w2n vi.vs_initial_fmp < 2 ** 254` by
    (strip_tac >> qpat_assum `vi.vs_initial_fmp = fmp`
       (SUBST1_TAC o AP_TERM ``w2n : bytes32 -> num``) >>
     conj_tac
     >- (qpat_assum `unit_alloca_budget runtime_unit.cu_context + _ <= _` mp_tac >>
         decide_tac) >>
     FIRST_ASSUM ACCEPT_TAC) >>
  `LENGTH tx.calldata < 2 ** 64` by
    (qpat_assum `es.contexts = (ctxt,rb)::rest` (fn contexts =>
       qpat_assum `evm_state_ok es`
         (mp_tac o SIMP_RULE (srw_ss()) [contexts, evm_state_ok_def,
           vfmCalldataBoundTheory.calldata_bounded_def])) >>
     qpat_assum `frame_tx_rel tx es ctxt` (mp_tac o REWRITE_RULE [frame_tx_rel_def]) >>
     rpt strip_tac >>
     qpat_assum `buffer_to_list ctxt.msgParams.data = tx.calldata`
       (fn calldata => PURE_REWRITE_TAC [GSYM calldata, vfmBufferTheory.LENGTH_buffer_to_list]) >>
     simp[]) >>
  `ctx_has_dalloca runtime_unit.cu_context ==>
    !fn inst s. raw_reachable (vi with vs_outcomes := []) runtime_unit.cu_context
      fn inst s ==> dalloca_fmp_headroom inst s` by
    (strip_tac >>
     `account_code_lengths_ok vi.vs_accounts /\ ~vi.vs_halted /\
      vi.vs_fmp = vi.vs_initial_fmp` by
       (qpat_assum `initial_venom_state_rel_mods mods am _ vi`
          (strip_assume_tac o PURE_REWRITE_RULE [initial_venom_state_rel_mods_def]) >>
        conj_tac
        >- (qpat_assum `vi.vs_accounts = _` SUBST1_TAC >>
            qpat_assum `machine_well_typed am`
              (ACCEPT_TAC o MATCH_MP
                (Q.INST [`tx` |-> tx_quote] initial_account_codes_after_transfer))) >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     `!fn i s. MEM fn runtime_unit.cu_context.ctx_functions /\
       active_inst fn i s /\ i.inst_opcode = DALLOCA ==>
         raw_call_dalloca_window fn i s \/ create_copy_dalloca_window fn i s \/
         create_blueprint_dalloca_window fn i s` by
       (rpt gen_tac >> strip_tac >>
        rename1 `active_inst fn i active` >>
        mp_tac (Q.INST [`fn` |-> `fn`, `i` |-> `i`, `s` |-> `active`]
          active_inst_dalloca_windows_with_blueprint) >>
        impl_tac
        >- (conj_tac
            >- (qpat_assum `lowering_context_ok runtime_unit.cu_context`
                  (mp_tac o SIMP_RULE (srw_ss()) [lowering_context_ok_def, EVERY_MEM]) >>
                simp[]) >>
            conj_tac >- qpat_assum `active_inst fn i active` ACCEPT_TAC >>
            conj_tac >- qpat_assum `i.inst_opcode = DALLOCA` ACCEPT_TAC >>
            gen_tac >> strip_tac >>
            mp_tac (Q.INST [`unit` |-> `runtime_unit`, `rp` |-> `rpolicy`,
              `window` |-> `\chunk k. raw_call_dalloca_chunk chunk k \/
                create_copy_dalloca_chunk chunk k \/ create_blueprint_dalloca_chunk chunk k`]
              lower_vyper_runtime_unit_dalloca_windows_mods) >>
            impl_tac >- simp[] >>
            disch_then (qspecl_then [`fn`, `bb`] mp_tac) >> simp[]) >>
        disch_then ACCEPT_TAC) >>
     mp_tac (Q.INST [`ctx` |-> `runtime_unit.cu_context`,
                   `vi` |-> `vi with vs_outcomes := []`]
       raw_headroom_from_dalloca_windows) >>
     simp[NoAsms, outcomes_accounts_typed_def] >>
     disch_then match_mp_tac >>
     conj_tac >- qpat_assum `lowering_context_ok runtime_unit.cu_context` ACCEPT_TAC >>
     conj_tac >- qpat_assum `account_code_lengths_ok vi.vs_accounts` ACCEPT_TAC >>
     conj_tac >- qpat_assum `~vi.vs_halted` ACCEPT_TAC >>
     conj_tac >- qpat_assum `vi.vs_fmp = vi.vs_initial_fmp` ACCEPT_TAC >>
     conj_tac
     >- (qpat_assum `vi.vs_initial_fmp = fmp` SUBST1_TAC >>
         qpat_assum `w2n fmp < 2 ** 254` (ACCEPT_TAC o REWRITE_RULE [EVAL ``2 ** 254:num``])) >>
     conj_tac
     >- (qpat_assum `vi.vs_call_ctx.cc_calldata = tx.calldata` SUBST1_TAC >>
         qpat_assum `LENGTH tx.calldata < 2 ** 64` (ACCEPT_TAC o REWRITE_RULE [EVAL ``2 ** 64:num``])) >>
     first_assum ACCEPT_TAC) >>
  linked_runtime_rejection_tac tx_quote;

Theorem vyper_call_correct_mods:
  !fin policy mods exps deploy_bc runtime_bc am tx es H.
    fin IN accepted_finalizers /\
    compile_vyper_mods fin policy mods exps = SOME (deploy_bc, runtime_bc) /\
    source_typing_ok_mods mods exps am tx /\
    call_state_rel_mods mods exps runtime_bc am tx es /\
    LENGTH (call_trace es) < 2 ** 64 /\
    e2eCorrectness$storage_ok H am tx /\
    call_within_mods H mods exps am tx es
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       calldata_result_rel_mods H mods exps am tx es r es')
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `compile_vyper_mods _ _ _ _ = _`
    (strip_assume_tac o MATCH_MP compile_vyper_with_mods_success_phases o
     REWRITE_RULE [compile_vyper_mods_def]) >>
  qpat_assum `call_state_rel_mods _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [call_state_rel_mods_def]) >>
  drule_all source_typing_ok_runtime_ready_mods >> strip_tac >>
  drule_all lower_vyper_runtime_unit_source_unit_ok_mods >> strip_tac >>
  drule lower_vyper_runtime_unit_raw_shape_mods >> strip_tac >>
  drule lower_vyper_runtime_unit_data_empty_mods >> strip_tac >>
  drule lower_vyper_runtime_unit_global_reserved_mods >> strip_tac >>
  `fixed_region_reserved 0 runtime_unit.cu_context /\
   reserved_intervals_wf runtime_unit.cu_context.ctx_global_reserved` by
    simp[fixed_region_reserved_def, reserved_intervals_wf_def] >>
  `o1PipelineCorrect$o1_pipeline rpolicy runtime_unit = SOME runtime_out` by
    fs[o1PipelineCorrectTheory.o1_pipeline_def] >>
  drule_all o1PipelineCorrectTheory.run_venom_pipeline_output_shape >> strip_tac >>
  `codegen_ready runtime_out.po_unit.cu_context` by
    (qpat_assum `o1PipelineCorrect$o1_pipeline _ runtime_unit = _`
       (mp_tac o MATCH_MP run_venom_pipeline_success_boundary o
        REWRITE_RULE [o1PipelineCorrectTheory.o1_pipeline_def]) >> simp[]) >>
  `!fn inst. MEM fn runtime_unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
     source_inst_ok ({"code_end"},T) inst` by
    metis_tac[lower_vyper_runtime_unit_label_checks_mods] >>
  drule_all source_own_flow >> strip_tac >>
  `!fn inst. MEM fn runtime_unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
     ~MEM (Label "runtime_begin") inst.inst_operands` by
    (rpt strip_tac >>
     drule_all (Q.INST [`source_checks` |-> `({"runtime_begin"},F)`]
       lower_vyper_runtime_unit_label_checks_mods) >>
     simp[source_inst_ok_def, EVERY_MEM, rb_operand_ok_for_def] >>
     qexists_tac `Label "runtime_begin"` >> simp[]) >>
  `sym_unit_static_ok runtime_out.po_unit` by
    (qspecl_then [`rpolicy`, `runtime_unit`, `runtime_out`]
       mp_tac o1_pipeline_sym_unit_static_ok >> simp[] >> metis_tac[]) >>
  drule_all gasFocusOptLabelFlowTheory.focus_opt_label_flow_own >> strip_tac >>
  qpat_assum `finalize_codegen _ _ _.po_unit = SOME runtime_bc`
    (strip_assume_tac o MATCH_MP finalize_codegen_success_plan) >>
  `assemble prog' <> []` by
    (Cases_on `fin = K SOME`
     >- (drule codegen_assembly_nonempty >> gvs[]) >>
     `fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
     qpat_x_assum `fin = asm_opt_finalizer` SUBST_ALL_TAC >>
     irule codegen_assembly_finalizer_nonempty >>
     qexistsl [`prog`,`rpolicy`,`runtime_out.po_unit`] >> simp[]) >>
  `cplan.cp_initial_fmp < 2 ** 254` by
    (fs[generate_context_plan_def] >>
     drule generate_context_plan_with_headroom >> simp[]) >>
  `?fmp:bytes32.
    w2n (opt_entry_state_own prog prog' cplan es).vs_initial_fmp <= w2n fmp /\
    w2n fmp < 2 ** 254 /\
    unit_alloca_budget runtime_unit.cu_context +
      32 * ctx_dload_count runtime_unit.cu_context <= w2n fmp` by
    (irule call_raw_fmp_exists_mods >> asm_rewrite_tac[]) >>
  `o1_initial_state_ok (opt_entry_state_own prog prog' cplan es) /\
   (opt_entry_state_own prog prog' cplan es).vs_fmp =
     (opt_entry_state_own prog prog' cplan es).vs_initial_fmp /\
   (opt_entry_state_own prog prog' cplan es).vs_initial_fmp = n2w cplan.cp_initial_fmp` by
    simp[opt_entry_state_own_def, entry_venom_state_def, o1_initial_state_ok_def,
         init_venom_state_def] >>
  `!eom. max_live_eom runtime_out.po_unit.cu_context = SOME eom ==>
          eom <= w2n (opt_entry_state_own prog prog' cplan es).vs_initial_fmp` by
    (qspecl_then [`runtime_out.po_unit.cu_context`, `cplan`,
        `opt_entry_state_own prog prog' cplan es`]
       mp_tac o1PipelineCorrectTheory.generate_context_plan_eom_room >> simp[]) >>
  `call_state_rel_mods mods exps (assemble prog') am tx es` by fs[] >>
  `code_layout_valid (opt_entry_state_own prog prog' cplan es)` by
    (qspecl_then [`fin`, `mods`, `exps`, `rpolicy`, `prog`, `prog'`,
         `am`, `tx`, `es`, `cplan`, `runtime_out.po_unit`]
       mp_tac opt_entry_code_layout_valid_own_mods >>
     asm_rewrite_tac[]) >>
  qspecl_then [`mods`, `exps`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`]
    mp_tac opt_entry_initial_venom_state_rel_mods >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  qspecl_then [`mods`, `exps`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`]
    mp_tac opt_entry_asm_rels_own_mods >> impl_tac >- asm_rewrite_tac[] >>
  strip_tac >>
  qspec_then `es` (qx_choosel_then [`r`, `es'`] assume_tac) run_call_total >>
  qexistsl [`r`, `es'`] >> simp[] >>
  Cases_on `frame_resource_starved es r es'` >> simp[] >>
  Cases_on `calldata_dispatch_mods mods exps tx.calldata` >>
  simp[calldata_result_rel_mods_def]
  >- (
     qabbrev_tac `vs = opt_entry_state_own prog prog' cplan es` >>
     qabbrev_tac `D = <|d_stor := K (K UNIV); d_trans := K (K UNIV);
                       d_imm := K UNIV; d_ret := K UNIV|>` >>
     `dead_wf D` by simp[Abbr `D`, dead_wf_def] >>
     `LENGTH vs.vs_data_section < dimword (:256) DIV 2` by
       (mp_tac (Q.INST [`vs` |-> `vs`, `prefix` |-> `assemble prog'`]
          e2eCorrectnessTheory.data_section_length_bound) >> asm_rewrite_tac[]) >>
     `!start vi. (start = vs \/ start = static_shadow vs) /\
       raw_variant fmp vi start ==>
       raw_unit_memory_ok runtime_unit.cu_context vi /\
       ptr_discipline 0 runtime_unit.cu_context vi /\
       mem_inv dload_offset_ok runtime_unit.cu_context vi /\
       mem_inv dload_headroom_ok runtime_unit.cu_context vi /\
       mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                                s.vs_code = vi.vs_code /\
                                s.vs_data_section = vi.vs_data_section)
         runtime_unit.cu_context vi /\
       ?fuel s. run_context fuel runtime_unit.cu_context vi = Abort Revert_abort s /\
                s.vs_returndata = []` by
       (map_every qx_gen_tac [`start`,`vi`] >> disch_then (map_every assume_tac o CONJUNCTS) >>
        qabbrev_tac `raw_tx = tx with is_static := start.vs_call_ctx.cc_static` >>
        `initial_venom_state_rel_mods mods am raw_tx vi /\
         code_layout_valid vi /\ vi.vs_fmp = fmp /\ vi.vs_initial_fmp = fmp` by
          (`vi = start with <|vs_fmp := fmp; vs_initial_fmp := fmp;
                              vs_gas_readings := vi.vs_gas_readings|>` by
             (qpat_assum `raw_variant fmp vi start`
                (mp_tac o PURE_REWRITE_RULE [raw_variant_def, gas_variant_def]) >>
              simp[NoAsms, venom_state_component_equality] >> strip_tac >>
              qpat_assum `fmp = vi.vs_initial_fmp` (fn h =>
                qpat_assum `fmp = vi.vs_fmp` (ACCEPT_TAC o TRANS (SYM h)))) >>
           qpat_assum `vi = _` SUBST1_TAC >>
           qunabbrev_tac `raw_tx` >>
           conj_tac
           >- (qpat_assum `initial_venom_state_rel_mods mods am tx vs` mp_tac >>
               qpat_assum `start = vs \/ start = static_shadow vs`
                 (DISJ_CASES_THEN SUBST1_TAC) >>
               POP_ASSUM_LIST (K ALL_TAC) >>
               simp[NoAsms, static_shadow_def, initial_venom_state_rel_mods_def] >>
               disch_then (map_every assume_tac o CONJUNCTS) >>
               asm_rewrite_tac[] >>
               simp[NoAsms, value_transfer_ok_def, accounts_after_transfer_def,
                    tx_env_ok_def] >>
               fs[venom_env_rel_def] >> fs[call_ctx_rel_def] >>
               fs[value_transfer_ok_def] >> fs[tx_env_ok_def]) >>
           qpat_assum `code_layout_valid vs` mp_tac >>
           qpat_assum `start = vs \/ start = static_shadow vs`
             (DISJ_CASES_THEN SUBST1_TAC) >>
           simp[NoAsms, code_layout_valid_def, static_shadow_def]) >>
        `source_typing_ok_mods mods exps am raw_tx` by
          (qpat_assum `source_typing_ok_mods mods exps am tx` mp_tac >>
           simp[NoAsms, Abbr `raw_tx`, source_typing_ok_mods_def, call_tx_well_typed_def]) >>
        `raw_tx.target = tx.target` by simp[NoAsms, Abbr `raw_tx`] >>
        `source_deployment_rel_mods mods exps am raw_tx` by
          (qpat_assum `source_deployment_rel_mods mods exps am tx`
             (mp_tac o PURE_REWRITE_RULE [source_deployment_rel_mods_def, layouts_agree_mods_def]) >>
           qpat_assum `raw_tx.target = tx.target` (fn target =>
             PURE_REWRITE_TAC [source_deployment_rel_mods_def, layouts_agree_mods_def, target]) >>
           DISCH_THEN ACCEPT_TAC) >>
        `vi.vs_call_ctx.cc_calldata = tx.calldata` by
          (qpat_assum `initial_venom_state_rel_mods mods am raw_tx vi`
             (strip_assume_tac o PURE_REWRITE_RULE
               [initial_venom_state_rel_mods_def, venom_env_rel_def, call_ctx_rel_def]) >>
           qpat_assum `vi.vs_call_ctx.cc_calldata = raw_tx.calldata` mp_tac >>
           simp[NoAsms, Abbr `raw_tx`]) >>
        `?fn s n.
           runtime_unit.cu_context.ctx_entry = SOME "__entry" /\
           lookup_function "__entry" runtime_unit.cu_context.ctx_functions = SOME fn /\
           fn_entry_label fn = SOME "__entry" /\
           s.vs_returndata = [] /\
           (?fuel. run_context fuel runtime_unit.cu_context vi = Abort Revert_abort s) /\
           gas_path_mem runtime_unit.cu_context fn
             (vi with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>)
             n (Abort Revert_abort s) /\
           (!fuel. ptr_safe_blocks D 0 fuel runtime_unit.cu_context fn [] FEMPTY entry_taint
             (vi with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>))` by
          (suspend "linked_runtime_rejection") >>
        `!fuel. mem_safe_blocks fuel runtime_unit.cu_context fn
           (vi with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>)` by
          (qspecl_then [`mods`, `exps`, `rpolicy`, `runtime_unit`, `fn`,
              `vi with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>`,
              `n`, `Abort Revert_abort s`]
            mp_tac lower_vyper_runtime_unit_exit_mem_safe_blocks_mods >>
           simp[exit_result_def]) >>
        `ptr_discipline 0 runtime_unit.cu_context vi` by
          (qspecl_then [`mods`,`exps`,`rpolicy`,`runtime_unit`,`vi`,`fn`,`"__entry"`,`D`]
             mp_tac lower_vyper_runtime_unit_ptr_taint_mods >> simp[]) >>
        `raw_unit_memory_ok runtime_unit.cu_context vi` by
          (Cases_on `ctx_has_dalloca runtime_unit.cu_context`
           >- (`!f inst s. raw_reachable vi runtime_unit.cu_context f inst s ==>
                   dalloca_no_wrap inst s /\ w2n s.vs_initial_fmp <= w2n s.vs_fmp` by
                 (qspecl_then [`0`,`runtime_unit.cu_context`,`"__entry"`,`fn`,`"__entry"`,`vi`]
                    mp_tac lowered_unit_checked_dalloca_facts >> asm_rewrite_tac[]) >>
               qspecl_then [`mods`,`exps`,`rpolicy`,`runtime_unit`,`am`,`raw_tx`,
                            `vi`,`fn`,`"__entry"`,`D`]
                 mp_tac lower_vyper_runtime_unit_memory_ok_from_no_wrap_mods >>
               impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >> simp[]) >>
           qspecl_then [`mods`,`exps`,`rpolicy`,`runtime_unit`,`am`,`raw_tx`,
                        `vi`,`fn`,`"__entry"`,`D`]
             mp_tac lower_vyper_runtime_unit_memory_ok_mods >> simp[]) >>
        `mem_inv dload_offset_ok runtime_unit.cu_context vi` by
          (qspecl_then [`mods`,`exps`,`rpolicy`,`runtime_unit`,`vi`,`fn`,`"__entry"`]
            mp_tac lower_vyper_runtime_unit_dload_offset_ok_mods >> simp[]) >>
        `mem_inv dload_headroom_ok runtime_unit.cu_context vi` by
          (qspecl_then [`mods`,`exps`,`rpolicy`,`runtime_unit`,`am`,`raw_tx`,`vi`]
            mp_tac lower_vyper_runtime_unit_dload_headroom_ok_mods >> simp[]) >>
        `mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                         s.vs_code = vi.vs_code /\ s.vs_data_section = vi.vs_data_section)
           runtime_unit.cu_context vi` by
          (qspecl_then [`mods`,`exps`,`rpolicy`,`runtime_unit`,`vi`,`fn`,`"__entry"`]
            mp_tac lower_vyper_runtime_unit_dload_in_section_mods >> simp[]) >>
        asm_rewrite_tac[] >> qexistsl [`fuel`,`s`] >> asm_rewrite_tac[]) >>
     `!vi. raw_variant fmp vi vs ==>
       raw_unit_memory_ok runtime_unit.cu_context vi /\
       ptr_discipline 0 runtime_unit.cu_context vi /\
       taint_within D runtime_unit.cu_context vi /\
       mem_inv dload_offset_ok runtime_unit.cu_context vi /\
       mem_inv dload_headroom_ok runtime_unit.cu_context vi /\
       mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                                s.vs_code = vi.vs_code /\
                                s.vs_data_section = vi.vs_data_section)
         runtime_unit.cu_context vi /\
       ?fuel s. run_context fuel runtime_unit.cu_context vi = Abort Revert_abort s /\
                s.vs_returndata = []` by
       (gen_tac >> strip_tac >>
        qpat_assum `!start vi. _ ==> raw_unit_memory_ok _ _ /\ _`
          (qspecl_then [`vs`, `vi`] mp_tac) >>
        asm_rewrite_tac[] >> simp[Abbr `D`, taint_within_def]) >>
     `code_end_offset_ok (raw_reachable vs) runtime_out.po_unit.cu_context` by
       (qspecl_then [`D`, `0`, `rpolicy`, `runtime_unit`, `runtime_out`, `vs`, `fmp`]
          mp_tac o1StaticPipelineCorrectTheory.o1_pipeline_code_end_offset_ok_static_abort >>
        impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
        disch_then (qx_choose_then `vcode` strip_assume_tac) >>
        qpat_assum `!vi. raw_variant _ vi vs ==> _` (drule_then strip_assume_tac) >>
        qpat_x_assum `_ ==> code_end_offset_ok _ _ /\ _` mp_tac >>
        impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
        disch_then (CONJUNCTS_THEN2 (K ALL_TAC) (DISJ_CASES_THEN assume_tac))
        >- FIRST_ASSUM ACCEPT_TAC >>
        rename1 `run_context n runtime_unit.cu_context vcode = Abort Revert_abort s0` >>
        qpat_x_assum `!n. terminates (run_context n runtime_unit.cu_context vcode) ==> _`
          (qspec_then `n` mp_tac) >> simp[terminates_def]) >>
     qspecl_then [`D`, `0`, `rpolicy`, `runtime_unit`, `runtime_out`, `vs`, `fmp`]
       mp_tac o1StaticPipelineCorrectTheory.run_venom_pipeline_correct_static_abort >>
     impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     disch_then (qx_choose_then `vraw` strip_assume_tac) >>
     qpat_assum `!vi. raw_variant _ vi vs ==> _` (drule_then strip_assume_tac) >>
     rename1 `run_context raw_fuel runtime_unit.cu_context vraw = Abort Revert_abort s0` >>
     qpat_x_assum `_ ==> ctx_sim D _ _ vraw vs /\ ctx_abort_rq D _ _ vraw vs /\ _`
       mp_tac >>
     impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 (K ALL_TAC) assume_tac)) >>
     `terminates (run_context raw_fuel runtime_unit.cu_context vraw)` by simp[terminates_def] >>
     `o1_lowered_inv runtime_out.po_unit.cu_context vs` by
       (qpat_x_assum `o1_lowered_inv _ _ \/ _`
          (DISJ_CASES_THEN2 ACCEPT_TAC STRIP_ASSUME_TAC) >>
        qpat_x_assum `!n. terminates (run_context n runtime_unit.cu_context vraw) ==> _`
          (qspec_then `raw_fuel` mp_tac) >> simp[]) >>
     qpat_x_assum `ctx_sim D _ _ vraw vs` mp_tac >>
     simp[ctx_sim_def] >> disch_then (qspec_then `raw_fuel` mp_tac) >>
     asm_rewrite_tac[] >> strip_tac >>
     rename1 `dead_result_rel D _ (run_context n runtime_out.po_unit.cu_context vs)` >>
     `?post. run_context n runtime_out.po_unit.cu_context vs = Abort Revert_abort post` by
       (qpat_x_assum `dead_result_rel D _ _` mp_tac >>
        Cases_on `run_context n runtime_out.po_unit.cu_context vs` >>
        simp[dead_result_rel_def]) >>
     `!start n s. (start = vs \/ start = static_shadow vs) /\
        start.vs_initial_fmp = vs.vs_initial_fmp /\ o1_run_state_ok start /\
        run_context n runtime_out.po_unit.cu_context start = Abort Revert_abort s ==>
        s.vs_returndata = []` by
       (map_every qx_gen_tac [`start`, `revert_n`, `revert_post`] >>
        disch_then (map_every assume_tac o CONJUNCTS) >>
        `run_venom_pipeline (K T) (K T) (K T) rpolicy o1_pipeline_spec runtime_unit =
            SOME runtime_out` by fs[o1PipelineCorrectTheory.o1_pipeline_def] >>
        drule_all o1_pipeline_sim_revert_empty >> strip_tac >>
        qpat_x_assum `!d raw z. _ ==> ?vi. raw_variant raw vi z /\ _`
          (qspecl_then [`D`, `fmp`, `start`] mp_tac) >>
        impl_tac >- asm_rewrite_tac[] >>
        disch_then (qx_choose_then `vi` strip_assume_tac) >>
        qpat_assum `!start vi. _ ==> raw_unit_memory_ok _ _ /\ _`
          (qspecl_then [`start`, `vi`] mp_tac) >>
        impl_tac >- asm_rewrite_tac[] >> strip_tac >>
        rename1 `run_context raw_n runtime_unit.cu_context vi = Abort Revert_abort raw_s` >>
        `mem_inv raw_mem_ok runtime_unit.cu_context vi` by
          (PURE_REWRITE_TAC [mem_inv_def, raw_mem_ok_def] >>
           qpat_assum `raw_unit_memory_ok _ vi`
             (ACCEPT_TAC o PURE_REWRITE_RULE [raw_unit_memory_ok_def])) >>
        `fmp_free_ctx runtime_unit.cu_context` by
          (irule source_fmp_free >> asm_rewrite_tac[]) >>
        `o1_src_inv D runtime_unit.cu_context vi` by
          (rewrite_tac[o1_src_inv_def] >> rpt conj_tac >>
           (FIRST_ASSUM ACCEPT_TAC ORELSE
           (qexists_tac `0` >> asm_rewrite_tac[]) ORELSE
           simp[Abbr `D`, taint_within_def])) >>
        `o1_pre_walk_inv D runtime_unit.cu_context vi` by
          (irule o1_source_pre_walk_inv >> asm_rewrite_tac[]) >>
        `fmp_variant_room (SOME fmp) runtime_out.po_unit.cu_context start` by
          (PURE_REWRITE_TAC [fmp_variant_room_def] >>
           qpat_assum `start.vs_initial_fmp = vs.vs_initial_fmp` SUBST1_TAC >>
           conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
        qpat_x_assum `_ ==> ctx_sim_fuel _ D _ _ vi start /\ _` mp_tac >>
        impl_tac >- asm_rewrite_tac[] >> strip_tac >>
        qpat_x_assum `!raw_n raw_s. _ ==> ?s. _`
          (qspecl_then [`raw_n`, `raw_s`] mp_tac) >>
        impl_tac >- asm_rewrite_tac[] >> strip_tac >>
        `run_context (MAX revert_n (cfg_norm_fuel runtime_out.po_unit.cu_context raw_n))
           runtime_out.po_unit.cu_context start =
           run_context revert_n runtime_out.po_unit.cu_context start` by
          (irule run_context_terminates_mono >> simp[terminates_def]) >>
        `run_context (MAX revert_n (cfg_norm_fuel runtime_out.po_unit.cu_context raw_n))
           runtime_out.po_unit.cu_context start =
           run_context (cfg_norm_fuel runtime_out.po_unit.cu_context raw_n)
             runtime_out.po_unit.cu_context start` by
          (irule run_context_terminates_mono >> simp[terminates_def]) >>
        gvs[]) >>
     `post.vs_returndata = []` by
       (Cases_on `vs.vs_call_ctx.cc_static`
        >- (mp_tac (Q.INST [`s` |-> `vs`, `sh` |-> `static_shadow vs`,
                              `C` |-> `runtime_out.po_unit.cu_context`,
                              `fuel` |-> `n`, `v` |-> `post`]
                     static_shadow_run_context_revert) >>
            impl_tac >- simp[static_shadow_rel_initial] >>
            disch_then (qx_choose_then `shadow_post` strip_assume_tac) >>
            `o1_run_state_ok (static_shadow vs)` by
              (irule static_shadow_o1_run_state_ok >> asm_rewrite_tac[]) >>
            qpat_assum `!start n s. _ ==> s.vs_returndata = []`
              (qspecl_then [`static_shadow vs`, `n`, `shadow_post`] mp_tac) >>
            impl_tac >- simp[static_shadow_def] >>
            strip_tac >>
            qpat_assum `static_shadow_rel post shadow_post`
              (mp_tac o AP_TERM ``\s:venom_state. s.vs_returndata`` o
               PURE_REWRITE_RULE [static_shadow_rel_def]) >>
            simp[static_shadow_def]) >>
        qpat_assum `!start n s. _ ==> s.vs_returndata = []`
          (qspecl_then [`vs`, `n`, `post`] mp_tac) >>
        simp[o1_run_state_ok_def]) >>
     drule_all o1_pipeline_memory_obligations_raw >> strip_tac >>
     drule_all o1_pipeline_codegen_obligations >> strip_tac >>
     `venom_frame_rel es r es' (Abort Revert_abort post)` by
       (Cases_on `fin = K SOME`
        >- (`prog' = prog` by fs[] >>
            qpat_x_assum `prog' = prog` SUBST_ALL_TAC >>
            `vs = entry_venom_state prog cplan es` by
              simp[Abbr `vs`, opt_entry_state_own_identity] >>
            `?fn fns. runtime_out.po_unit.cu_context.ctx_functions = fn::fns /\
                get_params (HD fn.fn_blocks).bb_instructions = []` by
              (qpat_assum `unit_shape_ok _`
                 (mp_tac o PURE_REWRITE_RULE [unit_shape_ok_def, entry_fn_first_def]) >>
               disch_then (CONJUNCTS_THEN2
                 (qx_choosel_then [`entry_name`, `entry_fn`, `other_fns`] strip_assume_tac)
                 strip_assume_tac) >>
               qexistsl [`entry_fn`, `other_fns`] >> conj_tac
               >- FIRST_ASSUM ACCEPT_TAC >>
               qpat_assum `get_params (HD (HD _).fn_blocks).bb_instructions = []` mp_tac >>
               qpat_assum `runtime_out.po_unit.cu_context.ctx_functions = entry_fn::other_fns`
                 SUBST1_TAC >>
               simp[NoAsms]) >>
            `es.txParams.blockNumber < dimword (:256)` by
              (fs[frame_tx_rel_def, tx_block_fields_rel_def, tx_env_ok_def] >>
               irule lt_dimword_256 >> qexists_tac `255` >> simp[]) >>
            drule_all entry_venom_state_evm_environment >> strip_tac >>
            `initial_state_rel cplan prog 0 fn vs es` by
              (qpat_assum `vs = entry_venom_state _ _ _` SUBST1_TAC >>
               gvs[initial_state_rel_def, stack_params_rel_def, frame_fresh_def,
                   entry_venom_state_fresh, entry_venom_state_frame_fields,
                   entry_venom_state_created_in_tx, asm_pc_to_offset_zero,
                   context_memory_rel_def]) >>
            `ctxt.msgParams.parsed = parse_code 0 FEMPTY ctxt.msgParams.code` by
              (qpat_assum `es.contexts = (ctxt,rb)::rest` (fn h =>
                 qpat_assum `evm_state_ok es` (mp_tac o SIMP_RULE (srw_ss())
                    [h, evm_state_ok_def, wf_state_def, wf_context_def])) >>
               strip_tac >> FIRST_ASSUM ACCEPT_TAC) >>
            `ctxt.msgParams.code = assemble prog ++ vs.vs_data_section` by
              (`vs.vs_code = ctxt.msgParams.code` by
                 (qpat_assum `vs = entry_venom_state _ _ _` SUBST1_TAC >>
                  qpat_assum `es.contexts = (ctxt,rb)::rest`
                    (fn th => simp_tac (srw_ss()) [th, entry_venom_state_frame_fields])) >>
               qpat_assum `vs.vs_code = ctxt.msgParams.code`
                 (fn th => REWRITE_TAC [GSYM th]) >>
               FIRST_ASSUM ACCEPT_TAC) >>
            `ctxt.msgParams.code <> [] ==>
                account_already_created (lookup_account ctxt.msgParams.callee es.rollback.accounts)` by
              (qpat_assum `frame_tx_rel tx es ctxt`
                 (strip_assume_tac o PURE_REWRITE_RULE [frame_tx_rel_def]) >>
               qpat_assum `ctxt.msgParams.callee = tx.target` (fn th => REWRITE_TAC [th]) >>
               qpat_assum `(lookup_account tx.target es.rollback.accounts).code = ctxt.msgParams.code`
                 (fn th => simp_tac (srw_ss()) [account_already_created_def, NULL_EQ, th])) >>
            `initial_ctx_rel cplan prog runtime_out.po_unit.cu_context vs es` by
              (qpat_assum `frame_fresh ctxt`
                 (strip_assume_tac o PURE_REWRITE_RULE [frame_fresh_def]) >>
               qpat_assum `evm_state_ok es`
                 (strip_assume_tac o PURE_REWRITE_RULE [evm_state_ok_def]) >>
               qpat_assum `vs = entry_venom_state _ _ _` (fn th =>
                 let val entry = Q.SPECL [`prog`, `cplan`, `es`]
                 in map_every (strip_assume_tac o SUBS [GSYM th] o entry)
                      [entry_venom_state_fresh, entry_venom_state_frame_fields]
                 end) >>
               `vs.vs_params = []` by
                 (qpat_assum `vs = entry_venom_state _ _ _` SUBST1_TAC >>
                  simp[NoAsms, entry_venom_state_def, init_venom_state_def]) >>
               PURE_REWRITE_TAC [initial_ctx_rel_def] >>
               qexistsl [`fn`, `fns`, `ctxt`, `rb`, `rest`] >>
               rpt conj_tac >>
               FIRST [FIRST_ASSUM ACCEPT_TAC,
                      qexists_tac `d` >> FIRST_ASSUM ACCEPT_TAC,
                      strip_tac >>
                      qpat_assum `ctxt.msgParams.code <> [] ==> _`
                        (fn th => irule th) >> FIRST_ASSUM ACCEPT_TAC]) >>
            qspecl_then [`n`, `rpolicy`, `runtime_out.po_unit`, `cplan`, `prog`,
                         `raw_reachable vs`, `vs`, `es`] mp_tac codegen_correct >>
            impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
            simp[]) >>
        `fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
        qpat_x_assum `fin = asm_opt_finalizer` SUBST_ALL_TAC >>
        qspecl_then [`n`, `rpolicy`, `runtime_out.po_unit`, `cplan`, `prog`, `prog'`,
                     `raw_reachable vs`, `vs`, `es`] mp_tac codegen_correct_asm_opt_own >>
        impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
        simp[]) >>
     qpat_assum `venom_frame_rel es r es' (Abort Revert_abort post)`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [venom_frame_rel_def]) >>
     conj_tac
     >- (irule (SIMP_RULE (srw_ss()) [vfm_abort_def]
                  (Q.INST [`exc` |-> `Reverted`] frame_inst_raises_frame_raises)) >>
         qexists_tac `Revert` >> FIRST_ASSUM ACCEPT_TAC) >>
     qexists_tac `lgs` >>
     qpat_assum `post.vs_returndata = []`
       (fn th => qpat_assum `frame_outcome es r es' (SOME Reverted) post.vs_returndata lgs`
         (ACCEPT_TAC o REWRITE_RULE [th]))) >>
  rename1 `calldata_dispatch_mods _ _ _ = SOME dispatched` >>
  PairCases_on `dispatched` >> simp[] >>
  qabbrev_tac `selected = tx with <| function_name := dispatched0; args := dispatched1 |>` >>
  `source_typing_ok_mods mods exps am selected /\
   call_state_rel_mods mods exps runtime_bc am selected es` by
    simp[Abbr `selected`, call_premises_dispatch_invariant_mods] >>
  `source_deployment_rel_mods mods exps am selected` by
    fs[call_state_rel_mods_def] >>
  irule call_result_rel_from_readings_mods >> asm_rewrite_tac[] >>
  conj_tac
  >- (qunabbrev_tac `selected` >> gen_tac >>
      drule_all valid_horizon_for_dispatch_mods >>
      disch_then (qspec_then `gobs` ACCEPT_TAC)) >>
  suspend "linked_runtime_certificate"
QED

Resume vyper_call_correct_mods[linked_runtime_rejection]:
  linked_runtime_correct_rejection_tac `raw_tx`
QED

Resume vyper_call_correct_mods[linked_runtime_certificate]:
  qabbrev_tac `vs = opt_entry_state_own prog prog' cplan es` >>
  `initial_venom_state_rel_mods mods am selected vs` by
    (qspecl_then [`mods`, `exps`, `prog`, `prog'`, `am`, `selected`, `es`, `cplan`]
       mp_tac opt_entry_initial_venom_state_rel_mods >>
     simp[NoAsms, Abbr `vs`] >>
     qpat_assum `runtime_bc = assemble prog'` (fn code =>
       PURE_REWRITE_TAC [GSYM code]) >>
     impl_tac >- first_assum ACCEPT_TAC >> DISCH_THEN ACCEPT_TAC) >>
  `vs.vs_outcomes = MAP SND (call_trace es)` by
    simp[NoAsms, Abbr `vs`, opt_entry_state_own_def, entry_venom_state_def] >>
  `outcomes_accounts_typed (SOME vs.vs_outcomes)` by
    (qpat_assum `vs.vs_outcomes = _` SUBST1_TAC >>
     `wf_state es /\ balance_bounded (2 ** 256 - 1) es /\ returndata_bounded es` by
       fs[evm_state_ok_def] >>
     drule_all call_trace_outcomes_bounded >>
     simp[outcomes_accounts_typed_def, EVERY_MEM]) >>
  `LENGTH tx.calldata < 2 ** 64` by
    (qpat_assum `es.contexts = (ctxt,rb)::rest` (fn contexts =>
       qpat_assum `evm_state_ok es`
         (mp_tac o SIMP_RULE (srw_ss()) [contexts, evm_state_ok_def,
           vfmCalldataBoundTheory.calldata_bounded_def])) >>
     qpat_assum `frame_tx_rel tx es ctxt` (mp_tac o REWRITE_RULE [frame_tx_rel_def]) >>
     rpt strip_tac >>
     qpat_assum `buffer_to_list ctxt.msgParams.data = tx.calldata`
       (fn calldata => PURE_REWRITE_TAC [GSYM calldata, vfmBufferTheory.LENGTH_buffer_to_list]) >>
     simp[]) >>
  mp_tac (Q.INST [`unit` |-> `runtime_unit`, `tx` |-> `selected`]
    linked_runtime_dispatched_readings_certificate) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `shadow_ctx` assume_tac) >>
  `!gs. ?marks.
    source_unit_execution_correct_with_mods shadow_ctx marks mods exps
      (external_return_type_mods mods exps selected.function_name) am selected
      runtime_unit (vs with <|vs_gas_readings := gs;
         vs_fmp := fmp; vs_initial_fmp := fmp|>)` by
    suspend "linked_runtime_marked_family" >>
  qpat_assum `!gs. ?marks. source_unit_execution_correct_with_mods _ _ _ _ _ _ _ _ _`
    mp_tac >>
  CONV_TAC (LAND_CONV SKOLEM_CONV) >>
  disch_then (qx_choose_then `markf` assume_tac) >>
  qpat_assum `!gs. source_unit_execution_correct_with_mods _ _ _ _ _ _ _ _ _`
    (qx_choosel_then [`entry_fn`,`shadow_entry_fn`]
       (map_every assume_tac o CONJUNCTS) o
     CONV_RULE (DEPTH_CONV BETA_CONV) o
     REWRITE_RULE [source_unit_execution_correct_with_mods_def] o Q.SPEC `[]`) >>
  suspend "linked_runtime_focus_replay"
QED

Resume vyper_call_correct_mods[linked_runtime_marked_family]:
  gen_tac >>
  qabbrev_tac `vi = vs with <|vs_gas_readings := gs;
         vs_fmp := fmp; vs_initial_fmp := fmp|>` >>
  `initial_venom_state_rel_mods mods am selected vi` by
    (qpat_assum `initial_venom_state_rel_mods mods am selected vs` mp_tac >>
     simp[NoAsms, Abbr `vi`, initial_venom_state_rel_mods_def,
          venom_env_rel_def, call_ctx_rel_def]) >>
  `vi.vs_call_ctx.cc_calldata = tx.calldata` by
    (qpat_assum `initial_venom_state_rel_mods mods am selected vi`
       (strip_assume_tac o PURE_REWRITE_RULE
          [initial_venom_state_rel_mods_def, venom_env_rel_def, call_ctx_rel_def]) >>
     qpat_assum `vi.vs_call_ctx.cc_calldata = selected.calldata` mp_tac >>
     simp[NoAsms, Abbr `selected`]) >>
  `vi.vs_outcomes = vs.vs_outcomes /\ vi.vs_initial_fmp = fmp` by
    simp[NoAsms, Abbr `vi`] >>
  `outcomes_accounts_typed (SOME vi.vs_outcomes)` by
    (qpat_assum `vi.vs_outcomes = vs.vs_outcomes` SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  `LENGTH vi.vs_outcomes < 2 ** 64` by
    (qpat_assum `vi.vs_outcomes = vs.vs_outcomes` SUBST1_TAC >>
     qpat_assum `vs.vs_outcomes = MAP SND (call_trace es)` SUBST1_TAC >>
     PURE_REWRITE_TAC [listTheory.LENGTH_MAP] >>
     first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca runtime_unit.cu_context ==>
    unit_alloca_budget runtime_unit.cu_context <= w2n vi.vs_initial_fmp /\
    w2n vi.vs_initial_fmp < 2 ** 254` by
    (strip_tac >> qpat_assum `vi.vs_initial_fmp = fmp` SUBST1_TAC >>
     conj_tac
     >- (qpat_assum `unit_alloca_budget runtime_unit.cu_context + _ <= _` mp_tac >>
         decide_tac) >>
     FIRST_ASSUM ACCEPT_TAC) >>
  `ctx_has_dalloca runtime_unit.cu_context ==>
     !f inst w. raw_reachable vi runtime_unit.cu_context f inst w ==>
       dalloca_fmp_headroom inst w` by
    suspend "linked_runtime_marked_headroom" >>
  qpat_assum `!s. _ ==> ?marks. source_unit_execution_correct_with_mods _ _ _ _ _ _ _ _ s /\ _`
    (qspec_then `vi` mp_tac) >>
  impl_tac
  >- (simp[Abbr `selected`] >> conj_tac
      >- (qpat_assum `LENGTH tx.calldata < 2 ** 64` mp_tac >> simp[NoAsms]) >>
      first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `marks` strip_assume_tac) >>
  qexists_tac `marks` >> first_assum ACCEPT_TAC
QED

Resume vyper_call_correct_mods[linked_runtime_marked_headroom]:
  strip_tac >>
  `account_code_lengths_ok vi.vs_accounts` by
    (qpat_assum `initial_venom_state_rel_mods mods am selected vi`
       (strip_assume_tac o PURE_REWRITE_RULE [initial_venom_state_rel_mods_def]) >>
     qpat_assum `vi.vs_accounts = _` SUBST1_TAC >>
     qpat_assum `machine_well_typed am`
       (ACCEPT_TAC o MATCH_MP
         (Q.INST [`tx` |-> `selected`] initial_account_codes_after_transfer))) >>
  `!fn i s. MEM fn runtime_unit.cu_context.ctx_functions /\
    active_inst fn i s /\ i.inst_opcode = DALLOCA ==>
      raw_call_dalloca_window fn i s \/ create_copy_dalloca_window fn i s \/
      create_blueprint_dalloca_window fn i s` by
    (rpt gen_tac >> strip_tac >>
     mp_tac (Q.INST [`fn` |-> `fn`, `i` |-> `i`, `s` |-> `s`]
       active_inst_dalloca_windows_with_blueprint) >>
     impl_tac
     >- (conj_tac >- fs[lowering_context_ok_def, EVERY_MEM] >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         rpt strip_tac >>
         mp_tac (Q.INST [`unit` |-> `runtime_unit`, `rp` |-> `rpolicy`,
             `window` |-> `\chunk k. raw_call_dalloca_chunk chunk k \/
               create_copy_dalloca_chunk chunk k \/ create_blueprint_dalloca_chunk chunk k`]
           lower_vyper_runtime_unit_dalloca_windows_mods) >>
         impl_tac >- simp[] >>
         disch_then (qspecl_then [`fn`, `bb`] mp_tac) >> simp[]) >>
     DISCH_THEN ACCEPT_TAC) >>
  mp_tac (Q.INST [`ctx` |-> `runtime_unit.cu_context`, `vi` |-> `vi`]
    raw_headroom_from_dalloca_windows) >>
  fs[initial_venom_state_rel_mods_def]
QED

Resume vyper_call_correct_mods[linked_runtime_focus_replay]:
  `LENGTH vs.vs_data_section < dimword (:256) DIV 2` by
    (mp_tac (Q.INST [`vs` |-> `vs`, `prefix` |-> `assemble prog'`]
       e2eCorrectnessTheory.data_section_length_bound) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     DISCH_THEN ACCEPT_TAC) >>
  qabbrev_tac `project_site = \(site:string # num).
    site IN gasExplicitSites$gas_explicit_sites runtime_unit.cu_context shadow_ctx` >>
  `~(?rf ri. MEM rf runtime_unit.cu_context.ctx_functions /\
               MEM ri (fn_insts rf) /\
               MEM (Label "runtime_begin") ri.inst_operands)` by
    (strip_tac >>
     qpat_assum `!fn inst. MEM fn _ /\ _ ==> ~MEM (Label "runtime_begin") _`
       (fn absent =>
         qpat_assum `MEM rf runtime_unit.cu_context.ctx_functions` (fn fm =>
           qpat_assum `MEM ri (fn_insts rf)` (fn im =>
             qpat_assum `MEM (Label "runtime_begin") ri.inst_operands`
               (CONTR_TAC o MP (NOT_ELIM (MATCH_MP absent (CONJ fm im)))))))) >>
  `fin = asm_opt_finalizer ==>
    label_flow_own_ok runtime_unit.cu_context /\
    (!fn inst. MEM fn runtime_unit.cu_context.ctx_functions /\
               MEM inst (fn_insts fn) ==> ~MEM (Label "code_end") inst.inst_operands) /\
    EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
      ds.ds_items) runtime_unit.cu_data_segment /\
    ((?fn inst. MEM fn runtime_unit.cu_context.ctx_functions /\
               MEM inst (fn_insts fn) /\
               MEM (Label "runtime_begin") inst.inst_operands) ==>
      EXISTS (\ds. ds.ds_label = "runtime_begin") runtime_unit.cu_data_segment) /\
    LENGTH vs.vs_data_section < dimword (:256) DIV 2` by
    (strip_tac >> asm_rewrite_tac[] >> simp[]) >>
  `!gs.
     ?D f extra.
       dead_wf D /\
       (fin = asm_opt_finalizer ==>
         !fn inst s.
           raw_reachable (vs with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>)
             runtime_unit.cu_context fn inst s /\
           gas_cut (MIN (LENGTH (markf gs)) (LENGTH gs))
             (vs with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>) s ==>
           inst_dload_in_section inst s) /\
       o1_safe_upto D 0 (MIN (LENGTH (markf gs)) (LENGTH gs)) runtime_unit.cu_context
         (vs with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
       MAP project_site (gas_events_blocks f runtime_unit.cu_context entry_fn
         (vs with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp;
                    vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>)) =
         markf gs ++ extra` by
    (qunabbrev_tac `project_site` >> suspend "linked_runtime_raw_focus") >>
  mp_tac (Q.INST [`unit` |-> `runtime_unit`, `out` |-> `runtime_out`,
    `vs0` |-> `vs`, `cpl` |-> `cplan`, `es0` |-> `es`,
    `nm` |-> `"__entry"`, `entryfn` |-> `entry_fn`, `lbl` |-> `"__entry"`,
    `lo` |-> `0`, `result` |-> `r`, `final` |-> `es'`,
    `project` |-> `project_site`, `markf` |-> `markf`]
      (Q.INST_TYPE [`:'a` |-> `:bool`] focus_producer_finalizer_static_own)) >>
  BETA_TAC >> PURE_REWRITE_TAC [asm_frame_rel_tail_nil] >>
  impl_tac
  >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`raw_slots`,`sites`,`unused`]
    (map_every assume_tac o CONJUNCTS)) >>
  PURE_REWRITE_TAC [gas_readings_rel_def] >>
  Q.ISPECL_THEN
    [`sites`, `project_site`,
     `raw_slots`,`unused`,`gas_readings es`,`markf`]
    (match_mp_tac o BETA_RULE) gas_mask_projection_padded >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `raw` >> strip_tac >>
  qpat_x_assum `!raw. LIST_REL _ raw_slots raw ==> _` (qspec_then `raw` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `tail` >> BETA_TAC >> strip_tac >>
  qabbrev_tac `vi = vs with <|vs_gas_readings := raw ++ [0w];
    vs_fmp := fmp; vs_initial_fmp := fmp|>` >>
  qabbrev_tac `marks = markf (raw ++ [0w])` >>
  qabbrev_tac `gs = gas_explicit marks vi.vs_gas_readings ++ tail` >>
  suspend "linked_runtime_replay_result"
QED

Resume vyper_call_correct_mods[linked_runtime_raw_focus]:
  gen_tac >>
  qabbrev_tac `vi = vs with <|vs_gas_readings := gs;
    vs_fmp := fmp; vs_initial_fmp := fmp|>` >>
  `initial_venom_state_rel_mods mods am selected vi` by
    (qpat_assum `initial_venom_state_rel_mods mods am selected vs` mp_tac >>
     simp[NoAsms, Abbr `vi`, initial_venom_state_rel_mods_def,
          venom_env_rel_def, call_ctx_rel_def]) >>
  `code_layout_valid vi` by
    (qpat_assum `code_layout_valid vs` mp_tac >> simp[NoAsms, Abbr `vi`, code_layout_valid_def]) >>
  `vi.vs_gas_readings = gs /\ vi.vs_initial_fmp = fmp` by simp[NoAsms, Abbr `vi`] >>
  qpat_assum `Abbrev (vi = _)` (fn vi =>
    qpat_assum `!gs. source_unit_execution_correct_with_mods _ _ _ _ _ _ _ _ _`
      (qspec_then `gs` (assume_tac o PURE_REWRITE_RULE
        [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] vi)]))) >>
  mp_tac (Q.INST [`unit` |-> `runtime_unit`, `rp` |-> `rpolicy`,
    `tx` |-> `selected`, `vs` |-> `vi`, `func` |-> `entry_fn`,
    `marks` |-> `(markf:bytes32 list -> bool list) gs`,
    `ret` |-> `external_return_type_mods mods exps selected.function_name`]
    (SPEC_ALL linked_runtime_certificate_raw_entry_boundary)) >>
  impl_tac
  >- (rpt conj_tac >>
      (first_assum ACCEPT_TAC ORELSE
        (strip_tac >> asm_rewrite_tac[]))) >>
  disch_then (qx_choosel_then [`D`,`nfuel`,`extra`] (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`D`,`nfuel`,`extra`] >>
  qpat_assum `Abbrev (vi = _)`
    (fn vi => PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] vi),
       venom_state_fupdcanon]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `vi.vs_gas_readings = gs` (fn reads =>
    conj_tac
    >- (strip_tac >>
        qpat_assum `!fn inst s. raw_reachable vi _ fn inst s /\ _ ==>
            inst_dload_in_section inst s`
          (ACCEPT_TAC o PURE_REWRITE_RULE [reads])) >>
    conj_tac
    >- qpat_assum `o1_safe_upto D 0 _ runtime_unit.cu_context vi`
           (ACCEPT_TAC o PURE_REWRITE_RULE [reads]) >>
    first_assum ACCEPT_TAC)
QED

Resume vyper_call_correct_mods[linked_runtime_replay_result]:
  `vi.vs_outcomes = MAP SND (call_trace es) /\
    vi.vs_fmp = fmp /\ vi.vs_initial_fmp = fmp /\
    vi.vs_code = vs.vs_code /\ vi.vs_data_section = vs.vs_data_section` by
    (qpat_assum `vs.vs_outcomes = _` (fn outcomes =>
       simp[NoAsms, Abbr `vi`, outcomes])) >>
  `call_storage_ok am selected vi.vs_outcomes gs` by
    simp[Abbr `gs`, Abbr `vi`, Abbr `marks`] >>
  `gs = gas_explicit marks (raw ++ [0w]) ++ tail` by
    simp[NoAsms, Abbr `gs`, Abbr `vi`] >>
  qpat_assum `gs = _` (PURE_REWRITE_TAC o single o GSYM) >>
  Cases_on `source_exempt_mods mods (call_external (SOME vi.vs_outcomes) gs am selected)`
  >- (qpat_x_assum `source_exempt_mods mods _` mp_tac >>
      qpat_assum `vi.vs_outcomes = _` (fn outcomes =>
        PURE_REWRITE_TAC [outcomes, source_exempt_mods_def, call_result_rel_at_mods_def,
                          exception_outcome_rel_mods_def, LET_THM]) >>
      Cases_on `call_external (SOME (MAP SND (call_trace es))) gs am selected` >>
      rename1 `call_external _ _ _ _ = (result,rest_result)` >>
      Cases_on `rest_result` >> Cases_on `result` >> simp[] >>
      rename1 `INR ex` >> Cases_on `ex` >> simp[]) >>
  `initial_venom_state_rel_mods mods am selected vi` by
    (qpat_assum `initial_venom_state_rel_mods mods am selected vs` mp_tac >>
     simp[NoAsms, Abbr `vi`, initial_venom_state_rel_mods_def, venom_env_rel_def]) >>
  `code_layout_valid vi` by
    (qpat_assum `code_layout_valid vs` mp_tac >>
     simp[NoAsms, Abbr `vi`, code_layout_valid_def]) >>
  `source_unit_execution_correct_with_mods shadow_ctx marks mods exps
     (external_return_type_mods mods exps selected.function_name) am selected runtime_unit vi` by
    (qunabbrev_tac `marks` >> qunabbrev_tac `vi` >>
     qpat_assum `!gs. source_unit_execution_correct_with_mods _ _ _ _ _ _ _ _ _`
       (qspec_then `raw ++ [0w]` ACCEPT_TAC)) >>
  mp_tac (Q.INST [`unit` |-> `runtime_unit`, `tx` |-> `selected`,
    `vs` |-> `vi`, `marks` |-> `marks`,
    `ret` |-> `external_return_type_mods mods exps selected.function_name`]
    (SPEC_ALL linked_runtime_certificate_exit)) >>
  qpat_assum `Abbrev (gs = _)` (fn gas =>
    PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] gas)]) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`raw_fn`,`raw_fuel`] (map_every assume_tac o CONJUNCTS)) >>
  `raw_fn = entry_fn` by
    (qpat_assum `venomInst$lookup_function "__entry" runtime_unit.cu_context.ctx_functions = SOME raw_fn`
       (fn raw_lookup =>
         qpat_assum `venomInst$lookup_function "__entry" runtime_unit.cu_context.ctx_functions = SOME entry_fn`
           (mp_tac o PURE_REWRITE_RULE [raw_lookup])) >>
     simp[NoAsms]) >>
  qpat_x_assum `raw_fn = entry_fn` SUBST_ALL_TAC >>
  qabbrev_tac `obs = source_storage_trace am selected vi.vs_outcomes gs` >>
  `valid_horizon (initial_evaluation_context am.sources am.layouts selected NONE)
    (initial_state am []) (storage_trace_horizon obs) obs` by
    (qpat_assum `storage_trace_domain _ _ _` (mp_tac o REWRITE_RULE [storage_trace_domain_def]) >>
     simp[NoAsms]) >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon obs` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `D = cx_dead (storage_trace_horizon obs)
    (initial_evaluation_context am.sources am.layouts selected NONE)` >>
  `dead_wf D` by
    (simp[Abbr `D`, cx_dead_def, initial_evaluation_context_def] >>
     MATCH_ACCEPT_TAC
       (SIMP_RULE (srw_ss()) [external_call_dead_def]
         (Q.INST [`src` |-> `(INL NoneV, am, [])`] external_call_dead_wf))) >>
  `w2n vi.vs_initial_fmp <= w2n vi.vs_fmp` by simp[] >>
  `mem_inv dload_offset_ok runtime_unit.cu_context vi /\
    mem_inv dload_headroom_ok runtime_unit.cu_context vi /\
    mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
      s.vs_code = vi.vs_code /\ s.vs_data_section = vi.vs_data_section)
      runtime_unit.cu_context vi` by
    (rpt conj_tac
     >- (qspecl_then [`mods`,`exps`,`rpolicy`,`runtime_unit`,`vi`,`entry_fn`,`"__entry"`]
           mp_tac lower_vyper_runtime_unit_dload_offset_ok_mods >> simp[])
     >- (qspecl_then [`mods`,`exps`,`rpolicy`,`runtime_unit`,`am`,`selected`,`vi`]
           mp_tac lower_vyper_runtime_unit_dload_headroom_ok_mods >> simp[]) >>
     qspecl_then [`mods`,`exps`,`rpolicy`,`runtime_unit`,`vi`,`entry_fn`,`"__entry"`]
       mp_tac lower_vyper_runtime_unit_dload_in_section_mods >> simp[]) >>
  `ptr_discipline 0 runtime_unit.cu_context vi` by
    (qspecl_then [`mods`, `exps`, `rpolicy`, `runtime_unit`, `vi`, `entry_fn`, `"__entry"`, `D`]
      mp_tac lower_vyper_runtime_unit_ptr_taint_mods >> simp[]) >>
  `raw_unit_memory_ok runtime_unit.cu_context vi /\
    ptr_discipline 0 runtime_unit.cu_context vi /\
    taint_within D runtime_unit.cu_context vi` by
    (Cases_on `ctx_has_dalloca runtime_unit.cu_context`
     >- (`!f inst s. raw_reachable vi runtime_unit.cu_context f inst s ==>
          dalloca_no_wrap inst s /\ w2n s.vs_initial_fmp <= w2n s.vs_fmp` by
           (qspecl_then [`0`,`runtime_unit.cu_context`,`"__entry"`,`entry_fn`,`"__entry"`,`vi`]
              mp_tac lowered_unit_checked_dalloca_facts >> asm_rewrite_tac[]) >>
         qspecl_then [`mods`,`exps`,`rpolicy`,`runtime_unit`,`am`,`selected`,
                      `vi`,`entry_fn`,`"__entry"`,`D`]
           mp_tac lower_vyper_runtime_unit_memory_ok_from_no_wrap_mods >>
         impl_tac >- asm_rewrite_tac[] >> simp[]) >>
     qspecl_then [`mods`,`exps`,`rpolicy`,`runtime_unit`,`am`,`selected`,
                  `vi`,`entry_fn`,`"__entry"`,`D`]
       mp_tac lower_vyper_runtime_unit_memory_ok_mods >> simp[]) >>
  `mem_inv raw_mem_ok runtime_unit.cu_context vi` by
    (PURE_REWRITE_TAC [mem_inv_def, raw_mem_ok_def] >>
     qpat_assum `raw_unit_memory_ok _ _`
       (ACCEPT_TAC o PURE_REWRITE_RULE [raw_unit_memory_ok_def])) >>
  `fmp_free_ctx runtime_unit.cu_context` by drule_all_then ACCEPT_TAC source_fmp_free >>
  `o1_src_inv D runtime_unit.cu_context vi` by
    (simp[o1_src_inv_def] >> qexists_tac `0` >> asm_rewrite_tac[]) >>
  `o1_pre_walk_inv D runtime_unit.cu_context vi` by
    drule_all_then ACCEPT_TAC o1_source_pre_walk_inv >>
  qpat_x_assum `!D. (?fr. terminates _) /\ _ ==> _`
    (qspec_then `D` mp_tac) >>
  qpat_assum `Abbrev (vi = _)`
    (fn vi => PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] vi)]) >>
  impl_tac
  >- (conj_tac >- (qexists_tac `raw_fuel` >> first_assum ACCEPT_TAC) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      strip_tac >>
      qpat_assum `vi.vs_code = vs.vs_code` (fn code =>
        qpat_assum `vi.vs_data_section = vs.vs_data_section` (fn data =>
          qpat_assum `mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\ _) _ vi`
            (ACCEPT_TAC o PURE_REWRITE_RULE [code, data])))) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `D = external_call_dead (storage_trace_horizon obs) selected
      (call_external (SOME vi.vs_outcomes) gs am selected)` by
    (Cases_on `call_external (SOME vi.vs_outcomes) gs am selected` >>
     rename1 `call_external _ _ _ _ = (result,rest_result)` >>
     Cases_on `rest_result` >>
     simp[NoAsms, Abbr `D`, cx_dead_def, external_call_dead_def, initial_evaluation_context_def]) >>
  suspend "linked_runtime_result_codegen"
QED

Resume vyper_call_correct_mods[linked_runtime_result_codegen]:
  `fin = K SOME ==> initial_ctx_rel cplan prog runtime_out.po_unit.cu_context vs es` by
    suspend "linked_runtime_identity_entry" >>
  `obs = source_storage_trace am selected (MAP SND (call_trace es)) gs` by
    simp[Abbr `obs`] >>
  `external_call_result_rel_mods (storage_trace_horizon obs) mods exps
      (external_return_type_mods mods exps selected.function_name) selected
      (call_external (SOME (MAP SND (call_trace es))) gs am selected)
      (run_context raw_fuel runtime_unit.cu_context vi)` by
    (qpat_assum `vi.vs_outcomes = _` (fn outcomes =>
       qpat_assum `external_call_result_rel_mods _ _ _ _ _ _ _`
         (ACCEPT_TAC o PURE_REWRITE_RULE [outcomes]))) >>
  `ctx_sim
      (external_call_dead (storage_trace_horizon obs) selected
        (call_external (SOME (MAP SND (call_trace es))) gs am selected))
      runtime_unit.cu_context runtime_out.po_unit.cu_context vi vs` by
    (qpat_assum `vi.vs_outcomes = _` (fn outcomes =>
       qpat_assum `D = external_call_dead _ _ _` (fn dead =>
         qpat_assum `ctx_sim D _ _ _ _`
           (ACCEPT_TAC o PURE_REWRITE_RULE [dead, outcomes])))) >>
  `call_result_rel_at_mods gs mods exps am selected es r es'`
    suffices_by simp[Abbr `gs`, Abbr `vi`, Abbr `marks`] >>
  qpat_x_assum `(o1_lowered_inv _ _ /\ _) \/ _`
    (DISJ_CASES_THEN (map_every assume_tac o CONJUNCTS))
  >- suspend "linked_runtime_result_normal" >>
  suspend "linked_runtime_result_static_abort"
QED

Resume vyper_call_correct_mods[linked_runtime_result_normal]:
  qspecl_then [`runtime_out`,`cplan`,`vs`] mp_tac o1_pipeline_memory_obligations_raw >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then assume_tac o1_pipeline_codegen_obligations >>
  `!n. ?r' es''. run_call es = SOME (r',es'') /\
      (frame_resource_starved es r' es'' \/
       venom_frame_rel es r' es'' (run_context n runtime_out.po_unit.cu_context vs))` by
    (gen_tac >> Cases_on `fin = K SOME`
     >- (qspecl_then [`n`,`rpolicy`,`runtime_out.po_unit`,`cplan`,`prog`,
                      `raw_reachable vs`,`vs`,`es`] mp_tac codegen_correct >>
         simp[]) >>
     `fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
     qpat_x_assum `fin = asm_opt_finalizer` SUBST_ALL_TAC >>
     qspecl_then [`n`,`rpolicy`,`runtime_out.po_unit`,`cplan`,`prog`,`prog'`,
                  `raw_reachable vs`,`vs`,`es`] mp_tac codegen_correct_asm_opt_own >>
     simp[]) >>
  mp_tac (Q.INST [`tx` |-> `selected`, `ctx` |-> `runtime_unit.cu_context`,
      `ctx'` |-> `runtime_out.po_unit.cu_context`, `vs` |-> `vi`, `vs'` |-> `vs`,
      `fuel` |-> `raw_fuel`, `ret` |-> `external_return_type_mods mods exps selected.function_name`]
    (SPEC_ALL linked_call_at_horizon_composition)) >>
  qpat_assum `obs = _` (fn trace => PURE_REWRITE_TAC [GSYM trace]) >>
  simp[]
QED

Resume vyper_call_correct_mods[linked_runtime_result_static_abort]:
  `!fn inst l. MEM fn runtime_out.po_unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) /\
     inst.inst_opcode <> PHI /\ MEM (Label l) (compute_operands inst) ==>
     IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)` by
    (mp_tac (Q.INST [`rp` |-> `rpolicy`, `unit` |-> `runtime_out.po_unit`,
                    `prog` |-> `prog`] request_cut_compute_labels_bound) >>
     impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
       conj_tac >- first_assum ACCEPT_TAC >>
       qpat_assum `sym_unit_static_ok runtime_out.po_unit`
         (ACCEPT_TAC o cj 2 o PURE_REWRITE_RULE [sym_unit_static_ok_def])) >>
     disch_then ACCEPT_TAC) >>
  qspecl_then [`rpolicy`,`runtime_unit`,`runtime_out`,`cplan`,`vs`]
    mp_tac o1_pipeline_context_obligations_lowered_abort >>
  impl_tac >- simp[lowered_mem_fact_def] >>
  disch_then (qx_choose_then `Inv` (map_every assume_tac o CONJUNCTS)) >>
  `!fn inst s. raw_reachable vs runtime_out.po_unit.cu_context fn inst s ==>
      Inv runtime_out.po_unit.cu_context fn inst s` by
    (rpt gen_tac >> strip_tac >> irule raw_reachable_least >>
     qexists_tac `vs` >> conj_tac >> first_assum ACCEPT_TAC) >>
  `codegen_context_obligations_abort (raw_reachable vs) runtime_out.po_unit.cu_context cplan` by
    (qpat_assum `!fn inst s. raw_reachable vs _ fn inst s ==> Inv _ fn inst s` mp_tac >>
     qpat_assum `codegen_context_obligations_abort Inv _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     PURE_REWRITE_TAC [codegen_context_obligations_abort_def, codegen_memory_obligations_abort_def] >>
     metis_tac[]) >>
  `codegen_reachability_package (raw_reachable vs) runtime_out.po_unit.cu_context vs` by
    (qpat_assum `codegen_reachability_package Inv _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     PURE_REWRITE_TAC [raw_reachable_package_iff, codegen_reachability_package_def] >>
     metis_tac[]) >>
  `!n a u. run_context n runtime_out.po_unit.cu_context vs = Abort a u ==>
     ?r' es''. run_call es = SOME (r',es'') /\
       (frame_resource_starved es r' es'' \/
        ?exc output lgs. frame_outcome es r' es'' (SOME exc) output lgs)` by
    (rpt gen_tac >> strip_tac >> Cases_on `fin = K SOME`
     >- (qspecl_then [`n`,`rpolicy`,`runtime_out.po_unit`,`cplan`,`prog`,
         `raw_reachable vs`,`vs`,`es`,`a`,`u`] mp_tac codegen_correct_static_abort >>
         impl_tac >- (qpat_x_assum `prog = _` kall_tac >> BETA_TAC >>
             simp[] >> first_assum ACCEPT_TAC) >>
         disch_then (ACCEPT_TAC o CONJUNCT1)) >>
     `fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
     qpat_x_assum `fin = asm_opt_finalizer` SUBST_ALL_TAC >>
     qspecl_then [`n`,`rpolicy`,`runtime_out.po_unit`,`cplan`,`prog`,`prog'`,
       `raw_reachable vs`,`vs`,`es`,`a`,`u`] mp_tac codegen_correct_static_abort_asm_opt_own >>
     impl_tac >- (qpat_x_assum `prog = _` kall_tac >> BETA_TAC >>
        qpat_assum `asm_opt_finalizer = asm_opt_finalizer ==> code_end_offset_ok _ _`
          (assume_tac o (fn offset => MATCH_MP offset (REFL ``asm_opt_finalizer``))) >>
        simp[] >> first_assum ACCEPT_TAC) >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  mp_tac (Q.INST [`tx` |-> `selected`, `ctx` |-> `runtime_unit.cu_context`,
      `ctx'` |-> `runtime_out.po_unit.cu_context`, `vs` |-> `vi`, `vs'` |-> `vs`,
      `fuel` |-> `raw_fuel`, `ret` |-> `external_return_type_mods mods exps selected.function_name`]
    (SPEC_ALL linked_call_at_horizon_static_abort_composition)) >>
  qpat_assum `obs = _` (fn trace => PURE_REWRITE_TAC [GSYM trace]) >>
  impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[NoAsms])) >>
  disch_then ACCEPT_TAC
QED

Resume vyper_call_correct_mods[linked_runtime_identity_entry]:
  strip_tac >>
  `prog' = prog` by fs[] >>
  qpat_x_assum `prog' = prog` SUBST_ALL_TAC >>
  `vs = entry_venom_state prog cplan es` by
    simp[Abbr `vs`, opt_entry_state_own_identity] >>
  `?fn fns. runtime_out.po_unit.cu_context.ctx_functions = fn::fns /\
      get_params (HD fn.fn_blocks).bb_instructions = []` by
    (qpat_assum `unit_shape_ok _`
       (mp_tac o PURE_REWRITE_RULE [unit_shape_ok_def, entry_fn_first_def]) >>
     disch_then (CONJUNCTS_THEN2
       (qx_choosel_then [`entry_name`, `entry_fn`, `other_fns`] strip_assume_tac)
       strip_assume_tac) >>
     qexistsl [`entry_fn`, `other_fns`] >> conj_tac
     >- FIRST_ASSUM ACCEPT_TAC >>
     qpat_assum `get_params (HD (HD _).fn_blocks).bb_instructions = []` mp_tac >>
     qpat_assum `runtime_out.po_unit.cu_context.ctx_functions = entry_fn::other_fns`
       SUBST1_TAC >>
     simp[NoAsms]) >>
  `es.txParams.blockNumber < dimword (:256)` by
    (fs[frame_tx_rel_def, tx_block_fields_rel_def, tx_env_ok_def] >>
     irule lt_dimword_256 >> qexists_tac `255` >> simp[]) >>
  drule_all entry_venom_state_evm_environment >> strip_tac >>
  `initial_state_rel cplan prog 0 fn vs es` by
    (qpat_assum `vs = entry_venom_state _ _ _` SUBST1_TAC >>
     qpat_assum `es.contexts = (ctxt,rb)::rest` (fn contexts =>
       qpat_assum `frame_fresh ctxt` (fn fresh =>
         qpat_assum `get_params (HD fn.fn_blocks).bb_instructions = []` (fn params =>
           qpat_assum `ctxt.msgParams.outputTo = Memory mr` (fn output =>
             qpat_assum `!prog cp'. msg_ctx_rel _ _ /\ _`
               (fn env => simp[NoAsms, contexts, params, output,
                 PURE_REWRITE_RULE [frame_fresh_def] fresh,
                 Q.SPECL [`prog`,`cplan`] env, initial_state_rel_def,
                 stack_params_rel_def, entry_venom_state_fresh,
                 entry_venom_state_frame_fields, entry_venom_state_created_in_tx,
                 asm_pc_to_offset_zero, context_memory_rel_def])))))) >>
  `ctxt.msgParams.parsed = parse_code 0 FEMPTY ctxt.msgParams.code` by
    (qpat_assum `es.contexts = (ctxt,rb)::rest` (fn h =>
       qpat_assum `evm_state_ok es` (mp_tac o SIMP_RULE (srw_ss())
          [h, evm_state_ok_def, wf_state_def, wf_context_def])) >>
     strip_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  `ctxt.msgParams.code = assemble prog ++ vs.vs_data_section` by
    (`vs.vs_code = ctxt.msgParams.code` by
       (qpat_assum `vs = entry_venom_state _ _ _` SUBST1_TAC >>
        qpat_assum `es.contexts = (ctxt,rb)::rest`
          (fn th => simp_tac (srw_ss()) [th, entry_venom_state_frame_fields])) >>
     qpat_assum `vs.vs_code = ctxt.msgParams.code`
       (fn th => REWRITE_TAC [GSYM th]) >>
     FIRST_ASSUM ACCEPT_TAC) >>
  `ctxt.msgParams.code <> [] ==>
      account_already_created (lookup_account ctxt.msgParams.callee es.rollback.accounts)` by
    (qpat_assum `frame_tx_rel tx es ctxt`
       (strip_assume_tac o PURE_REWRITE_RULE [frame_tx_rel_def]) >>
     qpat_assum `ctxt.msgParams.callee = tx.target` (fn th => REWRITE_TAC [th]) >>
     qpat_assum `(lookup_account tx.target es.rollback.accounts).code = ctxt.msgParams.code`
       (fn th => simp_tac (srw_ss()) [account_already_created_def, NULL_EQ, th])) >>
  `initial_ctx_rel cplan prog runtime_out.po_unit.cu_context vs es` by
    (qpat_assum `frame_fresh ctxt`
       (strip_assume_tac o PURE_REWRITE_RULE [frame_fresh_def]) >>
     qpat_assum `evm_state_ok es`
       (strip_assume_tac o PURE_REWRITE_RULE [evm_state_ok_def]) >>
     qpat_assum `vs = entry_venom_state _ _ _` (fn th =>
       let val entry = Q.SPECL [`prog`, `cplan`, `es`]
       in map_every (strip_assume_tac o SUBS [GSYM th] o entry)
            [entry_venom_state_fresh, entry_venom_state_frame_fields]
       end) >>
     `vs.vs_params = []` by
       (qpat_assum `vs = entry_venom_state _ _ _` SUBST1_TAC >>
        simp[NoAsms, entry_venom_state_def, init_venom_state_def]) >>
     PURE_REWRITE_TAC [initial_ctx_rel_def] >>
     qexistsl [`fn`, `fns`, `ctxt`, `rb`, `rest`] >>
     rpt conj_tac >>
     FIRST [FIRST_ASSUM ACCEPT_TAC,
            qexists_tac `d` >> FIRST_ASSUM ACCEPT_TAC,
            strip_tac >>
            qpat_assum `ctxt.msgParams.code <> [] ==> _`
              (fn th => irule th) >> FIRST_ASSUM ACCEPT_TAC])
  >> first_assum ACCEPT_TAC
QED

Finalise vyper_call_correct_mods

(* Both deployment tops start from the constructor selected by lowering. *)
val linked_deploy_constructor_source_tac =
  rename1 `classify_functions_unit mods exps = (exts,ints,fb,SOME constructor,imp_ctors)` >>
  `?tops. ALOOKUP mods NONE = SOME tops` by
    (qpat_assum `deploy_state_rel_mods mods exps (assemble prog') am tx _`
       (strip_assume_tac o PURE_REWRITE_RULE [deploy_state_rel_mods_def]) >>
     Cases_on `ALOOKUP mods NONE` >> fs[]) >>
  drule_all linked_deploy_constructor_source >>
  disch_then (qx_choosel_then [`mut`,`src_args`,`raw_body`] strip_assume_tac) >>
  `LENGTH tx.args = LENGTH src_args /\ tx.function_name = "__init__"` by
    (qpat_assum `deploy_state_rel_mods mods exps (assemble prog') am tx _`
       (strip_assume_tac o REWRITE_RULE [deploy_state_rel_mods_def]) >>
     conj_tac >- (
       qpat_assum `constructor_args_encode_mods mods tx _` mp_tac >>
       qpat_assum `ALOOKUP mods NONE = SOME _` (fn main_lookup =>
         qpat_assum `vyperInterpreter$lookup_function NONE "__init__" Deploy _ =
           SOME (mut,F,src_args,[],NoneT,raw_body)` (fn constructor_lookup =>
           simp[NoAsms, constructor_args_encode_mods_def, main_module_def, LET_THM,
                main_lookup, constructor_lookup])) >>
       strip_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     FIRST_ASSUM ACCEPT_TAC);

val linked_deploy_constructor_package_tac =
  Cases_on `set_constructor_package_target rpolicy.rpol_target
    (package_constructor_unit mods T (K global_nonreentrant_slot) constructor)` >>
  rename1 `set_constructor_package_target _ _ = cpkg` >>
  PairCases_on `cpkg` >>
  drule_all linked_deploy_constructor_run >> strip_tac;

val linked_deploy_constructor_package_flags_tac =
  `cpkg0.ce_nonreentrant = (F,global_nonreentrant_slot,T,F) /\
    cpkg2 = (mut = Payable)` by
    (qpat_assum `constructor = (mut,F,F,"__init__",src_args,[],NoneT,_)`
       (fn ctor => qpat_assum `set_constructor_package_target _ _ = _`
         (mp_tac o PURE_REWRITE_RULE [ctor, package_constructor_unit_def,
             LET_THM, combinTheory.K_THM])) >>
     simp_tac (srw_ss()) [set_constructor_package_target_def, update_cenv_nonreentrant_def] >>
     strip_tac >>
     asm_rewrite_tac[] >>
     qpat_assum `_ = cpkg0` (SUBST1_TAC o SYM) >>
     qpat_assum `mut <> View` (fn nview => simp[NoAsms, nview]));

val linked_deploy_constructor_code_tac =
  qmatch_asmsub_abbrev_tac
    `run_deploy_lowering T rpolicy runtime_bc (imm_len_mods mods)
      cpkg1 0 internals cpkg0 cpkg6 cpkg2 cpkg3 cpkg4 cpkg5 "__deploy"` >>
  `EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors internals)` by
    simp[Abbr `internals`, unit_package_internal_labels] >>
  drule_all run_linked_deploy_constructor_code >> strip_tac;

val linked_deploy_ctor_ptr_environment_tac = fn frame_quote =>
  mp_tac (Q.INST [`unit` |-> `deploy_unit`, `deploy_bc` |-> `assemble prog'`,
      `es` |-> frame_quote, `ce0` |-> `cpkg0`, `pos_args` |-> `cpkg1`,
      `payable` |-> `mut = Payable`, `nr` |-> `F`, `key` |-> `global_nonreentrant_slot`,
      `ut` |-> `T`, `ctor_body` |-> `cpkg6`, `ret` |-> `cpkg7`,
      `cf` |-> `constructor`, `imported_ctor_fns` |-> `imp_ctors`,
      `cap` |-> `imm_len_mods mods`, `ce` |-> `ctor_ce`]
    deploy_ptr_ctor_environment_mods) >>
  impl_tac >- (simp[Abbr `ctor_ce`] >> rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  strip_tac;

val linked_deploy_ctor_accepted_inputs_tac =
  qpat_assum `deploy_state_rel_mods mods exps (assemble prog') am tx _`
    (strip_assume_tac o PURE_REWRITE_RULE [deploy_state_rel_mods_def]) >>
  rename1 `constructor_args_encode_mods mods tx args_bytes` >>
  qpat_assum `constructor_args_encode_mods mods tx args_bytes` mp_tac >>
  qpat_assum `ALOOKUP mods NONE = SOME _` (fn main_lookup =>
    qpat_assum `vyperInterpreter$lookup_function NONE "__init__" Deploy _ =
      SOME (mut,F,src_args,[],NoneT,raw_body)` (fn ctor_lookup =>
        simp[NoAsms, constructor_args_encode_mods_def, LET_THM, main_module_def,
             main_lookup, ctor_lookup, optionTheory.IS_SOME_EXISTS])) >>
  strip_tac >>
  rename1 `bind_arguments (type_env_all_modules mods) src_args tx.args = SOME scope` >>
  rename1 `vyper_to_abi_list (type_env_all_modules mods) (MAP SND src_args) tx.args = SOME avs` >>
  drule_all_then assume_tac (Q.INST [`in_deploy` |-> `T`] ctor_task_checked_params) >>
  `contract_namespaces_ok T mods` by
    (qpat_assum `check_contract T _ _ mods = SOME _`
       (ACCEPT_TAC o MATCH_MP check_contract_namespaces_ok)) >>
  `fn_allocs_ok_unit mods (NONE,constructor)` by
    (qpat_assum `lower_vyper_deploy_unit_mods mods exps _ _ = SOME deploy_unit` mp_tac >>
     qpat_assum `classify_functions_unit mods exps = (exts,ints,fb,SOME constructor,imp_ctors)`
        (fn class_eq => simp[NoAsms, lower_vyper_deploy_unit_mods_def, class_eq,
                             LET_THM, EVERY_APPEND, AllCaseEqs()]) >>
     rpt strip_tac >> FIRST_ASSUM ACCEPT_TAC);

val linked_deploy_ctor_source_trace_tac =
  qpat_assum `~(mut <> Payable /\ _)`
    (assume_tac o SIMP_RULE (srw_ss()) [DE_MORGAN_THM]) >>
  drule_all (Q.INST [`exps` |-> `exps`] linked_constructor_source_trace) >>
  disch_then (qx_choosel_then [`imms`,`am0`,`am_c`,`es0`]
    (map_every assume_tac o CONJUNCTS));

val linked_deploy_ctor_registration_metadata_tac =
  qabbrev_tac `ce_before_registration = cpkg0 with ce_imm_alloca :=
    if imm_len_mods mods > 0 then SOME imm else NONE` >>
  `cpkg6 = subst_consts_stmts_mods (consts_env_mods mods) raw_body /\ cpkg7 = NoneT` by
    (qpat_assum `constructor = _` (fn ctor =>
       qpat_assum `set_constructor_package_target _ _ = _` mp_tac >>
       simp[NoAsms, ctor, set_constructor_package_target_def, package_constructor_unit_def]) >>
     simp[]) >>
  `fn_allocs_ok_unit mods (NONE,(mut,F,F,"__init__",src_args,[],
      NoneT,subst_consts_stmts_mods (consts_env_mods mods) raw_body))` by
    (qpat_assum `constructor = _` (PURE_REWRITE_TAC o single o SYM) >>
     first_assum ACCEPT_TAC) >>
  `set_constructor_package_target rpolicy.rpol_target
     (package_constructor_unit mods T (K global_nonreentrant_slot)
       (mut,F,F,"__init__",src_args,([]:expr list),NoneT,
        subst_consts_stmts_mods (consts_env_mods mods) raw_body)) =
     (cpkg0,cpkg1,mut = Payable,F,global_nonreentrant_slot,T,
      subst_consts_stmts_mods (consts_env_mods mods) raw_body,NoneT)` by
    (qpat_assum `constructor = _` (fn ctor =>
       qpat_assum `cpkg6 = _` (fn body =>
         qpat_assum `cpkg7 = NoneT` (fn ret =>
           qpat_assum `set_constructor_package_target _ _ =
               (cpkg0,cpkg1,mut = Payable,F,global_nonreentrant_slot,T,cpkg6,cpkg7)`
             (ACCEPT_TAC o PURE_REWRITE_RULE [ctor, body, ret]))))) >>
  `ce_before_registration = cpkg0 with ce_imm_alloca :=
     if imm_len_mods mods > 0 then SOME imm else NONE` by
    simp[Abbr `ce_before_registration`] >>
  drule_at (Pat `set_constructor_package_target _ (package_constructor_unit _ _ _ (_,_,_,_,_,_,_,_)) = _`)
    linked_constructor_registration_metadata >>
  disch_then (drule_at (Pat `ce_before_registration = _ with ce_imm_alloca := _`)) >>
  disch_then (drule_at (Pat `bind_arguments _ _ _ = _`)) >>
  disch_then (drule_at (Pat `vyper_to_abi_list _ _ _ = _`)) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS);

fun linked_deploy_ctor_prefix_fields_tac frame ctxt_code =
  `vs.vs_call_ctx.cc_callvalue = n2w tx.value` by
    (qpat_assum ([QUOTE "deploy_state_rel_mods mods exps (assemble prog') am tx "] @ frame)
       (strip_assume_tac o PURE_REWRITE_RULE [deploy_state_rel_mods_def]) >>
     simp[Abbr `vs`, opt_entry_state_own_def, entry_venom_state_def]) >>
  `vs.vs_code = tx.code` by
    (qpat_assum `tx with code := vs.vs_code = tx`
       (mp_tac o AP_TERM ``\t:call_txn. t.code``) >> simp[NoAsms]) >>
  `vs.vs_data_section = args_bytes` by
    (qpat_assum `vs.vs_code = assemble prog' ++ vs.vs_data_section` (fn code =>
       qpat_assum `vs.vs_code = tx.code` (fn tx_code =>
         qpat_assum ([QUOTE "tx.code = "] @ ctxt_code) (fn input =>
           qpat_assum (ctxt_code @ [QUOTE " = assemble prog' ++ args_bytes"])
             (mp_tac o PURE_REWRITE_RULE [GSYM input, GSYM tx_code, code])))) >>
     simp[NoAsms]);

val linked_deploy_ctor_prefix_code_tac =
  `fn_has_code (initial_compile_state "__deploy") st1 fn /\ fn_has_code st1 st2 fn` by
    (qspecl_then [`mut = Payable`,`imm_len_mods mods`,
        `cpkg0`,`cpkg1`,`F`,`global_nonreentrant_slot`,`T`,
        `initial_compile_state "__deploy"`,`st_pay`,`imm`,`st1`,`ce1`,
        `st2`,`st2`,`exit_lbl`,`sa`,`fn`] mp_tac deploy_ctor_registration_code >>
     qpat_assum `ce_before_registration = cpkg0 with ce_imm_alloca := _`
       (fn ce => PURE_REWRITE_TAC [GSYM ce]) >>
     impl_tac
     >- (rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE simp[NoAsms, comp_return_def])) >>
     DISCH_THEN ACCEPT_TAC);

val linked_deploy_ctor_before_registration_tac =
  `!vi. raw_variant fmp vi vs ==>
    ?t. fresh_vars_wrt st1 t /\ ~t.vs_halted /\
      t.vs_current_bb = st1.cs_current_bb /\
      t.vs_inst_idx = LENGTH st1.cs_current_insts /\ eval_operand imm t = SOME 0w /\
      vars_pc_only vi t /\
      gas_path deploy_unit.cu_context fn
        (vi with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>)
        0 (OK t)` by
    suspend "linked_deploy_ctor_raw_prefix";

Theorem e2e_deploy_correctness_mods:
  !fin policy mods exps deploy_bc runtime_bc am tx es.
    fin IN accepted_finalizers /\
    compile_vyper_mods fin policy mods exps = SOME (deploy_bc, runtime_bc) /\
    deploy_typing_ok_mods mods exps am tx /\
    deploy_state_rel_mods mods exps deploy_bc am tx es /\
    LENGTH (call_trace es) < 2 ** 64
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (creation_resource_starved es r es' \/
       deploy_call_result_rel_mods mods exps runtime_bc am tx es r es')
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `compile_vyper_mods _ _ _ _ = _`
    (strip_assume_tac o MATCH_MP compile_vyper_with_mods_success_phases o
     REWRITE_RULE [compile_vyper_mods_def]) >>
  qpat_assum `deploy_typing_ok_mods _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [deploy_typing_ok_mods_def]) >>
  qpat_assum `check_contract T am.layouts tx.target mods = SOME _`
    (strip_assume_tac o MATCH_MP
      vyperTypeContractModesTheory.check_contract_deploy_implies_runtime) >>
  drule_all checked_lower_vyper_deploy_unit_source_shape_mods >> strip_tac >>
  drule lower_vyper_deploy_unit_raw_shape_mods >> strip_tac >>
  drule lower_vyper_deploy_unit_global_reserved_mods >> strip_tac >>
  `o1PipelineCorrect$o1_pipeline rpolicy deploy_unit = SOME deploy_out` by
    fs[o1PipelineCorrectTheory.o1_pipeline_def] >>
  drule_all o1PipelineCorrectTheory.run_venom_pipeline_output_shape >> strip_tac >>
  `deploy_unit.cu_data_segment =
      [<|ds_label := "runtime_begin"; ds_items := [DataBytes runtime_bc]|>]` by
    (drule_then ACCEPT_TAC lower_vyper_deploy_unit_runtime_data_mods) >>
  `?pre. deploy_out.po_unit.cu_data_segment =
      pre ++ [<|ds_label := "runtime_begin"; ds_items := [DataBytes runtime_bc]|>]` by
    (qpat_assum `o1PipelineCorrect$o1_pipeline _ deploy_unit = _`
       (mp_tac o REWRITE_RULE [o1PipelineCorrectTheory.o1_pipeline_def]) >>
     strip_tac >> drule deploy_pipeline_runtime_suffix >>
     disch_then (qspec_then `runtime_bc` mp_tac) >> simp[]) >>
  `!fn inst. MEM fn deploy_unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
     source_inst_ok ({"code_end"},T) inst` by
    (rpt strip_tac >>
     mp_tac (Q.INST [`unit` |-> `deploy_unit`, `rpolicy` |-> `rpolicy`,
                    `mods` |-> `mods`, `exps` |-> `exps`, `bytes` |-> `runtime_bc`,
                    `fn` |-> `fn`, `inst` |-> `inst`,
                    `checks` |-> `({"code_end"},T)`]
       lower_vyper_deploy_unit_label_checks_mods) >>
     simp[]) >>
  drule_all source_own_flow >> strip_tac >>
  drule_all gasFocusOptLabelFlowTheory.focus_opt_label_flow_own >> strip_tac >>
  `sym_unit_static_ok deploy_out.po_unit` by
    (qspecl_then [`rpolicy`, `deploy_unit`, `deploy_out`]
       mp_tac o1_pipeline_sym_unit_static_ok >> simp[]) >>
  `codegen_ready deploy_out.po_unit.cu_context` by
    (qpat_assum `o1PipelineCorrect$o1_pipeline _ deploy_unit = _`
       (mp_tac o MATCH_MP run_venom_pipeline_success_boundary o
        REWRITE_RULE [o1PipelineCorrectTheory.o1_pipeline_def]) >> simp[]) >>
  `runtime_bc <> []` by
    (qpat_assum `finalize_codegen fin rpolicy runtime_out.po_unit = SOME runtime_bc`
       (strip_assume_tac o MATCH_MP finalize_codegen_success_plan) >>
     Cases_on `fin = K SOME`
     >- (drule codegen_assembly_nonempty >> gvs[]) >>
     `fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
     qpat_assum `fin = asm_opt_finalizer` SUBST_ALL_TAC >>
     qpat_x_assum `runtime_bc = assemble prog'` SUBST1_TAC >>
     irule codegen_assembly_finalizer_nonempty >>
     qexistsl [`prog`,`rpolicy`,`runtime_out.po_unit`] >> simp[]) >>
  `~(?t. runtime_bc = 0xEFw :: t)` by metis_tac[finalize_codegen_not_ef] >>
  qspec_then `es` (qx_choosel_then [`r`, `es'`] assume_tac) run_call_total >>
  qexistsl [`r`, `es'`] >> simp[] >>
  Cases_on `creation_resource_starved es r es'` >> simp[] >>
  qpat_assum `finalize_codegen _ _ _.po_unit = SOME deploy_bc`
    (strip_assume_tac o MATCH_MP finalize_codegen_success_plan) >>
  `asm_static_wf prog` by
    (drule_all codegen_asm_static_wf >> simp[]) >>
  `FLOOKUP (lo_reloc prog prog') "code_end" = SOME (LENGTH (assemble prog')) /\
   LENGTH (assemble prog') < 65536` by
    (drule_all finalized_codegen_code_end >> simp[]) >>
  `?pre. prog = pre ++ [AsmDataHeader "runtime_begin"; AsmDataItem runtime_bc;
                       AsmDataHeader "code_end"]` by
    (fs[data_segment_asm_def, data_section_asm_def, MAP_APPEND, FLAT_APPEND] >>
     metis_tac[APPEND_ASSOC]) >>
  `?off. FLOOKUP (lo_reloc prog prog') "runtime_begin" = SOME off /\
        DROP off (assemble prog') = runtime_bc /\
        off <= LENGTH (assemble prog') /\ off < dimword(:256)` by
    (mp_tac (Q.INST [`unit` |-> `deploy_out.po_unit`, `bytes` |-> `runtime_bc`]
       finalized_deploy_runtime_slice) >>
     impl_tac >- (asm_rewrite_tac[] >> qexists_tac `pre'` >> REFL_TAC) >>
     disch_then ACCEPT_TAC) >>
  `cplan.cp_initial_fmp < 2 ** 254` by
    (fs[generate_context_plan_def] >>
     drule generate_context_plan_with_headroom >> simp[]) >>
  `assemble prog' <> []` by
    (Cases_on `fin = K SOME`
     >- (drule codegen_assembly_nonempty >> gvs[]) >>
     `fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
     qpat_x_assum `fin = asm_opt_finalizer` SUBST_ALL_TAC >>
     irule codegen_assembly_finalizer_nonempty >>
     qexistsl [`prog`,`rpolicy`,`deploy_out.po_unit`] >> simp[]) >>
  qabbrev_tac `vs = opt_entry_state_own prog prog' cplan es with
                     vs_alloca_next := imm_len_mods mods` >>
  `deploy_state_rel_mods mods exps (assemble prog') am tx es` by fs[] >>
  `tx with code := vs.vs_code = tx` by
    (qspecl_then [`mods`, `exps`, `assemble prog'`, `am`, `tx`, `prog`,
         `prog'`, `cplan`, `es`] mp_tac deploy_own_txp_identity_mods >>
     simp[Abbr `vs`]) >>
  `?fmp:bytes32.
    w2n (opt_entry_state_own prog prog' cplan es).vs_initial_fmp <= w2n fmp /\
    w2n fmp < 2 ** 254 /\
    imm_len_mods mods + unit_alloca_budget deploy_unit.cu_context +
      32 * ctx_dload_count deploy_unit.cu_context <= w2n fmp` by
    (irule deploy_raw_fmp_exists_mods >> asm_rewrite_tac[] >>
     qexistsl [`exps`, `rpolicy`, `runtime_bc`] >> asm_rewrite_tac[]) >>
  `imm_len_mods mods < dimword (:256)` by
    (qpat_assum `imm_len_mods mods + _ + _ <= _` mp_tac >>
     qpat_assum `w2n fmp < 2 ** 254` mp_tac >>
     simp[NoAsms, wordsTheory.dimword_def, venomLayoutTheory.dimindex_256] >>
     decide_tac) >>
  `fixed_region_reserved (imm_len_mods mods) deploy_unit.cu_context /\
   reserved_intervals_wf deploy_unit.cu_context.ctx_global_reserved` by
    (Cases_on `imm_len_mods mods = 0` >>
     fs[fixed_region_reserved_def, reserved_intervals_wf_def, reserved_interval_wf_def]) >>
  rename1 `w2n (opt_entry_state_own prog prog' cplan es).vs_initial_fmp <= w2n fmp` >>
  qspecl_then [`mods`, `exps`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`, `vs`]
    mp_tac opt_deploy_asm_rels_own_mods >>
  impl_tac >- (qpat_assum `Abbrev (vs = _)` (fn abbrev =>
    asm_rewrite_tac[REWRITE_RULE [markerTheory.Abbrev_def] abbrev])) >>
  strip_tac >>
  qpat_assum `deploy_state_rel_mods mods exps (assemble prog') am tx es`
    (strip_assume_tac o PURE_REWRITE_RULE [deploy_state_rel_mods_def]) >>
  drule_all deploy_shadow_run_not_starved >> strip_tac >>
  `asm_frame_rel_tail [] prog' vs.vs_data_section (shadow_root es)
    (entry_asm_state vs (shadow_root es)) (shadow_root es)` by
    simp[asm_frame_rel_tail_nil] >>
  `gas_readings (shadow_root es) = gas_readings es` by
    simp[gas_readings_def, shadow_root_frame_obs] >>
  `o1_initial_state_ok vs /\ ~vs.vs_call_ctx.cc_static /\
   vs.vs_initial_fmp = n2w cplan.cp_initial_fmp /\
   vs.vs_fmp = vs.vs_initial_fmp /\ vs.vs_alloca_next = imm_len_mods mods /\
   vs.vs_outcomes = MAP SND (call_trace es) /\ vs.vs_gas_readings = gas_readings es` by
    simp[Abbr `vs`, opt_entry_state_own_def, entry_venom_state_def,
         init_venom_state_def, o1_initial_state_ok_def] >>
  `!eom. max_live_eom deploy_out.po_unit.cu_context = SOME eom ==>
          eom <= w2n vs.vs_initial_fmp` by
    (qspecl_then [`deploy_out.po_unit.cu_context`, `cplan`, `vs`]
      mp_tac o1PipelineCorrectTheory.generate_context_plan_eom_room >> simp[]) >>
  `fin = K SOME ==> initial_ctx_rel cplan prog deploy_out.po_unit.cu_context vs
        (shadow_root es)` by
    (strip_tac >>
     `prog' = prog` by fs[] >>
     qpat_x_assum `prog' = prog` SUBST_ALL_TAC >>
     `vs = entry_venom_state prog cplan es with vs_alloca_next := imm_len_mods mods` by
       simp[Abbr `vs`, opt_entry_state_own_identity] >>
     `es.txParams.blockNumber < dimword (:256)` by
       (fs[tx_block_fields_rel_def, tx_env_ok_def] >>
        irule lt_dimword_256 >> qexists_tac `255` >> simp[]) >>
     `call_trace (shadow_root es) = call_trace es` by
       simp[call_trace_def, shadow_root_frame_obs] >>
     `?fn fns. deploy_out.po_unit.cu_context.ctx_functions = fn::fns /\
               get_params (HD fn.fn_blocks).bb_instructions = []` by
       (qpat_assum `unit_shape_ok _`
          (mp_tac o PURE_REWRITE_RULE [unit_shape_ok_def, entry_fn_first_def]) >>
        disch_then (CONJUNCTS_THEN2
          (qx_choosel_then [`entry_name`, `entry_fn`, `other_fns`] strip_assume_tac)
          strip_assume_tac) >>
        qexistsl [`entry_fn`, `other_fns`] >> conj_tac
        >- FIRST_ASSUM ACCEPT_TAC >>
        qpat_assum `get_params (HD (HD _).fn_blocks).bb_instructions = []` mp_tac >>
        qpat_assum `deploy_out.po_unit.cu_context.ctx_functions = entry_fn::other_fns` SUBST1_TAC >>
        simp[NoAsms]) >>
     qabbrev_tac `c = ctxt with msgParams updated_by
                          (\mp. mp with outputTo := Memory <|offset := 0; size := 0|>)` >>
     `(shadow_root es).contexts = [(c,rb)]` by
       simp[Abbr `c`, shadow_root_def, shadow_root_contexts_def] >>
     `msg_ctx_rel vs.vs_call_ctx c.msgParams /\
      tx_ctx_rel vs.vs_tx_ctx (shadow_root es).txParams /\
      block_ctx_rel vs.vs_block_ctx (shadow_root es).txParams /\
      blockhash_rel vs (shadow_root es).txParams` by
       (qpat_assum `vs = _ with vs_alloca_next := _` SUBST1_TAC >>
        qspecl_then [`es`,`ctxt`,`rb`,`[]`,`prog`,`cplan`] mp_tac
          entry_venom_state_evm_environment >>
        impl_tac >- (conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
        simp[NoAsms, Abbr `c`, shadow_root_def, msg_ctx_rel_def, blockhash_rel_def]) >>
     `vs.vs_params = []` by
       (qpat_assum `vs = _ with vs_alloca_next := _` SUBST1_TAC >>
        simp[NoAsms, entry_venom_state_def, init_venom_state_def]) >>
     `initial_state_rel cplan prog 0 fn vs (shadow_root es)` by
       (PURE_REWRITE_TAC [initial_state_rel_def] >>
        qpat_assum `(shadow_root es).contexts = [(c,rb)]` (fn th =>
          simp_tac (srw_ss()) [th, stack_params_rel_def]) >>
        asm_rewrite_tac[] >>
        qpat_assum `vs = _ with vs_alloca_next := _` SUBST1_TAC >>
        simp[entry_venom_state_fresh, entry_venom_state_frame_fields,
             entry_venom_state_created_in_tx, asm_pc_to_offset_zero,
             context_memory_rel_def, Abbr `c`, shadow_root_def,
             rich_listTheory.DROP_LENGTH_APPEND]) >>
     PURE_REWRITE_TAC [initial_ctx_rel_def] >>
     qexistsl [`fn`, `fns`, `c`, `rb`, `[]`] >>
     `(shadow_root es).msdomain = es.msdomain` by simp[shadow_root_def] >>
     `c.msgParams.code = assemble prog ++ vs.vs_data_section` by
       (qpat_assum `vs = _ with vs_alloca_next := _` SUBST1_TAC >>
        simp[Abbr `c`, entry_venom_state_frame_fields, rich_listTheory.DROP_LENGTH_APPEND]) >>
     `vs.vs_call_ctx.cc_created_in_tx` by
       (qpat_assum `vs = _ with vs_alloca_next := _` SUBST1_TAC >>
        simp[entry_venom_state_created_in_tx]) >>
     `c.msgParams.parsed = parse_code 0 FEMPTY c.msgParams.code /\ c.logs = []` by
       (simp[NoAsms, Abbr `c`] >> conj_tac
        >- (qpat_assum `ctxt.msgParams.code = assemble prog ++ args_bytes`
              (fn th => REWRITE_TAC [th]) >> FIRST_ASSUM ACCEPT_TAC) >>
        FIRST_ASSUM ACCEPT_TAC) >>
     simp[shadow_root_wf_state] >>
     qpat_assum `vs = _ with vs_alloca_next := _` SUBST1_TAC >>
     simp[entry_venom_state_fresh, entry_venom_state_frame_fields] >>
     simp[initial_codegen_state_rel_def, entry_venom_state_def, init_venom_state_def]) >>
  `!fuel. o1_lowered_inv deploy_out.po_unit.cu_context vs /\
          code_end_offset_ok (raw_reachable vs) deploy_out.po_unit.cu_context ==>
          venom_frame_rel (shadow_root es) sr sg
            (run_context fuel deploy_out.po_unit.cu_context vs)` by
    (gen_tac >> strip_tac >>
     drule_all o1_pipeline_memory_obligations_raw >> strip_tac >>
     drule_all o1_pipeline_codegen_obligations >> strip_tac >>
     Cases_on `fin = K SOME`
     >- (qspecl_then [`fuel`,`rpolicy`,`deploy_out.po_unit`,`cplan`,`prog`,
                      `raw_reachable vs`,`vs`,`shadow_root es`] mp_tac codegen_correct >>
         impl_tac >- (rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE fs[])) >>
         simp[]) >>
     `fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
     qpat_x_assum `fin = asm_opt_finalizer` SUBST_ALL_TAC >>
     qspecl_then [`fuel`,`rpolicy`,`deploy_out.po_unit`,`cplan`,`prog`,`prog'`,
                  `raw_reachable vs`,`vs`,`shadow_root es`]
       mp_tac codegen_correct_asm_opt_own >>
     impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >> simp[]) >>
  qabbrev_tac `os = MAP SND (call_trace es)` >>
  qabbrev_tac `deploy_post = \gs res.
    case (load_contract (SOME os) gs am tx mods exps,res) of
      (INL (installed,rqs),Halt post) =>
        accounts_agree
          (storage_trace_horizon
             (deploy_storage_trace_mods (SOME os) gs am tx mods exps))
          tx.target installed.accounts
          (process_deletions post.vs_pending_deletions
             (if ALOOKUP installed.sources tx.target = NONE then post.vs_accounts
              else update_account tx.target
                (lookup_account tx.target post.vs_accounts with
                   code := (lookup_account tx.target installed.accounts).code)
                post.vs_accounts)) /\
        transient_agree
          (storage_trace_horizon
             (deploy_storage_trace_mods (SOME os) gs am tx mods exps))
          tx.target installed.tStorage post.vs_transient /\
        installed.logs = post.vs_logs /\
        LIST_REL (request_agree
          (storage_trace_horizon
             (deploy_storage_trace_mods (SOME os) gs am tx mods exps)) tx.target)
          rqs post.vs_requests /\
        (if ALOOKUP installed.sources tx.target = NONE then
           post.vs_returndata = [] /\ MEM tx.target post.vs_pending_deletions
         else ?section.
           post.vs_returndata = runtime_bc ++ section /\
           immutables_section_rel_mods mods (account_immutables installed tx.target) section)
    | (INR (AssertException msg),Abort Revert_abort _) => T
    | (INR (AssertException msg),Abort ExHalt_abort _) => msg = "UNREACHABLE"
    | (INR (Error e),Abort a _) => !d. e = RevertData d ==> a = Revert_abort
    | _ => F` >>
  `gas_readings_rel (gas_readings es) (\gs.
    deploy_storage_ok_mods mods exps am tx os gs ==>
    deploy_source_exempt_mods mods (load_contract (SOME os) gs am tx mods exps) \/
    ?fuel. o1_lowered_inv deploy_out.po_unit.cu_context vs /\
           code_end_offset_ok (raw_reachable vs) deploy_out.po_unit.cu_context /\
           deploy_post gs (run_context fuel deploy_out.po_unit.cu_context vs))`
    suffices_by
      (strip_tac >>
       PURE_REWRITE_TAC [deploy_call_result_rel_mods_def, LET_THM] >>
       qpat_assum `Abbrev (os = _)`
         (PURE_REWRITE_TAC o single o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
       qpat_assum `gas_readings_rel _ _`
         (mp_tac o MATCH_MP (SIMP_RULE bool_ss [GSYM AND_IMP_INTRO] gas_readings_rel_mono)) >>
       BETA_TAC >> disch_then irule >>
       gen_tac >> BETA_TAC >> strip_tac >> strip_tac >>
       qpat_x_assum `deploy_storage_ok_mods mods exps am tx os _ ==> _` drule >>
       disch_then (DISJ_CASES_THEN2 assume_tac (qx_choose_then `fuel` strip_assume_tac))
       >- (rename1 `deploy_source_exempt_mods mods src` >>
           qpat_x_assum `deploy_source_exempt_mods mods src` mp_tac >>
           Cases_on `src`
           >- simp[NoAsms, deploy_source_exempt_mods_def] >>
           rename1 `INR exc` >> Cases_on `exc` >>
           simp[NoAsms, deploy_source_exempt_mods_def, deploy_result_rel_mods_def,
                exception_outcome_rel_mods_def]) >>
       `venom_frame_rel (shadow_root es) sr sg
          (run_context fuel deploy_out.po_unit.cu_context vs)` by
         (qpat_assum `!fuel. _ ==> venom_frame_rel (shadow_root es) sr sg (run_context fuel _ vs)`
            (MATCH_MP_TAC o SPEC_ALL) >>
          conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
       qpat_x_assum `deploy_post _ _` mp_tac >>
       simp[NoAsms, Abbr `deploy_post`] >>
       qabbrev_tac `src = load_contract (SOME os) gs am tx mods exps` >>
       qabbrev_tac `res = run_context fuel deploy_out.po_unit.cu_context vs` >>
       namedCases_on `src` ["installed_result","exc"] >>
       simp[]
       >- (PairCases_on `installed_result` >>
           namedCases_on `res` ["st","post","a st","ir st","msg"] >> simp[] >>
           disch_then (map_every assume_tac o CONJUNCTS) >>
           `call_requests (shadow_root es) = call_requests es` by
             simp[call_requests_def, call_trace_def, shadow_root_frame_obs] >>
           qpat_x_assum `venom_frame_rel (shadow_root es) sr sg (Halt post)`
             (strip_assume_tac o SIMP_RULE (srw_ss()) [venom_frame_rel_def]) >>
           drule_all deploy_frame_halt_mid >>
           disch_then (qx_choosel_then [`mid`,`created`,`saved`] strip_assume_tac) >>
           `case created.returnData of h::_ => h <> n2w 0xef | [] => T` by
             (qpat_assum `created.returnData = _` SUBST1_TAC >>
              qpat_x_assum `if ALOOKUP installed_result0.sources tx.target = NONE then _ else _`
                mp_tac >>
              Cases_on `ALOOKUP installed_result0.sources tx.target = NONE` >>
              asm_rewrite_tac[]
              >- simp[NoAsms] >>
              disch_then (qx_choose_then `suffix` (SUBST1_TAC o cj 1)) >>
              qpat_assum `runtime_bc <> []` mp_tac >>
              qpat_assum `~(?t. runtime_bc = _ :: t)` mp_tac >>
              Cases_on `runtime_bc` >> simp[NoAsms]) >>
           qspecl_then [`mid`,`created`,`saved`,`tx.target`] mp_tac
             deploy_frame_complete >>
           impl_tac >- simp[] >>
           disch_then (qx_choosel_then [`cr`,`created_state`] strip_assume_tac) >>
           `cr = r /\ created_state = es'` by fs[] >>
           pop_assum (map_every SUBST_ALL_TAC o CONJUNCTS)
           >- (drule_all creation_resource_starved_single_transfer >> simp[]) >>
           `frame_outcome es r es' NONE post.vs_returndata installed_result0.logs` by
             (irule frame_outcome_single_transfer_none >>
              qexistsl_tac [`ctxt`,`created`,`mid`,`rb`,`saved`] >>
              simp[] >>
              qpat_assum `cr = r` (SUBST1_TAC o SYM) >>
              qpat_assum `created.returnData = _` (SUBST1_TAC o SYM) >>
              FIRST_ASSUM ACCEPT_TAC) >>
           Cases_on `ALOOKUP installed_result0.sources tx.target = NONE` >>
           fs[deploy_result_rel_mods_def, effects_agree_def]
           >- (simp[lookup_account_def, update_account_def,
                     combinTheory.APPLY_UPDATE_THM] >>
               `process_deletions post.vs_pending_deletions
                  (update_account tx.target
                    (lookup_account tx.target post.vs_accounts with code := [])
                    post.vs_accounts) =
                process_deletions post.vs_pending_deletions post.vs_accounts` by
                 (irule process_deletions_update_mem >> simp[]) >>
               fs[update_account_def, lookup_account_def] >>
               qpat_x_assum `frame_outcome es r es' NONE post.vs_returndata installed_result0.logs` mp_tac >>
               simp[]) >>
           qexists_tac `section` >>
           gvs[lookup_account_def, update_account_def, combinTheory.APPLY_UPDATE_THM]) >>
       Cases_on `exc` >>
       namedCases_on `res` ["st","st","a st","ir st","msg"] >> simp[] >>
       Cases_on `a` >>
       qpat_x_assum `venom_frame_rel (shadow_root es) sr sg _`
         (strip_assume_tac o SRULE [venom_frame_rel_def]) >>
       simp[NoAsms, deploy_result_rel_mods_def, exception_outcome_rel_mods_def] >>
       rpt strip_tac >>
       drule_all deploy_frame_exception >>
       disch_then (qx_choose_then `out_state` strip_assume_tac) >>
       TRY (qpat_assum `!logs. frame_outcome es sr out_state (SOME Reverted) _ logs`
              (qspec_then `[]` assume_tac) >>
            `LENGTH es.contexts = 1 /\ ~vfmExecution$vfm_abort (SOME Reverted)` by
              simp[vfmExecutionTheory.vfm_abort_def] >>
            drule_all run_call_root_frame_outcome_raises >> strip_tac) >>
       `sr = r /\ out_state = es'` by
         (qpat_assum `run_call es = SOME (sr,out_state)` mp_tac >>
          qpat_assum `run_call es = SOME (r,es')`
            (fn run => simp[NoAsms,run]) >> simp[NoAsms]) >>
       pop_assum (map_every (SUBST1_TAC o SYM) o CONJUNCTS) >>
       TRY DISJ2_TAC >>
       qmatch_asmsub_rename_tac
         `!logs. frame_outcome es sr out_state (SOME reason) out logs` >>
       qexistsl [`reason`,`out`,`[]`] >>
       qpat_assum `!logs. frame_outcome es sr out_state _ _ logs`
         (qspec_then `[]` mp_tac) >> fs[]) >>
  suspend "linked_deploy_certificate"
QED

Resume e2e_deploy_correctness_mods[linked_deploy_certificate]:
  Cases_on `classify_functions_unit mods exps` >>
  PairCases_on `r'` >>
  rename1 `classify_functions_unit mods exps = (exts,ints,fb,ctor,imp_ctors)` >>
  Cases_on `ctor`
  >- (drule_all linked_empty_deploy_source >>
      disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
        (qx_choose_then `installed` strip_assume_tac))) >>
      `vs.vs_data_section = [] /\ vs.vs_allocas = FEMPTY /\ ~vs.vs_halted` by
        simp[Abbr `vs`, opt_entry_state_own_def, entry_venom_state_frame_fields,
             entry_venom_state_fresh, rich_listTheory.DROP_LENGTH_APPEND] >>
      `FLOOKUP vs.vs_labels "runtime_begin" = SOME (n2w off)` by
        (qpat_assum `FLOOKUP (lo_reloc prog prog') "runtime_begin" = SOME off`
           (fn lab => simp[NoAsms, Abbr `vs`, opt_entry_state_own_def,
                         finite_mapTheory.FLOOKUP_o_f, lab])) >>
      `DROP off vs.vs_code = runtime_bc` by
        (qpat_assum `vs.vs_code = _` SUBST1_TAC >> asm_rewrite_tac[APPEND_NIL]) >>
      `LENGTH runtime_bc <= LENGTH (assemble prog')` by
        (qpat_assum `DROP off (assemble prog') = runtime_bc` (SUBST1_TAC o SYM) >>
         simp[listTheory.LENGTH_DROP]) >>
      `LENGTH runtime_bc + imm_len_mods mods < dimword (:256)` by
        (qpat_assum `imm_len_mods mods + _ + _ <= _` mp_tac >>
         qpat_assum `w2n fmp < 2 ** 254` mp_tac >>
         simp[NoAsms, wordsTheory.dimword_def, venomLayoutTheory.dimindex_256] >>
         decide_tac) >>
      mp_tac (Q.INST [`unit` |-> `deploy_unit`, `rp` |-> `rpolicy`,
          `vs` |-> `vs`, `off` |-> `off`]
        (SPEC_ALL linked_empty_deploy_target)) >>
      impl_tac >- asm_rewrite_tac[] >>
      disch_then (qx_choosel_then [`entry_fn`, `raw_post`] strip_assume_tac) >>
      suspend "linked_empty_deploy_s4") >>
  linked_deploy_constructor_source_tac >>
  linked_deploy_constructor_package_tac >>
  linked_deploy_constructor_package_flags_tac >>
  linked_deploy_constructor_code_tac >>
  suspend "linked_present_deploy"
QED

Resume e2e_deploy_correctness_mods[linked_present_deploy]:
  Q.ASM_CASES_TAC `mut <> Payable /\ tx.value <> 0`
  >- suspend "linked_present_deploy_rejected_value" >>
  suspend "linked_present_deploy_accepted_value"
QED

(* Shared facts about the guarded entry, before choosing a raw variant. *)
val linked_deploy_reject_entry_tac =
  qpat_assum `mut <> Payable /\ tx.value <> 0` strip_assume_tac >>
  `deploy_unit.cu_context.ctx_entry = SOME "__deploy"` by
    (drule_all run_deploy_lowering_ctor_trace >> strip_tac >>
     qpat_assum `deploy_unit.cu_context = install_immutable_reservation _ _` SUBST1_TAC >>
     qpat_assum `extract_context_with_internals "__deploy" _ _ = SOME (_,_)` mp_tac >>
     simp[NoAsms, extract_context_with_internals_def, AllCaseEqs()] >>
     rpt strip_tac >>
     FIRST [qpat_assum `mk_venom_context _ _ = _` (SUBST1_TAC o SYM),
            qpat_assum `_ = mk_venom_context _ _` SUBST1_TAC] >>
     simp[NoAsms, install_immutable_reservation_def, mk_venom_context_def]) >>
  `~cpkg2` by asm_rewrite_tac[] >>
  qpat_assum `(if cpkg2 then _ else _) (initial_compile_state "__deploy") = ((),st_pay)`
    (fn guard => qpat_assum `~cpkg2`
       (assume_tac o (fn flag => REWRITE_RULE [flag] guard))) >>
  drule_all deploy_constructor_value_guard_code >> strip_tac;

fun linked_deploy_reject_state_tac frame =
  `sfields_tenv_consistent (make_struct_fields_map_mods mods) (type_env_all_modules mods)` by
    (irule make_struct_fields_map_mods_consistent >>
     qexists_tac `F` >>
     qpat_assum `check_contract F am.layouts tx.target mods = SOME _`
       (ACCEPT_TAC o MATCH_MP check_contract_runtime_namespaces)) >>
  `!bs. constructor_args_encode_mods mods tx bs ==> LENGTH bs < 2 ** 128` by
    (gen_tac >> strip_tac >>
     drule_all constructor_args_size_bounded_mods >> simp[NoAsms]) >>
  `code_layout_valid vs` by
    (mp_tac (Q.INST [`es` |-> frame, `cplan` |-> `cplan`]
       deploy_entry_code_layout_mods) >>
     impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     simp[NoAsms, Abbr `vs`, code_layout_valid_def]) >>
  `o1_run_state_ok vs` by simp[o1_run_state_ok_def] >>
  `LENGTH vs.vs_data_section < dimword (:256) DIV 2` by
    (mp_tac (Q.INST [`vs` |-> `vs`, `prefix` |-> `assemble prog'`]
       e2eCorrectnessTheory.data_section_length_bound) >> asm_rewrite_tac[]) >>
  `vs.vs_allocas = FEMPTY /\ ~vs.vs_halted` by
    simp[Abbr `vs`, opt_entry_state_own_def, entry_venom_state_fresh] >>
  `vs.vs_call_ctx.cc_callvalue = n2w tx.value` by
    (qpat_assum ([QUOTE "deploy_state_rel_mods mods exps (assemble prog') am tx "] @ frame)
       (strip_assume_tac o PURE_REWRITE_RULE [deploy_state_rel_mods_def]) >>
     simp[Abbr `vs`, opt_entry_state_own_def, entry_venom_state_def]) >>
  `tx.value < dimword (:256)` by
    (qpat_assum `call_tx_well_typed tx` mp_tac >>
     simp[NoAsms, call_tx_well_typed_def, wordsTheory.dimword_def,
          venomLayoutTheory.dimindex_256]) >>
  `vs.vs_call_ctx.cc_callvalue <> 0w` by
    (qpat_assum `vs.vs_call_ctx.cc_callvalue = _` SUBST1_TAC >>
     simp[wordsTheory.n2w_11, arithmeticTheory.LESS_MOD]);

val linked_deploy_reject_raw_tac =
  `!vi. raw_variant fmp vi vs ==>
    raw_unit_memory_ok deploy_unit.cu_context vi /\
    ptr_discipline (imm_len_mods mods) deploy_unit.cu_context vi /\
    taint_within D deploy_unit.cu_context vi /\
    mem_inv dload_offset_ok deploy_unit.cu_context vi /\
    mem_inv dload_headroom_ok deploy_unit.cu_context vi /\
    mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                             s.vs_code = vi.vs_code /\ s.vs_data_section = vi.vs_data_section)
      deploy_unit.cu_context vi /\
    ?raw. run_context 1 deploy_unit.cu_context vi = Abort Revert_abort raw` by
    (gen_tac >> strip_tac >>
     `vi = vs with <|vs_fmp := fmp; vs_initial_fmp := fmp;
                         vs_gas_readings := vi.vs_gas_readings|>` by
       (qpat_assum `raw_variant fmp vi vs`
          (mp_tac o PURE_REWRITE_RULE [raw_variant_def, gas_variant_def]) >>
        simp[NoAsms, venom_state_component_equality] >> strip_tac >>
        qpat_assum `fmp = vi.vs_initial_fmp` (fn h =>
          qpat_assum `fmp = vi.vs_fmp` (ACCEPT_TAC o TRANS (SYM h)))) >>
     `code_layout_valid vi /\ vi.vs_fmp = fmp /\ vi.vs_initial_fmp = fmp /\
      vi.vs_alloca_next = imm_len_mods mods /\ vi.vs_allocas = FEMPTY /\
      ~vi.vs_halted /\ vi.vs_call_ctx.cc_callvalue <> 0w` by
       (qpat_assum `vi = _` SUBST1_TAC >>
        qpat_assum `code_layout_valid vs` mp_tac >>
        simp[NoAsms, code_layout_valid_def] >> strip_tac >>
        rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     qpat_x_assum `vi = vs with <|vs_fmp := fmp; vs_initial_fmp := fmp;
                                 vs_gas_readings := vi.vs_gas_readings|>` kall_tac >>
     `allocas_below_fmp vi` by simp[allocas_below_fmp_def] >>
     `?raw. run_context 1 deploy_unit.cu_context vi = Abort Revert_abort raw` by
       (qspecl_then [`deploy_unit.cu_context`,`fn`,`bb`,`tail`,`vi`]
          (mp_tac o REWRITE_RULE [GSYM mk_inst_def]) deploy_prefix_context_guard_abort >>
        asm_rewrite_tac[]) >>
     mp_tac (Q.INST [`ctx` |-> `deploy_unit.cu_context`, `vs` |-> `vi`,
                     `D` |-> `D`, `cap` |-> `imm_len_mods mods`]
       (SPEC_ALL linked_deploy_constructor_reject_prefix)) >>
     impl_tac >- asm_rewrite_tac[] >>
     disch_then strip_assume_tac >>
     `mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                   s.vs_code = vi.vs_code /\ s.vs_data_section = vi.vs_data_section)
        deploy_unit.cu_context vi` by
       (qspecl_then [`deploy_unit.cu_context`,`"__deploy"`,`fn`,`"__deploy"`,`vi`]
          mp_tac lowered_unit_dload_in_section >>
        impl_tac >- asm_rewrite_tac[] >>
        simp[mem_inv_raw_reachable] >> strip_tac >> rpt gen_tac >> disch_tac >>
        conj_tac
        >- first_x_assum (drule_then ACCEPT_TAC) >>
        drule_then ACCEPT_TAC o1SafeUptoTheory.raw_reachable_code_data) >>
     asm_rewrite_tac[] >>
     Cases_on `ctx_has_dalloca deploy_unit.cu_context`
     >- (mp_tac (Q.INST [`dunit` |-> `deploy_unit`, `vs` |-> `vi`, `D` |-> `D`,
                        `func` |-> `fn`] (SPEC_ALL deploy_selected_memory_from_checked_mods)) >>
         simp[]) >>
     mp_tac (Q.INST [`dunit` |-> `deploy_unit`, `vs` |-> `vi`, `D` |-> `D`,
                    `func` |-> `fn`] (SPEC_ALL deploy_selected_memory_mods)) >>
     simp[]);

(* Only a static ExHalt could need the weaker code-end invariant. *)
val linked_deploy_reject_code_end_tac =
  `code_end_offset_ok (raw_reachable vs) deploy_out.po_unit.cu_context` by
    (qspecl_then [`D`, `imm_len_mods mods`, `rpolicy`, `deploy_unit`,
                  `deploy_out`, `vs`, `fmp`]
       mp_tac o1StaticPipelineCorrectTheory.o1_pipeline_code_end_offset_ok_static_abort >>
     impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     disch_then (qx_choose_then `vcode` strip_assume_tac) >>
     qpat_assum `!vi. raw_variant _ vi vs ==> _` (drule_then strip_assume_tac) >>
     qpat_x_assum `_ ==> code_end_offset_ok _ _ /\ _` mp_tac >>
     impl_tac >- asm_rewrite_tac[] >>
     disch_then (CONJUNCTS_THEN2 (K ALL_TAC)
       (DISJ_CASES_THEN2 ACCEPT_TAC (qspec_then `1` mp_tac))) >>
     qpat_assum `run_context 1 deploy_unit.cu_context vcode = Abort Revert_abort _`
       (fn run => simp[NoAsms, run, terminates_def]));

val linked_deploy_reject_sim_tac =
  qspecl_then [`D`, `imm_len_mods mods`, `rpolicy`, `deploy_unit`,
                `deploy_out`, `vs`, `fmp`]
    mp_tac o1PipelineCorrectTheory.run_venom_pipeline_correct >>
  impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  disch_then (qx_choose_then `vrun` strip_assume_tac) >>
  qpat_assum `!vi. raw_variant _ vi vs ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `_ ==> ctx_sim D _ _ vrun vs /\ _` mp_tac >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then strip_assume_tac >>
  `?opt_fuel post. run_context opt_fuel deploy_out.po_unit.cu_context vs =
                   Abort Revert_abort post` by
    (qpat_assum `ctx_sim D _ _ vrun vs` (mp_tac o PURE_REWRITE_RULE [ctx_sim_def]) >>
     disch_then (qspec_then `1` mp_tac) >>
     qpat_assum `run_context 1 deploy_unit.cu_context vrun = Abort Revert_abort _`
       (fn run => simp[NoAsms, run, terminates_def]) >>
     disch_then (qx_choose_then `opt_fuel` assume_tac) >>
     qexists_tac `opt_fuel` >>
     Cases_on `run_context opt_fuel deploy_out.po_unit.cu_context vs` >>
     qpat_x_assum `dead_result_rel D (Abort Revert_abort _) _` mp_tac >>
     simp[NoAsms, dead_result_rel_def]);

Resume e2e_deploy_correctness_mods[linked_present_deploy_rejected_value]:
  `w2n vs.vs_initial_fmp <= w2n fmp` by
    (qpat_assum `w2n (opt_entry_state_own prog prog' cplan es).vs_initial_fmp <= w2n fmp`
       mp_tac >> simp[NoAsms, Abbr `vs`]) >>
  qabbrev_tac `D = <|d_stor := K (K UNIV); d_trans := K (K UNIV);
                       d_imm := K UNIV; d_ret := K UNIV|>` >>
  `dead_wf D` by simp[Abbr `D`, dead_wf_def] >>
  linked_deploy_reject_entry_tac >>
  linked_deploy_reject_state_tac `es` >>
  linked_deploy_reject_raw_tac >>
  linked_deploy_reject_code_end_tac >>
  linked_deploy_reject_sim_tac >>
  `!orc gs. load_contract_trace orc gs am tx mods exps =
      (INR (Error (RuntimeError "not Payable")),[])` by
    (qpat_assum `tx.function_name = "__init__"` (fn name =>
       drule_all (REWRITE_RULE [name] (Q.INST [`tx` |-> `tx`]
         (SPEC_ALL linked_nonpayable_deploy_source)))) >>
     disch_then (qspec_then `exps` ACCEPT_TAC)) >>
  rewrite_tac[gas_readings_rel_def] >>
  qexistsl_tac [`[]`, `gas_readings es`] >> simp[] >>
  qx_gen_tac `gs` >> strip_tac >> disj2_tac >>
  rename1 `run_context opt_fuel deploy_out.po_unit.cu_context vs = Abort Revert_abort post` >>
  qexists_tac `opt_fuel` >> asm_rewrite_tac[] >>
  qpat_assum `!orc gs. load_contract_trace orc gs am tx mods exps = _`
    (qspecl_then [`SOME os`,`gs`] assume_tac) >>
  simp[Abbr `deploy_post`, load_contract_def]
QED

Resume e2e_deploy_correctness_mods[linked_present_deploy_accepted_value]:
  `cpkg3 = F /\ cpkg4 = global_nonreentrant_slot /\ cpkg5 = T` by
    (qpat_assum `constructor = (mut,F,F,"__init__",src_args,[],NoneT,_)`
       (fn ctor => qpat_assum `set_constructor_package_target _ _ = _`
         (mp_tac o SUBS [ctor])) >>
     simp[package_constructor_unit_def, set_constructor_package_target_def]) >>
  qpat_x_assum `cpkg3 = F` SUBST_ALL_TAC >>
  qpat_x_assum `cpkg4 = global_nonreentrant_slot` SUBST_ALL_TAC >>
  qpat_x_assum `cpkg5 = T` SUBST_ALL_TAC >>
  qpat_x_assum `cpkg2 = (mut = Payable)` SUBST_ALL_TAC >>
  `st3 = st2` by fs[comp_return_def] >>
  qpat_x_assum `st3 = st2` SUBST_ALL_TAC >>
  qabbrev_tac `ctor_ce = ce1 with ce_ctor_exit_label := SOME exit_lbl` >>
  mp_tac (Q.INST [`ce0` |-> `cpkg0`, `key` |-> `global_nonreentrant_slot`,
      `ut` |-> `T`, `rp` |-> `rpolicy`, `cap` |-> `imm_len_mods mods`,
      `args` |-> `cpkg1`, `ifns` |-> `internals`, `stmts` |-> `cpkg6`,
      `pay` |-> `mut = Payable`, `unit` |-> `deploy_unit`, `ce` |-> `ctor_ce`]
    linked_constructor_body_shadow_code) >>
  impl_tac >- simp[Abbr `ctor_ce`] >>
  disch_then (qx_choosel_then [`shadow_unit`,`shadow_fn`,`shadow_sb`]
    strip_assume_tac) >>
  linked_deploy_ctor_ptr_environment_tac `es` >>
  `shadow_body_inv_mods mods exps deploy_unit.cu_context shadow_unit.cu_context` by
    (qpat_assum `Abbrev (internals = _)`
       (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     drule_all_then ACCEPT_TAC deploy_shadow_body_inv_mods) >>
  linked_deploy_ctor_accepted_inputs_tac >>
  linked_deploy_ctor_source_trace_tac >>
  linked_deploy_ctor_registration_metadata_tac >>
  linked_deploy_ctor_prefix_fields_tac `es` `ctxt.msgParams.code` >>
  linked_deploy_ctor_prefix_code_tac >>
  linked_deploy_ctor_before_registration_tac >>
  suspend "linked_present_deploy_accepted_value_body"
QED

(* Static part of the linked constructor entry, shared by the two resumes. *)
val linked_ctor_active_contract_tac =
  qabbrev_tac `cx = deploy_evaluation_context_mods mods am tx` >>
  `cx.in_deploy /\ cx.layouts = am.layouts /\ cx.txn.target = tx.target /\
   ALOOKUP cx.sources cx.txn.target = SOME mods /\
   cx.nonreentrant_slot = lookup_nonreentrant_slot cx.layouts cx.txn.target` by
    simp[Abbr `cx`, deploy_evaluation_context_mods_def, initial_evaluation_context_def] >>
  `module_body_inv mods NONE tops' ctor_ce cx` by
    (rewrite_tac[module_body_inv_def] >> conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  qabbrev_tac `ce_base = build_compile_env_unit mods NONE Deploy mut "__init__"
      src_args NoneT cpkg6 T with ce_target := rpolicy.rpol_target` >>
  `contract_inv mods exps deploy_unit.cu_context ce_base cx` by
    (simp[NoAsms, Abbr `ce_base`] >>
     irule linkedContractInvProducerTheory.checked_linked_contract_inv >>
     simp[optionTheory.IS_SOME_EQ_NOT_NONE] >>
     conj_tac >- (qexists_tac `runtime_bc` >> FIRST_ASSUM ACCEPT_TAC) >>
     qexistsl_tac [`am`,`tx`] >> simp[]);

val linked_ctor_registration_fields_tac =
  `!pos ce off size cs ce' cs'.
      compile_register_constructor_args ce pos off size cs = (ce',cs') ==>
      ce' = ce with ce_vars := ce'.ce_vars` by
    (POP_ASSUM_LIST (K ALL_TAC) >>
     Induct >- simp[moduleLoweringTheory.compile_register_constructor_args_def, comp_return_def] >>
     PairCases >> rpt gen_tac >>
     Cases_on `FLOOKUP ce.ce_vars h0` >> simp[Once moduleLoweringTheory.compile_register_constructor_args_def]
     >- (strip_tac >> first_x_assum drule >> simp[]) >>
     rename1 `FLOOKUP ce.ce_vars h0 = SOME loc` >>
     Cases_on `var_location_memory_size loc` >> simp[]
     >- (strip_tac >> first_x_assum drule >> simp[]) >>
     simp[comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> first_x_assum drule >> simp[]);

val linked_ctor_package_fields_tac =
  `cpkg0 = ce_base with <|ce_is_ctor := T; ce_raw_return := F;
                           ce_nonreentrant := (F,global_nonreentrant_slot,T,F)|>` by
    (qpat_assum `set_constructor_package_target _ _ =
      (cpkg0,cpkg1,_,_,_,_,cpkg6,cpkg7)` mp_tac >>
     qpat_assum `constructor = _` (fn ctor => PURE_REWRITE_TAC [ctor]) >>
     qpat_assum `cpkg6 = _` (fn ss =>
       qpat_assum `mut <> View` (fn nview =>
         simp[NoAsms, package_constructor_unit_def, set_constructor_package_target_def,
              update_cenv_nonreentrant_def, Abbr `ce_base`, ss, nview])) >>
     disch_then (fn th => ACCEPT_TAC (SYM (cj 1 th))));

val linked_ctor_transport_contract_tac =
  `contract_inv mods exps deploy_unit.cu_context ctor_ce cx` by
  (qpat_assum `!pos ce off size cs ce' cs'. _ ==> _`
    (drule_then (fn reg =>
      qpat_assum `Abbrev (ctor_ce = _)`
        (PURE_REWRITE_TAC o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
      PURE_ONCE_REWRITE_TAC [reg] >>
      qpat_assum `ce_before_registration = _` (fn before_reg =>
        qpat_assum `cpkg0 = _` (fn pkg =>
          qpat_assum `cx.in_deploy` (fn dep =>
            let val rules = [contract_inv_def, cenv_module_pins_mods_def,
                             immutable_section_layout_mods_def, dep]
            in qpat_assum `contract_inv mods exps deploy_unit.cu_context ce_base cx`
                 (map_every assume_tac o CONJUNCTS o SIMP_RULE (srw_ss()) rules) >>
               simp[NoAsms, before_reg, pkg, dep, contract_inv_def,
                    cenv_module_pins_mods_def, immutable_section_layout_mods_def] >>
               rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC
            end))))));

val linked_ctor_stmts_env_code_tac =
  `?ce_end ce_shadow_end.
    stmts_env ctor_ce NoLoop NoneT cpkg6 sa = (ce_end,sb) /\
    stmts_env (gas_shadow_env T ctor_ce) NoLoop NoneT
      (MAP gas_shadow_stmt cpkg6) sa = (ce_shadow_end,shadow_sb)` by
    (`SND (stmts_env ctor_ce NoLoop NoneT cpkg6 sa) = sb` by
       (qpat_assum `compile_stmts _ NoLoop NoneT cpkg6 sa = ((),sb)` mp_tac >>
        simp[NoAsms, stmtSimPropsTheory.compile_stmts_env, Abbr `ctor_ce`]) >>
     `SND (stmts_env (gas_shadow_env T ctor_ce) NoLoop NoneT
        (MAP gas_shadow_stmt cpkg6) sa) = shadow_sb` by
       (qpat_assum `compile_stmts (gas_shadow_env T ctor_ce) NoLoop NoneT _ sa =
            ((),shadow_sb)` mp_tac >> simp[NoAsms, stmtSimPropsTheory.compile_stmts_env]) >>
     qexistsl_tac [`FST (stmts_env ctor_ce NoLoop NoneT cpkg6 sa)`,
       `FST (stmts_env (gas_shadow_env T ctor_ce) NoLoop NoneT (MAP gas_shadow_stmt cpkg6) sa)`] >>
     conj_tac >> simp[Once pairTheory.PAIR_FST_SND_EQ]);

(* Interpret the compiler's qualified variable and hashmap tables at a
   declaration key. The source-local folds retain their fallback on misses. *)
val linked_ctor_builder_src_other_tac =
  `!tops src other id var_rest hash_rest. src <> other ==>
      build_var_type_map_src src tops var_rest (other,id) = var_rest (other,id) /\
      build_hashmap_info_src src tops hash_rest (other,id) = hash_rest (other,id)` by
    (POP_ASSUM_LIST (K ALL_TAC) >>
     Induct >> simp[build_var_type_map_src_def, build_hashmap_info_src_def] >>
     Cases >> simp[build_var_type_map_src_def, build_hashmap_info_src_def]);

val linked_ctor_builder_src_absent_tac =
  `!tops src id rest.
    ~MEM (src,id) (FLAT (MAP (toplevel_vtype_keys_toplevel src) tops)) ==>
    build_hashmap_info_src src tops rest (src,id) = rest (src,id)` by
    (POP_ASSUM_LIST (K ALL_TAC) >>
     Induct >> simp[build_hashmap_info_src_def] >>
     Cases >> simp[build_hashmap_info_src_def, toplevel_vtype_keys_toplevel_def]);

val linked_ctor_builder_src_decl_tac =
  `!tops src id vis mut ty slot var_rest hash_rest.
      ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) tops)) /\
      MEM (VariableDecl vis mut id ty slot) tops ==>
      build_var_type_map_src src tops var_rest (src,id) = SOME ty /\
      build_hashmap_info_src src tops hash_rest (src,id) = hash_rest (src,id)` by
    (qpat_assum `!tops src id rest. _ ==> build_hashmap_info_src _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> disch_tac >>
     Induct >> simp[] >> Cases >>
     simp[build_var_type_map_src_def, build_hashmap_info_src_def,
          toplevel_vtype_keys_toplevel_def, ALL_DISTINCT_APPEND] >>
     rpt strip_tac >> gvs[] >>
     metis_tac[vyperTypeContractStaticMapsTheory.module_toplevel_vtype_key_MEM_Variable]) >>
  `!tops src id vis tr kt vt slot rest.
      ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) tops)) /\
      MEM (HashMapDecl vis tr id kt vt slot) tops ==>
      build_hashmap_info_src src tops rest (src,id) = SOME (tr,kt,vt)` by
    (POP_ASSUM_LIST (K ALL_TAC) >> Induct >> simp[] >> Cases >>
     simp[build_hashmap_info_src_def, toplevel_vtype_keys_toplevel_def, ALL_DISTINCT_APPEND] >>
     rpt strip_tac >> gvs[] >>
     metis_tac[vyperTypeContractStaticMapsTheory.module_toplevel_vtype_key_MEM]);

val linked_ctor_builder_mods_absent_tac =
  `!ms src id. ~MEM src (MAP FST ms) ==> build_hashmap_info_mods ms (src,id) = NONE` by
    (qpat_assum `!tops src other id var_rest hash_rest. _ ==> _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> disch_tac >>
     Induct >> simp[build_hashmap_info_mods_def] >> PairCases >>
     rw[build_hashmap_info_mods_def] >> metis_tac[]);

val linked_ctor_builder_mods_var_tac =
  `!ms src ts id vis mut ty slot.
      ALL_DISTINCT (MAP FST ms) /\ ALOOKUP ms src = SOME ts /\
      ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts)) /\
      MEM (VariableDecl vis mut id ty slot) ts ==>
      build_hashmap_info_mods ms (src,id) = NONE /\
      build_var_type_map_mods ms (src,id) = SOME ty` by
    (qpat_assum `!ms src id. _ ==> build_hashmap_info_mods ms (src,id) = NONE` mp_tac >>
     qpat_assum `!tops src id vis mut ty slot var_rest hash_rest. _ ==> _ /\ _` mp_tac >>
     qpat_assum `!tops src other id var_rest hash_rest. _ ==> _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     Induct >> simp[] >> PairCases >>
     rw[build_hashmap_info_mods_def, build_var_type_map_mods_def] >> metis_tac[]);

val linked_ctor_builder_mods_hash_tac =
  `!ms src ts id vis tr kt vt slot.
      ALOOKUP ms src = SOME ts /\
      ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts)) /\
      MEM (HashMapDecl vis tr id kt vt slot) ts ==>
      build_hashmap_info_mods ms (src,id) = SOME (tr,kt,vt)` by
    (qpat_assum `!tops src id vis tr kt vt slot rest. _ ==> build_hashmap_info_src _ _ _ _ = _` mp_tac >>
     qpat_assum `!tops src other id var_rest hash_rest. _ ==> _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     Induct >> simp[] >> PairCases >> rw[build_hashmap_info_mods_def] >> metis_tac[]);

val linked_ctor_builder_decl_tac =
  (`!src ts id vis mut ty slot.
      ALOOKUP mods src = SOME ts /\ MEM (VariableDecl vis mut id ty slot) ts ==>
      ctor_ce.ce_hashmap_info (src,id) = NONE /\ ctor_ce.ce_module_var_type (src,id) = SOME ty` by
    (qpat_assum `!ms src ts id vis mut ty slot. _ ==> _ /\ _` mp_tac >>
     qpat_assum `contract_inv mods exps deploy_unit.cu_context ctor_ce cx`
       (mp_tac o PURE_REWRITE_RULE [contract_inv_def, cenv_module_pins_mods_def]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >> disch_tac >>
     simp[] >> rpt gen_tac >> strip_tac >>
     qpat_assum `!s tops. ALOOKUP mods s = SOME tops ==> _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!ms src ts id vis mut ty slot. _ ==> _ /\ _` (drule_all_then ACCEPT_TAC))) >>
  (`!src ts id vis tr kt vt slot.
      ALOOKUP mods src = SOME ts /\ MEM (HashMapDecl vis tr id kt vt slot) ts ==>
      ctor_ce.ce_hashmap_info (src,id) = SOME (tr,kt,vt)` by
    (qpat_assum `!ms src ts id vis tr kt vt slot. _ ==> build_hashmap_info_mods _ _ = _` mp_tac >>
     qpat_assum `contract_inv mods exps deploy_unit.cu_context ctor_ce cx`
       (mp_tac o PURE_REWRITE_RULE [contract_inv_def]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >> disch_tac >>
     simp[] >> rpt gen_tac >> strip_tac >>
     qpat_assum `!s tops. ALOOKUP mods s = SOME tops ==> _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!ms src ts id vis tr kt vt slot. _ ==> build_hashmap_info_mods _ _ = _`
       (drule_all_then ACCEPT_TAC)));

(* The deployment checker fixes the same entry environment for both bodies. *)
val linked_ctor_checked_entry_env_tac =
  `check_function_body am.layouts tx.target mods deploy_art NONE Deploy
      mut F src_args [] NoneT raw_body` by
    (drule_all_then ACCEPT_TAC check_contract_deploy_function_body_MEM) >>
  `?env raw_env'.
    env = function_entry_env deploy_art mods NONE Deploy src_args /\
    env.current_src = NONE /\ env.type_defs = type_env_all_modules mods /\
    env.fn_sigs = deploy_art.cta_fn_sigs /\
    env.bare_globals = deploy_art.cta_bare_globals /\
    env.bare_global_assignable = deploy_art.cta_bare_global_assignable /\
    env.toplevel_vtypes = deploy_art.cta_toplevel_vtypes /\
    env.flag_members = deploy_art.cta_flag_members /\
    type_stmts env NoneT raw_body = SOME raw_env' /\
    (!id ty. MEM (id,ty) src_args ==>
      FLOOKUP env.var_types id = SOME ty /\ IS_SOME (FLOOKUP env.var_assignable id)) /\
    (!id ty. FLOOKUP env.var_types id = SOME ty ==> MEM (id,ty) src_args) /\
    (!id b. FLOOKUP env.var_assignable id = SOME b ==> ?ty. MEM (id,ty) src_args)` by
    (drule_all vyperTypeDeploymentMachineTheory.checked_constructor_body_typing_package >>
     simp[]) >>
  `?env'. type_stmts env NoneT cpkg6 = SOME env'` by
    (qpat_assum `check_function_body _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[NoAsms, check_function_body_def, LET_THM, GSYM optionTheory.IS_SOME_EXISTS] >>
     qpat_assum `env = function_entry_env _ _ _ _ _`
       (fn entry => PURE_REWRITE_TAC [GSYM entry]) >>
     qpat_assum `cpkg6 = subst_consts_stmts_mods _ raw_body`
       (fn body => PURE_REWRITE_TAC [GSYM body]) >>
     disch_then (map_every assume_tac o CONJUNCTS) >> FIRST_ASSUM ACCEPT_TAC) >>
  `frame_maps env deploy_art` by
    (simp[constSubstCorrectTheory.frame_maps_def]);

val linked_ctor_immutable_guards_tac =
  `immutable_section_layout_mods mods ctor_ce` by
    (qpat_assum `contract_inv mods exps deploy_unit.cu_context ctor_ce cx`
       (strip_assume_tac o PURE_REWRITE_RULE [contract_inv_def]) >>
     FIRST_ASSUM ACCEPT_TAC) >>
  `check_linked_state_ownership am.layouts tx.target mods
      (vyperTypeContract$linked_live_functions mods exps)` by
    (drule_all_then (ACCEPT_TAC o REWRITE_RULE [linked_state_ownership_ok_def])
       (Q.INST [`in_deploy` |-> `T`] check_contract_linked_state_ownership_ok)) >>
  `MEM (NONE,"__init__") (vyperTypeContract$linked_live_functions mods exps) /\
   (!key r. ALOOKUP (consts_env_mods mods) key = SOME r ==>
      vyperSubscriptOverlap$accesses_expr r = []) ==>
   ~supported_stmts_expr_exists (unallocated_bare_global_root ctor_ce env) cpkg6 /\
   (!key. MEM (vyperSubscriptOverlap$WriteAcc (vyperSubscriptOverlap$StateRef key))
           (vyperSubscriptOverlap$accesses_stmts cpkg6) /\
          IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
          IS_SOME (FLOOKUP ctor_ce.ce_module_vars key))` by
    (disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `cpkg6 = subst_consts_stmts_mods _ raw_body` SUBST1_TAC >>
     drule_all_then ACCEPT_TAC
       (Q.INST [`mode` |-> `T`, `vis` |-> `Deploy`, `name` |-> `"__init__"`]
          linkedEntryImmutableGuardsTheory.linked_checked_body_immutable_guards));

fun linked_ctor_source_observation_tac frame =
  `returndata_bounded ^frame` by
    (qpat_assum `^frame.contexts = [(_,_)]` (fn contexts =>
       qpat_assum `_.returnData = []` (fn data =>
         simp[NoAsms, vfmReturndataBoundTheory.returndata_bounded_def, contexts, data]))) >>
  `outcomes_accounts_typed (SOME (MAP SND (call_trace ^frame)))` by
    (drule_all call_trace_outcomes_bounded >>
     simp[outcomes_accounts_typed_def, EVERY_MEM]);

val linked_ctor_source_well_typed_tac =
  `cx = (initial_evaluation_context ((tx.target,mods)::am.sources) am.layouts
             (tx with created_in_tx := T) NONE with in_deploy := T)` by
    simp[Abbr `cx`, deploy_evaluation_context_mods_def] >>
  `context_well_typed cx` by
    (qpat_assum `cx = _` SUBST1_TAC >>
     qpat_assum `call_tx_well_typed tx` mp_tac >>
     simp[NoAsms, call_tx_well_typed_def, vyperTypeInvariantsTheory.context_well_typed_def,
          initial_evaluation_context_def]) >>
  `evaluate_all_constants cx am0 tx.target mods = SOME am_c` by
    (qpat_assum `evaluate_module_constants_trace _ am0 _ _ = _` mp_tac >>
     simp[Abbr `cx`, evaluate_all_constants_def, evaluate_module_constants_def]) >>
  `machine_well_typed am_c` by
    (drule_all vyperTypeDeploymentSoundnessTheory.checked_constructor_constants_exist >>
     disch_then (qspec_then `exps` (qx_choose_then `checked_machine` strip_assume_tac)) >>
     `am_c = checked_machine` by
       (qpat_assum `am0 = _` (fn installed =>
          qpat_assum `evaluate_all_constants cx _ tx.target mods = SOME checked_machine`
            (mp_tac o PURE_REWRITE_RULE [GSYM installed])) >>
        qpat_assum `evaluate_all_constants cx am0 tx.target mods = SOME am_c`
          (fn run => simp[NoAsms, run])) >>
     simp[]);

val linked_ctor_source_scope_tac =
  `scope_well_typed scope` by
    (drule_then ACCEPT_TAC vyperTypeBindArgumentsTheory.bind_arguments_scope_well_typed_from_success) >>
  `popped_keys_indexed [scope]` by
    (drule_then ACCEPT_TAC ctorDeployLoweringFrameTheory.deploy_frame_bound_arguments_indexed) >>
  `state_well_typed es0` by
    (qpat_assum `es0 = _` SUBST1_TAC >>
     qpat_assum `machine_well_typed am_c` mp_tac >>
     qpat_assum `scope_well_typed scope` (fn well =>
       simp[NoAsms, well, vyperTypeInitialStateTheory.machine_well_typed_def,
            vyperTypeInvariantsTheory.state_well_typed_def, vyperInterpreterTheory.initial_state_def]));

val linked_ctor_source_accounts_tac =
  `am_c.accounts = am.accounts` by
    (qpat_assum `am_c = am0 with immutables := _`
       (mp_tac o Q.AP_TERM `\m:abstract_machine. m.accounts`) >>
     qpat_assum `am0 = _` (fn installed => simp[NoAsms, installed])) >>
  qabbrev_tac `unpaid = vyperInterpreter$initial_state am_c [scope]` >>
  `state_well_typed unpaid /\ accounts_well_typed unpaid.accounts` by
    (qpat_assum `machine_well_typed am_c` mp_tac >>
     qpat_assum `scope_well_typed scope` (fn well =>
       simp[NoAsms, well, Abbr `unpaid`, vyperTypeInitialStateTheory.machine_well_typed_def,
            vyperTypeInvariantsTheory.state_well_typed_def, vyperInterpreterTheory.initial_state_def])) >>
  `value_transfer_ok cx.txn unpaid.accounts` by
    (qpat_assum `cx = _` (fn context =>
       qpat_assum `am_c.accounts = am.accounts` (fn accounts =>
         qpat_assum `value_transfer_ok tx am.accounts` (fn transfer =>
           simp[NoAsms, Abbr `unpaid`, context, accounts, transfer,
                vyperInterpreterTheory.initial_state_def, initial_evaluation_context_def,
                e2eDeployDefsTheory.value_transfer_created_in_tx]))));

val linked_ctor_send_value_tac =
  `?paid. send_call_value mut cx unpaid = (INL (),paid)` by
    (Cases_on `send_call_value mut cx unpaid` >> Cases_on `q` >> simp[] >>
     drule_all sourceValueRejectionTheory.send_call_value_reject_condition >>
     qpat_assum `~(mut <> Payable /\ tx.value <> 0)` mp_tac >>
     qpat_assum `cx = _` (fn context => simp[NoAsms, context, initial_evaluation_context_def]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]);

val linked_ctor_paid_accounts_tac =
  `paid.accounts = es0.accounts` by
    (drule ctorDeployLoweringEntrySourceFrameTheory.deploy_ctor_send_value_accounts >>
     qpat_assum `cx = _` (fn context =>
       qpat_assum `es0 = _` (fn start =>
         qpat_assum `am_c.accounts = am.accounts` (fn accounts =>
           simp[NoAsms, Abbr `unpaid`, context, start, accounts,
                vyperInterpreterTheory.initial_state_def, initial_evaluation_context_def,
                accounts_after_transfer_def, LET_THM])))) >>
  `accounts_well_typed es0.accounts` by
    (qpat_assum `paid.accounts = es0.accounts` (SUBST1_TAC o SYM) >>
     qpat_assum `state_well_typed unpaid` mp_tac >>
     qpat_assum `accounts_well_typed unpaid.accounts` mp_tac >>
     qpat_assum `send_call_value mut cx unpaid = (INL (),paid)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rpt strip_tac >> drule_all send_call_value_state_sound_c53 >> simp[]);

val linked_ctor_env_consistency_tac =
  `(es0:evaluation_state).scopes = [scope]` by
    (qpat_assum `es0 = unpaid with accounts := _` SUBST1_TAC >>
     simp[Abbr `unpaid`, vyperInterpreterTheory.initial_state_def]) >>
  `env_immutables_consistent (artifact_env deploy_art mods NONE) cx es0` by
    (`es0.immutables = unpaid.immutables` by
       (qpat_assum `es0 = unpaid with accounts := _` SUBST1_TAC >> simp[NoAsms]) >>
     qpat_assum `es0.immutables = unpaid.immutables`
       (fn eq => rewrite_tac [MATCH_MP
         vyperTypeInitialStateTheory.env_immutables_consistent_immutables_cong eq]) >>
     qpat_assum `am0 = _` (fn installed =>
       qpat_assum `evaluate_all_constants cx am0 tx.target mods = SOME am_c`
         (assume_tac o PURE_REWRITE_RULE [installed])) >>
     drule_all vyperTypeDeploymentSoundnessTheory.checked_constructor_initial_immutables_consistent >>
     disch_then (qspecl_then [`scope`,`[]`,`NONE`,`[]`] mp_tac) >>
     simp[NoAsms, Abbr `unpaid`, vyperInterpreterTheory.initial_state_def]) >>
  `env_consistent env cx es0 /\ functions_well_typed cx` by
    (`ALOOKUP ((tx.target,mods)::am.sources) tx.target = SOME mods` by simp[] >>
     `vyperInterpreter$lookup_function NONE tx.function_name Deploy tops' =
       SOME (mut,F,src_args,[],NoneT,raw_body)` by simp[] >>
     drule_all ctorDeployLoweringFrameTheory.deploy_frame_checked_body_setup >>
     disch_then (qx_choosel_then [`checked_env`,`checked_after`]
       (map_every assume_tac o CONJUNCTS)) >>
     `checked_env = env` by
       (qpat_assum `checked_env = function_entry_env _ _ _ _ _` SUBST1_TAC >>
        qpat_assum `env = function_entry_env _ _ _ _ _` (ACCEPT_TAC o SYM)) >>
     qpat_x_assum `checked_env = env` SUBST_ALL_TAC >>
     conj_tac >> FIRST_ASSUM ACCEPT_TAC);

val linked_ctor_alloc_env_tac =
  `ctor_ce = ce_base with <|ce_vars := ce1.ce_vars; ce_is_ctor := T;
    ce_raw_return := F; ce_nonreentrant := (F,global_nonreentrant_slot,T,F);
    ce_imm_alloca := (if imm_len_mods mods > 0 then SOME imm else NONE);
    ce_ctor_exit_label := SOME exit_lbl|>` by
    (qpat_assum `!pos ce off size cs ce' cs'. _ ==> _`
      (drule_then (fn reg =>
        qpat_assum `Abbrev (ctor_ce = _)`
          (PURE_REWRITE_TAC o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
        PURE_ONCE_REWRITE_TAC [reg] >>
        qpat_assum `ce_before_registration = _` (fn before_reg =>
          qpat_assum `cpkg0 = _` (fn pkg =>
            simp[NoAsms, before_reg, pkg, compile_env_component_equality]))))) >>
  `alloc_env_agree (build_compile_env_unit mods NONE Internal mut "__init__"
      src_args NoneT cpkg6 F) ctor_ce /\ ~ctor_ce.ce_is_external` by
    (qpat_assum `ctor_ce = _` SUBST1_TAC >>
     simp[Abbr `ce_base`, allocLimitsPropsTheory.alloc_env_agree_def,
          build_compile_env_unit_def, LET_THM, pairTheory.ELIM_UNCURRY]);

val linked_ctor_typed_allocation_tac =
  qmatch_asmsub_abbrev_tac `alloc_env_agree alloc_ce ctor_ce` >>
  `!ty. type_memory_bytes ctor_ce ty = type_memory_bytes alloc_ce ty` by
    (qpat_assum `alloc_env_agree alloc_ce ctor_ce`
      (mp_tac o cj 1 o REWRITE_RULE [allocLimitsPropsTheory.alloc_env_agree_def]) >>
     simp[NoAsms, GSYM structFieldsPropsTheory.type_mem_bytes_type_memory_bytes]) >>
  `alloc_limits_stmts ctor_ce cpkg6 = alloc_limits_stmts alloc_ce cpkg6` by
    (irule (CONJUNCT2 allocLimitsPropsTheory.alloc_limits_stmt_struct_fields) >>
     FIRST_ASSUM ACCEPT_TAC) >>
  `EVERY (\a. type_memory_bytes ctor_ce (SND a) < 2 ** 64) src_args /\
   alloc_limits_stmts ctor_ce cpkg6` by
    (qpat_assum `fn_allocs_ok_unit mods (NONE,mut,F,F,"__init__",src_args,[],NoneT,_)` mp_tac >>
     qpat_assum `cpkg6 = subst_consts_stmts_mods _ raw_body`
       (fn body => PURE_REWRITE_TAC [GSYM body]) >>
     simp[fn_allocs_ok_unit_def, LET_THM, GSYM markerTheory.Abbrev_def, pairTheory.ELIM_UNCURRY]);

val linked_ctor_register_domain_tac =
  `!args ce off dsz st ce' st' n l.
     compile_register_constructor_args ce args off dsz st = (ce',st') /\
     FLOOKUP ce'.ce_vars n = SOME l ==>
     ?l0. FLOOKUP ce.ce_vars n = SOME l0` by
    (POP_ASSUM_LIST (K ALL_TAC) >>
     Induct >- simp[moduleLoweringTheory.compile_register_constructor_args_def, comp_return_def] >>
     PairCases >> rpt gen_tac >>
     simp[Once moduleLoweringTheory.compile_register_constructor_args_def] >>
     rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
     simp[comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
     rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
     first_x_assum drule_all >> simp[finite_mapTheory.FLOOKUP_UPDATE] >> rw[] >> gvs[]);

val linked_ctor_formal_domain_tac =
  `ce_before_registration.ce_vars =
     FST (allocate_args (get_struct_fields (make_struct_fields_map_mods mods))
             src_args 0 FEMPTY)` by
    (qpat_assum `ce_before_registration = _` SUBST1_TAC >>
     qpat_assum `cpkg0 = _` SUBST1_TAC >>
     simp[NoAsms, Abbr `ce_base`, build_compile_env_unit_def, LET_THM,
          pairTheory.ELIM_UNCURRY]) >>
  `!n l. FLOOKUP ce_before_registration.ce_vars n = SOME l ==> MEM n (MAP FST src_args)` by
    (qpat_assum `ce_before_registration.ce_vars = _` SUBST1_TAC >>
     qpat_assum `ALL_DISTINCT (MAP FST src_args)`
       (qspecl_then [`get_struct_fields (make_struct_fields_map_mods mods)`,`0`,`FEMPTY`]
         (assume_tac o cj 1) o MATCH_MP entryStateRelTheory.allocate_args_lookup) >>
     rpt gen_tac >> Cases_on `MEM n (MAP FST src_args)` >- simp[] >>
     qpat_assum `!k. ~MEM k (MAP FST src_args) ==> _`
       (qspec_then `n` mp_tac) >> simp[finite_mapTheory.FLOOKUP_EMPTY]);

val linked_ctor_post_registration_domain_tac =
  `!n l. FLOOKUP ctor_ce.ce_vars n = SOME l ==> MEM n (MAP FST src_args)` by
    (qpat_assum `ctor_ce = _` SUBST1_TAC >> simp[NoAsms] >> rpt strip_tac >>
     qpat_assum `!args ce off dsz st ce' st' n l. _ ==> _`
       (fn th => drule_all_then strip_assume_tac th) >>
     qpat_assum `!n l. FLOOKUP ce_before_registration.ce_vars n = SOME l ==> _`
       (fn th => drule_then ACCEPT_TAC th)) >>
  `ce_locals_declared ctor_ce env` by
    (qpat_assum `!n l. FLOOKUP ctor_ce.ce_vars n = SOME l ==> _` mp_tac >>
     qpat_assum `!id ty. MEM (id,ty) src_args ==> FLOOKUP env.var_types id = SOME ty /\ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[bodySimTheory.ce_locals_declared_def, MEM_MAP, pairTheory.EXISTS_PROD] >>
     metis_tac[vyperTypeScopePopTheory.FLOOKUP_SOME_IN_FDOM]);

val linked_ctor_registered_pointers_tac =
  `!x. ce_before_registration.ce_imm_alloca = SOME (Var x) ==>
       not_fresh_at st1 x` by
    (qpat_assum `ce_before_registration = cpkg0 with ce_imm_alloca := _` SUBST1_TAC >>
     qpat_assum `(if imm_len_mods mods > 0 then _ else _) st_pay = (imm,st1)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `imm_len_mods mods > 0` >> simp[comp_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
     rename1 `compile_fixed_region_with_id _ st_pay = (r,st1)` >>
     PairCases_on `r` >> drule contextTheory.compile_fixed_region_with_id_result >>
     simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
     rpt strip_tac >> gvs[]);

val linked_ctor_formal_pointers_tac =
  `!id ty. FLOOKUP env.var_types id = SOME ty ==>
     ?p sz. FLOOKUP ctor_ce.ce_vars id = SOME (PtrVar (Var p) sz)` by
    (`!id. (?off sz. FLOOKUP ce_before_registration.ce_vars id = SOME (MemLoc off sz)) \/
          (?p sz. FLOOKUP ce_before_registration.ce_vars id = SOME (PtrVar (Var p) sz)) ==>
          ?p sz. FLOOKUP ce1.ce_vars id = SOME (PtrVar (Var p) sz)` by
       (qpat_assum `!n l. FLOOKUP ce_before_registration.ce_vars n = SOME l ==> _` mp_tac >>
        qpat_assum `!id p sz. FLOOKUP ce_before_registration.ce_vars id <> SOME (PtrVar (Var p) sz)` mp_tac >>
        qpat_assum `!x. ce_before_registration.ce_imm_alloca = SOME (Var x) ==> _` mp_tac >>
        qpat_assum `compile_register_constructor_args ce_before_registration (build_positional_args _ _) 0 0 st1 = _`
          (mp_then Any mp_tac entryLocalsTheory.compile_register_constructor_args_reserved) >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[entryLocalsTheory.build_positional_args_FST] >> metis_tac[]) >>
     qpat_assum `ctor_ce = _` SUBST1_TAC >> simp[NoAsms] >>
     qpat_assum `!id. _ ==> ?p sz. FLOOKUP ce1.ce_vars id = _` mp_tac >>
     qpat_assum `!id ty. FLOOKUP env.var_types id = SOME ty ==> _` mp_tac >>
     qpat_assum `EVERY (\a. ?off. FLOOKUP ce_before_registration.ce_vars (FST a) = _) src_args` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]);

(* A qualified constant declared in a module is present in the unit table. *)
val linked_ctor_const_key_tac =
  `!ts acc id. MEM id (MAP FST (module_consts_env ts acc)) ==>
    MEM id (MAP FST acc) \/
    ?vis e ty slot. MEM (VariableDecl vis (Constant e) id ty slot) ts` by
    (POP_ASSUM_LIST (K ALL_TAC) >> ho_match_mp_tac constSubstTheory.module_consts_env_ind >>
     simp[constSubstTheory.module_consts_env_def, MEM_APPEND] >> metis_tac[]) >>
  `!src ts acc key. MEM key (MAP FST acc) \/
    (?vis e id ty slot. key = (src,id) /\
      MEM (VariableDecl vis (Constant e) id ty slot) ts) ==>
    MEM key (MAP FST (module_consts_env_mods src ts acc))` by
    (POP_ASSUM_LIST (K ALL_TAC) >> ho_match_mp_tac constSubstModsTheory.module_consts_env_mods_ind >>
     simp[constSubstModsTheory.module_consts_env_mods_def, MEM_APPEND] >> metis_tac[]) >>
  `!ms acc key. MEM key (MAP FST acc) \/
    (?src ts vis e id ty slot. key = (src,id) /\ MEM (src,ts) ms /\
      MEM (VariableDecl vis (Constant e) id ty slot) ts) ==>
    MEM key (MAP FST (consts_env_mods_acc ms acc))` by
    (qpat_assum `!src ts acc key. _ ==> MEM key (MAP FST (module_consts_env_mods _ _ _))` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> disch_tac >> Induct >>
     simp[constSubstModsTheory.consts_env_mods_acc_def, pairTheory.FORALL_PROD] >>
     rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
  Q.SUBGOAL_THEN `!key. cx_const_name_mods mods key ==> IS_SOME (ALOOKUP (consts_env_mods mods) key)` assume_tac;

val linked_ctor_const_key_member_tac =
  qx_gen_tac `key` >> PairCases_on `key` >>
  simp[cx_const_name_mods_def, optionTheory.IS_SOME_EQ_NOT_NONE, alistTheory.ALOOKUP_NONE,
       constSubstModsTheory.consts_env_mods_def, consts_env_modules_order_eq] >>
  disch_then (qx_choose_then `decls` strip_assume_tac) >>
  `MEM (key0,decls) mods` by (irule alistTheory.ALOOKUP_MEM >> first_assum ACCEPT_TAC) >>
  qpat_assum `!ts acc id. MEM id (MAP FST (module_consts_env ts acc)) ==> _`
    (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >>
  qpat_assum `!ms acc key. _ ==> MEM key (MAP FST (consts_env_mods_acc ms acc))` irule >>
  simp[MEM_constants_order] >>
  qpat_assum `MEM (VariableDecl _ (Constant _) _ _ _) decls` mp_tac >>
  qpat_assum `MEM (key0,decls) mods` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[];

(* An access-free replacement cannot contain a qualified constant root. *)
val linked_ctor_access_free_root_tac =
  `(!e. accesses_expr e = [] ==> ~supported_expr_exists (const_name_root_mods mods) e) /\
   (!t. accesses_target t = [] ==> ~supported_target_exists (const_name_root_mods mods) t) /\
   (!es. accesses_exprs es = [] ==> ~supported_exprs_exists (const_name_root_mods mods) es) /\
   (!opt. accesses_opt opt = [] ==> ~supported_opt_exists (const_name_root_mods mods) opt) /\
   (!fs. accesses_named_exprs fs = [] ==> ~supported_fields_exists (const_name_root_mods mods) fs)` by
    (POP_ASSUM_LIST (K ALL_TAC) >> ho_match_mp_tac vyperSubscriptOverlapTheory.accesses_expr_ind >>
     simp[vyperSubscriptOverlapTheory.accesses_expr_def,
          supportedExprTraverseTheory.supported_expr_exists_def, const_name_root_mods_def] >>
     metis_tac[]);

(* At a hit use the replacement's access bound; at a miss the key is not constant. *)
val linked_ctor_subst_expr_roots_tac =
  Q.SUBGOAL_THEN
  `(!e. ~supported_expr_exists (const_name_root_mods mods)
           (subst_consts_expr_mods (consts_env_mods mods) e)) /\
   (!t. ~supported_target_exists (const_name_root_mods mods)
           (subst_consts_btarget_mods (consts_env_mods mods) t)) /\
   (!es. ~supported_exprs_exists (const_name_root_mods mods)
           (subst_consts_exprs_mods (consts_env_mods mods) es)) /\
   (!opt. ~supported_opt_exists (const_name_root_mods mods)
           (subst_consts_opt_mods (consts_env_mods mods) opt)) /\
   (!fs. ~supported_fields_exists (const_name_root_mods mods)
           (subst_consts_fields_mods (consts_env_mods mods) fs))`
    (map_every assume_tac o CONJUNCTS)
  >- (ho_match_mp_tac vyperSubscriptOverlapTheory.accesses_expr_ind >>
      simp[constSubstModsTheory.subst_consts_expr_mods_def,
           supportedExprTraverseTheory.supported_expr_exists_def, const_name_root_mods_def] >>
      rpt gen_tac >>
      qmatch_goalsub_rename_tac `TopLevelName ann key` >> PairCases_on `key` >>
      Cases_on `ALOOKUP (consts_env_mods mods) (key0,key1)` >>
      simp[constSubstModsTheory.subst_consts_expr_mods_def,
           supportedExprTraverseTheory.supported_expr_exists_def, const_name_root_mods_def] >>
      qpat_assum `ALOOKUP (consts_env_mods mods) (key0,key1) = _` mp_tac
      >- (qpat_assum `!k. cx_const_name_mods mods k ==> _` mp_tac >>
          POP_ASSUM_LIST (K ALL_TAC) >> simp[optionTheory.IS_SOME_EQ_NOT_NONE] >> metis_tac[])
      >> qpat_assum `!k r. ALOOKUP (consts_env_mods mods) k = SOME r ==> _` mp_tac >>
      qpat_assum `!e. accesses_expr e = [] ==> ~supported_expr_exists (const_name_root_mods mods) e` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]);

val linked_ctor_subst_stmt_roots_tac =
  `(!t. ~supported_assignment_exists (const_name_root_mods mods)
           (subst_consts_target_mods (consts_env_mods mods) t)) /\
   (!ts. ~supported_assignments_exists (const_name_root_mods mods)
           (subst_consts_targets_mods (consts_env_mods mods) ts))` by
    (ho_match_mp_tac vyperSubscriptOverlapTheory.accesses_atarget_ind >>
     simp[constSubstModsTheory.subst_consts_target_mods_def,
          supportedStmtTraverseTheory.supported_assignment_exists_def]) >>
  `!es fs. EXISTS (supported_expr_exists (const_name_root_mods mods)) (es ++ MAP SND fs) <=>
    supported_exprs_exists (const_name_root_mods mods) es \/
    supported_fields_exists (const_name_root_mods mods) fs` by
    simp[EXISTS_APPEND, EXISTS_MAP, combinTheory.o_DEF,
         supportedExprTraverseTheory.supported_exprs_exists_every,
         supportedExprTraverseTheory.supported_fields_exists_every] >>
  `!err. ~EXISTS (supported_expr_exists (const_name_root_mods mods))
       (custom_error_exprs (subst_consts_error_mods (consts_env_mods mods) err))` by
    (Cases >> pure_rewrite_tac[constSubstModsTheory.subst_consts_error_mods_def,
                                vyperASTTheory.custom_error_exprs_def] >>
     qpat_assum `!es fs. EXISTS _ (es ++ MAP SND fs) <=> _` (pure_rewrite_tac o single) >>
     simp[]) >>
  `!r. ~supported_assert_exists (const_name_root_mods mods)
           (subst_consts_areason_mods (consts_env_mods mods) r)` by
    (Cases >> simp[constSubstModsTheory.subst_consts_areason_mods_def,
                   supportedStmtTraverseTheory.supported_assert_exists_def]) >>
  `!r. ~supported_raise_exists (const_name_root_mods mods)
           (subst_consts_rreason_mods (consts_env_mods mods) r)` by
    (Cases >> simp[constSubstModsTheory.subst_consts_rreason_mods_def,
                   supportedStmtTraverseTheory.supported_raise_exists_def]) >>
  `!i. ~supported_iterator_exists (const_name_root_mods mods)
           (subst_consts_iter_mods (consts_env_mods mods) i)` by
    (Cases >> simp[constSubstModsTheory.subst_consts_iter_mods_def,
                   supportedStmtTraverseTheory.supported_iterator_exists_def]) >>
  `(!s. ~supported_stmt_expr_exists (const_name_root_mods mods)
           (subst_consts_stmt_mods (consts_env_mods mods) s)) /\
   (!ss. ~supported_stmts_expr_exists (const_name_root_mods mods)
           (subst_consts_stmts_mods (consts_env_mods mods) ss))`
    suffices_by (disch_then (qspec_then `raw_body` ACCEPT_TAC o CONJUNCT2)) >>
  ho_match_mp_tac vyperSubscriptOverlapTheory.accesses_stmt_ind >>
  simp[constSubstModsTheory.subst_consts_stmt_mods_def,
       supportedStmtTraverseTheory.supported_stmt_expr_exists_def];

val linked_ctor_const_name_free_tac =
  Q.SUBGOAL_THEN
    `(!k r. ALOOKUP (consts_env_mods mods) k = SOME r ==> accesses_expr r = []) ==>
     ~supported_stmts_expr_exists (const_name_root_mods ctor_ce.ce_modules) cpkg6`
    assume_tac;

val linked_ctor_const_name_free_body_tac =
  qpat_assum `contract_inv mods exps _ ctor_ce cx`
    (SUBST1_TAC o MATCH_MP bodyInvCodePropsTheory.contract_inv_cenv_modules) >>
  qpat_assum `cpkg6 = subst_consts_stmts_mods _ raw_body` SUBST1_TAC >>
  POP_ASSUM_LIST (K ALL_TAC) >> disch_tac;

val linked_ctor_stmts_exprs_ok_tac =
  `locals_alloc_ok ctor_ce env` by
    (irule ctorDeployLoweringFrameTheory.deploy_frame_formal_locals_alloc_ok >>
     qexists_tac `src_args` >> simp[]) >>
  `qualified_stmts_decls_ok ctor_ce.ce_modules cpkg6` by
    (drule_then SUBST1_TAC bodyInvCodePropsTheory.contract_inv_cenv_modules >>
     qpat_assum `cpkg6 = subst_consts_stmts_mods _ raw_body` SUBST1_TAC >>
     drule_all_then ACCEPT_TAC
       linkedConstAnnotationsTheory.checked_qualified_body_decl_resolution) >>
  `(!id ty. FLOOKUP env.var_types id = SOME ty ==> well_formed_type env.type_defs ty) /\
   (!id vt. FLOOKUP env.toplevel_vtypes id = SOME vt ==> well_formed_vtype env.type_defs vt)` by
    (`!n ty. FLOOKUP env.var_types n = SOME ty ==> ?id. MEM (id,ty) src_args /\ n = id` by simp[] >>
     drule_all_then ACCEPT_TAC (Q.INST [`in_deploy` |-> `T`]
       (SPEC_ALL ctorDeployLoweringFrameTheory.deploy_frame_constructor_env_well_formed))) >>
  `~supported_stmts_expr_exists (const_name_root_mods ctor_ce.ce_modules) cpkg6 ==>
   stmts_exprs_ok ctor_ce cpkg6` by
    (strip_tac >> drule_all_then ACCEPT_TAC
       ctorDeployLoweringFrameTheory.deploy_frame_typed_allocated_stmts_exprs_ok);

val linked_ctor_formal_types_tac =
  `!ss id. MEM id (MAP FST (collect_locals ss)) <=>
      MEM id (MAP FST (supported_stmts_bindings T ss)) \/
      MEM id (MAP FST (supported_stmts_bindings F ss))` by
    (POP_ASSUM_LIST (K ALL_TAC) >> recInduct moduleLoweringTheory.collect_locals_ind >>
     simp[moduleLoweringTheory.collect_locals_def, supportedStmtTraverseTheory.supported_stmt_bindings_def] >>
     metis_tac[]) >>
  `EVERY (\n. n NOTIN FDOM env.var_types)
      (MAP FST (supported_stmts_bindings T cpkg6 ++ supported_stmts_bindings F cpkg6))` by
    (drule_then ACCEPT_TAC (cj 2 whitelistCheckerDeclsTheory.type_stmt_bindings_fresh)) >>
  `!id ty. FLOOKUP env.var_types id = SOME ty ==>
      ALOOKUP (REVERSE (src_args ++ collect_locals cpkg6)) id = SOME ty` by
    (rpt gen_tac >> disch_tac >>
     `MEM (id,ty) src_args` by
       (qpat_assum `!id ty. FLOOKUP env.var_types id = SOME ty ==> MEM (id,ty) src_args`
          (drule_then ACCEPT_TAC)) >>
     `id IN FDOM env.var_types` by
       (drule_then ACCEPT_TAC vyperTypeScopePopTheory.FLOOKUP_SOME_IN_FDOM) >>
     `ALOOKUP (REVERSE (collect_locals cpkg6)) id = NONE` by
       (simp[NoAsms, alistTheory.ALOOKUP_NONE, MAP_REVERSE] >>
        qpat_assum `!ss id. MEM id (MAP FST (collect_locals ss)) <=> _` (fn names => simp[NoAsms, names]) >>
        qpat_assum `EVERY (\n. n NOTIN FDOM env.var_types) _` mp_tac >>
        qpat_assum `id IN FDOM env.var_types` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[EVERY_MEM] >> metis_tac[]) >>
     qpat_assum `ALOOKUP (REVERSE (collect_locals cpkg6)) id = NONE`
       (fn no_local => simp[NoAsms, REVERSE_APPEND, alistTheory.ALOOKUP_APPEND, no_local]) >>
     irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM >> simp[MAP_REVERSE]) >>
  `!id ty. FLOOKUP env.var_types id = SOME ty ==> ctor_ce.ce_var_type id = SOME ty` by
    (qpat_assum `!id ty. FLOOKUP env.var_types id = SOME ty ==> ALOOKUP _ id = SOME ty` mp_tac >>
     qpat_assum `ctor_ce = _` SUBST1_TAC >>
     qpat_assum `Abbrev (ce_base = _)`
       (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[markerTheory.Abbrev_def, build_compile_env_unit_def, LET_THM,
          pairTheory.ELIM_UNCURRY]);

val linked_ctor_expr_metadata_tac =
  `linked_fn_sigs_declared mods cx env.fn_sigs` by
    (qpat_assum `env.fn_sigs = _` SUBST1_TAC >>
     drule_then ACCEPT_TAC bodyCallSupportTheory.check_contract_linked_fn_sigs_declared) >>
  `get_tenv cx = type_env_all_modules mods` by
    (drule_then ACCEPT_TAC bodyInvMetadataPropsTheory.contract_inv_type_env) >>
  `!fname tys. ctor_ce.ce_method_id fname tys =
       w2n (calldata_method_id
              (function_selector fname (vyper_to_abi_types (get_tenv cx) tys)))` by
    (qpat_assum `ctor_ce = _` SUBST1_TAC >>
     simp[NoAsms, Abbr `ce_base`, build_compile_env_unit_def, LET_THM,
          pairTheory.ELIM_UNCURRY] >> simp[]) >>
  `sfields_tenv_consistent ctor_ce.ce_struct_fields (get_tenv cx)` by
    (drule_then SUBST1_TAC bodyInvCodePropsTheory.contract_inv_struct_fields >>
     simp[] >> irule make_struct_fields_map_mods_consistent >> qexists_tac `T` >>
     first_assum ACCEPT_TAC);

(* Field-name uniqueness comes from the checked declaration; byte sizes
   come from the compiler's decoration of precisely those fields. *)
val linked_ctor_struct_fields_tac =
  `!args tenv. EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) (build_struct_fields_one tenv args)` by
    (POP_ASSUM_LIST (K ALL_TAC) >>
     pure_rewrite_tac[build_struct_fields_one_def, listTheory.EVERY_MAP] >>
     simp[listTheory.EVERY_MEM, pairTheory.FORALL_PROD, field_mem_bytes_def] >>
     rpt strip_tac >> simp[]) >>
  sg `!name fields. FLOOKUP ctor_ce.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
       sz = type_memory_size tv) fields` >-
    (map_every qx_gen_tac [`struct_name`, `struct_fields`] >> disch_tac >>
     qpat_assum `sfields_tenv_consistent _ _`
       (strip_assume_tac o REWRITE_RULE [sfields_tenv_consistent_def]) >>
     qpat_assum `!name fields. FLOOKUP ctor_ce.ce_struct_fields name = SOME fields ==> _`
       (drule_then (qx_choosel_then [`struct_key`,`struct_args`] strip_assume_tac)) >>
     `contract_namespaces_ok T mods` by
       (drule_then ACCEPT_TAC check_contract_namespaces_ok) >>
     `FLOOKUP (type_env_all_modules mods) struct_key = SOME (StructArgs struct_args)` by
       (qpat_assum `get_tenv cx = _` (SUBST1_TAC o SYM) >> FIRST_ASSUM ACCEPT_TAC) >>
     `struct_fields = build_struct_fields_one (type_env_all_modules mods) struct_args` by
       (drule_all_then assume_tac make_struct_fields_map_mods_lookup >>
        qpat_assum `FLOOKUP ctor_ce.ce_struct_fields struct_name = SOME struct_fields` mp_tac >>
        drule_then SUBST1_TAC bodyInvCodePropsTheory.contract_inv_struct_fields >>
        simp[]) >>
     conj_tac >-
       (qpat_assum `MAP FST struct_fields = MAP FST struct_args` SUBST1_TAC >>
        PairCases_on `struct_key` >>
        `ALL_DISTINCT (MAP FST mods)` by
          (qpat_assum `contract_namespaces_ok T mods`
             (mp_tac o REWRITE_RULE [contract_namespaces_ok_def]) >> simp[]) >>
        qpat_assum `FLOOKUP (type_env_all_modules mods) _ = SOME (StructArgs struct_args)` mp_tac >>
        qpat_assum `ALL_DISTINCT (MAP FST mods)` (fn distinct =>
          simp[NoAsms, MATCH_MP (SPEC_ALL vyperTypeConstantFoldTheory.FLOOKUP_type_env_all_modules)
            distinct]) >>
        Cases_on `ALOOKUP mods struct_key0` >> simp[] >> disch_tac >>
        rename1 `ALOOKUP mods struct_key0 = SOME struct_decls` >>
        drule_then strip_assume_tac structFieldsPropsTheory.type_env_for_module_struct_mem >>
        `MEM (struct_key0,struct_decls) mods` by
          (irule alistTheory.ALOOKUP_MEM >> FIRST_ASSUM ACCEPT_TAC) >>
        drule_all_then ACCEPT_TAC check_contract_struct_fields_distinct) >>
     qpat_assum `struct_fields = build_struct_fields_one _ _` SUBST1_TAC >>
     qpat_assum `get_tenv cx = _` SUBST1_TAC >>
     qpat_assum `!args tenv. EVERY _ (build_struct_fields_one tenv args)` irule);

fun linked_ctor_observed_env_tac frame =
  `!gs. env_consistent env cx (es0 with <|gas_obs := gs;
          outcomes := SOME (MAP SND (call_trace ^frame))|>) /\
        state_well_typed (es0 with <|gas_obs := gs;
          outcomes := SOME (MAP SND (call_trace ^frame))|>)` by
    (simp[NoAsms, vyperTypeInvariantsTheory.gas_obs_type_invariants,
          vyperTypeInvariantsTheory.outcomes_type_invariants] >>
     conj_tac >> first_assum ACCEPT_TAC);

(* Every checked signature has a real declaration, including in singleton
   modules; the callable lookup alone can also return a synthetic constructor. *)
val linked_ctor_return_decl_tac =
  `contract_namespaces_ok T mods` by
    (qpat_assum `check_contract T _ _ mods = SOME deploy_art`
       (ACCEPT_TAC o MATCH_MP check_contract_namespaces_ok)) >>
  `!sid nm sg. FLOOKUP env.fn_sigs (sid,nm) = SOME sg ==>
       ?ts vis mu nr raw ps ds ss.
         ALOOKUP mods sid = SOME ts /\
         MEM (FunctionDecl vis mu nr raw nm ps ds sg.ret_ty ss) ts /\
         include_fn_sig T vis` by
    (qpat_assum `env.fn_sigs = deploy_art.cta_fn_sigs` SUBST1_TAC >>
     qpat_assum `contract_namespaces_ok T mods` mp_tac >>
     qpat_assum `check_contract T _ _ mods = SOME deploy_art`
       (mp_tac o cj 2 o MATCH_MP check_contract_artifact_fields) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     disch_then SUBST1_TAC >> strip_tac >>
     simp_tac bool_ss [FLOOKUP_DRESTRICT_SOME] >>
     rpt gen_tac >> strip_tac >>
     drule_all_then (strip_assume_tac) build_contract_type_artifact_fn_sigs_declared_sound >>
     metis_tac[]);

(* A source fold only changes the keys supplied by its included declarations. *)
val linked_ctor_return_miss_goal =
  SUBGOAL_THEN
    ``!ts sid key base.
        EVERY (\k. ~MEM #"." (SND k)) (FLAT (MAP (fn_sig_keys_toplevel T sid) ts)) /\
        ~MEM #"." (SND key) /\
        ~MEM key (FLAT (MAP (fn_sig_keys_toplevel T sid) ts)) ==>
        build_func_return_type_src sid ts base (nsid_to_string key) =
          base (nsid_to_string key)`` ASSUME_TAC;

val linked_ctor_return_miss_tac =
  POP_ASSUM_LIST (K ALL_TAC) >>
  Induct_on `ts` >- simp[build_func_return_type_src_def] >>
  Cases_on `h` >>
  simp[build_func_return_type_src_def, fn_sig_keys_toplevel_def] >>
  qmatch_goalsub_rename_tac `include_fn_sig T vis` >>
  Cases_on `vis` >> simp[include_fn_sig_def] >> rpt strip_tac >>
  qmatch_goalsub_rename_tac `nsid_to_string (sid,nm)` >>
  `nsid_to_string key <> nsid_to_string (sid,nm)` by
    (strip_tac >>
     `key = (sid,nm)` by
       (irule linkedNsidPropsTheory.nsid_to_string_dot_free_injective >> simp[]) >>
     fs[]) >>
  simp[];

val linked_ctor_return_key_member_tac =
  `!ts (sid:num option) nm vis mu nr raw ps ds ret ss.
     include_fn_sig T vis /\ MEM (FunctionDecl vis mu nr raw nm ps ds ret ss) ts ==>
     MEM (sid,nm) (FLAT (MAP (fn_sig_keys_toplevel T sid) ts))` by
    (POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     simp[listTheory.MEM_FLAT,listTheory.MEM_MAP,PULL_EXISTS] >>
     qexists_tac `FunctionDecl vis mu nr raw nm ps ds ret ss` >>
     simp[fn_sig_keys_toplevel_def]);

val linked_ctor_return_hit_goal =
  SUBGOAL_THEN
    ``!ts sid nm vis mu nr raw ps ds ret ss base.
        EVERY (\k. ~MEM #"." (SND k)) (FLAT (MAP (fn_sig_keys_toplevel T sid) ts)) /\
        ALL_DISTINCT (FLAT (MAP (fn_sig_keys_toplevel T sid) ts)) /\
        ~MEM #"." nm /\ include_fn_sig T vis /\ MEM (FunctionDecl vis mu nr raw nm ps ds ret ss) ts ==>
        build_func_return_type_src sid ts base (nsid_to_string (sid,nm)) = ret``
    ASSUME_TAC;

val linked_ctor_return_hit_tac =
  qpat_assum `!ts sid nm vis mu nr raw ps ds ret ss. include_fn_sig T vis /\ _ ==> _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> disch_tac >>
  Induct_on `ts` >- simp[] >>
  Cases_on `h` >> simp[build_func_return_type_src_def, fn_sig_keys_toplevel_def] >>
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (qmatch_goalsub_rename_tac `include_fn_sig T head_vis` >>
    Cases_on `head_vis` >> simp[include_fn_sig_def] >> rpt strip_tac >>
    gvs[include_fn_sig_def] >>
    ((FIRST_ASSUM irule >> metis_tac[]) ORELSE
     (IF_CASES_TAC >-
        (qmatch_asmsub_rename_tac `nsid_to_string (sid,nm) = nsid_to_string (sid,head_nm)` >>
         `(sid,nm) = (sid,head_nm)` by
           (irule linkedNsidPropsTheory.nsid_to_string_dot_free_injective >> simp[]) >>
         gvs[] >> metis_tac[]) >>
      FIRST_ASSUM irule >> metis_tac[]))));

val linked_ctor_return_checked_keys_tac =
  `ALL_DISTINCT (contract_keys (fn_sig_keys_toplevel T) mods)` by
    (qpat_assum `contract_namespaces_ok T mods`
       (ACCEPT_TAC o cj 3 o PURE_REWRITE_RULE [contract_namespaces_ok_def])) >>
  `EVERY (\k. ~MEM #"." (SND k)) (contract_keys (fn_sig_keys_toplevel T) mods)` by
    (qpat_assum `contract_namespaces_ok T mods`
       (mp_tac o cj 12 o PURE_REWRITE_RULE [contract_namespaces_ok_def]) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[listTheory.EVERY_MEM, contract_keys_def, listTheory.MEM_FLAT,
          listTheory.MEM_MAP, PULL_EXISTS, pairTheory.EXISTS_PROD] >>
     rpt strip_tac >>
     rename [`MEM (sid,ts) mods`, `MEM tl ts`, `MEM key (fn_sig_keys_toplevel T sid tl)`] >>
     qpat_x_assum `!e. MEM e mods ==> _` (qspec_then `(sid,ts)` mp_tac) >>
     simp[] >> qexists_tac `tl` >>
     Cases_on `tl` >> fs[fn_sig_keys_toplevel_def] >>
     qmatch_asmsub_rename_tac `include_fn_sig T vis` >>
     Cases_on `vis` >> gvs[include_fn_sig_def]);

val linked_ctor_return_mod_key_tac =
  `!ms (sid:num option) ts nm.
      MEM (sid,ts) ms /\ MEM (sid,nm) (FLAT (MAP (fn_sig_keys_toplevel T sid) ts)) ==>
      MEM (sid,nm) (contract_keys (fn_sig_keys_toplevel T) ms)` by
    (POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     pure_rewrite_tac[contract_keys_def,listTheory.MEM_FLAT] >>
     qexists_tac `FLAT (MAP (fn_sig_keys_toplevel T sid) ts)` >>
     simp[] >> pure_rewrite_tac[listTheory.MEM_MAP] >>
     qexists_tac `(sid,ts)` >> simp[]);

val linked_ctor_return_mods_goal =
  SUBGOAL_THEN
    ``!ms sid ts nm vis mu nr raw ps ds ret ss.
        EVERY (\k. ~MEM #"." (SND k)) (contract_keys (fn_sig_keys_toplevel T) ms) /\
        ALL_DISTINCT (contract_keys (fn_sig_keys_toplevel T) ms) /\
        MEM (sid,ts) ms /\ include_fn_sig T vis /\
        MEM (FunctionDecl vis mu nr raw nm ps ds ret ss) ts ==>
        build_func_return_type_mods ms (nsid_to_string (sid,nm)) = ret``
    ASSUME_TAC;

val linked_ctor_return_mods_tac =
  qpat_assum `!ts sid nm vis mu nr raw ps ds ret ss base. _ ==> _` mp_tac >>
  qpat_assum `!ts sid key base. _ ==> build_func_return_type_src _ _ _ _ = _` mp_tac >>
  qpat_assum `!ts sid nm vis mu nr raw ps ds ret ss. include_fn_sig T vis /\ _ ==> _` mp_tac >>
  qpat_assum `!ms sid ts nm. _ ==> MEM (sid,nm) (contract_keys _ ms)` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> ntac 4 disch_tac >>
  Induct_on `ms` >- simp[] >>
  Cases_on `h` >>
  simp[contract_keys_def,build_func_return_type_mods_def,ALL_DISTINCT_APPEND] >>
  rpt strip_tac >> gvs[GSYM contract_keys_def] >>
  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  qpat_assum `!ts sid nm vis mu nr raw ps ds ret ss. include_fn_sig T vis /\ _ ==> _`
    (fn key_mem => drule_all_then assume_tac key_mem) >>
  (rename1 `build_func_return_type_src sid ts _ (nsid_to_string (sid,nm)) = ret` >>
   `~MEM #"." nm` by
     (qpat_assum `EVERY _ (FLAT (MAP (fn_sig_keys_toplevel T sid) ts))`
        (qspec_then `(sid,nm)` mp_tac o PURE_REWRITE_RULE [listTheory.EVERY_MEM]) >> simp[]) >>
   qpat_assum `!ts sid nm vis mu nr raw ps ds ret ss base. _ ==> _` irule >>
   simp[] >> metis_tac[]
   ORELSE
   (rename1 `build_func_return_type_src head_sid head_ts (build_func_return_type_mods ms)
               (nsid_to_string (sid,nm)) = ret` >>
    `MEM (sid,nm) (contract_keys (fn_sig_keys_toplevel T) ms)` by
      (qpat_assum `!ms sid ts nm. _ ==> MEM (sid,nm) (contract_keys _ ms)` irule >>
       qexists_tac `ts` >> simp[]) >>
    `~MEM #"." nm` by
      (qpat_assum `EVERY _ (contract_keys (fn_sig_keys_toplevel T) ms)`
         (qspec_then `(sid,nm)` mp_tac o PURE_REWRITE_RULE [listTheory.EVERY_MEM]) >> simp[]) >>
    `~MEM (sid,nm) (FLAT (MAP (fn_sig_keys_toplevel T head_sid) head_ts))` by
      (qpat_assum `!e. MEM e (FLAT _) ==> _` (qspec_then `(sid,nm)` mp_tac) >> simp[]) >>
    `build_func_return_type_src head_sid head_ts (build_func_return_type_mods ms)
         (nsid_to_string (sid,nm)) = build_func_return_type_mods ms (nsid_to_string (sid,nm))` by
      (qpat_assum `!ts sid key base. _ ==> build_func_return_type_src _ _ _ _ = _` irule >> simp[]) >>
    simp[] >>
    qpat_assum `!sid ts nm vis mu nr raw ps ds ret ss. _ ==> build_func_return_type_mods ms _ = _` irule >>
    simp[] >> metis_tac[]));

val linked_ctor_return_types_tac =
  `!fid sg. FLOOKUP env.fn_sigs fid = SOME sg ==>
      ctor_ce.ce_func_return_type (nsid_to_string fid) = sg.ret_ty` by
    (qpat_assum `contract_inv mods exps deploy_unit.cu_context ctor_ce cx`
       (SUBST1_TAC o MATCH_MP bodyInvExecutionPropsTheory.contract_inv_return_types) >>
     qpat_assum `!ms sid ts nm vis mu nr raw ps ds ret ss. _ ==> build_func_return_type_mods ms _ = _` mp_tac >>
     qpat_assum `EVERY _ (contract_keys (fn_sig_keys_toplevel T) mods)` mp_tac >>
     qpat_assum `ALL_DISTINCT (contract_keys (fn_sig_keys_toplevel T) mods)` mp_tac >>
     qpat_assum `!sid nm sg. FLOOKUP env.fn_sigs (sid,nm) = SOME sg ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> ntac 4 disch_tac >>
     qx_gen_tac `fid` >> PairCases_on `fid` >> rpt strip_tac >>
     qpat_x_assum `!sid nm sg. FLOOKUP env.fn_sigs (sid,nm) = SOME sg ==> _`
       (fn declared => drule_then strip_assume_tac declared) >>
     qpat_x_assum `!ms sid ts nm vis mu nr raw ps ds ret ss. _ ==> build_func_return_type_mods ms _ = _`
       irule >> simp[] >> metis_tac[alistTheory.ALOOKUP_MEM]);

(* The left accumulator stores the member function of the last hit. *)
val linked_ctor_flag_fold_tac =
  `!decls sid fmid fnm key members.
     (!name ms. MEM (FlagDecl name ms) decls /\
       nsid_to_string (sid,name) = key ==> ms = members) ==>
     FST (build_flag_info_src sid decls fmid fnm) key =
       if (?name ms. MEM (FlagDecl name ms) decls /\
           nsid_to_string (sid,name) = key)
       then build_flag_member_id_one members 0 else fmid key` by
    (POP_ASSUM_LIST (K ALL_TAC) >> Induct >> simp[build_flag_info_src_def] >>
     gen_tac >> Cases_on `h` >> simp[build_flag_info_src_def] >>
     rpt gen_tac >> strip_tac >>
     TRY (first_x_assum irule >> first_assum ACCEPT_TAC >> NO_TAC) >>
     qmatch_goalsub_abbrev_tac `build_flag_info_src sid decls next_id next_count` >>
     qpat_assum `!sid fmid fnm key members. _`
       (qspecl_then [`sid`,`next_id`,`next_count`,`key`,`members`] mp_tac) >>
     (impl_tac >- (rpt strip_tac >> first_x_assum irule >> qexists_tac `name` >> simp[])) >>
     disch_then SUBST1_TAC >>
     simp[Abbr `next_id`, LEFT_AND_OVER_OR, EXISTS_OR_THM, PULL_EXISTS] >>
     Cases_on `nsid_to_string (sid,s) = key` >> simp[] >> metis_tac[]) >>
  `!units fmid fnm key members.
     (!sid decls name ms. MEM (sid,decls) units /\ MEM (FlagDecl name ms) decls /\
       nsid_to_string (sid,name) = key ==> ms = members) ==>
     FST (build_flag_info_mods units fmid fnm) key =
       if (?sid decls name ms. MEM (sid,decls) units /\ MEM (FlagDecl name ms) decls /\
           nsid_to_string (sid,name) = key)
       then build_flag_member_id_one members 0 else fmid key` by
    (qpat_assum `!decls sid fmid fnm key members. _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> disch_tac >>
     Induct >> simp[build_flag_info_mods_def] >>
     gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
     `FST (build_flag_info_src h0 h1 fmid fnm) key =
        if (?name ms. MEM (FlagDecl name ms) h1 /\ nsid_to_string (h0,name) = key)
        then build_flag_member_id_one members 0 else fmid key` by
       (qpat_assum `!decls sid fmid fnm key members. _` irule >> metis_tac[MEM]) >>
     qabbrev_tac `info = build_flag_info_src h0 h1 fmid fnm` >> PairCases_on `info` >>
     simp[build_flag_info_mods_def, GSYM markerTheory.Abbrev_def] >>
     qpat_assum `!fmid fnm key members. _`
       (qspecl_then [`info0`,`info1`,`key`,`members`] mp_tac) >>
     (impl_tac >- (rpt strip_tac >>
       qpat_assum `!sid decls name ms. _` (qspecl_then [`sid`,`decls`,`name`,`ms`] mp_tac) >> simp[])) >>
     disch_then SUBST1_TAC >>
     `info0 key = if (?name ms. MEM (FlagDecl name ms) h1 /\
          nsid_to_string (h0,name) = key) then build_flag_member_id_one members 0 else fmid key` by
       (Cases_on `build_flag_info_src h0 h1 fmid fnm` >> fs[markerTheory.Abbrev_def]) >>
     simp[LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM, PULL_EXISTS] >>
     Cases_on `?name ms. MEM (FlagDecl name ms) h1 /\
                  nsid_to_string (h0,name) = key` >> simp[]);

val linked_ctor_flag_index_helpers_tac =
  `! (members:string list) mid j i. INDEX_OF mid members = SOME i ==>
      build_flag_member_id_one members j mid = j + i` by
    (POP_ASSUM_LIST (K ALL_TAC) >> Induct
     >- simp[INDEX_OF_def, INDEX_FIND_def] >>
     rpt gen_tac >> simp[build_flag_member_id_one_def, asmSpliceTheory.INDEX_OF_CONS] >>
     Cases_on `mid = h` >> simp[] >> Cases_on `INDEX_OF mid members` >> simp[] >>
     strip_tac >> first_x_assum drule >> simp[arithmeticTheory.ADD_CLAUSES]) >>
  `!decls fid members. lookup_flag fid decls = SOME members ==>
      MEM (FlagDecl fid members) decls` by
    (POP_ASSUM_LIST (K ALL_TAC) >> Induct >> simp[vyperStateTheory.lookup_flag_def] >>
     gen_tac >> Cases_on `h` >> rw[vyperStateTheory.lookup_flag_def] >> gvs[] >> metis_tac[]);

val linked_ctor_flags_tac =
  `ctor_ce.ce_flag_member_id = FST (build_flag_info_mods mods (K (K 0)) (K 0)) /\
   ctor_ce.ce_flag_n_members = SND (build_flag_info_mods mods (K (K 0)) (K 0))` by
    (qpat_assum `contract_inv _ _ _ ctor_ce cx`
      (mp_tac o PURE_REWRITE_RULE [contract_inv_def, cenv_module_pins_mods_def]) >> simp[]) >>
  `!nsid m. FLOOKUP (get_tenv cx) nsid = SOME (FlagArgs m) ==>
    ctor_ce.ce_flag_n_members (nsid_to_string nsid) = m` by
    (map_every qx_gen_tac [`flag_key`,`flag_count`] >> disch_tac >>
     qpat_assum `ctor_ce.ce_flag_n_members = _` SUBST1_TAC >>
     `FLOOKUP (type_env_all_modules mods) flag_key = SOME (FlagArgs flag_count)` by
       (qpat_assum `get_tenv cx = _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
     drule_all_then ACCEPT_TAC linkedFlagCountTheory.linked_flag_member_count);

val linked_ctor_flag_namespace_tac =
  `!sid decls name ms. MEM (sid,decls) mods /\ MEM (FlagDecl name ms) decls ==>
      ~MEM #"." name` by
    (map_every qx_gen_tac [`flag_sid`,`flag_decls`,`flag_name`,`flag_members`] >> strip_tac >>
     qpat_assum `contract_namespaces_ok T mods`
       (mp_tac o List.last o CONJUNCTS o PURE_REWRITE_RULE [contract_namespaces_ok_def]) >>
     simp[Once EVERY_MEM] >> disch_then (qspec_then `(flag_sid,flag_decls)` mp_tac) >>
     simp[Once EVERY_MEM] >> disch_then (qspec_then `FlagDecl flag_name flag_members` mp_tac) >> simp[]) >>
  (sg `!sid decls name ms. MEM (sid,decls) mods /\ MEM (FlagDecl name ms) decls ==>
      lookup_flag name decls = SOME ms /\ ALOOKUP mods sid = SOME decls` >-
    (qpat_assum `contract_namespaces_ok T mods` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac bool_ss [contract_namespaces_ok_def] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     map_every qx_gen_tac [`flag_sid`,`flag_decls`,`flag_name`,`flag_members`] >> strip_tac >>
     conj_tac
     >- (irule vyperTypeContractStaticMapsTheory.lookup_flag_MEM_FlagDecl >> simp[] >>
         qexists_tac `flag_sid` >>
         irule vyperTypeContractStaticMapsTheory.contract_keys_module_distinct >>
         qexists_tac `mods` >> simp[]) >>
     irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM >> simp[]));

val linked_ctor_flag_member_tac =
  sg `!src fid ts ls mid i. get_module_code cx src = SOME ts /\
     lookup_flag fid ts = SOME ls /\ INDEX_OF mid ls = SOME i ==>
     ctor_ce.ce_flag_member_id (nsid_to_string (src,fid)) mid = i` >-
    (qpat_assum `contract_inv _ _ _ ctor_ce cx`
       (mp_tac o MATCH_MP bodyInvCodePropsTheory.contract_inv_module_codes) >>
     qpat_assum `ctor_ce.ce_flag_member_id = _` mp_tac >>
     qpat_assum `!units fmid fnm key members. _ ==> FST (build_flag_info_mods _ _ _) _ = _` mp_tac >>
     qpat_assum `!members mid j i. INDEX_OF mid members = SOME i ==> _` mp_tac >>
     qpat_assum `!decls fid members. lookup_flag fid decls = SOME members ==> _` mp_tac >>
     qpat_assum `!sid decls name ms. _ ==> ~MEM #"." name` mp_tac >>
     qpat_assum `!sid decls name ms. _ ==> lookup_flag name decls = _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> ntac 3 disch_tac >>
     disch_then (mk_asm "flag_index") >> ntac 3 disch_tac >>
     map_every qx_gen_tac [`src`,`fid`,`ts`,`ls`,`mid`,`i`] >> strip_tac >>
     `ALOOKUP mods src = SOME ts` by
       (qpat_assum `!s. get_module_code cx s = ALOOKUP mods s`
          (qspec_then `src` (SUBST1_TAC o SYM)) >> first_assum ACCEPT_TAC) >>
     `MEM (src,ts) mods` by (irule alistTheory.ALOOKUP_MEM >> first_assum ACCEPT_TAC) >>
     `MEM (FlagDecl fid ls) ts` by
       (qpat_assum `!decls fid members. lookup_flag fid decls = SOME members ==> _`
         (drule_then ACCEPT_TAC)) >>
     `!sid decls name ms. MEM (sid,decls) mods /\ MEM (FlagDecl name ms) decls /\
         nsid_to_string (sid,name) = nsid_to_string (src,fid) ==> ms = ls` by
       (rpt gen_tac >> strip_tac >>
        `~MEM #"." fid /\ ~MEM #"." name` by
          (qpat_assum `!sid decls name ms. _ ==> ~MEM #"." name`
             (fn th => map_every (fn args => mp_tac (Q.SPECL args th))
                        [[`src`,`ts`,`fid`,`ls`],[`sid`,`decls`,`name`,`ms`]]) >> simp[]) >>
        `(sid,name) = (src,fid)` by
          (irule linkedNsidPropsTheory.nsid_to_string_dot_free_injective >> simp[]) >>
        `lookup_flag name decls = SOME ms /\ ALOOKUP mods sid = SOME decls` by
          (qpat_assum `!sid decls name ms. _ ==> lookup_flag name decls = _ /\ _`
             (qspecl_then [`sid`,`decls`,`name`,`ms`] mp_tac) >> simp[]) >>
        gvs[]) >>
     `FST (build_flag_info_mods mods (K (K 0)) (K 0))
        (nsid_to_string (src,fid)) = build_flag_member_id_one ls 0` by
       (qpat_assum `!units fmid fnm key members. _ ==> FST (build_flag_info_mods _ _ _) _ = _`
          (qspecl_then [`mods`,`K (K 0)`,`K 0`,`nsid_to_string (src,fid)`,`ls`] mp_tac) >>
        (impl_tac >- first_assum ACCEPT_TAC) >>
        Q.SUBGOAL_THEN
          `?sid decls name ms. MEM (sid,decls) mods /\ MEM (FlagDecl name ms) decls /\
             nsid_to_string (sid,name) = nsid_to_string (src,fid)`
          (fn hit => pure_rewrite_tac[hit, COND_CLAUSES])
        >- (qexistsl_tac [`src`,`ts`,`fid`,`ls`] >> simp[]) >>
        disch_then ACCEPT_TAC) >>
     qpat_assum `ctor_ce.ce_flag_member_id = _` SUBST1_TAC >>
     qpat_assum `FST (build_flag_info_mods _ _ _) _ = _` SUBST1_TAC >>
     asm "flag_index" (qspecl_then [`ls`,`mid`,`0`,`i`] mp_tac) >>
     simp[]);

(* Checked lookups identify a declaration; interpret the declaration only
   after passing through the restriction on allocated toplevel variables. *)
val linked_ctor_checked_storage_tables_tac =
  `(!src ts vis mut id ty slot. ALOOKUP mods src = SOME ts /\
       MEM (VariableDecl vis mut id ty slot) ts ==>
       ctor_ce.ce_hashmap_info (src,id) = NONE /\
       ctor_ce.ce_module_var_type (src,id) = SOME ty) ==>
   !src id ts tr typ id_str. get_module_code cx src = SOME ts /\
     find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) ==>
     ctor_ce.ce_hashmap_info (src,id) = NONE /\ ctor_ce.ce_module_var_type (src,id) = SOME typ` by
    (disch_then (mk_asm "variable_decl") >>
     map_every qx_gen_tac
       [`storage_src`,`storage_id`,`storage_tops`,`storage_tr`,`storage_ty`,`storage_id_str`] >>
     strip_tac >>
     `ALOOKUP mods storage_src = SOME storage_tops` by
       (qpat_assum `get_module_code cx storage_src = SOME storage_tops` mp_tac >>
        qpat_assum `ALOOKUP cx.sources cx.txn.target = SOME mods`
          (fn lookup => simp[NoAsms, vyperContextTheory.get_module_code_def, lookup])) >>
     drule_then strip_assume_tac bodyStorageMetadataTheory.find_var_decl_storage_mem >>
     asm "variable_decl" (drule_all_then ACCEPT_TAC));

val linked_ctor_checked_map_projections_tac =
  `contract_namespaces_ok F mods` by
    (irule vyperTypeContractStaticMapsTheory.contract_namespaces_ok_deploy_implies_runtime >>
     qpat_assum `check_contract T _ _ mods = SOME deploy_art`
       (ACCEPT_TAC o MATCH_MP check_contract_namespaces_ok)) >>
  `env.toplevel_vtypes = DRESTRICT (build_contract_type_artifact F mods).cta_toplevel_vtypes
       (var_allocated am.layouts tx.target mods) /\
   env.bare_globals = (build_contract_type_artifact F mods).cta_bare_globals` by
    (qpat_assum `check_contract T _ _ mods = SOME deploy_art`
       (mp_tac o MATCH_MP vyperTypeContractStaticMapsTheory.check_contract_nonsig_maps) >>
     simp[]);

val linked_ctor_checked_place_tables_tac =
  `(!src ts vis mut id ty slot. ALOOKUP mods src = SOME ts /\
       MEM (VariableDecl vis mut id ty slot) ts ==>
       ctor_ce.ce_hashmap_info (src,id) = NONE /\
       ctor_ce.ce_module_var_type (src,id) = SOME ty) /\
   (!src ts vis tr id kt vt slot. ALOOKUP mods src = SOME ts /\
       MEM (HashMapDecl vis tr id kt vt slot) ts ==>
       ctor_ce.ce_hashmap_info (src,id) = SOME (tr,kt,vt)) ==>
   place_map_tables_agree_on_defined ctor_ce env` by
    (disch_then (CONJUNCTS_THEN2 (mk_asm "variable_decl") (mk_asm "hashmap_decl")) >>
     pure_rewrite_tac [placeTypingPropsTheory.place_map_tables_agree_on_defined_def] >>
     map_every qx_gen_tac [`map_key`,`map_vt`] >> PairCases_on `map_key` >> strip_tac >>
     `FLOOKUP (build_contract_type_artifact F mods).cta_toplevel_vtypes
        (map_key0,map_key1) = SOME map_vt` by
       (qpat_assum `FLOOKUP env.toplevel_vtypes _ = SOME map_vt` mp_tac >>
        qpat_assum `env.toplevel_vtypes = DRESTRICT _ _`
          (fn tables => simp[NoAsms, tables,
             vyperTypeContractStaticMapsTheory.FLOOKUP_DRESTRICT_SOME])) >>
     qpat_assum `FLOOKUP (build_contract_type_artifact F mods).cta_toplevel_vtypes _ = SOME map_vt` mp_tac >>
     qpat_assum `contract_namespaces_ok F mods` mp_tac >>
     asm "variable_decl" mp_tac >> asm "hashmap_decl" mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     disch_then (mk_asm "hashmap_decl") >> disch_then (mk_asm "variable_decl") >>
     ntac 2 disch_tac >>
     drule_all_then strip_assume_tac
       vyperTypeContractStaticMapsTheory.build_contract_type_artifact_toplevel_vtypes_sound >>
     gvs[] >-
       (asm "variable_decl" (drule_all_then strip_assume_tac) >> simp[]) >>
     asm "hashmap_decl" (drule_all_then assume_tac) >> simp[]);

val linked_ctor_checked_bare_hash_tac =
  `(!src ts vis mut id ty slot. ALOOKUP mods src = SOME ts /\
      MEM (VariableDecl vis mut id ty slot) ts ==>
      ctor_ce.ce_hashmap_info (src,id) = NONE /\
      ctor_ce.ce_module_var_type (src,id) = SOME ty) ==>
   !nsid ty. FLOOKUP env.bare_globals nsid = SOME ty ==> ctor_ce.ce_hashmap_info nsid = NONE` by
    (disch_then (mk_asm "variable_decl") >>
     map_every qx_gen_tac [`bare_key`,`bare_ty`] >> PairCases_on `bare_key` >> strip_tac >>
     `FLOOKUP (build_contract_type_artifact F mods).cta_bare_globals
        (bare_key0,bare_key1) = SOME bare_ty` by
       (qpat_assum `FLOOKUP env.bare_globals _ = SOME bare_ty` mp_tac >>
        qpat_assum `env.bare_globals = (build_contract_type_artifact F mods).cta_bare_globals`
          (fn tables => simp[NoAsms, tables])) >>
     qpat_assum `FLOOKUP (build_contract_type_artifact F mods).cta_bare_globals _ = SOME bare_ty` mp_tac >>
     qpat_assum `contract_namespaces_ok F mods` mp_tac >> asm "variable_decl" mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> disch_then (mk_asm "variable_decl") >> ntac 2 disch_tac >>
     drule_all_then strip_assume_tac
       vyperTypeContractStaticMapsTheory.build_contract_type_artifact_bare_globals_sound >>
     gvs[] >> asm "variable_decl" (drule_all_then strip_assume_tac) >> simp[]);

(* Assemble the layout at entry without assuming any expression invariant. *)
val linked_ctor_bare_globals_layout_tac =
  Q.SUBGOAL_THEN `(!src id off n. immutable_region_mods mods src id off n ==>
      ?ty. FLOOKUP env.bare_globals (src,id) = SOME ty /\
        (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==> n = type_memory_size tv)) ==>
   bare_globals_layout ctor_ce.ce_is_ctor ctor_ce.ce_module_var_type
     ctor_ce.ce_module_vars ctor_ce.ce_modules cx env.bare_globals env.bare_global_assignable` assume_tac;

val linked_ctor_bare_globals_layout_setup_tac =
  qpat_assum `contract_inv mods exps deploy_unit.cu_context ctor_ce cx` mp_tac >>
  qpat_assum `module_body_inv mods NONE tops' ctor_ce cx` mp_tac >>
  qpat_assum `env_consistent env cx es0` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> ntac 4 disch_tac >>
  qpat_assum `contract_inv _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o
     PURE_REWRITE_RULE [immutable_section_layout_mods_def] o
     MATCH_MP contract_inv_immutable_section_layout);

val linked_ctor_bare_globals_regions_tac =
  `!src id off. FLOOKUP ctor_ce.ce_module_vars (src,id) = SOME (ImmutableLoc off) ==>
    ?n ty. immutable_region_mods mods src id off n /\
           FLOOKUP env.bare_globals (src,id) = SOME ty /\
           (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==> n = type_memory_size tv)` by
    (rpt gen_tac >> disch_tac >>
     `?n. immutable_region_mods mods src id off n` by
       (qpat_assum `!src id off. (FLOOKUP ctor_ce.ce_module_vars (src,id) = SOME (ImmutableLoc off)) <=> _`
         (qspecl_then [`src`,`id`,`off`] (drule_then ACCEPT_TAC o fst o EQ_IMP_RULE))) >>
     rename1 `immutable_region_mods mods src id off n` >>
     qpat_assum `!src id off n. immutable_region_mods mods src id off n ==> _`
       (drule_then (qx_choose_then `ty` (map_every assume_tac o CONJUNCTS))) >>
     qexistsl_tac [`n`,`ty`] >> rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC);

val linked_ctor_bare_globals_layout_head_tac =
  pure_rewrite_tac[bare_globals_layout_def] >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!src id off. FLOOKUP ctor_ce.ce_module_vars (src,id) = SOME (ImmutableLoc off) ==> _`
        (drule_then (qx_choosel_then [`n`,`ty`] strip_assume_tac)) >>
      qexists_tac `ty` >> FIRST_ASSUM ACCEPT_TAC) >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      drule_then ACCEPT_TAC bodyInvMetadataPropsTheory.contract_inv_constructor) >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      drule_all_then ACCEPT_TAC bodySimEntryTheory.body_inv_bare_global_type_mods);

val linked_ctor_bare_globals_disjoint_tac =
  qpat_assum `!src id off. FLOOKUP ctor_ce.ce_module_vars (src,id) = SOME (ImmutableLoc off) ==> _` mp_tac >>
  qpat_assum `!src id off size src' id' off' size'. _ ==> regions_disjoint _ _ _ _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> ntac 2 disch_tac >>
  `!src id ty off tv. FLOOKUP env.bare_globals (src,id) = SOME ty /\
     FLOOKUP ctor_ce.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
     evaluate_type (get_tenv cx) ty = SOME tv ==>
     immutable_region_mods mods src id off (type_memory_size tv)` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `!src id off. FLOOKUP ctor_ce.ce_module_vars (src,id) = SOME (ImmutableLoc off) ==> _`
       (drule_then (qx_choosel_then [`n`,`ty'`] (map_every assume_tac o CONJUNCTS))) >>
     `ty' = ty` by fs[] >> pop_assum SUBST_ALL_TAC >>
     `n = type_memory_size tv` by
       (qpat_assum `!tv. evaluate_type _ _ = SOME tv ==> _`
          (qspec_then `tv` (drule_then ACCEPT_TAC))) >>
     pop_assum (SUBST1_TAC o SYM) >> FIRST_ASSUM ACCEPT_TAC) >>
  qpat_x_assum `!src id off. FLOOKUP ctor_ce.ce_module_vars (src,id) = SOME (ImmutableLoc off) ==> _` kall_tac >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `immutable_region_mods mods src id1 off1 (type_memory_size tv1)` by
    (qpat_assum `!src id ty off tv. _ ==> immutable_region_mods _ _ _ _ _`
       (qspecl_then [`src`,`id1`,`ty1`,`off1`,`tv1`] mp_tac) >> simp[]) >>
  `immutable_region_mods mods src id2 off2 (type_memory_size tv2)` by
    (qpat_assum `!src id ty off tv. _ ==> immutable_region_mods _ _ _ _ _`
       (qspecl_then [`src`,`id2`,`ty2`,`off2`,`tv2`] mp_tac) >> simp[]) >>
  `(src,id1) <> (src,id2)` by simp[];

val linked_ctor_bare_globals_disjoint_finish_tac =
  qpat_x_assum `!src id off size src' id' off' size'. _ ==> regions_disjoint _ _ _ _` irule >>
  metis_tac[];

val linked_ctor_bare_globals_modules_tac =
  drule_all_then ACCEPT_TAC bodySimModsPropsTheory.body_inv_modules_aligned_mods;

(* The raw entry budget gives the strict machine bound on the immutable section. *)
val linked_ctor_bare_endpoint_tac =
  SUBGOAL_THEN ``(!src id off n. immutable_region_mods mods src id off n ==>
       ?ty. FLOOKUP env.bare_globals (src,id) = SOME ty /\
         (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==> n = type_memory_size tv)) ==>
   !src id ty off tv. FLOOKUP env.bare_globals (src,id) = SOME ty /\
     FLOOKUP ctor_ce.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
     evaluate_type (get_tenv cx) ty = SOME tv ==>
     off + type_memory_size tv < dimword (:256)`` assume_tac;

val linked_ctor_bare_endpoint_proof_tac =
  qpat_assum `immutable_section_layout_mods mods ctor_ce` mp_tac >>
  qpat_assum `imm_len_mods mods < dimword (:256)` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> disch_tac >>
  pure_rewrite_tac[immutable_section_layout_mods_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >> disch_tac >>
  map_every qx_gen_tac [`loc_src`,`loc_id`,`loc_ty`,`loc_off`,`loc_tv`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  (SUBGOAL_THEN ``?n. immutable_region_mods mods loc_src loc_id loc_off n``
     (qx_choose_then `loc_n` assume_tac) >-
      (qpat_assum `!s i off. FLOOKUP _ (s,i) = SOME (ImmutableLoc off) <=> _`
         (fn layout => pure_rewrite_tac [GSYM layout]) >> FIRST_ASSUM ACCEPT_TAC)) >>
  `loc_off + loc_n <= imm_len_mods mods` by
    (qpat_assum `!s i off n. immutable_region_mods mods s i off n ==> off + n <= _`
       (drule_then ACCEPT_TAC)) >>
  `loc_n = type_memory_size loc_tv` by metis_tac[optionTheory.SOME_11] >>
  metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS];

(* The base map only assigns locations to storage, transient or hashmap keys. *)
val linked_ctor_bare_slot_source_tac =
  `!ts owner base src id loc.
     FLOOKUP (add_module_var_locations_src owner ts base) (src,id) = SOME loc ==>
     FLOOKUP base (src,id) = SOME loc \/
     (src = owner /\ find_var_decl_by_name id ts <> NONE)` by
    (POP_ASSUM_LIST (K ALL_TAC) >>
     Induct >> simp[add_module_var_locations_src_def] >>
     Cases >> simp[add_module_var_locations_src_def, vyperStateTheory.find_var_decl_by_name_def] >>
     rpt gen_tac >> rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
     strip_tac >> first_x_assum drule >>
     simp[finite_mapTheory.FLOOKUP_UPDATE] >> rpt strip_tac >> gvs[AllCaseEqs()]) >>
  `!ms base src id loc.
     ALL_DISTINCT (MAP FST ms) /\
     FLOOKUP (add_module_var_locations_mods ms base) (src,id) = SOME loc ==>
     FLOOKUP base (src,id) = SOME loc \/
     ?ts. ALOOKUP ms src = SOME ts /\ find_var_decl_by_name id ts <> NONE` by
    (qpat_assum `!ts owner base src id loc. FLOOKUP (add_module_var_locations_src _ _ _) _ = _ ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> disch_tac >>
     Induct >> simp[add_module_var_locations_mods_def] >>
     PairCases >> simp[add_module_var_locations_mods_def] >>
     rename1 `MEM owner (MAP FST rest)` >>
     rpt strip_tac >> first_x_assum (drule_all_then strip_assume_tac)
     >- (qpat_assum `!ts owner base src id loc. FLOOKUP (add_module_var_locations_src _ _ _) _ = _ ==> _`
           (drule_then strip_assume_tac) >> simp[]) >>
     Cases_on `owner = src` >> gvs[] >>
     `ALOOKUP rest owner = NONE` by simp[alistTheory.ALOOKUP_NONE] >> gvs[]);

(* Adding immutable regions cannot create a non-immutable location. *)
val linked_ctor_bare_slot_frame_tac =
  `!ts src base key loc. (!off. loc <> ImmutableLoc off) /\
     FLOOKUP (add_annotated_immutables_src src ts base) key = SOME loc ==>
     FLOOKUP base key = SOME loc` by
    (POP_ASSUM_LIST (K ALL_TAC) >>
     Induct >> simp[add_annotated_immutables_src_def] >>
     Cases >> simp[add_annotated_immutables_src_def] >>
     rpt gen_tac >> rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
     strip_tac >> first_x_assum drule_all >>
     simp[finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()] >> metis_tac[]) >>
  `!ms base key loc. (!off. loc <> ImmutableLoc off) /\
     FLOOKUP (add_annotated_immutables_mods ms base) key = SOME loc ==>
     FLOOKUP base key = SOME loc` by
    (qpat_assum `!ts src base key loc. _ /\ FLOOKUP (add_annotated_immutables_src _ _ _) _ = _ ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> disch_tac >>
     Induct >> simp[add_annotated_immutables_mods_def] >>
     PairCases >> simp[add_annotated_immutables_mods_def] >>
     rpt strip_tac >> first_x_assum (drule_all_then assume_tac) >>
     qpat_assum `!ts src base key loc. _ /\ FLOOKUP (add_annotated_immutables_src _ _ _) _ = _ ==> _`
       (drule_all_then ACCEPT_TAC)) >>
  `!ms sft base key loc. FLOOKUP (add_immutable_locations_unit sft ms base) key = SOME loc /\
     (!off. loc <> ImmutableLoc off) ==> FLOOKUP base key = SOME loc` by
    (qpat_assum `!ms base key loc. _ /\ FLOOKUP (add_annotated_immutables_mods _ _) _ = _ ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> disch_tac >>
     rpt gen_tac >> Cases_on `ms`
     >- simp[add_immutable_locations_unit_def, add_annotated_immutables_mods_def] >>
     rename1 `FLOOKUP (add_immutable_locations_unit _ (entry::rest) _) _ = _` >>
     Cases_on `rest` >> PairCases_on `entry` >>
     rename1 `FLOOKUP (add_immutable_locations_unit _ ((owner,_)::_) _) _ = _` >>
     Cases_on `owner` >> simp[add_immutable_locations_unit_def] >>
     rpt strip_tac >> metis_tac[add_immutable_locations_FLOOKUP]);

val linked_ctor_bare_classify_tac =
  SUBGOAL_THEN ``!src id ty loc. FLOOKUP env.bare_globals (src,id) = SOME ty /\
      FLOOKUP ctor_ce.ce_module_vars (src,id) = SOME loc ==>
      ?off. loc = ImmutableLoc off`` assume_tac;

val linked_ctor_bare_classify_prefix_tac =
     qpat_assum `!ms sft base key loc. FLOOKUP (add_immutable_locations_unit _ _ _) _ = _ /\ _ ==> _` mp_tac >>
     qpat_assum `!ms base src id loc. ALL_DISTINCT _ /\ FLOOKUP (add_module_var_locations_mods _ _) _ = _ ==> _` mp_tac >>
     qpat_assum `contract_inv mods exps deploy_unit.cu_context ctor_ce cx` mp_tac >>
     qpat_assum `env.bare_globals = deploy_art.cta_bare_globals` mp_tac >>
     qpat_assum `check_contract T am.layouts tx.target mods = SOME deploy_art` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> ntac 2 disch_tac >>
     pure_rewrite_tac [contract_inv_def, cenv_module_pins_mods_def] >>
     disch_then (map_every assume_tac o CONJUNCTS) >> ntac 2 disch_tac >>
     map_every qx_gen_tac [`loc_src`,`loc_id`,`loc_ty`,`bare_loc`] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     CCONTR_TAC >>
     `!a. bare_loc <> ImmutableLoc a` by (rpt strip_tac >> metis_tac[]) >>
     `FLOOKUP (add_module_var_locations_mods mods FEMPTY) (loc_src,loc_id) = SOME bare_loc` by
       (qpat_assum `ctor_ce.ce_module_vars = _`
          (fn eq => qpat_assum `FLOOKUP ctor_ce.ce_module_vars _ = _`
             (assume_tac o REWRITE_RULE [eq])) >>
        qpat_assum `!ms sft base key loc. FLOOKUP (add_immutable_locations_unit _ _ _) _ = _ /\ _ ==> _`
          (drule_all_then ACCEPT_TAC)) >>
     qpat_assum `!ms base src id loc. ALL_DISTINCT _ /\ FLOOKUP (add_module_var_locations_mods _ _) _ = _ ==> _`
       (drule_all_then (mp_tac o SIMP_RULE (srw_ss()) [finite_mapTheory.FLOOKUP_EMPTY])) >>
     disch_then (qx_choose_then `slot_tops` strip_assume_tac);

val linked_ctor_bare_classify_checker_tac =
  `FLOOKUP deploy_art.cta_bare_globals (loc_src,loc_id) = SOME loc_ty` by
    (qpat_assum `env.bare_globals = deploy_art.cta_bare_globals`
       (PURE_REWRITE_TAC o single o SYM) >> FIRST_ASSUM ACCEPT_TAC) >>
  `find_var_decl_by_name loc_id slot_tops = NONE` by
    (qpat_assum `check_contract T am.layouts tx.target mods = SOME deploy_art` mp_tac >>
     qpat_assum `ALOOKUP cx.sources cx.txn.target = SOME mods` mp_tac >>
     qpat_assum `ALOOKUP mods loc_src = SOME slot_tops` mp_tac >>
     qpat_assum `FLOOKUP deploy_art.cta_bare_globals (loc_src,loc_id) = SOME loc_ty` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     metis_tac[optionTheory.SOME_11,
       SIMP_RULE (srw_ss()) [vyperContextTheory.get_module_code_def, initial_evaluation_context_def]
         vyperTypeContractStaticMapsTheory.check_contract_bare_globals_consistent_checked]) >>
  gvs[];

val linked_ctor_bare_placement_tac =
  `ctor_ce.ce_module = NONE` by
    (qpat_assum `module_body_inv mods NONE tops' ctor_ce cx`
       (ACCEPT_TAC o cj 2 o PURE_REWRITE_RULE [module_body_inv_def])) >>
  `(!src id off n. immutable_region_mods mods src id off n ==>
       ?ty. FLOOKUP env.bare_globals (src,id) = SOME ty /\
         (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==> n = type_memory_size tv)) ==>
   !src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty /\
     (~cx_const_name_mods mods (src,id) \/ IS_SOME (FLOOKUP env.bare_global_assignable (src,id))) ==>
     (src = env.current_src ==> src = ctor_ce.ce_module) /\
     (IS_SOME (FLOOKUP ctor_ce.ce_module_vars (src,id)) ==>
       ?off. FLOOKUP ctor_ce.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
          !tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
               off + type_memory_size tv < dimword (:256))` by
    (qpat_assum `!src id ty loc. FLOOKUP env.bare_globals _ = _ /\ FLOOKUP ctor_ce.ce_module_vars _ = _ ==> _` mp_tac >>
     qpat_assum `(!src id off n. immutable_region_mods mods src id off n ==> _) ==> !src id ty off tv. _` mp_tac >>
     qpat_assum `ctor_ce.ce_module = NONE` mp_tac >>
     qpat_assum `env.current_src = NONE` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> ntac 4 disch_tac >>
     disch_then (fn reg => first_x_assum (assume_tac o C MP reg)) >>
     map_every qx_gen_tac [`loc_src`,`loc_id`,`loc_ty`] >> strip_tac >>
     conj_tac >- simp[] >>
     Cases_on `FLOOKUP ctor_ce.ce_module_vars (loc_src,loc_id)` >> simp[] >>
     qpat_assum `!src id ty loc. FLOOKUP env.bare_globals _ = _ /\ FLOOKUP ctor_ce.ce_module_vars _ = _ ==> _`
       (drule_all_then (qx_choose_then `loc_off` strip_assume_tac)) >>
     qexists_tac `loc_off` >> gvs[] >>
     rpt strip_tac >> first_x_assum (drule_all_then ACCEPT_TAC)) >>
  qpat_x_assum `(!src id off n. immutable_region_mods mods src id off n ==> _) ==> !src id ty off tv. _` kall_tac >>
  qpat_x_assum `!src id ty loc. FLOOKUP env.bare_globals _ = _ /\ FLOOKUP ctor_ce.ce_module_vars _ = _ ==> _` kall_tac;

val linked_ctor_bare_slot_cleanup_tac =
  qpat_x_assum `!ts owner base src id loc. FLOOKUP (add_module_var_locations_src _ _ _) _ = _ ==> _` kall_tac >>
  qpat_x_assum `!ms base src id loc. ALL_DISTINCT _ /\ FLOOKUP (add_module_var_locations_mods _ _) _ = _ ==> _` kall_tac >>
  qpat_x_assum `!ts src base key loc. _ /\ FLOOKUP (add_annotated_immutables_src _ _ _) _ = _ ==> _` kall_tac >>
  qpat_x_assum `!ms base key loc. _ /\ FLOOKUP (add_annotated_immutables_mods _ _) _ = _ ==> _` kall_tac >>
  qpat_x_assum `!ms sft base key loc. FLOOKUP (add_immutable_locations_unit _ _ _) _ = _ /\ _ ==> _` kall_tac;

(* Each region records the declaration used by both the checker and
   the compiler's immutable layout. *)
val linked_ctor_immutable_region_type_tac =
  `contract_namespaces_ok F mods` by
    (qpat_assum `check_contract T am.layouts tx.target mods = SOME deploy_art`
       (irule o MATCH_MP vyperTypeContractStaticMapsTheory.check_contract_runtime_namespaces)) >>
  `env.bare_globals = (build_contract_type_artifact F mods).cta_bare_globals` by
    (qpat_assum `env.bare_globals = deploy_art.cta_bare_globals` SUBST1_TAC >>
     qpat_assum `check_contract T am.layouts tx.target mods = SOME deploy_art`
       (ACCEPT_TAC o CONJUNCT1 o MATCH_MP vyperTypeContractStaticMapsTheory.check_contract_nonsig_maps)) >>
  `ctor_ce.ce_struct_fields = make_struct_fields_map_mods mods` by
    (drule_then ACCEPT_TAC bodyInvCodePropsTheory.contract_inv_struct_fields) >>
  `get_tenv cx SUBMAP type_env_all_modules mods` by
    (qpat_assum `get_tenv cx = type_env_all_modules mods`
       (fn tenv => simp[NoAsms, tenv]));

val linked_ctor_immutable_region_type_goal_tac =
  sg `!src id off n. immutable_region_mods mods src id off n ==> ?ty.
        FLOOKUP env.bare_globals (src,id) = SOME ty /\
        (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==> n = type_memory_size tv)`;

val linked_ctor_immutable_region_open_tac =
  map_every qx_gen_tac [`region_src`,`region_id`,`region_off`,`region_n`] >>
  disch_then (strip_assume_tac o PURE_REWRITE_RULE [immutable_region_mods_def]) >>
  rename1 `ALOOKUP mods region_src = SOME region_tops` >>
  rename1 `region_tops = _ ++ VariableDecl region_vis Immutable region_id region_ty region_slot :: _` >>
  `MEM (VariableDecl region_vis Immutable region_id region_ty region_slot) region_tops` by
    (qpat_assum `region_tops = _` (fn tops => simp[NoAsms, tops])) >>
  qexists_tac `region_ty` >> conj_tac;

val linked_ctor_immutable_region_lookup_tac =
  qpat_assum `env.bare_globals = (build_contract_type_artifact F mods).cta_bare_globals`
    SUBST1_TAC >>
  drule_all_then ACCEPT_TAC
    (SIMP_RULE (srw_ss()) [] (Q.INST [`mut` |-> `Immutable`]
      vyperTypeContractStaticMapsTheory.build_contract_type_artifact_bare_globals_complete));

val linked_ctor_immutable_region_size_tac =
  `region_n = type_memory_bytes ctor_ce region_ty` by
    (qpat_assum `region_n = type_mem_bytes _ region_ty` SUBST1_TAC >>
     qpat_assum `ctor_ce.ce_struct_fields = make_struct_fields_map_mods mods`
       (fn fields => simp[NoAsms, GSYM fields, structFieldsPropsTheory.type_mem_bytes_type_memory_bytes])) >>
  qpat_assum `region_n = type_memory_bytes ctor_ce region_ty` SUBST1_TAC >>
  gen_tac >> disch_tac >>
  drule_all_then ACCEPT_TAC linkedStructMemorySizeTheory.make_struct_fields_map_mods_memory_size;

(* Discharge the table adapters with the linked builder's declaration hits. *)
val linked_ctor_expr_table_join_tac =
  `!src ts vis mut id ty slot. ALOOKUP mods src = SOME ts /\
     MEM (VariableDecl vis mut id ty slot) ts ==>
       ctor_ce.ce_hashmap_info (src,id) = NONE /\ ctor_ce.ce_module_var_type (src,id) = SOME ty` by
    (qpat_assum `!src ts id vis mut ty slot. _ ==> ctor_ce.ce_hashmap_info _ = NONE /\ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `!src ts vis tr id kt vt slot. ALOOKUP mods src = SOME ts /\
     MEM (HashMapDecl vis tr id kt vt slot) ts ==>
       ctor_ce.ce_hashmap_info (src,id) = SOME (tr,kt,vt)` by
    (qpat_assum `!src ts id vis tr kt vt slot. _ ==> ctor_ce.ce_hashmap_info _ = SOME _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `!src id ts tr typ id_str. get_module_code cx src = SOME ts /\
     find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) ==>
       ctor_ce.ce_hashmap_info (src,id) = NONE /\ ctor_ce.ce_module_var_type (src,id) = SOME typ` by
    (qpat_assum `_ ==> !src id ts tr typ id_str. _ ==> ctor_ce.ce_hashmap_info _ = NONE /\ _`
       (drule_then ACCEPT_TAC)) >>
  `place_map_tables_agree_on_defined ctor_ce env` by
    (qpat_assum `_ ==> place_map_tables_agree_on_defined ctor_ce env`
       (drule_all_then ACCEPT_TAC)) >>
  `!nsid ty. FLOOKUP env.bare_globals nsid = SOME ty ==> ctor_ce.ce_hashmap_info nsid = NONE` by
    (qpat_assum `_ ==> !nsid ty. FLOOKUP env.bare_globals nsid = SOME ty ==> _`
       (drule_then ACCEPT_TAC));

val linked_ctor_expr_layout_join_tac =
  `bare_globals_layout ctor_ce.ce_is_ctor ctor_ce.ce_module_var_type
     ctor_ce.ce_module_vars ctor_ce.ce_modules cx env.bare_globals env.bare_global_assignable` by
    (qpat_assum `_ ==> bare_globals_layout _ _ _ _ _ _ _`
       (drule_then ACCEPT_TAC)) >>
  `!src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty /\
     (~cx_const_name_mods mods (src,id) \/ IS_SOME (FLOOKUP env.bare_global_assignable (src,id))) ==>
     (src = env.current_src ==> src = ctor_ce.ce_module) /\
     (IS_SOME (FLOOKUP ctor_ce.ce_module_vars (src,id)) ==>
      ?off. FLOOKUP ctor_ce.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
        !tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
             off + type_memory_size tv < dimword (:256))` by
    (qpat_assum `(!src id off n. immutable_region_mods mods src id off n ==> _) ==>
         !src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty /\ _ ==> _`
       (drule_then ACCEPT_TAC));

fun linked_ctor_observed_expr_inv_tac frame =
  sg `!gs. expr_sim_inv_mods mods ctor_ce cx env
       (es0 with <|gas_obs := gs; outcomes := SOME (MAP SND (call_trace ^frame))|>)`;

fun linked_ctor_observed_expr_project_tac frame =
  qx_gen_tac `gs` >>
  qpat_assum `!gs. env_consistent env cx (es0 with <|gas_obs := gs;
      outcomes := SOME (MAP SND (call_trace ^frame))|>) /\ _`
    (qspec_then `gs` strip_assume_tac) >>
  simp[NoAsms, exprSimHypsDefsTheory.expr_sim_inv_mods_def];

val linked_ctor_observed_expr_finish_tac =
  rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE
    FIRST [(qpat_assum `es0.scopes = [scope]` SUBST1_TAC >>
            qpat_assum `popped_keys_indexed [scope]` ACCEPT_TAC),
           (qpat_assum `!src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty /\ _ ==> _` mp_tac >>
            POP_ASSUM_LIST (K ALL_TAC) >> simp[])]);

val linked_ctor_expr_roots_join_tac =
  `!key r. ALOOKUP (consts_env_mods mods) key = SOME r ==> accesses_expr r = []` by
    (qpat_assum `!key r. ALOOKUP (consts_env_mods mods) key = SOME r ==> constant_expr mods r /\ _`
       (ACCEPT_TAC o cj 2)) >>
  `~supported_stmts_expr_exists (const_name_root_mods ctor_ce.ce_modules) cpkg6` by
    (qpat_assum `_ ==> ~supported_stmts_expr_exists (const_name_root_mods ctor_ce.ce_modules) cpkg6`
       (drule_then ACCEPT_TAC)) >>
  `stmts_exprs_ok ctor_ce cpkg6` by
    (qpat_assum `_ ==> stmts_exprs_ok ctor_ce cpkg6` (drule_then ACCEPT_TAC)) >>
  qpat_assum `_ ==> ~supported_stmts_expr_exists (unallocated_bare_global_root ctor_ce env) cpkg6 /\ _`
    (drule_all_then (map_every assume_tac o CONJUNCTS));

(* Checker projections for the selected constructor and the linked call graph. *)
val linked_ctor_checker_calls_tac =
  `exports_ok cx.layouts cx.txn.target mods exps` by
    (qpat_assum `cx.layouts = am.layouts` SUBST1_TAC >>
     qpat_assum `cx.txn.target = tx.target` SUBST1_TAC >> FIRST_ASSUM ACCEPT_TAC) >>
  `MEM (NONE,tops') mods` by
    (irule alistTheory.ALOOKUP_MEM >> FIRST_ASSUM ACCEPT_TAC) >>
  `!sid ts vis mut nr raw name args dflts ret body.
       ALOOKUP mods sid = SOME ts /\
       MEM (FunctionDecl vis mut nr raw name args dflts ret body) ts ==>
       stmts_loop_calls_ok mods
         (subst_consts_stmts_mods (consts_env_mods mods) body)` by
    (map_every qx_gen_tac [`sid`,`ts`,`vv`,`mm`,`nn`,`rr`,`nm`,`aa`,`dd`,`rt`,`decl_stmts`] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     `MEM (sid,ts) mods` by (irule alistTheory.ALOOKUP_MEM >> FIRST_ASSUM ACCEPT_TAC) >>
     `stmts_loop_calls_ok mods decl_stmts` by
       (drule_all_then ACCEPT_TAC bodyLoopCallsTheory.checked_function_loop_calls_ok) >>
     drule_all_then ACCEPT_TAC linkedBodyLoopCallsTheory.checked_subst_consts_loop_calls_ok_mods) >>
  `stmts_loop_calls_ok mods cpkg6` by
    (qpat_assum `cpkg6 = _` SUBST1_TAC >>
     qpat_assum `!sid ts vis mut nr raw name args dflts ret decl_stmts. _ ==> _`
       (drule_all_then ACCEPT_TAC)) >>
  `MEM (NONE,"__init__") (linked_live_functions mods exps)` by
    (rewrite_tac[vyperTypeCallGraphSoundnessTheory.linked_live_functions_member] >> disj1_tac >>
     simp_tac bool_ss [linked_live_functions_from_def, LET_THM] >>
     irule (cj 1 vyperTypeCallGraphSoundnessTheory.call_closure_from_roots) >>
     qpat_assum `ALOOKUP mods NONE = SOME tops'` (fn lookup =>
       simp_tac bool_ss [linked_main_roots_def, lookup, optionTheory.option_case_def, listTheory.MEM_APPEND]) >>
     disj2_tac >>
     simp_tac bool_ss [listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
     qexists_tac `[(NONE,"__init__")]` >> conj_tac >-
       (qexists_tac `FunctionDecl Deploy mut F F "__init__" src_args [] NoneT raw_body` >> simp[]) >>
     simp[]) >>
  `EVERY (\k. MEM k (linked_live_functions mods exps)) (int_calls_stmts cpkg6)` by
    (qpat_assum `cpkg6 = _` SUBST1_TAC >>
     drule_all_then ACCEPT_TAC linkedLiveBodyEntryTheory.checked_live_body_subst_calls_mods) >>
  `int_calls_stmts cpkg6 = int_calls_stmts raw_body` by
    (qpat_assum `cpkg6 = _` SUBST1_TAC >>
     qpat_assum `check_contract T _ _ mods = SOME _`
       (fn checked => simp[NoAsms,
         MATCH_MP linkedBodyLoopCallsTheory.checked_subst_consts_int_calls_mods checked])) >>
  `call_evaluation_safe cx (int_calls_stmts cpkg6)` by
    (qpat_assum `int_calls_stmts cpkg6 = _` SUBST1_TAC >>
     irule vyperTypeDeploymentSoundnessTheory.checked_constructor_call_evaluation_safe >>
     qexistsl_tac [`src_args`,`deploy_art`,`[]`,`am.layouts`,`mods`,`mut`,
                  `F`,`NoneT`,`(tx.target,mods)::am.sources`,`tops'`,`tx with created_in_tx := T`] >>
     simp[Abbr `cx`, deploy_evaluation_context_mods_def]);

(* Use the checked deploy signatures to type the actual substituted body. *)
val linked_ctor_rewritten_checked_args_tac =
     `check_function_body am.layouts tx.target mods deploy_art NONE Deploy mut F
        src_args [] NoneT raw_body` by
       drule_all_then ACCEPT_TAC
         vyperTypeContractContextTheory.check_contract_deploy_function_body_MEM >>
     drule_all (SIMP_RULE (srw_ss()) []
       (Q.INST [`mode` |-> `T`, `name` |-> `"__init__"`,
                `vis` |-> `Deploy`, `src` |-> `NONE`]
          whitelistLinkedBodyCallsTheory.linked_checked_body_calls)) >>
     disch_then (qx_choose_then `fs` strip_assume_tac) >>
     qabbrev_tac `checked_env =
       (function_entry_env deploy_art mods NONE Deploy src_args) with fn_sigs := fs` >>
     `checked_env.type_defs = type_env_all_modules mods /\
      checked_env.bare_globals = deploy_art.cta_bare_globals /\
      checked_env.bare_global_assignable = deploy_art.cta_bare_global_assignable /\
      checked_env.toplevel_vtypes = deploy_art.cta_toplevel_vtypes /\
      checked_env.event_fields = deploy_art.cta_event_fields` by
       simp[NoAsms, Abbr `checked_env`, function_entry_env_def, artifact_env_def,
            vyperTypeContractContextTheory.FOLDL_extend_local_args_static] >>
     `FDOM checked_env.var_types = set (MAP FST src_args)` by
       simp[NoAsms, Abbr `checked_env`, whitelistCheckerDeclsTheory.function_entry_env_var_types_fdom] >>
     `params_ok (type_env_all_modules mods) src_args` by
       (qpat_assum `check_function_body _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
        simp[NoAsms, check_function_body_def]) >>
     qpat_assum `params_ok _ _` (strip_assume_tac o REWRITE_RULE [params_ok_def]) >>
     `!x ty. FLOOKUP checked_env.var_types x = SOME ty ==>
          assignable_type (type_env_all_modules mods) ty` by
       (map_every qx_gen_tac [`formal_id`,`formal_ty`] >>
        simp[NoAsms, Abbr `checked_env`, function_entry_env_def] >> strip_tac >>
        drule_all (Q.INST [`asg` |-> `F`]
          vyperTypeContractContextTheory.FOLDL_extend_local_args_var_types_range) >>
        simp[NoAsms, artifact_env_def] >>
        disch_then strip_assume_tac >>
        qpat_assum `EVERY _ src_args` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
        disch_then (qspec_then `(formal_id,formal_ty)` mp_tac) >> simp[]);

val linked_ctor_rewritten_checked_env_tac =
     `whitelistLinkedBodyEnv$linked_body_type_facts tops' (NONE:num option)
        (type_env_all_modules mods)` by
       drule_all_then ACCEPT_TAC (Q.INST [`mode` |-> `T`, `src` |-> `NONE`]
         whitelistLinkedBodyTypesTheory.linked_checked_body_type_facts) >>
     `layouts_agree tops' am tx` by
       (qpat_assum `layouts_agree_mods mods exps am tx` mp_tac >>
        simp[NoAsms, layouts_agree_mods_def, layouts_agree_def] >>
        pairarg_tac >> simp[] >> strip_tac >>
        first_x_assum (qspecl_then [`NONE`,`tops'`] mp_tac) >> simp[]) >>
     `whitelistLinkedBodyEnv$linked_body_data_env tops' (NONE:num option) checked_env` by
       (irule (Q.INST [`mode` |-> `T`] whitelistLinkedBodyDataTheory.linked_checked_data_env) >>
        qexistsl_tac [`am`,`deploy_art`,`mods`,`tx`] >> simp[] >>
        qpat_assum `whitelistLinkedBodyEnv$linked_body_type_facts _ _ _` mp_tac >>
        simp[NoAsms, whitelistLinkedBodyEnvTheory.linked_body_type_facts_def]) >>
     `!k ty. FLOOKUP checked_env.bare_global_assignable k = SOME ty ==>
             FLOOKUP checked_env.bare_globals k = SOME ty` by
       (qx_gen_tac `key` >> PairCases_on `key` >> qx_gen_tac `place_ty` >>
        `!sid id ty. FLOOKUP deploy_art.cta_bare_global_assignable (sid,id) = SOME ty ==>
                     FLOOKUP deploy_art.cta_bare_globals (sid,id) = SOME ty` by
          (drule (Q.INST [`sources` |-> `[(addr,mods)]`,
                          `tx` |-> `empty_call_txn with target := addr`]
             vyperTypeContractStaticMapsTheory.check_contract_bare_global_assignable_consistent_deploy) >>
           simp[NoAsms] >> strip_tac >> rpt gen_tac >> strip_tac >>
           first_x_assum (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
        simp[]) >>
     `whitelistLinkedBodyEnv$linked_body_env tops' (NONE:num option)
        (type_env_all_modules mods) checked_env` by
       (rewrite_tac[whitelistLinkedBodyEnvTheory.linked_body_env_def] >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
     `!name. ~MEM (StructDecl name []) tops'` by
       (qx_gen_tac `empty_struct` >> strip_tac >>
        drule_all (Q.INST [`mode` |-> `T`, `src` |-> `NONE`,
          `tl` |-> `StructDecl empty_struct []`]
            vyperTypeContractStaticMapsTheory.check_contract_toplevel_decl_MEM_checked) >>
        simp[NoAsms, check_toplevel_decl_def]) >>
     `?checked_out. type_stmts checked_env NoneT cpkg6 = SOME checked_out` by
       (qpat_assum `cpkg6 = _` (fn ss =>
         simp[NoAsms, Abbr `checked_env`, ss, GSYM optionTheory.IS_SOME_EXISTS]) >>
        first_assum ACCEPT_TAC);

val linked_ctor_rewritten_supported_stmts_tac =
  `subst_consts_stmts_mods (consts_env_mods mods) cpkg6 = cpkg6 /\
   custom_errors_stmts_ok mods cpkg6 ==> ?bindings. supported_stmts tops' bindings cpkg6` by
    (linked_ctor_rewritten_checked_args_tac >>
     linked_ctor_rewritten_checked_env_tac >>
     qpat_x_assum `cpkg6 = subst_consts_stmts_mods _ raw_body` kall_tac >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     `supported_function_body tops' Deploy src_args cpkg6` by
       (irule (Q.INST [`src` |-> `NONE:num option`, `ret` |-> `NoneT`]
          (INST_TYPE [``:'a`` |-> ``:num``]
             whitelistLinkedBodyStmtsTheory.linked_typed_body_supported)) >>
        simp[] >> qexistsl_tac [`checked_env`,`mods`,`checked_out`,`type_env_all_modules mods`] >>
        simp[] >>
        qpat_assum `!name. ~MEM (StructDecl name []) tops'`
          (mp_tac o MATCH_MP (SIMP_RULE (srw_ss()) []
            (Q.INST [`src` |-> `NONE:num option`, `tenv` |-> `type_env_all_modules mods`]
              (INST_TYPE [``:'a`` |-> ``:num``]
                whitelistLinkedBodyExprsTheory.linked_well_typed_expr_supported)))) >>
        disch_then (map_every assume_tac o CONJUNCTS) >>
        rpt conj_tac
        >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
            qpat_assum `!env e. well_typed_expr _ _ ==> _`
              (drule_then (drule_then (ACCEPT_TAC o cj 1))))
        >- (rpt gen_tac >>
            rewrite_tac[constSubstModsTheory.subst_consts_stmt_mods_def,
                        constSubstModsTheory.subst_consts_iter_mods_def] >>
            disch_then (map_every assume_tac o CONJUNCTS) >>
            drule_all (SIMP_RULE (srw_ss()) [] (Q.INST [`mode` |-> `T`, `src` |-> `NONE`]
              whitelistLinkedBodyRangeTheory.linked_checked_range_literals)) >> simp[]) >>
        map_every qx_gen_tac [`leaf_env`,`leaf_ret`,`leaf_stmt`,`leaf_out`] >>
        disch_then (map_every assume_tac o CONJUNCTS) >>
        irule (Q.INST [`src` |-> `NONE:num option`]
          (INST_TYPE [``:'a`` |-> ``:num``]
             whitelistLinkedBodyStmtFormsTheory.linked_stmt_leaf_supported)) >>
        simp[] >> conj_tac >- (qexists_tac `mods` >> simp[]) >>
        qexistsl_tac [`leaf_env`,`leaf_out`,`leaf_ret`,`type_env_all_modules mods`] >>
        simp[] >> rpt conj_tac
        >- (map_every qx_gen_tac [`leaf_bt`,`leaf_vt`] >> strip_tac >>
            qpat_assum `!en tgt. IS_SOME (type_place_target en tgt) ==> _`
              (qspecl_then [`leaf_env`,`leaf_bt`] mp_tac) >> simp[])
        >- (qx_gen_tac `leaf_expr` >> strip_tac >>
            qpat_assum `!en e. well_typed_expr en e ==> _`
              (qspecl_then [`leaf_env`,`leaf_expr`] mp_tac) >> simp[])
        >- (qx_gen_tac `leaf_exprs` >> strip_tac >>
            qpat_assum `!en es. well_typed_exprs en es ==> _`
              (qspecl_then [`leaf_env`,`leaf_exprs`] mp_tac) >> simp[]) >>
        qpat_assum `whitelistLinkedBodyEnv$linked_body_env tops' _ _ leaf_env`
          (ACCEPT_TAC o cj 6 o REWRITE_RULE [whitelistLinkedBodyEnvTheory.linked_body_env_def])) >>
     qpat_assum `supportedProgram$supported_function_body tops' Deploy src_args cpkg6`
       (strip_assume_tac o SIMP_RULE bool_ss [supportedProgramTheory.supported_function_body_def, LET_THM]) >>
     qpat_assum `supported_stmts tops' _ cpkg6` (irule_at Any));

(* Distinct checker type keys give struct-field uniqueness in every module. *)
val linked_ctor_struct_args_tac =
  `!sid:num option. !name args ts. MEM (StructDecl name args) ts ==>
     MEM (sid,name) (FLAT (MAP (type_def_keys_toplevel sid) ts))` by
    (rpt strip_tac >> pure_rewrite_tac[listTheory.MEM_FLAT] >>
     qexists_tac `type_def_keys_toplevel sid (StructDecl name args)` >>
     conj_tac >-
       (pure_rewrite_tac[listTheory.MEM_MAP] >>
        qexists_tac `StructDecl name args` >> simp[]) >>
     simp[type_def_keys_toplevel_def]) >>
  `!sid:num option. !ts. ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel sid) ts)) ==>
     struct_args_unique ts` by
    (qpat_assum `!sid name args ts. MEM (StructDecl name args) ts ==> _`
       (fn member => POP_ASSUM_LIST (K ALL_TAC) >>
         qx_gen_tac `sid` >> Induct_on `ts` >-
           simp[typedCopyMetadataTheory.struct_args_unique_def] >>
         Cases_on `h` >> simp[type_def_keys_toplevel_def] >> rpt strip_tac >>
         fs[typedCopyMetadataTheory.struct_args_unique_def] >> rpt strip_tac >>
         gvs[] >> metis_tac[member])) >>
  `ALL_DISTINCT (contract_keys type_def_keys_toplevel mods)` by
    (qpat_assum `check_contract T _ _ mods = SOME _`
       (mp_tac o MATCH_MP check_contract_namespaces_ok) >>
     simp_tac bool_ss [contract_namespaces_ok_def]) >>
  `!sid ts. MEM (sid,ts) mods ==> struct_args_unique ts` by
    (map_every qx_gen_tac [`sid`, `ts`] >> strip_tac >>
     qpat_assum `!sid:num option. !ts. ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel sid) ts)) ==> _`
       irule >>
     qexists_tac `sid` >>
     drule_all_then ACCEPT_TAC vyperTypeContractStaticMapsTheory.contract_keys_module_distinct) >>
  `EVERY (struct_args_unique o SND) mods` by
    (pure_rewrite_tac[listTheory.EVERY_MEM] >> qx_gen_tac `m` >>
     PairCases_on `m` >> simp_tac bool_ss [combinTheory.o_THM, pairTheory.SND] >>
     strip_tac >>
     qpat_assum `!sid ts. MEM (sid,ts) mods ==> struct_args_unique ts`
       (drule_then ACCEPT_TAC));

(* Constant replacements cannot introduce ABI decode, even across modules. *)
val linked_ctor_decode_expr_reflect_tac =
  `EVERY (constant_expr mods o SND) (consts_env_mods mods)` by
    (qpat_assum `check_contract T _ _ mods = SOME _`
       (ACCEPT_TAC o MATCH_MP whitelistLinkedBodyCallSitesTheory.checked_const_mods_constant)) >>
  `!key replacement target. ALOOKUP (consts_env_mods mods) key = SOME replacement ==>
     ~supported_expr_exists (expr_abi_decode_target_root target) replacement` by
    (map_every qx_gen_tac [`decode_key`,`decode_replacement`,`decode_ty`] >> disch_tac >>
     `MEM (decode_key,decode_replacement) (consts_env_mods mods)` by
       (irule alistTheory.ALOOKUP_MEM >> FIRST_ASSUM ACCEPT_TAC) >>
     `constant_expr mods decode_replacement` by
       (qpat_assum `EVERY (constant_expr mods o SND) _`
          (qspec_then `(decode_key,decode_replacement)` mp_tac o REWRITE_RULE [listTheory.EVERY_MEM]) >>
        simp[combinTheory.o_THM]) >>
     irule (cj 1 constSubstStmtsPreserveTheory.constant_expr_no_abi_decode) >>
     qexists_tac `mods` >> FIRST_ASSUM ACCEPT_TAC) >>
  `!target.
     (!env e. (!key r. ALOOKUP env key = SOME r ==>
                 ~supported_expr_exists (expr_abi_decode_target_root target) r) ==>
          supported_expr_exists (expr_abi_decode_target_root target)
            (subst_consts_expr_mods env e) ==>
          supported_expr_exists (expr_abi_decode_target_root target) e) /\
     (!env t. (!key r. ALOOKUP env key = SOME r ==>
                 ~supported_expr_exists (expr_abi_decode_target_root target) r) ==>
          supported_target_exists (expr_abi_decode_target_root target)
            (subst_consts_btarget_mods env t) ==>
          supported_target_exists (expr_abi_decode_target_root target) t) /\
     (!env es. (!key r. ALOOKUP env key = SOME r ==>
                  ~supported_expr_exists (expr_abi_decode_target_root target) r) ==>
          supported_exprs_exists (expr_abi_decode_target_root target)
            (subst_consts_exprs_mods env es) ==>
          supported_exprs_exists (expr_abi_decode_target_root target) es) /\
     (!env opt. (!key r. ALOOKUP env key = SOME r ==>
                   ~supported_expr_exists (expr_abi_decode_target_root target) r) ==>
          supported_opt_exists (expr_abi_decode_target_root target)
            (subst_consts_opt_mods env opt) ==>
          supported_opt_exists (expr_abi_decode_target_root target) opt) /\
     (!env fs. (!key r. ALOOKUP env key = SOME r ==>
                  ~supported_expr_exists (expr_abi_decode_target_root target) r) ==>
          supported_fields_exists (expr_abi_decode_target_root target)
            (subst_consts_fields_mods env fs) ==>
          supported_fields_exists (expr_abi_decode_target_root target) fs)` by
    (POP_ASSUM_LIST (K ALL_TAC) >> qx_gen_tac `decode_ty` >>
     ho_match_mp_tac constSubstModsTheory.subst_consts_expr_mods_ind >>
     simp[constSubstModsTheory.subst_consts_expr_mods_def,
          supportedExprTraverseTheory.supported_expr_exists_def,
          supportedProgramTheory.expr_abi_decode_target_root_def] >>
     rpt strip_tac >> gvs[]
     >~ [`F`]
     >- (qmatch_asmsub_rename_tac `ALOOKUP decode_env (decode_ns,decode_id)` >>
         Cases_on `ALOOKUP decode_env (decode_ns,decode_id)` >>
         gvs[supportedExprTraverseTheory.supported_expr_exists_def,
             supportedProgramTheory.expr_abi_decode_target_root_def] >> metis_tac[])
     >> TRY (qmatch_goalsub_rename_tac `expr_abi_decode_target_root _
               (TypeBuiltin _ decode_builtin _ _)` >>
             Cases_on `decode_builtin` >>
             gvs[supportedProgramTheory.expr_abi_decode_target_root_def] >>
             metis_tac[] >> NO_TAC)
     >> metis_tac[]);

(* Lift qualified decode-root reflection from expressions to a whole body. *)
val linked_ctor_decode_target_reflection_tac =
  `(!E' t. E' = E ==>
      supported_assignment_exists p (subst_consts_target_mods E' t) ==>
      supported_assignment_exists p t) /\
   (!E' ts. E' = E ==>
      supported_assignments_exists p (subst_consts_targets_mods E' ts) ==>
      supported_assignments_exists p ts)` by
    (ho_match_mp_tac constSubstModsTheory.subst_consts_target_mods_ind >>
     simp[constSubstModsTheory.subst_consts_target_mods_def,
          supportedStmtTraverseTheory.supported_assignment_exists_def] >>
     metis_tac[]);

val linked_ctor_decode_reason_reflection_tac =
  `!es fs. EXISTS (supported_expr_exists p) (es ++ MAP SND fs) <=>
      supported_exprs_exists p es \/ supported_fields_exists p fs` by
    simp[listTheory.EXISTS_APPEND, listTheory.EXISTS_MAP, combinTheory.o_DEF,
         supportedExprTraverseTheory.supported_exprs_exists_every,
         supportedExprTraverseTheory.supported_fields_exists_every] >>
  `!err. EXISTS (supported_expr_exists p)
          (custom_error_exprs (subst_consts_error_mods E err)) ==>
        EXISTS (supported_expr_exists p) (custom_error_exprs err)` by
    (Cases >> simp[constSubstModsTheory.subst_consts_error_mods_def,
                   vyperASTTheory.custom_error_exprs_def] >> metis_tac[]) >>
  `!r. supported_assert_exists p (subst_consts_areason_mods E r) ==>
       supported_assert_exists p r` by
    (Cases >> simp[constSubstModsTheory.subst_consts_areason_mods_def,
                   supportedStmtTraverseTheory.supported_assert_exists_def]) >>
  `!r. supported_raise_exists p (subst_consts_rreason_mods E r) ==>
       supported_raise_exists p r` by
    (Cases >> simp[constSubstModsTheory.subst_consts_rreason_mods_def,
                   supportedStmtTraverseTheory.supported_raise_exists_def]) >>
  `!it. supported_iterator_exists p (subst_consts_iter_mods E it) ==>
        supported_iterator_exists p it` by
    (Cases >> simp[constSubstModsTheory.subst_consts_iter_mods_def,
                   supportedStmtTraverseTheory.supported_iterator_exists_def] >>
     metis_tac[]);

val linked_ctor_decode_stmt_reflection_tac =
  linked_ctor_decode_target_reflection_tac >>
  linked_ctor_decode_reason_reflection_tac >>
  `(!E' s. E' = E ==>
      supported_stmt_expr_exists p (subst_consts_stmt_mods E' s) ==>
      supported_stmt_expr_exists p s) /\
   (!E' ss. E' = E ==>
      supported_stmts_expr_exists p (subst_consts_stmts_mods E' ss) ==>
      supported_stmts_expr_exists p ss)` by
    (ho_match_mp_tac constSubstModsTheory.subst_consts_stmt_mods_ind >>
     simp[constSubstModsTheory.subst_consts_stmt_mods_def,
          supportedStmtTraverseTheory.supported_stmt_expr_exists_def] >>
     metis_tac[]) >>
  qpat_assum `!E' ss. E' = E ==> supported_stmts_expr_exists p _ ==> _`
    (qspec_then `E` mp_tac) >> simp[];

val linked_ctor_decode_occurrence_tac =
  sg `(!target.
      (!e. supported_expr_exists (expr_abi_decode_target_root target)
             (subst_consts_expr_mods (consts_env_mods mods) e) ==>
           supported_expr_exists (expr_abi_decode_target_root target) e) /\
      (!t. supported_target_exists (expr_abi_decode_target_root target)
             (subst_consts_btarget_mods (consts_env_mods mods) t) ==>
           supported_target_exists (expr_abi_decode_target_root target) t) /\
      (!es. supported_exprs_exists (expr_abi_decode_target_root target)
              (subst_consts_exprs_mods (consts_env_mods mods) es) ==>
            supported_exprs_exists (expr_abi_decode_target_root target) es) /\
      (!opt. supported_opt_exists (expr_abi_decode_target_root target)
               (subst_consts_opt_mods (consts_env_mods mods) opt) ==>
             supported_opt_exists (expr_abi_decode_target_root target) opt) /\
      (!fs. supported_fields_exists (expr_abi_decode_target_root target)
              (subst_consts_fields_mods (consts_env_mods mods) fs) ==>
            supported_fields_exists (expr_abi_decode_target_root target) fs)) ==>
      !target. supported_stmts_expr_exists (expr_abi_decode_target_root target) cpkg6 ==>
        EXISTS (occurs_abi_decode_target target o SND) mods`
  >- (disch_then (fn family =>
        qx_gen_tac `target` >> qspec_then `target` assume_tac family) >>
      qabbrev_tac `p = expr_abi_decode_target_root target` >>
      qabbrev_tac `E = consts_env_mods mods` >>
      sg `!ss. supported_stmts_expr_exists p (subst_consts_stmts_mods E ss) ==>
               supported_stmts_expr_exists p ss`
      >- (qpat_assum `(!e. supported_expr_exists p _ ==> _) /\ _`
            (fn clauses => POP_ASSUM_LIST (K ALL_TAC) >>
              map_every assume_tac (CONJUNCTS clauses)) >>
          linked_ctor_decode_stmt_reflection_tac) >>
      qpat_assum `cpkg6 = _` SUBST1_TAC >> disch_tac >>
      `supported_stmts_expr_exists p raw_body` by
        (qpat_assum `!ss. supported_stmts_expr_exists p _ ==> _` irule >>
         simp[Abbr `E`]) >>
      simp[NoAsms, listTheory.EXISTS_MEM, supportedProgramTheory.occurs_abi_decode_target_def] >>
      qexists_tac `(NONE,tops')` >> conj_tac
      >- (irule alistTheory.ALOOKUP_MEM >> FIRST_ASSUM ACCEPT_TAC) >>
      qexists_tac `FunctionDecl Deploy mut F F "__init__" src_args [] NoneT raw_body` >>
      qpat_assum `supported_stmts_expr_exists p raw_body` mp_tac >>
      simp[Abbr `p`, supportedProgramTheory.declaration_abi_decode_target_def]);

(* Access-free constant replacements are fixed points of qualified substitution. *)
val linked_ctor_closed_subst_tac =
  `(!e. constant_expr mods e /\ vyperSubscriptOverlap$accesses_expr e = [] ==>
      subst_consts_expr_mods E e = e) /\
   (!es. EVERY (constant_expr mods) es /\ vyperSubscriptOverlap$accesses_exprs es = [] ==>
      subst_consts_exprs_mods E es = es) /\
   (!fs. EVERY (constant_expr mods) (MAP SND fs) /\
      vyperSubscriptOverlap$accesses_named_exprs fs = [] ==>
      subst_consts_fields_mods E fs = fs)` by
    (POP_ASSUM_LIST (K ALL_TAC) >>
     ho_match_mp_tac constSubstCorrectTheory.const_local_refs_ind >>
     simp[constant_expr_def, constSubstModsTheory.subst_consts_expr_mods_def,
          vyperSubscriptOverlapTheory.accesses_expr_def, SF ETA_ss] >>
     rpt strip_tac >> rename1 `risky_builtin bi` >>
     Cases_on `vyperSubscriptOverlap$risky_builtin bi` >> gvs[SF ETA_ss]);

val linked_ctor_expr_subst_idempotent_tac =
  `(!e. subst_consts_expr_mods E (subst_consts_expr_mods E e) = subst_consts_expr_mods E e) /\
   (!t. subst_consts_btarget_mods E (subst_consts_btarget_mods E t) = subst_consts_btarget_mods E t) /\
   (!es. subst_consts_exprs_mods E (subst_consts_exprs_mods E es) = subst_consts_exprs_mods E es) /\
   (!d. subst_consts_opt_mods E (subst_consts_opt_mods E d) = subst_consts_opt_mods E d) /\
   (!fs. subst_consts_fields_mods E (subst_consts_fields_mods E fs) = subst_consts_fields_mods E fs)` by
    (ho_match_mp_tac constSubstTheory.fold_const_expr_ind >>
     simp[constSubstModsTheory.subst_consts_expr_mods_def] >>
     rpt gen_tac >> PairCases_on `ns` >>
     Cases_on `ALOOKUP E (ns0,ns1)` >> simp[constSubstModsTheory.subst_consts_expr_mods_def] >>
     qpat_assum `!key r. ALOOKUP E key = SOME r ==> subst_consts_expr_mods E r = r`
       (drule_then ACCEPT_TAC));

val linked_ctor_stmt_subst_idempotent_tac =
  `(!E' t. E' = E ==>
      subst_consts_target_mods E' (subst_consts_target_mods E' t) = subst_consts_target_mods E' t) /\
   (!E' ts. E' = E ==>
      subst_consts_targets_mods E' (subst_consts_targets_mods E' ts) = subst_consts_targets_mods E' ts)` by
    (ho_match_mp_tac constSubstModsTheory.subst_consts_target_mods_ind >>
     simp[constSubstModsTheory.subst_consts_target_mods_def]) >>
  `!it. subst_consts_iter_mods E (subst_consts_iter_mods E it) = subst_consts_iter_mods E it` by
    (Cases >> simp[constSubstModsTheory.subst_consts_iter_mods_def]) >>
  `!err. subst_consts_error_mods E (subst_consts_error_mods E err) = subst_consts_error_mods E err` by
    (Cases >> simp[constSubstModsTheory.subst_consts_error_mods_def]) >>
  `!r. subst_consts_areason_mods E (subst_consts_areason_mods E r) = subst_consts_areason_mods E r` by
    (Cases >> simp[constSubstModsTheory.subst_consts_areason_mods_def]) >>
  `!r. subst_consts_rreason_mods E (subst_consts_rreason_mods E r) = subst_consts_rreason_mods E r` by
    (Cases >> simp[constSubstModsTheory.subst_consts_rreason_mods_def]) >>
  `(!E' s. E' = E ==>
      subst_consts_stmt_mods E' (subst_consts_stmt_mods E' s) = subst_consts_stmt_mods E' s) /\
   (!E' ss. E' = E ==>
      subst_consts_stmts_mods E' (subst_consts_stmts_mods E' ss) = subst_consts_stmts_mods E' ss)` by
    (ho_match_mp_tac constSubstModsTheory.subst_consts_stmt_mods_ind >>
     simp[constSubstModsTheory.subst_consts_stmt_mods_def]);

val linked_ctor_subst_idempotent_tac =
  sg `(!key r. ALOOKUP (consts_env_mods mods) key = SOME r ==>
        constant_expr mods r /\ vyperSubscriptOverlap$accesses_expr r = []) ==>
      subst_consts_stmts_mods (consts_env_mods mods) cpkg6 = cpkg6` >-
    (qpat_assum `cpkg6 = _` SUBST1_TAC >> POP_ASSUM_LIST (K ALL_TAC) >>
     qabbrev_tac `E = consts_env_mods mods` >> strip_tac >>
     linked_ctor_closed_subst_tac >>
     `!key r. ALOOKUP E key = SOME r ==> subst_consts_expr_mods E r = r` by
       (rpt gen_tac >> disch_tac >>
        qpat_assum `!key r. ALOOKUP E key = SOME r ==> constant_expr _ r /\ _`
          (drule_then strip_assume_tac) >>
        qpat_assum `!e. constant_expr mods e /\ _ ==> _` irule >>
        conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     linked_ctor_expr_subst_idempotent_tac >>
     linked_ctor_stmt_subst_idempotent_tac >> simp[]);

(* Instantiate the body judgement without assuming any source-side obligations. *)
val linked_ctor_conditional_body_tac =
  `IS_SOME (check_contract F cx.layouts cx.txn.target mods)` by
    (qpat_assum `check_contract F am.layouts tx.target mods = SOME _`
       (fn checked => simp[NoAsms, Abbr `cx`, deploy_evaluation_context_mods_def,
                           initial_evaluation_context_def, checked])) >>
  `!DF lo d PG RetQ env env' bindings src_es.
    EVERY (struct_args_unique o SND) mods /\
    supported_stmts tops' bindings cpkg6 /\
    (!sid ts vis mut nr raw name args dflts ret body.
       ALOOKUP mods sid = SOME ts /\
       MEM (FunctionDecl vis mut nr raw name args dflts ret body) ts ==>
       stmts_loop_calls_ok mods
         (subst_consts_stmts_mods (consts_env_mods mods) body)) /\
    qualified_stmts_decls_ok mods cpkg6 /\
    stmts_loop_calls_ok mods cpkg6 /\
    EVERY (\k. MEM k (vyperTypeContract$linked_live_functions mods exps))
      (int_calls_stmts cpkg6) /\
    (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) cpkg6 ==>
       EXISTS (occurs_abi_decode_target target o SND) mods) /\
    body_const_cells_agree_mods mods cx env src_es /\
    expr_sim_inv_mods mods ctor_ce cx env src_es /\
    ce_locals_declared ctor_ce env /\ locals_alloc_ok ctor_ce env /\
    type_stmts env NoneT cpkg6 = SOME env' /\ stmts_exprs_ok ctor_ce cpkg6 /\
    ~supported_stmts_expr_exists (unallocated_bare_global_root ctor_ce env) cpkg6 /\
    (!key. MEM (vyperSubscriptOverlap$WriteAcc (vyperSubscriptOverlap$StateRef key))
                 (vyperSubscriptOverlap$accesses_stmts cpkg6) /\
           IS_SOME (FLOOKUP env.bare_global_assignable key) ==>
           IS_SOME (FLOOKUP ctor_ce.ce_module_vars key)) /\
    call_evaluation_safe cx (int_calls_stmts cpkg6) /\
    frame_ret_ok_full_mods mods
      (DF,lo,d,deploy_unit.cu_context,shadow_unit.cu_context,PG,fn,shadow_fn)
      cx RetQ ctor_ce NoneT ==>
    stmt_frag_full_mods
      (DF,lo,d,deploy_unit.cu_context,shadow_unit.cu_context,PG,fn,shadow_fn)
      cx NoLoop RetQ ctor_ce (stmts_env ctor_ce NoLoop NoneT cpkg6)
      (stmts_env (gas_shadow_env T ctor_ce) NoLoop NoneT (MAP gas_shadow_stmt cpkg6))
      (eval_stmts cx cpkg6) src_es` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     irule bodySimFullMainTheory.body_stmts_sim_full_mods >>
     conj_tac >- FIRST_ASSUM ACCEPT_TAC >> conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
     qexistsl_tac [`bindings`,`env`,`env'`,`exps`,`mods`,`NONE`,`tops'`] >>
     rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE simp[]));

(* At the checked entry, only the constructor return frame is still needed. *)
fun linked_ctor_body_except_frame_tac frame =
  sg `!DF lo disp PG RetQ gs.
    frame_ret_ok_full_mods mods
      (DF,lo,disp,deploy_unit.cu_context,shadow_unit.cu_context,PG,fn,shadow_fn)
      cx RetQ ctor_ce NoneT ==>
    stmt_frag_full_mods
      (DF,lo,disp,deploy_unit.cu_context,shadow_unit.cu_context,PG,fn,shadow_fn)
      cx NoLoop RetQ ctor_ce (stmts_env ctor_ce NoLoop NoneT cpkg6)
      (stmts_env (gas_shadow_env T ctor_ce) NoLoop NoneT (MAP gas_shadow_stmt cpkg6))
      (eval_stmts cx cpkg6)
      (es0 with <|gas_obs := gs; outcomes := SOME (MAP SND (call_trace ^frame))|>)` >-
    (map_every qx_gen_tac [`DF`,`lo`,`disp`,`PG`,`RetQ`,`gs`] >> disch_tac >>
     qpat_assum `!gs. expr_sim_inv_mods mods ctor_ce cx env _`
       (qspec_then `gs` assume_tac) >>
     qpat_assum `!gs. env_consistent env cx _ /\ state_well_typed _`
       (qspec_then `gs` (assume_tac o CONJUNCT2)) >>
     `body_const_cells_agree_mods mods cx env
       (es0 with <|gas_obs := gs; outcomes := SOME (MAP SND (call_trace ^frame))|>)` by
       (qpat_assum `!env src_es. _ ==> body_const_cells_agree_mods mods cx env src_es` irule >>
        rpt conj_tac >>
        (FIRST_ASSUM ACCEPT_TAC ORELSE
         (qpat_assum `get_tenv cx = type_env_all_modules mods` SUBST1_TAC >>
          FIRST_ASSUM ACCEPT_TAC) ORELSE simp[NoAsms])) >>
     `qualified_stmts_decls_ok mods cpkg6` by
       (qpat_assum `qualified_stmts_decls_ok ctor_ce.ce_modules cpkg6` mp_tac >>
        qpat_assum `contract_inv mods exps deploy_unit.cu_context ctor_ce cx`
          (fn inv => PURE_REWRITE_TAC
            [MATCH_MP bodyInvCodePropsTheory.contract_inv_cenv_modules inv]) >>
        disch_then ACCEPT_TAC) >>
     qpat_assum `!DF lo d PG RetQ env env' bindings src_es.
         _ ==> stmt_frag_full_mods _ cx NoLoop RetQ ctor_ce _ _ _ src_es` irule >>
     rpt conj_tac >>
     FIRST [FIRST_ASSUM ACCEPT_TAC,
            qexists_tac `bindings` >> FIRST_ASSUM ACCEPT_TAC,
            qexistsl_tac [`env`,`env'`] >> rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC]);

(* Install the body fragment at the proven constructor frame, for every observation. *)
val linked_ctor_body_at_return_frame_tac =
  qpat_assum `!DF lo disp PG RetQ gs.
    frame_ret_ok_full_mods mods _ cx RetQ ctor_ce NoneT ==>
    stmt_frag_full_mods _ cx NoLoop RetQ ctor_ce _ _ _ _`
    (drule_then assume_tac) >>
  qpat_x_assum `!gs. stmt_frag_full_mods
    (linked_ret_DF,imm_len_mods mods,NONE,deploy_unit.cu_context,
     shadow_unit.cu_context,[],fn,shadow_fn)
    cx NoLoop _ ctor_ce _ _ (eval_stmts cx cpkg6) _`
    (mk_asm "linked_ctor_body_frag");

(* Constant substitution cannot introduce a loop-control escape.  Preserve
   no-fallthrough too, because it can make the tail of a list unreachable. *)
val linked_ctor_subst_control_tac =
  `!E e. expr_no_fallthrough e ==>
          expr_no_fallthrough (subst_consts_expr_mods E e)` by
    (POP_ASSUM_LIST (K ALL_TAC) >> gen_tac >> Cases >>
     simp[vyperTypeSystemTheory.expr_no_fallthrough_def,
          constSubstModsTheory.subst_consts_expr_mods_def] >>
     rename1 `expr_no_fallthrough (Call _ target _ _) ==> _` >>
     Cases_on `target` >> simp[vyperTypeSystemTheory.expr_no_fallthrough_def]) >>
  `(!E s. (stmt_no_fallthrough s ==>
           stmt_no_fallthrough (subst_consts_stmt_mods E s)) /\
          (stmt_no_control_escape s ==>
           stmt_no_control_escape (subst_consts_stmt_mods E s))) /\
   (!E ss. (stmts_no_fallthrough ss ==>
            stmts_no_fallthrough (subst_consts_stmts_mods E ss)) /\
           (stmts_no_control_escape ss ==>
            stmts_no_control_escape (subst_consts_stmts_mods E ss)))` by
    (pop_assum (fn expr => POP_ASSUM_LIST (K ALL_TAC) >> assume_tac expr) >>
     ho_match_mp_tac constSubstModsTheory.subst_consts_stmt_mods_ind >>
     simp[constSubstModsTheory.subst_consts_stmt_mods_def,
          vyperTypeSystemTheory.stmt_no_fallthrough_def,
          vyperTypeSystemTheory.stmt_no_control_escape_def] >>
     rpt strip_tac >> metis_tac[]) >>
  `stmts_no_control_escape raw_body` by
    (qpat_assum `tx.function_name = "__init__"` (fn init =>
       drule_all_then ACCEPT_TAC (PURE_REWRITE_RULE [init]
         vyperTypeDeploymentSoundnessTheory.checked_constructor_no_control_escape))) >>
  `stmts_no_control_escape cpkg6` by
    (qpat_assum `cpkg6 = _` SUBST1_TAC >>
     qpat_assum `!E ss. (_ ==> _) /\ (stmts_no_control_escape ss ==> _)`
       (irule o cj 2) >> FIRST_ASSUM ACCEPT_TAC);

fun linked_ctor_source_admissible_tac frame =
  `!gs. gas_admissible (eval_stmts cx cpkg6) (stmt_res_ok NoLoop)
         (es0 with <|gas_obs := gs; outcomes := SOME (MAP SND (call_trace ^frame))|>)` by
    (map_every (fn p => qpat_assum p mp_tac)
       [`!gs. env_consistent env cx (es0 with <|gas_obs := gs;
          outcomes := SOME (MAP SND (call_trace ^frame))|>) /\ state_well_typed _`,
        `type_stmts env NoneT cpkg6 = SOME _`, `context_well_typed cx`,
        `functions_well_typed cx`, `accounts_well_typed es0.accounts`,
        `call_evaluation_safe cx (int_calls_stmts cpkg6)`,
        `stmts_no_control_escape cpkg6`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> ntac 7 (disch_then assume_tac) >>
     rewrite_tac[gasContextTheory.gas_admissible_def] >>
     map_every qx_gen_tac [`gs`,`gs'`,`res`,`ee`] >>
     `(es0 with <|gas_obs := gs; outcomes := SOME (MAP SND (call_trace ^frame))|>)
        with gas_obs := gs' =
      es0 with <|gas_obs := gs'; outcomes := SOME (MAP SND (call_trace ^frame))|>` by
       simp[NoAsms, vyperStateTheory.evaluation_state_component_equality] >>
     pop_assum (pure_rewrite_tac o single) >> disch_tac >>
     qpat_assum `!gs. env_consistent env cx _ /\ state_well_typed _`
       (qspec_then `gs'` strip_assume_tac) >>
     `accounts_well_typed
        (es0 with <|gas_obs := gs'; outcomes := SOME (MAP SND (call_trace ^frame))|>).accounts` by
       (simp[NoAsms] >> FIRST_ASSUM ACCEPT_TAC) >>
     `no_type_error_eval (res,ee)` by
       (qpat_assum `eval_stmts cx cpkg6 _ = (res,ee)` (SUBST1_TAC o SYM) >>
        drule_all_then ACCEPT_TAC vyperTypeStmtSoundnessTheory.eval_stmts_no_type_error) >>
     Cases_on `res` >> simp[stmtSimDefsTheory.stmt_res_ok_def] >> rename1 `INR exc` >>
     drule_all_then strip_assume_tac
       vyperTypeEvalProofsTheory.stmts_no_control_escape_eval_stmts_no_loop_control >>
     Cases_on `exc` >>
     gvs[vyperTypeExprSoundnessTheory.no_type_error_eval_def,
         vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
     rename1 `INR (Error err)` >> Cases_on `err` >> gvs[]);

val linked_ctor_paired_env_tac =
  `stmts_env (gas_shadow_env T ctor_ce) NoLoop NoneT
     (MAP gas_shadow_stmt cpkg6) sa = (gas_shadow_env T ce_end,shadow_sb)` by
    (mp_tac (Q.SPECL [`cpkg6`,`ctor_ce`,`NoLoop`,`NoneT`]
              (Q.INST [`sd` |-> `T`] gasShadowStmtEnvTheory.gas_shadow_stmts_env_env)) >>
     rewrite_tac[gasShadowCompileStmtBaseTheory.gas_shadow_compiles_env_def] >>
     disch_then (qspecl_then [`sa`,`sa`] mp_tac) >>
     simp[gasShadowStateTheory.gas_shadow_state_refl]);

val linked_ctor_body_dead_low_tac =
  `!H. dead_lo_ok_mods H (linked_ret_DF H) (imm_len_mods mods) ctor_ce cx` by
    (qpat_assum `contract_inv mods exps deploy_unit.cu_context ctor_ce cx`
       (assume_tac o MATCH_MP bodyInvCodePropsTheory.contract_inv_cenv_modules) >>
     qpat_assum `ctor_ce.ce_modules = mods` (fn modules =>
       qpat_assum `cx.txn.target = tx.target` (fn target =>
         qpat_assum `ctor_ce.ce_is_ctor` (fn ctor =>
           simp[NoAsms, bodyFullShadowBodyInvTheory.dead_lo_ok_mods_def,
                bodyPtrDefsTheory.dead_sub_def, sourceUnitExecutionTheory.cx_dead_def,
                Abbr `linked_ret_DF`, modules, target, ctor]))));

(* The registered endpoint preserves the selected frame, independently of gs. *)
fun linked_entry_machine_parts_goal_tac frame =
  let val source = ``es0 with <|gas_obs := gs; outcomes := SOME (MAP SND (call_trace ^frame))|>``
  in Q.SUBGOAL_THEN `!vi (actual:venom_state) gs (H : (bool # bytes32 # type_value) list # num list).
    raw_variant fmp vi vs /\
    actual.vs_accounts = vi.vs_accounts /\
    actual.vs_transient = vi.vs_transient /\
    actual.vs_logs = vi.vs_logs /\
    actual.vs_requests = vi.vs_requests /\
    actual.vs_pending_deletions = vi.vs_pending_deletions /\
    actual.vs_outcomes = vi.vs_outcomes /\
    actual.vs_call_ctx = vi.vs_call_ctx /\
    actual.vs_tx_ctx = vi.vs_tx_ctx /\
    actual.vs_block_ctx = vi.vs_block_ctx /\
    actual.vs_code = vi.vs_code /\ actual.vs_labels = vi.vs_labels /\
    local_ptrs_rel fn ce1 [scope] actual /\
    alloca_inv actual /\
    (!site. alloca_frontier_inv_from (imm_len_mods mods) deploy_unit.cu_context fn site actual) /\
    fmp_room deploy_unit.cu_context fn actual /\
    (!inst n base sz. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
       inst.inst_operands = [Lit n] /\
       FLOOKUP actual.vs_allocas inst.inst_id = SOME (base,sz) ==> sz = w2n n) /\
    eval_operand imm actual = SOME 0w /\
    es0.scopes = [scope] /\ es0.accounts = accounts_after_transfer tx am.accounts /\
    es0.tStorage = (initial_state am []).tStorage /\ es0.immutables = am_c.immutables /\
    es0.logs = (initial_state am_c [scope]).logs /\
    es0.requests = (initial_state am_c [scope]).requests /\
    es0.pending_deletions = (initial_state am_c [scope]).pending_deletions ==>
    local_ptrs_rel fn ctor_ce (^source).scopes actual /\
    storage_rel H cx.txn.target ^source actual /\ storage_vars_rel ctor_ce cx /\
    transient_rel H cx.txn.target ^source actual /\ transient_vars_rel ctor_ce cx /\
    accounts_rel H cx ^source actual /\ logs_rel ctor_ce cx.txn.target ^source actual /\
    call_ctx_rel cx.txn actual.vs_call_ctx actual.vs_tx_ctx actual.vs_block_ctx /\
    (^source).outcomes = SOME actual.vs_outcomes /\
    LIST_REL (request_agree H cx.txn.target) (^source).requests actual.vs_requests /\
    (^source).pending_deletions = actual.vs_pending_deletions /\
    alloca_inv actual /\ alloca_room deploy_unit.cu_context fn actual /\
    fmp_room deploy_unit.cu_context fn actual /\ immutable_base_zero ctor_ce actual /\
    (!inst n base sz. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
       inst.inst_operands = [Lit n] /\
       FLOOKUP actual.vs_allocas inst.inst_id = SOME (base,sz) ==> sz = w2n n)`
    (mk_asm "linked_entry_machine_parts")
  end;

val linked_entry_machine_variant_tac =
  `vi.vs_accounts = vs.vs_accounts /\ vi.vs_transient = vs.vs_transient /\
   vi.vs_logs = vs.vs_logs /\ vi.vs_requests = vs.vs_requests /\
   vi.vs_pending_deletions = vs.vs_pending_deletions /\ vi.vs_outcomes = vs.vs_outcomes /\
   vi.vs_call_ctx = vs.vs_call_ctx /\ vi.vs_tx_ctx = vs.vs_tx_ctx /\
   vi.vs_block_ctx = vs.vs_block_ctx /\ vi.vs_code = vs.vs_code /\ vi.vs_labels = vs.vs_labels` by
    (qpat_assum `raw_variant fmp vi vs`
       (mp_tac o Q.AP_TERM `\s. (s.vs_accounts,s.vs_transient,s.vs_logs,
          s.vs_requests,s.vs_pending_deletions,s.vs_outcomes,s.vs_call_ctx,
          s.vs_tx_ctx,s.vs_block_ctx,s.vs_code,s.vs_labels)` o
        PURE_REWRITE_RULE [raw_variant_def, gas_variant_def]) >> simp[NoAsms]) >>
  pop_assum strip_assume_tac;

val linked_entry_machine_slots_tac =
  (sg `storage_vars_rel ctor_ce cx /\ transient_vars_rel ctor_ce cx` >-
    (qpat_assum `contract_inv mods exps deploy_unit.cu_context ctor_ce cx`
       (strip_assume_tac o PURE_REWRITE_RULE [contract_inv_def, cenv_module_pins_mods_def]) >>
     irule entryModuleLocationsTheory.unit_module_locations_slot_relations >>
     qexistsl_tac [`am with <| sources := cx.sources;
                              exports updated_by CONS (tx.target,exps) |>`,
                   `exps`,`mods`,`tx`] >>
     rpt conj_tac >> FIRST [FIRST_ASSUM ACCEPT_TAC,
       simp[NoAsms, contract_keys_def] >> FIRST_ASSUM ACCEPT_TAC,
       simp[NoAsms] >> FIRST_ASSUM ACCEPT_TAC,
       (pure_rewrite_tac[source_deployment_rel_mods_def] >>
        conj_tac >-
          (qpat_assum `cx.txn.target = tx.target` (fn target =>
             qpat_assum `ALOOKUP cx.sources cx.txn.target = SOME mods`
               (fn lookup => simp[NoAsms, REWRITE_RULE [target] lookup]))) >>
        conj_tac >-
          (qpat_assum `IS_SOME (ALOOKUP mods NONE)`
             (ACCEPT_TAC o PURE_REWRITE_RULE [optionTheory.IS_SOME_EQ_NOT_NONE])) >>
        conj_tac >- simp[NoAsms] >>
        pure_rewrite_tac [layouts_agree_mods_def,
          vyperInterpreterTheory.abstract_machine_accfupds] >>
        qpat_assum `layouts_agree_mods mods exps am tx`
          (ACCEPT_TAC o PURE_REWRITE_RULE [layouts_agree_mods_def]))])) >>
  pop_assum strip_assume_tac;

fun linked_entry_machine_frame_tac frame =
  qpat_assum `deploy_state_rel_mods mods exps (assemble prog') am tx ^frame`
    (mp_tac o PURE_REWRITE_RULE [deploy_state_rel_mods_def]) >>
  disch_then (qx_choosel_then [`entry_ctxt`,`entry_rb`,`entry_args`]
    (map_every assume_tac o CONJUNCTS)) >>
  `cx.txn = tx` by
    (qpat_assum `cx = _` SUBST1_TAC >>
     qpat_assum `tx.created_in_tx` (fn created =>
       simp[NoAsms, initial_evaluation_context_def,
            vyperContextTheory.call_txn_component_equality, created])) >>
  `am_c.logs = am.logs /\ am_c.pending_deletions = am.pending_deletions` by
    (qpat_assum `am_c = am0 with immutables := _`
       (mp_tac o Q.AP_TERM `\m:abstract_machine. (m.logs,m.pending_deletions)`) >>
     qpat_assum `am0 = _` (fn installed => simp[NoAsms, installed])) >>
  pop_assum strip_assume_tac;

val linked_entry_machine_alloca_tac =
  irule allocaFrontierRoomTheory.deploy_ctor_frontier_alloca_room >>
  qexistsl_tac [`imm_len_mods mods`,`mk_inst 0 STOP [] []`] >>
  rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE
    qpat_assum `!site. alloca_frontier_inv_from _ _ _ site actual`
      (qspec_then `mk_inst 0 STOP [] []` ACCEPT_TAC));

val linked_entry_machine_base_tac =
  rewrite_tac[immutable_base_zero_def] >> conj_tac
  >- (qpat_assum `ctor_ce = _` SUBST1_TAC >>
      Cases_on `0 < imm_len_mods mods` >>
      qpat_assum `eval_operand imm actual = SOME 0w` mp_tac >> simp[]) >>
  qpat_assum `actual.vs_labels = vi.vs_labels` SUBST1_TAC >>
  qpat_assum `vi.vs_labels = vs.vs_labels` SUBST1_TAC >>
  qpat_assum `FLOOKUP (lo_reloc prog prog') "runtime_begin" = SOME off`
    (fn lab => simp[NoAsms, Abbr `vs`, opt_entry_state_own_def, finite_mapTheory.FLOOKUP_o_f, lab]);

fun linked_entry_machine_world_tac frame =
  (sg `actual.vs_accounts = entry_src.accounts /\
   actual.vs_transient = entry_src.tStorage /\
   actual.vs_code = cx.txn.code /\
   actual.vs_logs = [] /\ entry_src.logs = [] /\
   actual.vs_requests = [] /\ entry_src.requests = [] /\
   entry_src.outcomes = SOME actual.vs_outcomes /\
   entry_src.pending_deletions = actual.vs_pending_deletions` >-
    (qpat_assum `cx.txn = tx` SUBST1_TAC >>
     qpat_assum `^frame.contexts = [(entry_ctxt,entry_rb)]` (fn contexts =>
       simp[Abbr `entry_src`, Abbr `vs`, Abbr `unpaid`, opt_entry_state_own_def,
            entry_venom_state_frame_fields,
            entry_venom_state_fresh, vyperInterpreterTheory.initial_state_def, contexts]))) >>
  pop_assum strip_assume_tac;

fun linked_entry_machine_call_fields_tac frame =
  qpat_assum `actual.vs_call_ctx = vi.vs_call_ctx` SUBST1_TAC >>
  qpat_assum `actual.vs_tx_ctx = vi.vs_tx_ctx` SUBST1_TAC >>
  qpat_assum `actual.vs_block_ctx = vi.vs_block_ctx` SUBST1_TAC >>
  qpat_assum `vi.vs_call_ctx = vs.vs_call_ctx` SUBST1_TAC >>
  qpat_assum `vi.vs_tx_ctx = vs.vs_tx_ctx` SUBST1_TAC >>
  qpat_assum `vi.vs_block_ctx = vs.vs_block_ctx` SUBST1_TAC >>
  qpat_assum `cx.txn = tx` SUBST1_TAC >>
  qpat_assum `tx_block_fields_rel tx ^frame.txParams`
    (strip_assume_tac o PURE_REWRITE_RULE [tx_block_fields_rel_def]) >>
  simp[Abbr `vs`, opt_entry_state_own_def, entry_venom_state_def, call_ctx_rel_def];

fun linked_entry_machine_call_hashes_tac frame =
  qx_gen_tac `n` >>
  Cases_on `n < tx.block_number /\ tx.block_number - 256 <= n` >> simp[] >>
  `tx.block_number - n - 1 < 256` by decide_tac >>
  simp[listTheory.EL_TAKE, listTheory.LENGTH_TAKE_EQ] >>
  Cases_on `256 <= LENGTH (^frame).txParams.prevHashes` >>
  simp[listTheory.LENGTH_TAKE_EQ] >> decide_tac;

fun linked_entry_machine_call_tac frame =
  linked_entry_machine_call_fields_tac frame >> linked_entry_machine_call_hashes_tac frame;

val linked_entry_machine_address_tac =
  qpat_assum `call_ctx_rel cx.txn actual.vs_call_ctx _ _` mp_tac >>
  simp[NoAsms, call_ctx_rel_def];

val linked_entry_machine_conjuncts_tac =
  FIRST [irule exprLoweringPropsTheory.local_ptrs_rel_cenv_cong >>
         qexists_tac `ce1` >>
         qpat_assum `ctor_ce = _` SUBST1_TAC >> simp[Abbr `entry_src`],
         simp[storage_rel_def, transient_rel_def, contract_storage_def,
              contract_transient_def, accounts_rel_def, accounts_agree_def,
              transient_agree_def, logs_rel_def] >> NO_TAC,
         linked_entry_machine_alloca_tac,
         linked_entry_machine_base_tac];
(* Relate the registered low-memory prefix to the evaluated linked cells. *)
fun linked_entry_immutable_goal_tac frame =
  Q.SUBGOAL_THEN `!vi actual gs. raw_variant fmp vi vs /\
    eval_operand imm actual = SOME 0w /\
    (!p. p < imm_len_mods mods ==>
       mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 vi.vs_memory) /\
    imm_len_mods mods <= actual.vs_alloca_next /\
    (!aid b sz. FLOOKUP actual.vs_allocas aid = SOME (b,sz) ==> imm_len_mods mods <= b) /\
    (!id b sz. local_region ce1 [scope] actual id b sz ==> imm_len_mods mods <= b) /\
    es0.scopes = [scope] /\ es0.immutables = am_c.immutables ==>
    immutable_frame_mods fn ctor_ce cx
      (es0 with <|gas_obs := gs; outcomes := SOME (MAP SND (call_trace ^frame))|>) actual`
    (mk_asm "linked_entry_immutable");

val linked_entry_immutable_prefix_tac =
  `vi.vs_memory = []` by
    (qpat_assum `raw_variant fmp vi vs`
       (mp_tac o PURE_REWRITE_RULE [raw_variant_def, gas_variant_def]) >>
     simp[NoAsms, venom_state_component_equality, Abbr `vs`,
          opt_entry_state_own_def, entry_venom_state_fresh]) >>
  `mem_bytes_at 0 (imm_len_mods mods) actual.vs_memory =
     REPLICATE (imm_len_mods mods) 0w` by
    (irule ctorDeployLoweringEntryImmutableMemoryTheory.deploy_ctor_zero_prefix_section >>
     qpat_assum `vi.vs_memory = []` (SUBST1_TAC o SYM) >> FIRST_ASSUM ACCEPT_TAC);

val linked_entry_immutable_section_tac =
  (sg `immutables_section_rel_mods mods (account_immutables am_c tx.target)
     (REPLICATE (imm_len_mods mods) 0w)` >-
    (irule linkedZeroImmutablesTheory.linked_initialized_zero_immutables >>
     qexistsl_tac [`am`,`runtime_art`,`e2eDeployModsDefs$deploy_evaluation_context_mods`,
                  `exps`,`imms`] >>
     conj_tac >-
       (qpat_assum `Abbrev (cx = _)`
          (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
        qpat_assum `am0 = _` (SUBST1_TAC o SYM) >>
        qpat_assum `cx.txn.target = tx.target` (SUBST1_TAC o SYM) >>
        FIRST_ASSUM ACCEPT_TAC) >>
     rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
  `ALOOKUP es0.immutables cx.txn.target = SOME cells` by FIRST_ASSUM ACCEPT_TAC >>
  `immutables_section_rel_mods mods cells (REPLICATE (imm_len_mods mods) 0w)` by
    (qpat_assum `immutables_section_rel_mods mods (account_immutables am_c _) _` mp_tac >>
     qpat_assum `cx.txn.target = tx.target` (SUBST1_TAC o SYM) >>
     asm "installed_cells" (fn lookup => simp[NoAsms, account_immutables_def, lookup]));

val linked_entry_immutable_regions_tac =
  qpat_assum `immutable_section_layout_mods mods ctor_ce`
    (map_every assume_tac o List.take o (fn th => (CONJUNCTS th,2)) o
     PURE_REWRITE_RULE [immutable_section_layout_mods_def]) >>
  qpat_assum `immutables_section_rel_mods mods cells _`
    (assume_tac o CONJUNCT2 o PURE_REWRITE_RULE [immutables_section_rel_mods_def]) >>
  (sg `!src name off. FLOOKUP ctor_ce.ce_module_vars (src,name) = SOME (ImmutableLoc off) ==>
      ?tv v. FLOOKUP (get_source_immutables src cells) name = SOME (tv,v) /\
        off + type_memory_size tv <= imm_len_mods mods /\
        immutable_value_admissible tv v /\
        val_in_memory tv v off (REPLICATE (imm_len_mods mods) 0w) /\
        immutable_value_bytes_rel tv v
          (mem_bytes_at off (type_memory_size tv) (REPLICATE (imm_len_mods mods) 0w))` >-
    (map_every qx_gen_tac [`isrc`,`iname`,`ioff`] >> disch_tac >>
     qpat_assum `!src name off. FLOOKUP ctor_ce.ce_module_vars _ = _ <=> _`
       (qspecl_then [`isrc`,`iname`,`ioff`] mp_tac) >>
     qpat_assum `FLOOKUP ctor_ce.ce_module_vars (isrc,iname) = _`
       (fn loc => simp[NoAsms, loc]) >>
     disch_then (qx_choose_then `isize` assume_tac) >>
     qpat_assum `!src name off size. immutable_region_mods mods src name off size ==>
         off + size <= imm_len_mods mods` (drule_then assume_tac) >>
     qpat_assum `!src name off size. immutable_region_mods mods src name off size ==>
         ?tv v. _` (drule_then (qx_choosel_then [`itv`,`iv`] strip_assume_tac)) >>
     qexistsl_tac [`itv`,`iv`] >> rpt conj_tac >>
     (FIRST_ASSUM ACCEPT_TAC ORELSE
      (qpat_assum `type_memory_size itv = isize` SUBST1_TAC >> FIRST_ASSUM ACCEPT_TAC))));

val linked_entry_immutable_repr_tac =
  simp[NoAsms, immutables_rel_mods_def, immutables_rel_def, LET_THM] >>
  qpat_assum `ctor_ce.ce_is_ctor` (fn ctor =>
    qpat_assum `ALOOKUP es0.immutables cx.txn.target = SOME cells`
      (fn cells => simp[NoAsms, ctor, cells])) >>
  map_every qx_gen_tac [`isrc`,`itops`] >> disch_tac >>
  map_every qx_gen_tac [`iname`,`itv`,`iv`,`ioff`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!src name off. FLOOKUP ctor_ce.ce_module_vars _ = _ ==> ?tv v. _`
    (drule_then (qx_choosel_then [`ctv`,`cv`] strip_assume_tac)) >>
  `ctv = itv /\ cv = iv` by
    (qpat_assum `FLOOKUP (get_source_immutables isrc cells) iname = SOME (itv,iv)`
       (fn cell => qpat_assum `FLOOKUP (get_source_immutables isrc cells) iname = SOME (ctv,cv)`
         (mp_tac o REWRITE_RULE [cell])) >> simp[NoAsms]) >>
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `cv = iv` SUBST_ALL_TAC >>
  qpat_x_assum `ctv = itv` SUBST_ALL_TAC >>
  (sg `mem_bytes_at ioff (type_memory_size itv) actual.vs_memory =
       mem_bytes_at ioff (type_memory_size itv) (REPLICATE (imm_len_mods mods) 0w)` >-
    (irule (cj 1 valueEncodingProofsTheory.mem_bytes_at_agree_window) >>
     qexistsl_tac [`imm_len_mods mods`,`0`] >>
     qpat_assum `mem_bytes_at 0 (imm_len_mods mods) actual.vs_memory = _`
       (fn prefix => simp[NoAsms, prefix, valueEncodingDefsTheory.mem_bytes_at_def,
                            listTheory.TAKE_APPEND1]) >>
     FIRST_ASSUM ACCEPT_TAC)) >>
  conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
  conj_tac >-
    (drule (cj 1 valueEncodingProofsTheory.val_in_memory_mem_agree_proof) >>
     disch_then irule >>
     rpt conj_tac >>
     (FIRST_ASSUM ACCEPT_TAC ORELSE
      drule_then ACCEPT_TAC (cj 1 loweringSliceTheory.immutable_admissible_val_wf) ORELSE
      qpat_assum `mem_bytes_at ioff (type_memory_size itv) actual.vs_memory = _`
        (ACCEPT_TAC o SYM))) >>
  qpat_assum `mem_bytes_at ioff (type_memory_size itv) actual.vs_memory = _` SUBST1_TAC >>
  FIRST_ASSUM ACCEPT_TAC;

val linked_entry_immutable_decl_tac =
  (sg `!src name off ty tv.
    FLOOKUP ctor_ce.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
    ctor_ce.ce_module_var_type (src,name) = SOME ty /\
    evaluate_type (get_tenv cx) ty = SOME tv ==>
    off + type_memory_size tv <= imm_len_mods mods` >-
   (map_every qx_gen_tac [`isrc`,`iname`,`ioff`,`ity`,`itv`] >> strip_tac >>
    qpat_assum `!src name off. FLOOKUP ctor_ce.ce_module_vars _ = _ <=> _`
      (qspecl_then [`isrc`,`iname`,`ioff`] mp_tac) >>
    qpat_assum `FLOOKUP ctor_ce.ce_module_vars (isrc,iname) = _`
      (fn loc => simp[NoAsms, loc]) >>
    disch_then (qx_choose_then `isize` assume_tac) >>
    qpat_assum `!src name off size. immutable_region_mods mods src name off size ==>
        off + size <= imm_len_mods mods` (drule_then assume_tac) >>
    qpat_assum `!gs. expr_sim_inv_mods mods ctor_ce cx env _`
      (qspec_then `gs` assume_tac) >>
    drule_all immutableRegionTypingPropsTheory.immutable_region_mods_type >>
    disch_then (qx_choosel_then [`ity_tops`,`jty`,`jtv`] strip_assume_tac) >>
    map_every (fn p => qpat_assum p mp_tac)
      [`ctor_ce.ce_module_var_type (isrc,iname) = SOME jty`,
       `evaluate_type (get_tenv cx) jty = SOME jtv`,
       `isize = type_memory_size jtv`, `ioff + isize <= imm_len_mods mods`,
       `ctor_ce.ce_module_var_type (isrc,iname) = SOME ity`,
       `evaluate_type (get_tenv cx) ity = SOME itv`] >>
    POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[optionTheory.SOME_11]));

val linked_entry_immutable_floor_tac =
  `ctor_ce.ce_vars = ce1.ce_vars` by simp[NoAsms, Abbr `ctor_ce`] >>
  (sg `!src id b sz. local_region (ctor_ce with ce_module := src) [scope] actual id b sz ==>
       imm_len_mods mods <= b` >-
   (qpat_assum `!id b sz. local_region ce1 [scope] actual id b sz ==> _` mp_tac >>
    qpat_assum `ctor_ce.ce_vars = ce1.ce_vars` (fn vars =>
       simp[NoAsms, local_region_def, vars]))) >>
  (sg `!src off width. off + width <= imm_len_mods mods ==>
       off + width <= actual.vs_alloca_next /\
       (!aid b sz. FLOOKUP actual.vs_allocas aid = SOME (b,sz) ==>
         loweringStateRelDefs$regions_disjoint off width b sz) /\
       (!id b sz. local_region (ctor_ce with ce_module := src) [scope] actual id b sz ==>
         loweringStateRelDefs$regions_disjoint off width b sz)` >-
   (rpt gen_tac >> disch_tac >> conj_tac
    >- (irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `imm_len_mods mods` >> simp[]) >>
    conj_tac
    >- (rpt strip_tac >> qpat_assum `!aid b sz. FLOOKUP actual.vs_allocas _ = _ ==> _`
         (drule_then assume_tac) >>
        simp[loweringStateRelDefsTheory.regions_disjoint_def] >> disj1_tac >>
        irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `imm_len_mods mods` >> simp[]) >>
    rpt strip_tac >> qpat_assum `!src id b sz. local_region (ctor_ce with ce_module := src) _ _ _ _ _ ==> _`
      (drule_then assume_tac) >>
    simp[loweringStateRelDefsTheory.regions_disjoint_def] >> disj1_tac >>
    irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `imm_len_mods mods` >> simp[]));

val linked_entry_immutable_sep_tac =
  qpat_assum `es0.scopes = [scope]` (fn scopes =>
    qpat_assum `ctor_ce.ce_is_ctor` (fn ctor =>
      qpat_assum `ALOOKUP es0.immutables cx.txn.target = SOME cells` (fn cells =>
        qpat_assum `ctor_ce.ce_vars = ce1.ce_vars` (fn vars =>
          simp[NoAsms, immutable_alloca_sep_mods_def, exprLoweringPropsTheory.immutable_alloca_sep_def,
               exprLoweringPropsTheory.immutable_decl_sep_def, scopes, ctor, cells, vars])))) >>
  map_every qx_gen_tac [`isrc`,`itops`] >> disch_tac >> conj_tac
  >- (map_every qx_gen_tac [`iname`,`ity`,`itv`,`ioff`] >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_assum `!src name off ty tv. _ ==> off + type_memory_size tv <= imm_len_mods mods`
        (drule_all_then assume_tac) >>
      qpat_assum `!src off width. off + width <= imm_len_mods mods ==>
          off + width <= actual.vs_alloca_next /\ _ /\ _`
        (qspecl_then [`isrc`,`ioff`,`type_memory_size itv`] mp_tac) >>
      (impl_tac >- FIRST_ASSUM ACCEPT_TAC) >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
      conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
      map_every qx_gen_tac [`lid`,`lsz`,`lentry`,`lp`,`lw`] >> strip_tac >>
      qpat_assum `!id b sz. local_region (ctor_ce with ce_module := isrc) [scope] actual id b sz ==> _`
        irule >> qexists_tac `lid` >>
      qpat_assum `ctor_ce.ce_vars = ce1.ce_vars` (fn vars =>
        simp[NoAsms, local_region_def, venomStateTheory.lookup_var_def, vars]) >>
      qexistsl_tac [`lentry`,`lp`] >> simp[]) >>
  map_every qx_gen_tac [`iname`,`itv`,`iv`,`ioff`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!src name off. FLOOKUP ctor_ce.ce_module_vars _ = _ ==> ?tv v. _`
    (drule_then (qx_choosel_then [`ctv`,`cv`] strip_assume_tac)) >>
  `ctv = itv` by
    (qpat_assum `FLOOKUP (get_source_immutables isrc cells) iname = SOME (itv,iv)`
       (fn cell => qpat_assum `FLOOKUP (get_source_immutables isrc cells) iname = SOME (ctv,cv)`
         (mp_tac o REWRITE_RULE [cell])) >> simp[NoAsms]) >>
  qpat_x_assum `ctv = itv` SUBST_ALL_TAC >>
  qpat_assum `!src off width. off + width <= imm_len_mods mods ==>
      off + width <= actual.vs_alloca_next /\ _ /\ _`
    (qspecl_then [`isrc`,`ioff`,`type_memory_size itv`] mp_tac) >>
  (impl_tac >- FIRST_ASSUM ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
  reverse conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
  rpt strip_tac >>
  qpat_assum `!aid b sz. FLOOKUP actual.vs_allocas aid = _ ==> loweringStateRelDefs$regions_disjoint _ _ b sz`
    (drule_then ACCEPT_TAC);

fun linked_entry_immutable_tac frame =
  linked_entry_immutable_goal_tac frame >-
    (map_every qx_gen_tac [`vi`,`actual`,`gs`] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     linked_entry_immutable_prefix_tac >> linked_entry_immutable_section_tac >>
     linked_entry_immutable_regions_tac >>
     PURE_REWRITE_TAC [bodyFullPostsModsTheory.immutable_frame_mods_def] >> conj_tac
     >- linked_entry_immutable_repr_tac >>
     linked_entry_immutable_decl_tac >> linked_entry_immutable_floor_tac >>
     linked_entry_immutable_sep_tac);
(* Payable entry preserves the source fields and both storage backends. *)
val linked_ctor_paid_fields_tac =
  Q.SUBGOAL_THEN
     `es0.scopes = [scope] /\
      es0.accounts = accounts_after_transfer tx am.accounts /\
      es0.tStorage = (initial_state am []).tStorage /\
      es0.immutables = am_c.immutables /\
      es0.logs = (initial_state am_c [scope]).logs /\
      es0.requests = (initial_state am_c [scope]).requests /\
      es0.pending_deletions = (initial_state am_c [scope]).pending_deletions`
     (mk_asm "linked_paid_fields") >-
     (`am_c.tStorage = am.tStorage` by
        (qpat_assum `am_c = am0 with immutables := _`
           (mp_tac o Q.AP_TERM `\m:abstract_machine. m.tStorage`) >>
         qpat_assum `am0 = _` (fn installed => simp[NoAsms, installed])) >>
      qpat_assum `es0 = unpaid with accounts := _` SUBST1_TAC >>
      qpat_assum `am_c.tStorage = am.tStorage` (fn ts =>
        simp[NoAsms, Abbr `unpaid`, vyperInterpreterTheory.initial_state_def, ts]));

fun linked_ctor_paid_backends_tac frame =
  Q.SUBGOAL_THEN
     `!gs b. get_storage cx
        (es0 with <|gas_obs := gs; outcomes := SOME (MAP SND (call_trace ^frame))|>) b =
        get_storage cx (initial_state am []) b`
     (mk_asm "linked_paid_backends") >-
     (gen_tac >> Cases >>
      asm "linked_paid_fields" (fn fields =>
        simp[NoAsms, vyperStorageBackendTheory.get_storage_def, fields,
             vyperInterpreterTheory.initial_state_def]) >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      rw[accounts_after_transfer_def, LET_THM,
         vfmStateTheory.update_account_def, vfmStateTheory.lookup_account_def,
         combinTheory.APPLY_UPDATE_THM] >>
      rpt IF_CASES_TAC >> gvs[]);

fun linked_ctor_entry_storage_tac frame =
  Q.SUBGOAL_THEN
     `!gs H. valid_horizon cx (initial_state am []) H
         (es0 with <|gas_obs := gs; outcomes := SOME (MAP SND (call_trace ^frame))|>).storage_trace ==>
       storage_well_formed_on cx
         (es0 with <|gas_obs := gs; outcomes := SOME (MAP SND (call_trace ^frame))|>) (FST H)`
     (mk_asm "linked_entry_storage") >-
     (rpt gen_tac >> rewrite_tac[valid_horizon_def] >> strip_tac >>
      qpat_assum `storage_well_formed_on cx (initial_state am []) _` mp_tac >>
      asm "linked_paid_backends" (fn backends =>
        simp[NoAsms, storage_well_formed_on_def, backends]));

(* Join the entry premises at the same registered endpoint and observation. *)
fun linked_registered_state_frame_goal_tac frame =
  let val source = ``es0 with <|gas_obs := gs; outcomes := SOME (MAP SND (call_trace ^frame))|>``
  in Q.SUBGOAL_THEN `!vi (actual:venom_state) gs.
    raw_variant fmp vi vs /\
    actual.vs_accounts = vi.vs_accounts /\
    actual.vs_transient = vi.vs_transient /\
    actual.vs_logs = vi.vs_logs /\
    actual.vs_requests = vi.vs_requests /\
    actual.vs_pending_deletions = vi.vs_pending_deletions /\
    actual.vs_outcomes = vi.vs_outcomes /\
    actual.vs_call_ctx = vi.vs_call_ctx /\
    actual.vs_tx_ctx = vi.vs_tx_ctx /\
    actual.vs_block_ctx = vi.vs_block_ctx /\
    actual.vs_code = vi.vs_code /\ actual.vs_labels = vi.vs_labels /\
    local_ptrs_rel fn ce1 [scope] actual /\
    eval_operand imm actual = SOME 0w /\
    (!p. p < imm_len_mods mods ==>
       mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 vi.vs_memory) /\
    imm_len_mods mods <= actual.vs_alloca_next /\
    (!aid b sz. FLOOKUP actual.vs_allocas aid = SOME (b,sz) ==> imm_len_mods mods <= b) /\
    (!id b sz. local_region ce1 [scope] actual id b sz ==> imm_len_mods mods <= b) /\
    alloca_inv actual /\
    (!site. alloca_frontier_inv_from (imm_len_mods mods) deploy_unit.cu_context fn site actual) /\
    fmp_room deploy_unit.cu_context fn actual /\
    (!inst n base sz. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
       inst.inst_operands = [Lit n] /\
       FLOOKUP actual.vs_allocas inst.inst_id = SOME (base,sz) ==> sz = w2n n) ==>
    !H. valid_horizon cx (initial_state am []) H (^source).storage_trace ==>
       stmt_state_rel H deploy_unit.cu_context fn ctor_ce cx ^source actual /\
       immutable_frame_mods fn ctor_ce cx ^source actual /\
       storage_well_formed_on cx ^source (FST H)` (mk_asm "linked_registered_state_frame")
  end;

val linked_registered_active_module_tac =
  `ALOOKUP ctor_ce.ce_modules NONE = SOME tops'` by
    (qpat_assum `contract_inv mods exps deploy_unit.cu_context ctor_ce cx`
       (fn inv => rewrite_tac[MATCH_MP bodyInvCodePropsTheory.contract_inv_cenv_modules inv]) >>
     qpat_assum `module_body_inv mods NONE tops' ctor_ce cx`
       (ACCEPT_TAC o cj 1 o PURE_REWRITE_RULE [module_body_inv_def])) >>
  `ctor_ce with ce_module := NONE = ctor_ce` by
    (qpat_assum `ctor_ce.ce_module = NONE` (fn src =>
       simp[NoAsms, compile_env_component_equality, src])) >>
  asm "registered_immutable_frame"
    (fn th => let val parts = PURE_REWRITE_RULE [bodyFullPostsModsTheory.immutable_frame_mods_def,
                           immutables_rel_mods_def, immutable_alloca_sep_mods_def] th
              in qpat_assum `ALOOKUP ctor_ce.ce_modules NONE = SOME tops'`
                   (fn lookup =>
                      qpat_assum `ctor_ce.ce_module = NONE` (fn src =>
                        assume_tac (PURE_REWRITE_RULE [GSYM src] (MATCH_MP (cj 1 parts) lookup))) >>
                      qpat_assum `ctor_ce with ce_module := NONE = ctor_ce` (fn env =>
                        assume_tac (PURE_REWRITE_RULE [env] (MATCH_MP (cj 2 parts) lookup)))) end);

fun linked_registered_state_frame_tac frame =
  linked_registered_state_frame_goal_tac frame >-
    (map_every qx_gen_tac [`vi`,`actual`,`gs`] >>
     disch_then (map_every assume_tac o CONJUNCTS) >> qx_gen_tac `H` >> disch_tac >>
     asm "linked_paid_fields" (map_every assume_tac o CONJUNCTS) >>
     asm "linked_entry_immutable" (qspecl_then [`vi`,`actual`,`gs`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
     disch_then (mk_asm "registered_immutable_frame") >>
     asm "linked_entry_machine_parts" (qspecl_then [`vi`,`actual`,`gs`,`H`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     linked_registered_active_module_tac >> conj_tac
     >- (pure_rewrite_tac [exprLoweringPropsTheory.stmt_state_rel_def,
                          loweringStateRelDefsTheory.state_rel_def] >>
         rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     conj_tac >- asm "registered_immutable_frame" ACCEPT_TAC >>
     asm "linked_entry_storage" (qspecl_then [`gs`,`H`] mp_tac) >>
     (impl_tac >- FIRST_ASSUM ACCEPT_TAC) >> disch_then ACCEPT_TAC);

(* Pointer checking from the laid-out zero-capacity constructor tail. *)
fun linked_zero_epilogue_opcode_eq opc =
  valOf (List.find
    (fn th => aconv (rhs (fst (dest_imp (snd (strip_forall (concl th)))))) opc)
    (CONJUNCTS step_inst_base_opcode_eqs));

val linked_ctor_zero_epilogue_ptr_goal =
  sg `!body_ce D (H : (bool # bytes32 # type_value) list # num list) ee s G tn bb id buf.
     imm_len_mods mods = 0 /\ LENGTH runtime_bc < dimword (:256) /\
     stmt_state_rel H deploy_unit.cu_context fn body_ce cx ee s /\
     ghost_inv_at_mods D (imm_len_mods mods) NONE body_ce cx ee G tn s /\
     body_ce.ce_is_ctor /\
     lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
     MEM (mk_inst id ALLOCA [Lit (n2w (LENGTH runtime_bc))] [buf]) (fn_insts fn) /\
     get_instruction bb s.vs_inst_idx =
       SOME (mk_inst id ALLOCA [Lit (n2w (LENGTH runtime_bc))] [buf]) /\
     get_instruction bb (SUC s.vs_inst_idx) =
       SOME (mk_inst (id + 1) CODECOPY
         [Var buf; Label "runtime_begin"; Lit (n2w (LENGTH runtime_bc))] []) /\
     get_instruction bb (SUC (SUC s.vs_inst_idx)) =
       SOME (mk_inst (id + 2) RETURN [Var buf; Lit (n2w (LENGTH runtime_bc))] []) ==>
     !fuel. ptr_safe_run D (imm_len_mods mods) fuel deploy_unit.cu_context fn [] G tn s`;

val linked_ctor_zero_epilogue_setup_tac =
   POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >>
   disch_then (map_every assume_tac o CONJUNCTS) >> gen_tac >>
   qpat_assum `imm_len_mods mods = 0` SUBST1_TAC >>
   qabbrev_tac `ctx0 = deploy_unit.cu_context` >>
   qabbrev_tac `rt = LENGTH runtime_bc` >>
   qabbrev_tac `i0 = mk_inst id ALLOCA [Lit (n2w rt)] [buf]` >>
   qabbrev_tac `i1 = mk_inst (id + 1) CODECOPY [Var buf; Label "runtime_begin"; Lit (n2w rt)] []` >>
   qabbrev_tac `i2 = mk_inst (id + 2) RETURN [Var buf; Lit (n2w rt)] []` >>
   `alloca_room ctx0 fn s` by (drule stateRelProjTheory.stmt_state_rel_alloca_room >> simp[]) >>
   `alloca_inv s` by (drule stateRelProjTheory.stmt_state_rel_local_ptrs_alloca >> simp[]) >>
   `fmp_room ctx0 fn s` by (drule stateRelProjTheory.stmt_state_rel_fmp_room >> simp[]) >>
   `ctx_has_dalloca ctx0 ==> allocas_below_fmp s` by
     (drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> simp[]) >>
   `bodyPtrDefs$stor_taint_ok_at D tn s` by
     qpat_assum `ghost_inv_at_mods D _ _ _ _ _ _ _ s`
       (ACCEPT_TAC o cj 4 o PURE_REWRITE_RULE [bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def]) >>
   `?cpos. FLOOKUP s.vs_labels "runtime_begin" = SOME cpos` by
     (drule stateRelProjTheory.stmt_state_rel_immutable_base_zero >>
      simp[exprLoweringPropsTheory.immutable_base_zero_alt, optionTheory.IS_SOME_EXISTS]);

val linked_ctor_zero_epilogue_alloc_tac =
   `i0.inst_opcode = ALLOCA /\ i0.inst_operands = [Lit (n2w rt)] /\
    i0.inst_outputs = [buf] /\ i0.inst_id = id` by simp[Abbr `i0`, mk_inst_def] >>
   `!b sz. FLOOKUP s.vs_allocas i0.inst_id = SOME (b,sz) ==> sz = w2n (n2w rt : bytes32)` by
     (rpt strip_tac >> drule stateRelProjTheory.stmt_state_rel_alloca_size >>
      disch_then (qspecl_then [`i0`, `n2w rt`, `b`, `sz`] mp_tac) >> simp[]) >>
   drule_all allocaSiteResourceTheory.alloca_site_execute >> strip_tac >>
   qpat_x_assum `!b sz. FLOOKUP s.vs_allocas i0.inst_id = _ ==> _` kall_tac >>
   qpat_x_assum `!aid p sz. FLOOKUP s.vs_allocas aid = _ ==> FLOOKUP t.vs_allocas aid = _` kall_tac;

val linked_ctor_zero_epilogue_alloc_step_tac =
   `w2n (n2w rt : bytes32) = rt` by simp[] >>
   `b < dimword (:256)` by
     (irule arithmeticTheory.LESS_EQ_LESS_TRANS >> qexists_tac `t.vs_alloca_next` >>
      conj_tac >- (drule_at Any exprLoweringPropsTheory.alloca_room_next_lt >> simp[]) >>
      qpat_assum `b + _ <= t.vs_alloca_next` mp_tac >> simp[] >> decide_tac) >>
   `w2n (n2w b : bytes32) = b` by simp[];

val linked_ctor_zero_epilogue_alloc_exec_tac =
   `step_inst fuel ctx0 i0 s = OK t` by
     (qpat_assum `i0.inst_opcode = ALLOCA` (fn th =>
        simp[NoAsms, th, step_inst_non_invoke,
             MATCH_MP (linked_zero_epilogue_opcode_eq ``ALLOCA``) th]) >>
      qpat_assum `i0.inst_operands = _` (fn th => simp[NoAsms, th, eval_operand_def]) >>
      FIRST_ASSUM ACCEPT_TAC);

val linked_ctor_zero_epilogue_alloc_fmp_tac =
   `ctx_has_dalloca ctx0 ==> allocas_below_fmp t` by
     (`fmp_room ctx0 fn t` by (drule_all exprLoweringPropsTheory.fmp_room_exec_alloca >> simp[]) >>
      strip_tac >>
      irule groupedRejectCutAllocationPropsTheory.allocas_below_fmp_from_frontier >>
      conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
      qpat_assum `fmp_room ctx0 fn t`
        (mp_tac o PURE_REWRITE_RULE [exprLoweringPropsTheory.fmp_room_def]) >>
      simp[] >> decide_tac);

val linked_ctor_zero_epilogue_alloc_frame_tac =
   `t.vs_inst_idx = s.vs_inst_idx /\ t.vs_labels = s.vs_labels /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_immutables = s.vs_immutables` by
      (qpat_assum `exec_alloca i0 s _ = OK t` mp_tac >>
       pure_rewrite_tac [exec_alloca_def] >> simp[] >>
       Cases_on `FLOOKUP s.vs_allocas id`
       >- (simp[] >> strip_tac >> gvs[update_var_def]) >>
       rename1 `FLOOKUP s.vs_allocas id = SOME entry` >> PairCases_on `entry` >>
       simp[] >> strip_tac >> gvs[update_var_def]) >>
   `ptr_safe_step D 0 fuel ctx0 fn [] G tn i0 s` by
     (simp[Abbr `i0`, ctorDeployMemoryRunPtrPrefixStepsTheory.prefix_alloca_ptr_step,
           allocas_from_def]) >>
   `~is_terminator i0.inst_opcode /\ i0.inst_opcode <> INVOKE` by
     simp[is_terminator_def] >>
   pure_rewrite_tac[ptr_safe_run_def] >>
   qpat_assum `lookup_block s.vs_current_bb _ = _` (fn th => simp[NoAsms, th]) >>
   drule_all ptr_safe_block_step >> disch_then (fn th => PURE_REWRITE_TAC[th]) >>
   conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
   qabbrev_tac `s1 = t with vs_inst_idx := SUC s.vs_inst_idx` >>
   qabbrev_tac `G1 = G |+ (buf,(b,rt))` >>
   qabbrev_tac `tn1 = step_taint i0 s t tn` >>
   `ghost_step fuel ctx0 [] G tn i0 s = (G1,tn1)` by
     (drule_all ghost_step_non_invoke >>
      simp[Abbr `G1`, Abbr `tn1`, step_prov_def, out_prov_def, set_prov_def]) >>
   qpat_assum `ghost_step _ _ _ G tn i0 s = _` (fn th => PURE_REWRITE_TAC[th, pairTheory.FST, pairTheory.SND]) >>
   `op_taint tn1 (Var buf) = {} /\
    tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm` by
     simp[Abbr `tn1`, step_taint_def, out_taint_def, set_var_taint_def,
          store_taint_def, adopt_reset_def, imm_taint_def, op_taint_def,
          finite_mapTheory.FLOOKUP_UPDATE, eval_operand_def];

val linked_ctor_zero_epilogue_copy_tac =
   `i1.inst_opcode = CODECOPY /\ i1.inst_outputs = [] /\
    i1.inst_operands = [Var buf; Label "runtime_begin"; Lit (n2w rt)]` by
     simp[Abbr `i1`, mk_inst_def] >>
   `eval_operand (Var buf) s1 = SOME (n2w b) /\
    eval_operand (Label "runtime_begin") s1 = SOME cpos /\
    eval_operand (Lit (n2w rt)) s1 = SOME (n2w rt)` by
     (qpat_assum `lookup_var buf t = _`
        (assume_tac o PURE_REWRITE_RULE [lookup_var_def]) >>
      simp[Abbr `s1`, eval_operand_def, lookup_var_def]) >>
   qabbrev_tac `t2 = write_memory_with_expansion b
     (TAKE rt (DROP (w2n cpos) s1.vs_code ++ REPLICATE rt 0w)) s1` >>
   `step_inst_base i1 s1 = OK t2` by
     (simp[linked_zero_epilogue_opcode_eq ``CODECOPY``, Abbr `t2`] >> simp[eval_operand_def]) >>
   `step_inst fuel ctx0 i1 s1 = OK t2 /\ ~is_terminator i1.inst_opcode /\
    i1.inst_opcode <> INVOKE` by simp[step_inst_non_invoke, is_terminator_def] >>
   qabbrev_tac `tn2 = tn1 with t_mem := tn1.t_mem DIFF {i | b <= i /\ i < b + rt}` >>
   `step_prov [] G1 i1 t2 = G1 /\ step_taint i1 s1 t2 tn1 = tn2` by
     (drule_all lowerDloadPtrExpansionTransportTheory.dload_codecopy_state_ghost >>
      simp[Abbr `tn2`]) >>
   `get_instruction bb s1.vs_inst_idx = SOME i1` by simp[Abbr `s1`] >>
   `FLOOKUP G1 buf = SOME (b,rt)` by simp[Abbr `G1`, finite_mapTheory.FLOOKUP_UPDATE] >>
   `access_ok 0 G1 fn i1 s1 /\ taint_ok fn tn1 i1 s1` by
     (irule lowerDloadPtrExpansionTheory.dload_codecopy_safe >>
      simp[] >> simp[op_taint_def]) >>
   `t2.vs_requests = s1.vs_requests` by simp[Abbr `t2`, write_memory_with_expansion_def] >>
   `ctx_has_dalloca ctx0 ==> allocas_below_fmp s1` by
     (qpat_assum `ctx_has_dalloca ctx0 ==> allocas_below_fmp t` mp_tac >>
      simp[Abbr `s1`, allocas_below_fmp_def]) >>
   `ptr_safe_step D 0 fuel ctx0 fn [] G1 tn1 i1 s1` by
     simp[ptr_safe_step_def, ptr_inst_ok_def, allocas_from_def] >>
   qpat_x_assum `get_instruction bb s.vs_inst_idx = SOME i0` kall_tac >>
   drule_all ptr_safe_block_step >> disch_then (fn th => PURE_REWRITE_TAC[th]) >>
   conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
   qabbrev_tac `s2 = t2 with vs_inst_idx := SUC s1.vs_inst_idx` >>
   `ghost_step fuel ctx0 [] G1 tn1 i1 s1 = (G1,tn2)` by
     (drule_all ghost_step_non_invoke >> simp[Abbr `tn2`]) >>
   qpat_assum `ghost_step _ _ _ G1 tn1 i1 s1 = _`
     (fn th => PURE_REWRITE_TAC[th, pairTheory.FST, pairTheory.SND]);

val linked_ctor_zero_epilogue_return_tac =
   `get_instruction bb s2.vs_inst_idx = SOME i2` by simp[Abbr `s2`, Abbr `s1`] >>
   `lookup_var buf s2 = SOME (n2w b)` by
     (qpat_assum `lookup_var buf t = _`
        (assume_tac o PURE_REWRITE_RULE [lookup_var_def]) >>
      simp[Abbr `s2`, Abbr `t2`, Abbr `s1`, write_memory_with_expansion_def, lookup_var_def]) >>
   qabbrev_tac `sh = halt_state (set_returndata
     (TAKE rt (DROP b s2.vs_memory ++ REPLICATE rt 0w)) s2)` >>
   `step_inst fuel ctx0 i2 s2 = Halt sh` by
     simp[Abbr `i2`, Abbr `sh`, step_inst_non_invoke, mk_inst_def,
          linked_zero_epilogue_opcode_eq ``RETURN``, eval_operand_def] >>
   `ret_taint tn2 i2 s2 = {}` by
     (simp[Abbr `i2`, Abbr `tn2`, ret_taint_def, mk_inst_def, eval_operand_def,
           pred_setTheory.EXTENSION] >> gen_tac >> decide_tac) >>
   `(allocas_below_fmp s2 <=> allocas_below_fmp s1)` by
     simp[Abbr `s2`, Abbr `t2`, write_memory_with_expansion_def,
          allocas_below_fmp_def] >>
   `ctx_has_dalloca ctx0 ==> allocas_below_fmp s2` by asm_rewrite_tac[] >>
   `bodyPtrDefs$stor_taint_ok_at D (step_taint i2 s2 sh tn2) sh` by
     (qpat_x_assum `bodyPtrDefs$stor_taint_ok_at D tn s` mp_tac >>
      simp[bodyPtrDefsTheory.stor_taint_ok_at_def, Abbr `i2`, Abbr `tn2`,
           step_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
           mk_inst_def, Abbr `sh`, halt_state_def, set_returndata_def,
           Abbr `s2`, Abbr `t2`, Abbr `s1`, write_memory_with_expansion_def]) >>
   `op_taint tn2 (Var buf) = {}` by
     (qpat_x_assum `op_taint tn1 (Var buf) = _` mp_tac >> simp[Abbr `tn2`, op_taint_def]) >>
   `ptr_safe_step D 0 fuel ctx0 fn [] G1 tn2 i2 s2` by
     (qpat_assum `bodyPtrDefs$stor_taint_ok_at D (step_taint i2 s2 sh tn2) sh`
        (strip_assume_tac o PURE_REWRITE_RULE [bodyPtrDefsTheory.stor_taint_ok_at_def]) >>
      simp[ptr_safe_step_def, ptr_inst_ok_def, allocas_from_def] >>
      simp[Abbr `i2`, mk_inst_def, access_ok_def, taint_ok_def,
           source_memory_read_ranges_def, source_memory_write_ranges_def,
           memory_range_of_operands_def, memLocDefsTheory.mem_read_ops_def, eval_operand_def] >>
      qx_gen_tac `aop` >> Cases_on `aop = Var buf` >> simp[] >>
      Cases_on `aop = Lit (n2w rt)` >> simp[op_taint_def]) >>
   simp[Once ptr_safe_block_def];

(* Return NONE adds one unmarked jump before the constructor epilogue.
   The epilogue's common halt and ghosts are supplied by the antecedent. *)
val linked_ctor_return_bad_storage_tac =
  rewrite_tac[gasOutcomeFullModsTheory.gas_outcome_full_mods_def] >>
  qexists_tac `[]` >> disj1_tac >> conj_tac
  >- simp[gasStorageTheory.gas_bad_storage_at_def, gasSummaryTheory.gas_explicit_def] >>
  qexistsl_tac [`ARB`, `fn`, `[]`, `G0`, `tn0`, `s0`] >>
  simp[gasOutcomeFullTheory.gas_origin_ptr_focus_nil];

val linked_ctor_return_jump_entry_tac =
  `cenv'.ce_is_ctor /\ cenv'.ce_return_pc = NONE /\
   cenv'.ce_ctor_exit_label = SOME exit_lbl` by
    (qpat_assum `same_frame ctor_ce cenv'`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [bodySimTheory.same_frame_def]) >>
     simp[NoAsms, compile_env_component_equality] >> strip_tac >> simp[]) >>
  Q.SUBGOAL_THEN `emit_inst JMP [Label exit_lbl] [] sa = ((),sb)` assume_tac;

val linked_ctor_return_jmp_code_tac =
    qpat_assum `stmt_env cenv' lctx NoneT (Return NONE) sa = _` mp_tac >>
     qpat_assum `cenv'.ce_return_pc = NONE` (fn rpc =>
       qpat_assum `cenv'.ce_ctor_exit_label = SOME exit_lbl` (fn xlbl =>
         simp[NoAsms, rpc, xlbl, loweringPostsTheory.stmt_env_def,
              stmtLoweringTheory.declare_stmt_local_def, Once stmtLoweringTheory.compile_stmt_def,
              comp_ignore_bind_def, comp_bind_def, comp_return_def])) >>
     Cases_on `emit_inst JMP [Label exit_lbl] [] sa` >> simp[NoAsms];

val linked_ctor_return_landing_tac =
  qabbrev_tac `sx = jump_to exit_lbl s0` >>
  `~sx.vs_halted /\ sx.vs_current_bb = exit_lbl /\ sx.vs_inst_idx = 0` by
    simp[Abbr `sx`, jump_to_def] >>
  Q.SUBGOAL_THEN `(ctx_has_dalloca deploy_unit.cu_context ==> allocas_below_fmp sx)` assume_tac;

val linked_ctor_return_alloca_tac =
  simp[NoAsms, Abbr `sx`, allocas_below_fmp_def, jump_to_def] >>
  qpat_assum `ctx_has_dalloca _ ==> allocas_below_fmp s0`
    (ACCEPT_TAC o REWRITE_RULE [allocas_below_fmp_def]);

val linked_ctor_return_inv_goal_tac =
  Q.SUBGOAL_THEN `!H. valid_horizon cx st0 H src.storage_trace ==>
     stmt_state_rel H deploy_unit.cu_context fn cenv' cx src sx /\
     immutable_frame_mods fn cenv' cx src sx /\
     ghost_inv_at_mods (linked_ret_DF H) (imm_len_mods mods) NONE cenv' cx src G0 tn0 sx` assume_tac;

val linked_ctor_return_inv_tac =
    gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     conj_tac
     >- (qpat_assum `stmt_state_rel _ _ _ _ _ _ s0` mp_tac >>
         simp[NoAsms, Abbr `sx`, exprLoweringPropsTheory.stmt_state_rel_jump_to]) >>
     conj_tac
     >- (`immutable_frame_mods fn cenv' cx src sx = immutable_frame_mods fn cenv' cx src s0` by
           simp[NoAsms, Abbr `sx`, jump_to_def, bodyFullPostsModsTheory.immutable_frame_mods_def,
                immutables_rel_mods_def, immutable_alloca_sep_mods_def, immutables_rel_def,
                exprLoweringPropsTheory.immutable_alloca_sep_def, local_region_def, lookup_var_def] >>
         simp[]) >>
     rename1 `valid_horizon cx st0 H src.storage_trace` >>
     `ghost_inv_at_mods (linked_ret_DF H) (imm_len_mods mods) NONE cenv' cx src G0 tn0 sx =
      ghost_inv_at_mods (linked_ret_DF H) (imm_len_mods mods) NONE cenv' cx src G0 tn0 s0` by
       simp[NoAsms, Abbr `sx`, jump_to_def, bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def,
            bodyPtrDefsTheory.ptr_covers_def, bodyPtrDefsTheory.stor_taint_ok_at_def,
            lookup_var_def, allocas_from_def, bodyPtrDefsTheory.return_buf_ptr_def] >>
     simp[];

val linked_ctor_return_fields_goal_tac =
  Q.SUBGOAL_THEN
    `ctor_ce.ce_is_ctor /\ ctor_ce.ce_return_pc = NONE /\
     ctor_ce.ce_ctor_exit_label = SOME exit_lbl` assume_tac;

val linked_ctor_return_fields_tac =
  qpat_assum `!pos ce off size cs ce' cs'. _ ==> _`
    (drule_then (fn reg =>
      qpat_assum `Abbrev (ctor_ce = _)`
        (PURE_REWRITE_TAC o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
      PURE_ONCE_REWRITE_TAC [reg] >>
      qpat_assum `ce_before_registration = _` (fn before_reg =>
        qpat_assum `cpkg0 = _` (fn pkg =>
          simp[NoAsms, before_reg, pkg])))) >>
  qpat_assum `Abbrev (ce_base = _)`
    (PURE_REWRITE_TAC o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  simp[NoAsms, build_compile_env_unit_def, LET_THM, pairTheory.ELIM_UNCURRY];

val linked_ctor_return_fragment_tac =
  qabbrev_tac `linked_ret_DF = \(H : (bool # bytes32 # type_value) list # num list).
     <|d_stor := (\a st. if a = tx.target then {(k,b) | storage_dead H F st (w2n k) b} else {});
       d_trans := (\a st. if a = tx.target then {(k,b) | storage_dead H T st (w2n k) b} else {});
       d_imm := K UNIV;
       d_ret := (\r. {i | LENGTH runtime_bc <= i /\
          imm_section_dead_mods ctor_ce (DROP (LENGTH runtime_bc) r) (i - LENGTH runtime_bc)})|>` >>
  Q.SUBGOAL_THEN `(!body_ce st0 src sx G0 tn0.
    same_frame ctor_ce body_ce /\
    ~sx.vs_halted /\ sx.vs_current_bb = exit_lbl /\ sx.vs_inst_idx = 0 /\
    (ctx_has_dalloca deploy_unit.cu_context ==> allocas_below_fmp sx) /\
    storage_trace_domain cx st0 src.storage_trace /\
    (!H. valid_horizon cx st0 H src.storage_trace ==>
       stmt_state_rel H deploy_unit.cu_context fn body_ce cx src sx /\
       immutable_frame_mods fn body_ce cx src sx /\
       ghost_inv_at_mods (linked_ret_DF H) (imm_len_mods mods) NONE body_ce cx src G0 tn0 sx) ==>
    ?final G' tn' codepos.
      gas_path_mem deploy_unit.cu_context fn sx 0 (Halt final) /\
      final.vs_halted /\ FLOOKUP sx.vs_labels "runtime_begin" = SOME codepos /\
      final.vs_returndata =
        TAKE (LENGTH runtime_bc) (DROP (w2n codepos) sx.vs_code ++ REPLICATE (LENGTH runtime_bc) 0w) ++
        TAKE (imm_len_mods mods) (sx.vs_memory ++ REPLICATE (imm_len_mods mods) 0w) /\
      final.vs_accounts = sx.vs_accounts /\ final.vs_transient = sx.vs_transient /\
      final.vs_logs = sx.vs_logs /\ final.vs_outcomes = sx.vs_outcomes /\
      final.vs_requests = sx.vs_requests /\ final.vs_pending_deletions = sx.vs_pending_deletions /\
      final.vs_call_ctx = sx.vs_call_ctx /\ final.vs_tx_ctx = sx.vs_tx_ctx /\
      final.vs_block_ctx = sx.vs_block_ctx /\ final.vs_data_section = sx.vs_data_section /\
      final.vs_immutables = sx.vs_immutables /\ final.vs_code = sx.vs_code /\ final.vs_labels = sx.vs_labels /\
      (ctx_has_dalloca deploy_unit.cu_context ==> allocas_below_fmp final) /\
      !H. valid_horizon cx st0 H src.storage_trace ==>
        gas_origin_ptr_path (linked_ret_DF H,imm_len_mods mods,
          gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context,deploy_unit.cu_context,fn,[])
          (sx,G0,tn0) [] (Halt final,G',tn')) ==>
   frame_ret_ok_full_mods mods
      (linked_ret_DF,imm_len_mods mods,NONE,deploy_unit.cu_context,shadow_unit.cu_context,[],fn,shadow_fn)
      cx (\H v ee gt r. v = NoneV /\ ?before final codepos.
        r = Halt final /\ final.vs_halted /\
        state_rel H fn ctor_ce cx ee before /\
        immutables_rel_mods ctor_ce cx.txn.target T ee before /\
        FLOOKUP before.vs_labels "runtime_begin" = SOME codepos /\
        final.vs_returndata =
          TAKE (LENGTH runtime_bc) (DROP (w2n codepos) before.vs_code ++ REPLICATE (LENGTH runtime_bc) 0w) ++
          TAKE (imm_len_mods mods) (before.vs_memory ++ REPLICATE (imm_len_mods mods) 0w) /\
        final.vs_accounts = before.vs_accounts /\ final.vs_transient = before.vs_transient /\
        final.vs_logs = before.vs_logs /\ final.vs_outcomes = before.vs_outcomes /\
        final.vs_requests = before.vs_requests /\ final.vs_pending_deletions = before.vs_pending_deletions /\
        final.vs_call_ctx = before.vs_call_ctx /\ final.vs_tx_ctx = before.vs_tx_ctx /\
        final.vs_block_ctx = before.vs_block_ctx /\ final.vs_data_section = before.vs_data_section /\
        final.vs_immutables = before.vs_immutables /\ final.vs_code = before.vs_code /\
        final.vs_labels = before.vs_labels) ctor_ce NoneT` assume_tac;

val linked_ctor_return_open_fragment_tac =
    qpat_assum `ctor_ce.ce_is_ctor /\ _`
      (fn fields => POP_ASSUM_LIST (K ALL_TAC) >> strip_assume_tac fields) >>
    disch_tac >> pure_rewrite_tac[bodyFullPostsModsTheory.frame_ret_ok_full_mods_def] >>
     map_every qx_gen_tac [`cenv'`,`env`,`lctx`,`eo`,`src`] >> strip_tac >>
     reverse (Cases_on `eo`)
     >- (qpat_x_assum `IS_SOME (type_stmt _ _ (Return (SOME _)))` mp_tac >>
         simp[vyperTypeSystemTheory.type_stmt_def]) >>
     pure_rewrite_tac[optionTheory.OPTION_MAP_DEF,bodyFullPostsModsTheory.stmt_frag_full_mods_def] >>
     map_every qx_gen_tac [`st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,`s0`,`G0`,`tn0`,`ce_out`] >>
     strip_tac >>
     `!tail. eval_stmt cx (Return NONE) (src with gas_obs := tail) =
              (INR (ReturnException NoneV), src with gas_obs := tail)` by
       simp[Once evaluate_def, vyperStateTheory.raise_def] >>
     reverse (Cases_on `storage_trace_domain cx st0 src.storage_trace`)
     >- linked_ctor_return_bad_storage_tac;

val linked_ctor_return_epilogue_tac =
  qpat_assum `!body_ce st0 src sx G0 tn0. _ ==> ?final G' tn' codepos. _`
    (drule_all_then (qx_choosel_then [`final`,`G'`,`tn'`,`codepos`] strip_assume_tac));

val linked_ctor_return_outcome_tac =
  pure_rewrite_tac[gasOutcomeFullModsTheory.gas_outcome_full_mods_def] >>
  qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INR (ReturnException NoneV)`,`src`,`Halt final`,`G'`,`tn'`] >>
  conj_tac >- simp[gasSummaryTheory.gas_explicit_def] >>
  conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
  qx_gen_tac `H` >> disch_tac;

val linked_ctor_return_prepend_tac =
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ s0 /\ _`
    (drule_then strip_assume_tac) >>
  `allocas_from (imm_len_mods mods) s0` by
    (qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ s0`
       (mp_tac o REWRITE_RULE [bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def]) >>
     strip_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  Q.SUBGOAL_THEN `gas_origin_ptr_path (linked_ret_DF H,imm_len_mods mods,
      gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context,deploy_unit.cu_context,fn,[])
      (s0,G0,tn0) [] (OK sx,G0,tn0)` assume_tac;

val linked_ctor_return_jmp_path_tac =
  simp[NoAsms, Abbr `sx`] >> irule fragGasEmitCtrlTheory.emit_jmp_origin_ptr >>
  reverse (rpt conj_tac)
  >- (qexistsl_tac [`sa`,`sb`] >> rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  FIRST_ASSUM ACCEPT_TAC;

val linked_ctor_return_append_tac =
  drule fragGasOriginPtrTheory.gas_origin_ptr_path_append >>
  simp[] >> disch_then irule >> FIRST_ASSUM ACCEPT_TAC;

val linked_ctor_return_post_tac =
  disj2_tac >>
  simp[exit_result_def, bodyPtrDefsTheory.stmt_exit_ptr_def,
       exprSimDefsTheory.halt_exit_def, exprSimDefsTheory.expr_exit_def] >>
  qx_gen_tac `tail` >> qexistsl_tac [`sx`,`codepos`] >> simp[] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ sx /\ _`
    (drule_then strip_assume_tac) >>
  conj_tac
  >- (`state_rel H fn cenv' cx src sx` by
        (qpat_assum `stmt_state_rel _ _ _ _ _ _ sx`
           (mp_tac o REWRITE_RULE [exprLoweringPropsTheory.stmt_state_rel_def]) >>
         strip_tac >> FIRST_ASSUM ACCEPT_TAC) >>
      `state_rel H fn ctor_ce cx (src with scopes := []) sx` by
        (irule stmtSimReturnTheory.constructor_exit_state_rel >>
         qexists_tac `cenv'` >> simp[]) >>
      `state_rel H fn ctor_ce cx ((src with scopes := []) with gas_obs := tail) sx` by
        simp[state_rel_gas_obs] >>
      pop_assum (mp_tac o SIMP_RULE (srw_ss()) [vyperStateTheory.evaluation_state_fupdcanon]) >>
      simp[NoAsms]) >>
  `cenv'.ce_modules = ctor_ce.ce_modules /\ cenv'.ce_module_vars = ctor_ce.ce_module_vars` by
    (qpat_assum `same_frame ctor_ce cenv'`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [bodySimTheory.same_frame_def]) >>
     simp[NoAsms, compile_env_component_equality] >> strip_tac >> simp[]) >>
  qpat_assum `immutable_frame_mods _ _ _ _ sx`
    (mp_tac o CONJUNCT1 o REWRITE_RULE [bodyFullPostsModsTheory.immutable_frame_mods_def]) >>
  simp[immutables_rel_mods_def, immutables_rel_def];

(* Static registration inputs shared by every raw variant. *)
val linked_deploy_registration_inputs_tac =
  `deploy_unit.cu_context.ctx_entry = SOME "__deploy"` by
    (drule_all run_deploy_lowering_ctor_trace >> strip_tac >>
     qpat_assum `deploy_unit.cu_context = install_immutable_reservation _ _` SUBST1_TAC >>
     qpat_assum `extract_context_with_internals "__deploy" _ _ = SOME (_,_)` mp_tac >>
     simp[NoAsms, extract_context_with_internals_def, AllCaseEqs()] >>
     rpt strip_tac >>
     FIRST [qpat_assum `mk_venom_context _ _ = _` (SUBST1_TAC o SYM),
            qpat_assum `_ = mk_venom_context _ _` SUBST1_TAC] >>
     simp[NoAsms, install_immutable_reservation_def, mk_venom_context_def]) >>
  `ctx_wf deploy_unit.cu_context /\ wf_invoke_targets deploy_unit.cu_context /\
   reachable_call_graph_acyclic deploy_unit.cu_context` by
    (drule lowering_context_ok_integrity >> strip_tac >>
     drule lowering_context_ok_bridge >> strip_tac >>
     simp[venomWfTheory.ctx_wf_def, venomWfTheory.ctx_has_entry_def,
          reachable_call_graph_acyclic_def, ctx_fn_names_def] >>
     drule_then ACCEPT_TAC lookup_function_mem) >>
  `!bb. lookup_block st2.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0` by
    (gen_tac >> strip_tac >> drule_all_then ACCEPT_TAC acceptedContextPhiTheory.lowering_context_ok_block_phi) >>
  `imm_len_mods mods + unit_alloca_budget deploy_unit.cu_context < dimword (:256)` by
    (qpat_assum `imm_len_mods mods + _ + _ <= w2n fmp` mp_tac >>
     qpat_assum `w2n fmp < 2 ** 254` mp_tac >>
     simp[NoAsms, wordsTheory.dimword_def, venomLayoutTheory.dimindex_256] >> decide_tac) >>
  `sfields_tenv_consistent (make_struct_fields_map_mods mods) (type_env_all_modules mods)` by
    (irule make_struct_fields_map_mods_consistent >> qexists_tac `T` >> first_assum ACCEPT_TAC) >>
  `LENGTH args_bytes < 2 ** 128` by
    (mp_tac (Q.INST [`unit` |-> `deploy_unit`, `bs` |-> `args_bytes`]
       constructor_args_size_bounded_mods) >> asm_rewrite_tac[]) >>
  `LENGTH args_bytes < dimword (:256)` by
    (irule lt_dimword_256 >> qexists_tac `128` >> simp[]) >>
  `args_bytes = enc (Tuple (vyper_to_abi_types (type_env_all_modules mods)
      (MAP SND src_args))) (ListV avs)` by simp[];

val linked_ctor_registration_map_tac =
  `compile_register_constructor_args ce_before_registration
     (build_positional_args ce_before_registration src_args) 0 0 st1 = (ce1,st2)` by
    (qpat_assum `cpkg1 = build_positional_args _ _` (fn args =>
       qpat_assum `ce_before_registration = cpkg0 with ce_imm_alloca := _` (fn env =>
         qpat_assum `compile_register_constructor_args _ cpkg1 0 0 st1 = _`
           (ACCEPT_TAC o PURE_REWRITE_RULE [GSYM env,args])))) >>
  `!id p sz. FLOOKUP ce_before_registration.ce_vars id <> SOME (PtrVar (Var p) sz)` by
    (qpat_assum `set_constructor_package_target _ (package_constructor_unit _ _ _ (_,_,_,_,_,_,_,_)) = _`
       (strip_assume_tac o SIMP_RULE (srw_ss())
         [set_constructor_package_target_def, update_cenv_nonreentrant_def] o
        SIMP_RULE (srw_ss()) [package_constructor_unit_def, LET_THM]) >>
     qpat_assum `ce_before_registration = cpkg0 with ce_imm_alloca := _` SUBST1_TAC >>
     qpat_assum `_ = cpkg0` (SUBST1_TAC o SYM) >>
     simp_tac (srw_ss()) [] >>
     rpt strip_tac >>
     drule (CONJUNCT1 compileUnitPackageShapeTheory.build_compile_env_unit_static_locations) >>
     simp[loweringShapePropsTheory.static_loc_def]) >>
  `!s id b sz. ~local_region ce_before_registration [scope] s id b sz` by
    (qpat_assum `!id p sz. FLOOKUP ce_before_registration.ce_vars id <> _`
       (fn h => simp[NoAsms, local_region_def, h]));

(* Use the same prefix witness for the ABI reads and the composed path. *)
val linked_deploy_registration_prefix_tac =
  qpat_assum `!vi. raw_variant fmp vi vs ==> ?t. fresh_vars_wrt st1 t /\ _`
    (qspec_then `vi` (drule_then (qx_choose_then `t` (map_every assume_tac o CONJUNCTS)))) >>
  `vi = vs with <|vs_fmp := fmp; vs_initial_fmp := fmp;
                   vs_gas_readings := vi.vs_gas_readings|>` by
    (qpat_assum `raw_variant fmp vi vs`
       (mp_tac o PURE_REWRITE_RULE [raw_variant_def, gas_variant_def]) >>
     simp[NoAsms, venom_state_component_equality] >> strip_tac >>
     qpat_assum `fmp = vi.vs_initial_fmp` (fn h =>
       qpat_assum `fmp = vi.vs_fmp` (ACCEPT_TAC o TRANS (SYM h)))) >>
  qpat_assum `vars_pc_only vi t` (strip_assume_tac o MATCH_MP deploy_ctor_vars_pc_frame) >>
  `t.vs_outcomes = vi.vs_outcomes /\ t.vs_tx_ctx = vi.vs_tx_ctx /\
   t.vs_block_ctx = vi.vs_block_ctx /\ t.vs_immutables = vi.vs_immutables /\
   t.vs_fmp = vi.vs_fmp /\ t.vs_initial_fmp = vi.vs_initial_fmp` by
    (qpat_assum `vars_pc_only vi t` (mp_tac o PURE_REWRITE_RULE [vars_pc_only_def]) >>
     simp[NoAsms, venom_state_component_equality]) >>
  `vs.vs_allocas = FEMPTY` by
    simp[NoAsms, Abbr `vs`, opt_entry_state_own_def, entry_venom_state_fresh] >>
  `vi.vs_allocas = FEMPTY /\ vi.vs_alloca_next = imm_len_mods mods /\
   vi.vs_data_section = args_bytes` by
    (qpat_assum `vi = _` SUBST1_TAC >> simp[]) >>
  `t.vs_allocas = FEMPTY /\ t.vs_alloca_next = imm_len_mods mods /\
   t.vs_data_section = args_bytes` by
    (qpat_assum `vi = _` kall_tac >> asm_rewrite_tac[]);

val linked_deploy_registration_decode_tac =
  qspecl_then [`deploy_unit.cu_context`,`"__deploy"`,`fn`,`t`,`imm_len_mods mods`]
    mp_tac deploy_ctor_empty_alloca_frontier >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `mem_bytes_at 0 (LENGTH args_bytes) t.vs_data_section = args_bytes` by
    (qpat_assum `t.vs_data_section = args_bytes` SUBST1_TAC >>
     simp[NoAsms, valueEncodingDefsTheory.mem_bytes_at_def, rich_listTheory.TAKE_LENGTH_APPEND]) >>
  `local_ptrs_rel fn ce_before_registration [scope] t` by
    (qpat_assum `!func initial. local_ptrs_rel func _ _ initial`
       (qspecl_then [`fn`,`t`] ACCEPT_TAC)) >>
  qspecl_then [`imm_len_mods mods`,`imm_len_mods mods`,`ce_before_registration`,
    `type_env_all_modules mods`,`src_args`,`avs`,
    `vyper_to_abi_types (type_env_all_modules mods) (MAP SND src_args)`,
    `args_bytes`,`scope`,`0`,`st1`,`ce1`,`st2`,`deploy_unit.cu_context`,
    `fn`,`ARB:instruction`,`t`,`T`] mp_tac
    ctorDeployLoweringEntryLocalBoundsTheory.deploy_ctor_register_args_actual_coordinated_map_bounds_gas_path >>
  (impl_tac >-
    (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[NoAsms] >> NO_TAC,
       qpat_assum `t.vs_allocas = FEMPTY` (fn h => simp[NoAsms,h,finite_mapTheory.FLOOKUP_EMPTY]) >> NO_TAC,
       qpat_assum `t.vs_alloca_next = imm_len_mods mods` (fn h => simp[NoAsms,h]) >> NO_TAC,
       qpat_assum `!site. alloca_frontier_inv_from _ _ _ site t`
         (qspec_then `ARB:instruction` ACCEPT_TAC),
       qpat_assum `!s id b sz. ~local_region ce_before_registration [scope] s id b sz`
         (fn h => simp[NoAsms,h]) >> NO_TAC,
       qpat_assum `!bb. lookup_block st2.cs_current_bb _ = SOME bb ==> _`
         (fn h => disj2_tac >> ACCEPT_TAC h)])) >>
  disch_then (qx_choose_then `actual`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [boolTheory.IMP_CLAUSES])) >>
  qpat_assum `abi_encoder_registered_effect _ [] t actual`
    (map_every assume_tac o CONJUNCTS o
     PURE_REWRITE_RULE [abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def]);

val linked_deploy_registration_path_tac =
  `eval_operand imm actual = SOME 0w` by
    (irule ctorDeployLoweringEntryBodyResourcesTheory.deploy_ctor_entry_operand_frame >>
     qexistsl [`t`,`st1`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `gas_path deploy_unit.cu_context fn
      (vi with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>)
      0 (OK actual)` by
    (irule (SIMP_RULE std_ss [arithmeticTheory.ADD_CLAUSES]
      (Q.INST [`n` |-> `0`,`m` |-> `0`] fragGasPathTheory.gas_path_then)) >>
     qexists_tac `t` >> conj_tac >> first_assum ACCEPT_TAC) >>
  `!site. alloca_frontier_inv_from (imm_len_mods mods) deploy_unit.cu_context fn site actual` by
    (qpat_assum `alloca_frontier_inv_from _ _ _ ARB actual` mp_tac >>
     simp[NoAsms, allocaFrontierRoomTheory.alloca_frontier_inv_from_def]) >>
  qpat_assum `fresh_label "ctor_exit" st2 = (exit_lbl,sa)`
    (strip_assume_tac o MATCH_MP emitHelperPropsTheory.fresh_label_props) >>
  `actual.vs_current_bb = sa.cs_current_bb /\
   actual.vs_inst_idx = LENGTH sa.cs_current_insts` by
    (qpat_assum `sa.cs_current_bb = st2.cs_current_bb` SUBST1_TAC >>
     qpat_assum `sa.cs_current_insts = st2.cs_current_insts` SUBST1_TAC >>
     conj_tac >> first_assum ACCEPT_TAC);

(* Export the decoder effects at one endpoint, retaining the raw prefix frame. *)
val linked_deploy_registration_replay_entry_tac =
  sg `!vi. raw_variant fmp vi vs ==>
    ?actual. local_ptrs_rel fn ce1 [scope] actual /\
      eval_operand imm actual = SOME 0w /\
      gas_path deploy_unit.cu_context fn
        (vi with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>)
        0 (OK actual) /\
      ~actual.vs_halted /\ actual.vs_current_bb = sa.cs_current_bb /\
      actual.vs_inst_idx = LENGTH sa.cs_current_insts /\
      alloca_inv actual /\
      (!site. alloca_frontier_inv_from (imm_len_mods mods) deploy_unit.cu_context fn site actual) /\
      imm_len_mods mods <= actual.vs_alloca_next /\
      (!aid b sz. FLOOKUP actual.vs_allocas aid = SOME (b,sz) ==> imm_len_mods mods <= b) /\
      (!id b sz. local_region ce1 [scope] actual id b sz ==> imm_len_mods mods <= b) /\
      (!p. p < imm_len_mods mods ==>
        mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 vi.vs_memory) /\
      actual.vs_accounts = vi.vs_accounts /\ actual.vs_transient = vi.vs_transient /\
      actual.vs_logs = vi.vs_logs /\ actual.vs_requests = vi.vs_requests /\
      actual.vs_pending_deletions = vi.vs_pending_deletions /\
      actual.vs_immutables = vi.vs_immutables /\ actual.vs_outcomes = vi.vs_outcomes /\
      actual.vs_data_section = vi.vs_data_section /\ actual.vs_code = vi.vs_code /\
      actual.vs_labels = vi.vs_labels /\ actual.vs_gas_readings = vi.vs_gas_readings /\
      actual.vs_call_ctx = vi.vs_call_ctx /\ actual.vs_tx_ctx = vi.vs_tx_ctx /\
      actual.vs_block_ctx = vi.vs_block_ctx`;

val linked_deploy_registration_replay_bytes_tac =
  `!p. p < imm_len_mods mods ==>
     mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 vi.vs_memory` by
    (qx_gen_tac `p` >> disch_tac >>
     qpat_assum `!p. p < t.vs_alloca_next ==> _` (qspec_then `p` mp_tac) >>
     qpat_assum `t.vs_alloca_next = imm_len_mods mods` (fn cap =>
       qpat_assum `t.vs_memory = vi.vs_memory` (fn mem =>
         qpat_assum `p < imm_len_mods mods` (fn bound =>
           simp[NoAsms,cap,mem,bound]))));

val linked_deploy_registration_replay_finish_tac =
  let
    val fields = [`actual.vs_accounts = t.vs_accounts`,
      `actual.vs_transient = t.vs_transient`, `actual.vs_logs = t.vs_logs`,
      `actual.vs_requests = t.vs_requests`,
      `actual.vs_pending_deletions = t.vs_pending_deletions`,
      `actual.vs_immutables = t.vs_immutables`, `actual.vs_outcomes = t.vs_outcomes`,
      `actual.vs_data_section = t.vs_data_section`, `actual.vs_code = t.vs_code`,
      `actual.vs_labels = t.vs_labels`, `actual.vs_gas_readings = t.vs_gas_readings`,
      `actual.vs_call_ctx = t.vs_call_ctx`, `actual.vs_tx_ctx = t.vs_tx_ctx`,
      `actual.vs_block_ctx = t.vs_block_ctx`]
  in
    qexists_tac `actual` >> rpt conj_tac >>
    (FIRST_ASSUM ACCEPT_TAC ORELSE
     FIRST (map (fn field => qpat_assum field SUBST1_TAC >> FIRST_ASSUM ACCEPT_TAC) fields))
  end;

(* Checked payable and immutable prefix, with provenance rooted at raw entry. *)
val linked_checked_ctor_root_tac =
  qx_gen_tac `vi` >> disch_tac >>
  qabbrev_tac `root = vi with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>` >>
  `vi = vs with <|vs_fmp := fmp; vs_initial_fmp := fmp;
                 vs_gas_readings := vi.vs_gas_readings|>` by
    (qpat_assum `raw_variant fmp vi vs`
       (mp_tac o PURE_REWRITE_RULE [raw_variant_def, gas_variant_def]) >>
     simp[NoAsms, venom_state_component_equality] >> strip_tac >>
     qpat_assum `fmp = vi.vs_initial_fmp` (fn h =>
       qpat_assum `fmp = vi.vs_fmp` (ACCEPT_TAC o TRANS (SYM h))));

val linked_checked_ctor_root_empty_tac =
  `root.vs_allocas = FEMPTY /\ ~root.vs_halted /\
   root.vs_current_bb = (initial_compile_state "__deploy").cs_current_bb /\
   root.vs_inst_idx = LENGTH (initial_compile_state "__deploy").cs_current_insts /\
   root.vs_memory = []` by
    (qunabbrev_tac `root` >> qpat_assum `vi = _` SUBST1_TAC >>
     simp[NoAsms, Abbr `vs`, opt_entry_state_own_def,
          entry_venom_state_fresh, initial_compile_state_def]) >>
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  `fresh_vars_wrt (initial_compile_state "__deploy") root` by
    (qunabbrev_tac `root` >> qpat_assum `vi = _` SUBST1_TAC >>
     simp[NoAsms, Abbr `vs`, opt_entry_state_own_def, entry_venom_state_fresh,
          fresh_vars_wrt_def, initial_compile_state_def, lookup_var_def]) >>
  `alloca_history fn root` by
    (irule allocaHistoryTheory.alloca_history_empty >>
     conj_tac >- FIRST_ASSUM ACCEPT_TAC >> simp[NoAsms, Abbr `root`]) >>
  `allocas_from (imm_len_mods mods) root` by
    (qpat_assum `root.vs_allocas = FEMPTY` (fn h =>
       simp[NoAsms, allocas_from_def, h, finite_mapTheory.FLOOKUP_EMPTY]));

val linked_checked_ctor_root_bound_tac =
  `root.vs_alloca_next = imm_len_mods mods /\ root.vs_fmp = fmp /\
   root.vs_initial_fmp = fmp /\ root.vs_data_section = args_bytes` by
    (qunabbrev_tac `root` >> qpat_assum `vi = _` SUBST1_TAC >> simp[]) >>
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  `imm_len_mods mods + unit_alloca_budget deploy_unit.cu_context <= w2n fmp` by
    (qpat_assum `imm_len_mods mods + _ + _ <= w2n fmp` mp_tac >> decide_tac) >>
  `(ctx_has_dalloca deploy_unit.cu_context ==> allocas_below_fmp root)` by
    (qpat_assum `root.vs_initial_fmp = fmp` (fn k =>
     qpat_assum `root.vs_fmp = fmp` (fn f =>
     qpat_assum `root.vs_allocas = FEMPTY` (fn a =>
       simp[NoAsms, allocas_below_fmp_def, k, f, a, finite_mapTheory.FLOOKUP_EMPTY]))));

val linked_checked_ctor_prepare_tac =
  (SUBGOAL_THEN ``mut = Payable \/ root.vs_call_ctx.cc_callvalue = 0w`` ASSUME_TAC >-
    (`root.vs_call_ctx.cc_callvalue = n2w tx.value` by
       (drule raw_variant_call_ctx >> simp[Abbr `root`]) >>
     qpat_assum `mut = Payable \/ tx.value = 0` mp_tac >>
     qpat_assum `root.vs_call_ctx.cc_callvalue = _` (fn h => simp[NoAsms,h]) >>
     disch_then (DISJ_CASES_THEN (fn h => simp[NoAsms,h])))) >>
  mp_tac (Q.INST [`payable` |-> `mut = Payable`, `cap` |-> `imm_len_mods mods`,
      `st` |-> `initial_compile_state "__deploy"`, `pay` |-> `st_pay`,
      `last` |-> `st1`, `initial` |-> `root`, `func` |-> `fn`, `imm` |-> `imm`,
      `ctx` |-> `deploy_unit.cu_context`, `lo` |-> `imm_len_mods mods`,
      `PG` |-> `[]`, `G` |-> `FEMPTY`, `tn` |-> `entry_taint`,
      `D` |-> `linked_ret_DF (storage_trace_horizon es0.storage_trace)`]
    ctorDeployMemoryRunPtrPrefixEntryPrepareTheory.prefix_entry_prepare_actual_checked) >>
  impl_tac;

val linked_checked_ctor_open_prepared_tac =
  disch_then (qx_choosel_then [`t`,`Gpre`,`tnpre`]
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [boolTheory.IMP_CLAUSES]));

val linked_checked_ctor_prepared_tac =
  `t.vs_allocas = FEMPTY /\ t.vs_alloca_next = imm_len_mods mods /\
   t.vs_data_section = args_bytes /\ t.vs_fmp = fmp /\ t.vs_initial_fmp = fmp` by
    (rpt conj_tac >>
     FIRST (map (fn field => qpat_assum field SUBST1_TAC >> FIRST_ASSUM ACCEPT_TAC)
       [`t.vs_allocas = root.vs_allocas`,`t.vs_alloca_next = root.vs_alloca_next`,
        `t.vs_data_section = root.vs_data_section`,`t.vs_fmp = root.vs_fmp`,
        `t.vs_initial_fmp = root.vs_initial_fmp`])) >>
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  qspecl_then [`deploy_unit.cu_context`,`"__deploy"`,`fn`,`t`,`imm_len_mods mods`]
    mp_tac deploy_ctor_empty_alloca_frontier >>
  (impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `alloca_history fn t` by
    (qpat_assum `alloca_history fn root ==> alloca_history fn t` (drule_then ACCEPT_TAC));

val linked_checked_ctor_suffix_inputs_tac =
  `local_ptrs_rel fn ce_before_registration [scope] t` by
    (qpat_assum `!func initial. local_ptrs_rel func _ _ initial`
       (qspecl_then [`fn`,`t`] ACCEPT_TAC)) >>
  `mem_bytes_at 0 (LENGTH args_bytes) t.vs_data_section = args_bytes` by
    (qpat_assum `t.vs_data_section = args_bytes` SUBST1_TAC >>
     simp[NoAsms, valueEncodingDefsTheory.mem_bytes_at_def, rich_listTheory.TAKE_LENGTH_APPEND]) >>
  `allocas_from (imm_len_mods mods) t` by
    (qpat_assum `t.vs_allocas = FEMPTY` (fn h =>
       simp[NoAsms, allocas_from_def,h,finite_mapTheory.FLOOKUP_EMPTY])) >>
  `ctx_has_dalloca deploy_unit.cu_context ==> allocas_below_fmp t /\
   t.vs_alloca_next + pending_alloca_size fn t <= w2n t.vs_initial_fmp` by
    (disch_tac >> mp_tac (Q.INST [`ctx` |-> `deploy_unit.cu_context`,
       `func` |-> `fn`, `s` |-> `t`, `k` |-> `imm_len_mods mods`, `site` |-> `ARB:instruction`]
       ctorDeployLoweringEntryFmpTheory.deploy_entry_frontier_allocas_below_fmp) >>
     (impl_tac >-
       (conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
        conj_tac >- (qpat_assum `!site. alloca_frontier_inv_from _ _ _ site t`
                      (qspec_then `ARB:instruction` ACCEPT_TAC)) >>
        qpat_assum `t.vs_initial_fmp = fmp` SUBST1_TAC >>
        conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
        qpat_assum `t.vs_fmp = fmp` SUBST1_TAC >> simp[NoAsms])) >>
     disch_then ACCEPT_TAC);

val linked_checked_ctor_suffix_tac =
  `ce_before_registration with ce_vars := ce_before_registration.ce_vars = ce_before_registration` by
    simp[NoAsms,compile_env_component_equality] >>
  qpat_assum `ce_before_registration with ce_vars := _ = ce_before_registration` (fn same =>
  mp_tac (ctorDeployMemoryRunPtrPrefixEntryRegisterOriginsTheory.prefix_entry_register_suffix_origins_coverage_mode
    |> Q.SPEC `T` |> BETA_RULE
    |> Q.SPECL [`src_args:(string # type) list`,`ce_before_registration`,`ce_before_registration.ce_vars`,
      `type_env_all_modules mods`,`src_args:(string # type) list`,`avs`,
      `vyper_to_abi_types (type_env_all_modules mods) (MAP SND (src_args:(string # type) list))`,
      `args_bytes`,`scope`,`0`,`st1`,`ce1`,`st2`,`deploy_unit.cu_context`,`fn`,
      `ARB:instruction`,`t`,`Gpre`,`tnpre`,
      `linked_ret_DF (storage_trace_horizon es0.storage_trace)`,
      `imm_len_mods mods`,`[]`,`imm_len_mods mods`]
    |> SIMP_RULE bool_ss [listTheory.DROP_0, listTheory.TAKE_0, listTheory.MAP,
        listTheory.SUM, arithmeticTheory.ZERO_LESS_EQ, same])) >> impl_tac;

val linked_checked_ctor_suffix_premises_tac =
  rpt conj_tac >> FIRST [FIRST_ASSUM ACCEPT_TAC,
    qpat_assum `t.vs_data_section = args_bytes` SUBST1_TAC >> simp[NoAsms] >> NO_TAC,
    qpat_assum `t.vs_allocas = FEMPTY` (fn h => simp[NoAsms,h,finite_mapTheory.FLOOKUP_EMPTY]) >> NO_TAC,
    qpat_assum `t.vs_alloca_next = imm_len_mods mods` (fn h => simp[NoAsms,h]) >> NO_TAC,
    qpat_assum `!site. alloca_frontier_inv_from _ _ _ site t`
       (qspec_then `ARB:instruction` ACCEPT_TAC),
    qpat_assum `!bb. lookup_block st2.cs_current_bb _ = SOME bb ==> _`
       (fn h => disj2_tac >> ACCEPT_TAC h)];

val linked_checked_ctor_suffix_open_tac =
  disch_then (qx_choosel_then [`actual`,`Gbody`,`tnbody`]
    (map_every assume_tac o CONJUNCTS));

(* Keep the joint witnesses outside both the dead-mask and site quantifiers. *)
val linked_checked_ctor_entry_goal =
  Q.SUBGOAL_THEN `!vi. raw_variant fmp vi vs ==>
    ?actual Gbody tnbody.
      (!D explicit. gas_origin_ptr_path (D,imm_len_mods mods,explicit,deploy_unit.cu_context,fn,[])
        ((vi with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>),FEMPTY,entry_taint)
        [] (OK actual,Gbody,tnbody)) /\
      gas_path_mem deploy_unit.cu_context fn
        (vi with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>) 0 (OK actual) /\
      alloca_history fn actual /\
      ~actual.vs_halted /\ actual.vs_current_bb = sa.cs_current_bb /\
      actual.vs_inst_idx = LENGTH sa.cs_current_insts /\ fresh_vars_wrt st2 actual /\
      eval_operand imm actual = SOME 0w /\ op_taint tnbody imm = {} /\ op_prov Gbody imm = NONE /\
      local_ptrs_rel fn ce1 [scope] actual /\ alloca_inv actual /\
      (!site. alloca_frontier_inv_from (imm_len_mods mods) deploy_unit.cu_context fn site actual) /\
      allocas_from (imm_len_mods mods) actual /\ imm_len_mods mods <= actual.vs_alloca_next /\
      (!aid b sz. FLOOKUP actual.vs_allocas aid = SOME (b,sz) ==> imm_len_mods mods <= b) /\
      (!id b sz. local_region ce1 [scope] actual id b sz ==> imm_len_mods mods <= b) /\
      (ctx_has_dalloca deploy_unit.cu_context ==> allocas_below_fmp actual /\
         actual.vs_alloca_next + pending_alloca_size fn actual <= w2n actual.vs_initial_fmp) /\
      fmp_room deploy_unit.cu_context fn actual /\
      (!inst b sz n. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
        inst.inst_operands = [Lit n] /\ FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
      (!p. p < imm_len_mods mods ==> read_byte p actual.vs_memory = 0w) /\
      (!p. p < imm_len_mods mods ==>
        mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 vi.vs_memory) /\
      (!p. p < imm_len_mods mods ==> p NOTIN tnbody.t_mem) /\
      tnbody.t_stor = {} /\ tnbody.t_trans = {} /\ tnbody.t_imm = {} /\
      (!j. j < LENGTH src_args ==> ?entry d B.
        imm_len_mods mods <= d /\ lookup_scopes (FST (EL j src_args)) [scope] = SOME entry /\
        local_region ce1 [scope] actual (FST (EL j src_args)) d
          (type_memory_bytes ce_before_registration (SND (EL j src_args))) /\
        (?p. FLOOKUP ce1.ce_vars (FST (EL j src_args)) =
          SOME (PtrVar (Var p) (type_memory_bytes ce_before_registration (SND (EL j src_args)))) /\
          not_fresh_at st2 p /\ ptr_covers Gbody tnbody p actual
            (type_memory_bytes ce_before_registration (SND (EL j src_args)))) /\
        FINITE B /\ B SUBSET range_bytes [(d,type_memory_bytes ce_before_registration (SND (EL j src_args)))] /\
        DISJOINT B tnbody.t_mem /\ (!a. a IN B ==> a < actual.vs_alloca_next) /\
        (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
          val_in_memory entry.type entry.value d mem)) /\
      actual.vs_accounts = vi.vs_accounts /\ actual.vs_transient = vi.vs_transient /\
      actual.vs_logs = vi.vs_logs /\ actual.vs_requests = vi.vs_requests /\
      actual.vs_pending_deletions = vi.vs_pending_deletions /\ actual.vs_outcomes = vi.vs_outcomes /\
      actual.vs_data_section = vi.vs_data_section /\ actual.vs_code = vi.vs_code /\
      actual.vs_labels = vi.vs_labels /\ actual.vs_gas_readings = vi.vs_gas_readings /\
      actual.vs_call_ctx = vi.vs_call_ctx /\ actual.vs_tx_ctx = vi.vs_tx_ctx /\
      actual.vs_block_ctx = vi.vs_block_ctx` (mk_asm "linked_ctor_checked_entry");

val linked_checked_ctor_join_origin_goal =
  Q.SUBGOAL_THEN `!D explicit. gas_origin_ptr_path
    (D,imm_len_mods mods,explicit,deploy_unit.cu_context,fn,[])
    (root,FEMPTY,entry_taint) [] (OK actual,Gbody,tnbody)` ASSUME_TAC;

val linked_checked_ctor_join_origin_tac =
  qx_genl_tac [`D`,`explicit`] >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (root,_,_) [] _`
    (qspecl_then [`D`,`explicit`] assume_tac) >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (t,Gpre,tnpre) [] _`
    (qspecl_then [`D`,`explicit`] assume_tac) >>
  drule_all_then ACCEPT_TAC fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans;

val linked_checked_ctor_join_mem_tac =
  `gas_path_mem deploy_unit.cu_context fn root 0 (OK actual)` by
    (irule (SIMP_RULE std_ss [arithmeticTheory.ADD_CLAUSES]
       (Q.INST [`n` |-> `0`,`m` |-> `0`] fragGasPathMemTheory.gas_path_mem_then)) >>
     qexists_tac `t` >> conj_tac >> FIRST_ASSUM ACCEPT_TAC);

val linked_checked_ctor_cursor_tac =
  qpat_assum `fresh_label "ctor_exit" st2 = (exit_lbl,sa)`
    (map_every assume_tac o CONJUNCTS o MATCH_MP emitHelperPropsTheory.fresh_label_props) >>
  `actual.vs_current_bb = sa.cs_current_bb /\
   actual.vs_inst_idx = LENGTH sa.cs_current_insts` by
    (qpat_assum `sa.cs_current_bb = st2.cs_current_bb` SUBST1_TAC >>
     qpat_assum `sa.cs_current_insts = st2.cs_current_insts` SUBST1_TAC >>
     conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  `!site. alloca_frontier_inv_from (imm_len_mods mods) deploy_unit.cu_context fn site actual` by
    (qpat_assum `alloca_frontier_inv_from _ _ _ ARB actual` mp_tac >>
     simp[NoAsms,allocaFrontierRoomTheory.alloca_frontier_inv_from_def]);

val linked_checked_ctor_end_fmp_tac =
  qpat_assum `!D explicit. gas_origin_ptr_path _ (t,Gpre,tnpre) [] _`
    (qspecl_then [`linked_ret_DF (storage_trace_horizon es0.storage_trace)`,`{}:(string # num) set`] assume_tac) >>
  drule_all_then (map_every assume_tac o CONJUNCTS)
    decoderOriginAllocationFrameTheory.decoder_origin_path_allocation_frame >>
  `fmp_room deploy_unit.cu_context fn actual` by
    (qpat_assum `alloca_frontier_inv_from _ _ _ ARB actual`
       (mp_then Any irule ctorDeployLoweringEntryFmpTheory.deploy_entry_frontier_fmp_room) >>
     qpat_assum `actual.vs_initial_fmp = t.vs_initial_fmp` SUBST1_TAC >>
     qpat_assum `actual.vs_fmp = t.vs_fmp` SUBST1_TAC >>
     qpat_assum `t.vs_initial_fmp = fmp` SUBST1_TAC >>
     qpat_assum `t.vs_fmp = fmp` SUBST1_TAC >>
     qpat_assum `imm_len_mods mods + unit_alloca_budget deploy_unit.cu_context <= w2n fmp`
       (fn budget => qpat_assum `w2n fmp < 2 ** 254`
         (fn bound => simp[NoAsms,budget,bound])));

val linked_checked_ctor_low_tac =
  `!p. p < imm_len_mods mods ==> read_byte p actual.vs_memory = 0w` by
    (qx_gen_tac `p` >> disch_tac >>
     qpat_assum `!p. p < imm_len_mods mods ==> read_byte p actual.vs_memory = _`
       (drule_then SUBST1_TAC) >>
     qpat_assum `t.vs_memory = root.vs_memory` SUBST1_TAC >>
     qpat_assum `root.vs_memory = []` SUBST1_TAC >> simp[NoAsms,codegenRelTheory.read_byte_def]) >>
  `!p. p < imm_len_mods mods ==> p NOTIN tnbody.t_mem` by
    (qx_gen_tac `p` >> disch_tac >>
     qpat_assum `!p. p < t.vs_alloca_next /\ p IN tnbody.t_mem ==> _` (qspec_then `p` mp_tac) >>
     qpat_assum `t.vs_alloca_next = imm_len_mods mods`
       (fn floor => qpat_assum `tnpre.t_mem = {}`
         (fn clean => qpat_assum `p < imm_len_mods mods`
           (fn bound => simp[NoAsms,floor,clean,bound]))));

val linked_checked_ctor_bytes_tac =
  `!p. p < imm_len_mods mods ==>
     mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 vi.vs_memory` by
    (qx_gen_tac `p` >> disch_tac >>
     `vi.vs_memory = []` by
       (qpat_assum `root.vs_memory = []` mp_tac >> simp[NoAsms,Abbr `root`]) >>
     `read_byte p actual.vs_memory = 0w` by
       (qpat_assum `!p. p < imm_len_mods mods ==> read_byte p actual.vs_memory = 0w`
         (drule_then ACCEPT_TAC)) >>
     PURE_ONCE_REWRITE_TAC [listTheory.LIST_EQ_REWRITE] >>
     simp[immutableDeployAssignTransferTheory.immutable_mem_bytes_read_byte,
          codegenRelTheory.read_byte_def]);

val linked_checked_ctor_formal_regions_goal =
  Q.SUBGOAL_THEN `!j. j < LENGTH (src_args:(string # type) list) ==> ?d k.
      local_region ce1 [scope] actual (FST (EL j src_args)) d k /\
      imm_len_mods mods <= d` ASSUME_TAC;

val linked_checked_ctor_formal_regions_tac =
  qx_gen_tac `j` >> disch_tac >>
  qpat_assum `!j. j < LENGTH (src_args:(string # type) list) ==> ?entry d B.
    imm_len_mods mods <= d /\ _`
    (qspec_then `j` mp_tac) >>
  (impl_tac >- FIRST_ASSUM ACCEPT_TAC) >>
  disch_then strip_assume_tac >>
  rename1 `local_region ce1 [scope] actual (FST (EL j src_args)) base_at_j _` >>
  qexistsl_tac [`base_at_j`,`type_memory_bytes ce_before_registration
    (SND (EL j (src_args:(string # type) list)))`] >>
  conj_tac >> FIRST_ASSUM ACCEPT_TAC;

val linked_checked_ctor_region_tac =
  qpat_assum `allocas_from (imm_len_mods mods) actual`
    (assume_tac o PURE_REWRITE_RULE [allocas_from_def]) >>
  `!id b sz. local_region ce1 [scope] actual id b sz ==> imm_len_mods mods <= b` by
    (rpt gen_tac >> disch_tac >>
     irule ctorDeployMemoryRunPtrPrefixEntrySeparationTheory.prefix_entry_bound_argument_regions >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     qexistsl_tac [`type_env_all_modules mods`,`src_args`,`tx.args`] >>
     conj_tac >> FIRST_ASSUM ACCEPT_TAC);

val linked_checked_ctor_imm_tac =
  `eval_operand imm actual = SOME 0w` by
    (irule ctorDeployLoweringEntryBodyResourcesTheory.deploy_ctor_entry_operand_frame >>
     qexistsl_tac [`t`,`st1`] >> rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  `!x. imm = Var x ==> not_fresh_at st1 x` by
    (qpat_assum `fresh_vars_wrt st1 t`
       (mp_then Any mp_tac exprSimWordBuiltinsTheory.fresh_vars_wrt_not_fresh_at) >>
     disch_then (qspecl_then [`imm`,`0w`] mp_tac) >>
     qpat_assum `eval_operand imm t = SOME 0w` (fn ev => simp[NoAsms,ev])) >>
  `op_taint tnbody imm = {} /\ op_prov Gbody imm = NONE` by
    (qpat_assum `!x. not_fresh_at st1 x ==> FLOOKUP Gbody x = _ /\ _` mp_tac >>
     qpat_assum `!x. imm = Var x ==> not_fresh_at st1 x` mp_tac >>
     qpat_assum `op_taint tnpre imm = {}` mp_tac >>
     qpat_assum `op_prov Gpre imm = NONE` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `imm` >>
     simp[op_taint_def,op_prov_def] >> metis_tac[]) >>
  pop_assum (map_every assume_tac o CONJUNCTS);

fun linked_checked_ctor_field_tac field =
  let
    fun at s t = [QUOTE (s ^ "." ^ field ^ " = " ^ t ^ "." ^ field)]
  in
    qpat_assum (at "actual" "t") SUBST1_TAC >>
    qpat_assum (at "t" "root") SUBST1_TAC >>
    simp[NoAsms,Abbr `root`]
  end;

val linked_checked_ctor_finish_tac =
  qpat_assum `abi_encoder_registered_effect _ [] t actual`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE
      [abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def]) >>
  qexistsl_tac [`actual`,`Gbody`,`tnbody`] >> rpt conj_tac >>
  FIRST [FIRST_ASSUM ACCEPT_TAC,
    qmatch_goalsub_rename_tac `vi with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>` >>
      (qpat_assum `Abbrev (root = _)`
        (PURE_REWRITE_TAC o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def])) >>
      FIRST_ASSUM ACCEPT_TAC,
    qpat_assum `tnbody.t_stor = tnpre.t_stor` SUBST1_TAC >> FIRST_ASSUM ACCEPT_TAC,
    qpat_assum `tnbody.t_trans = tnpre.t_trans` SUBST1_TAC >> FIRST_ASSUM ACCEPT_TAC,
    qpat_assum `tnbody.t_imm = tnpre.t_imm` SUBST1_TAC >> FIRST_ASSUM ACCEPT_TAC,
    FIRST (map (fn field => linked_checked_ctor_field_tac field >> NO_TAC)
     ["vs_accounts","vs_transient","vs_logs","vs_requests","vs_pending_deletions","vs_outcomes",
      "vs_data_section","vs_code","vs_labels","vs_gas_readings","vs_call_ctx","vs_tx_ctx","vs_block_ctx"])];

(* Recover the evaluated linked constant table at the transferred entry. *)
val linked_ctor_constant_guards_tac =
  SUBGOAL_THEN ``EVERY (no_sha256_expr o SND) (consts_env_mods mods) /\
    EVERY (no_neg_exp_expr o SND) (consts_env_mods mods)``
    (map_every assume_tac o CONJUNCTS)
  >- (conj_tac >> CCONTR_TAC >>
      qpat_x_assum `lower_vyper_deploy_unit_mods mods exps _ _ = SOME deploy_unit` mp_tac >>
      qpat_assum `~EVERY _ (consts_env_mods mods)` (fn guard =>
        qpat_assum `classify_functions_unit mods exps = (_,_,_,SOME constructor,_)`
          (fn classification =>
            SIMP_TAC bool_ss [lower_vyper_deploy_unit_mods_def, classification, LET_THM,
              pairTheory.UNCURRY, guard, optionTheory.NOT_NONE_SOME])));

val linked_ctor_constant_cells_tac =
  `check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME deploy_art` by
    simp[] >>
  `ALOOKUP am0.immutables cx.txn.target = SOME imms` by
    (qpat_assum `am0 = _` SUBST1_TAC >> simp[]) >>
  `evaluate_all_constants cx am0 cx.txn.target mods = SOME am_c` by
    (qpat_assum `cx.txn.target = tx.target` SUBST1_TAC >>
     qpat_assum `evaluate_module_constants_trace cx am0 tx.target
        (constants_order mods) = (SOME am_c,[])`
       (fn trace => simp[NoAsms, evaluate_all_constants_def,
                        evaluate_module_constants_def, trace])) >>
  drule_all vyperLinkedConstantInstallTheory.checked_constants_installed_fold >>
  disch_then (qx_choose_then `cells`
    (CONJUNCTS_THEN2 assume_tac (mk_asm "installed_cells"))) >>
  `ALOOKUP (es0:evaluation_state).immutables cx.txn.target = SOME cells` by
    (qpat_assum `es0 = _` SUBST1_TAC >>
     asm "installed_cells" (fn lookup =>
       simp[NoAsms, vyperInterpreterTheory.initial_state_def, lookup]));

val linked_ctor_constant_folds_tac =
  `!src ts. MEM (src,ts) mods ==> ?A.
      constants_fold_module mods cells src ts FEMPTY = SOME A /\
      A SUBMAP get_source_immutables src cells` by
    (qpat_assum `check_contract T am.layouts tx.target mods = SOME deploy_art`
       (mp_then Any mp_tac
         (Q.INST [`dst` |-> `cells`, `last` |-> `cells`, `init` |-> `imms`]
           vyperLinkedConstantSlotReplayTheory.checked_ordered_fold_slot_replay)) >>
     disch_then (qspecl_then [`imms`,`cells`] mp_tac) >>
     qpat_assum `initial_immutables (type_env_all_modules mods) mods = SOME imms`
       (fn init => qpat_assum `constants_fold mods imms (constants_order mods) = SOME cells`
         (fn fold => simp[NoAsms, init, fold])));
(* For custom-error arguments only, the checker annotation must agree
   with the replacement at a qualified constant root. *)
val linked_ctor_error_annotation_tac =
  `!src id replacement. ALOOKUP (consts_env_mods mods) (src,id) = SOME replacement ==>
    ?ts vis init slot. MEM (src,ts) mods /\
      MEM (VariableDecl vis (Constant init) id (expr_type replacement) slot) ts` by
    (qpat_assum `check_contract T am.layouts tx.target mods = SOME deploy_art` mp_tac >>
     qpat_assum `!src ts. MEM (src,ts) mods ==> ?A. constants_fold_module mods cells src ts FEMPTY = SOME A /\ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> ntac 2 disch_tac >> rpt gen_tac >> disch_tac >>
     drule_all linkedConstantReplacementValueTheory.checked_linked_constant_replacement_value >>
     disch_then (qx_choosel_then [`decls`,`vis`,`init`,`ty`,`slot`,`tv`,`v`]
       (map_every assume_tac o CONJUNCTS)) >>
     qexistsl_tac [`decls`,`vis`,`init`,`slot`] >>
     conj_tac >- (irule alistTheory.ALOOKUP_MEM >> FIRST_ASSUM ACCEPT_TAC) >> simp[]) >>
  `!env e.
    env.bare_globals = deploy_art.cta_bare_globals /\
    env.toplevel_vtypes = deploy_art.cta_toplevel_vtypes /\
    env.type_defs = type_env_all_modules mods /\ well_typed_expr env e ==>
    expr_type (subst_consts_expr_mods (consts_env_mods mods) e) = expr_type e` by
    (rpt gen_tac >> Cases_on `e` >> simp[constSubstModsTheory.subst_consts_expr_mods_def, vyperASTTheory.expr_type_def] >>
     rename1 `well_typed_expr env (TopLevelName ann key)` >> PairCases_on `key` >>
     simp[constSubstModsTheory.subst_consts_expr_mods_def, vyperASTTheory.expr_type_def] >> strip_tac >>
     Cases_on `ALOOKUP (consts_env_mods mods) (key0,key1)` >> simp[vyperASTTheory.expr_type_def] >>
     rename1 `ALOOKUP (consts_env_mods mods) (key0,key1) = SOME replacement` >>
     qpat_assum `!src id replacement. ALOOKUP (consts_env_mods mods) (src,id) = SOME replacement ==> _`
       (drule_then strip_assume_tac) >>
     `well_typed_expr (artifact_env deploy_art mods NONE) (TopLevelName ann (key0,key1))` by
       (qpat_x_assum `well_typed_expr env (TopLevelName ann (key0,key1))` mp_tac >>
        simp[artifact_env_def, vyperTypeSystemTheory.well_typed_expr_def]) >>
     qpat_assum `well_typed_expr (artifact_env deploy_art mods NONE) _` mp_tac >>
     qpat_assum `MEM (VariableDecl _ (Constant _) key1 (expr_type replacement) _) _` mp_tac >>
     qpat_assum `MEM (key0,_) mods` mp_tac >>
     qpat_assum `ALOOKUP cx.sources cx.txn.target = SOME mods` mp_tac >>
     qpat_assum `check_contract T am.layouts tx.target mods = SOME deploy_art` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     metis_tac[vyperTypeConstantCellsTheory.checked_constant_declared_type]);

val linked_ctor_error_resolution_tac =
  `!env err.
    env.bare_globals = deploy_art.cta_bare_globals /\
    env.toplevel_vtypes = deploy_art.cta_toplevel_vtypes /\
    env.type_defs = type_env_all_modules mods /\
    well_typed_custom_error env err /\ custom_error_resolved mods err ==>
    custom_error_resolved mods (subst_consts_error_mods (consts_env_mods mods) err)` by
    (qpat_assum `!env e. _ ==> expr_type (subst_consts_expr_mods _ _) = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> disch_tac >>
     rpt gen_tac >> Cases_on `err` >>
     rename1 `custom_error_resolved mods (CustomError key pos kw)` >> PairCases_on `key` >>
     strip_tac >> qpat_x_assum `custom_error_resolved mods _` mp_tac >>
     simp[custom_error_resolved_def] >>
     Cases_on `ALOOKUP mods key0` >> simp[] >> rename1 `ALOOKUP mods key0 = SOME decls` >>
     Cases_on `lookup_custom_error_args_in key1 decls` >> simp[] >>
     rename1 `lookup_custom_error_args_in key1 decls = SOME params` >>
     Cases_on `order_custom_error_args params (CustomError (key0,key1) pos kw)` >> simp[] >>
     rename1 `order_custom_error_args params _ = SOME ordered` >> strip_tac >>
     `MAP expr_type (MAP (subst_consts_expr_mods (consts_env_mods mods)) ordered) =
      MAP expr_type ordered` by
       (pure_rewrite_tac[MAP_MAP_o] >> irule MAP_CONG >> simp[] >> rpt strip_tac >>
        drule vyperASTTheory.order_custom_error_args_perm >>
        disch_then (mp_tac o MATCH_MP sortingTheory.PERM_MEM_EQ) >> strip_tac >>
        qpat_assum `!env e. _ ==> expr_type (subst_consts_expr_mods _ _) = _` irule >>
        qexists_tac `env` >> simp[] >> irule exprSimSourceTheory.well_typed_exprs_member >>
        qexists_tac `custom_error_exprs (CustomError (key0,key1) pos kw)` >>
        fs[vyperTypeSystemTheory.well_typed_custom_error_def]) >>
     `order_custom_error_args params
       (subst_consts_error_mods (consts_env_mods mods) (CustomError (key0,key1) pos kw)) =
       SOME (MAP (subst_consts_expr_mods (consts_env_mods mods)) ordered)` by
       simp[linkedConstAnnotationsTheory.ordered_error_args_subst] >>
     pop_assum (mp_tac o REWRITE_RULE [constSubstModsTheory.subst_consts_error_mods_def]) >>
     simp[constSubstModsTheory.subst_consts_error_mods_def, custom_error_resolved_def]);

val linked_ctor_custom_errors_tac =
  `(!env ret s out.
      type_stmt env ret s = SOME out /\
      env.bare_globals = deploy_art.cta_bare_globals /\
      env.toplevel_vtypes = deploy_art.cta_toplevel_vtypes /\
      env.type_defs = type_env_all_modules mods /\ custom_errors_stmt_ok mods s ==>
      custom_errors_stmt_ok mods (subst_consts_stmt_mods (consts_env_mods mods) s)) /\
   (!env ret ss out.
      type_stmts env ret ss = SOME out /\
      env.bare_globals = deploy_art.cta_bare_globals /\
      env.toplevel_vtypes = deploy_art.cta_toplevel_vtypes /\
      env.type_defs = type_env_all_modules mods /\ custom_errors_stmts_ok mods ss ==>
      custom_errors_stmts_ok mods (subst_consts_stmts_mods (consts_env_mods mods) ss))` by
    (qpat_assum `!env err. _ ==> custom_error_resolved mods (subst_consts_error_mods _ _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> disch_tac >>
     ho_match_mp_tac vyperTypeSystemTheory.type_stmt_ind >> rpt conj_tac >> rpt gen_tac >>
     simp[custom_errors_stmt_ok_def, constSubstModsTheory.subst_consts_stmt_mods_def,
          constSubstModsTheory.subst_consts_rreason_mods_def,
          constSubstModsTheory.subst_consts_areason_mods_def]
     >- (simp[vyperTypeSystemTheory.type_stmt_def] >> metis_tac[])
     >- (simp[vyperTypeSystemTheory.type_stmt_def] >> metis_tac[])
     >- (rpt strip_tac >>
         qpat_x_assum `type_stmt _ _ (If _ _ _) = _` mp_tac >>
         simp[vyperTypeSystemTheory.type_stmt_def, COND_RAND, COND_RATOR, optionTheory.IS_SOME_EXISTS] >>
         metis_tac[])
     >- (rpt strip_tac >>
         qpat_x_assum `type_stmt _ _ (For _ _ _ _ _) = _` mp_tac >>
         simp[vyperTypeSystemTheory.type_stmt_def, COND_RAND, COND_RATOR, optionTheory.IS_SOME_EXISTS] >>
         strip_tac >> qpat_x_assum `!out. type_stmts _ _ _ = SOME out /\ _ ==> _` drule >>
         gvs[vyperTypeSystemTheory.extend_local_def]) >>
     rpt strip_tac >> Cases_on `type_stmt env ret s` >> gvs[vyperTypeSystemTheory.type_stmt_def] >>
     drule vyperTypeEnvExtensionTheory.type_stmt_preserve_nonlocal_fields >> metis_tac[]) >>
  `custom_errors_stmts_ok mods cpkg6` by
    (qpat_assum `cpkg6 = _` SUBST1_TAC >>
     `check_function_body am.layouts tx.target mods deploy_art NONE Deploy mut F src_args [] NoneT raw_body` by
       (drule_all_then ACCEPT_TAC vyperTypeContractContextTheory.check_contract_deploy_function_body_MEM) >>
     qpat_x_assum `check_function_body _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[NoAsms, check_function_body_def, LET_THM, optionTheory.IS_SOME_EXISTS] >>
     disch_then strip_assume_tac >>
     qpat_assum `!env ret ss out. _ ==>
       custom_errors_stmts_ok mods (subst_consts_stmts_mods _ ss)`
       (fn transport => qpat_assum `type_stmts _ NoneT raw_body = SOME _`
         (mp_then Any irule transport)) >>
     simp[function_entry_env_def, artifact_env_def, FOLDL_extend_local_args_static]);

(* The terminal run determines the exit ghosts before any horizon is chosen. *)
val linked_ctor_uniform_marked_tail_tac =
  let
    fun safe_exit dead =
      qpat_assum `!D. ptr_safe_run D _ _ _ _ _ _ _ _ ==> _`
        (qspec_then dead mp_tac) >>
      impl_tac >-
        (qpat_assum `!H. P H ==> ptr_safe_run (DF H) _ _ _ _ _ _ _ _`
           irule >> FIRST_ASSUM ACCEPT_TAC) >>
      strip_tac
  in
    `!P DF (H0 : (bool # bytes32 # type_value) list # num list) pre ret s tail_fuel G tn bb final.
       ~s.vs_halted /\
       lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (pre ++ [ret]) (DROP s.vs_inst_idx bb.bb_instructions) /\
       EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
                  ~is_terminator i.inst_opcode) pre /\
       ret.inst_opcode = RETURN /\
       run_from tail_fuel deploy_unit.cu_context fn s = Halt final /\
       gas_path_mem deploy_unit.cu_context fn s 0 (Halt final) /\
       P H0 /\
       (!H. P H ==> ptr_safe_run (DF H) (imm_len_mods mods) tail_fuel
          deploy_unit.cu_context fn [] G tn s) ==>
       ?G' tn'.
         (ctx_has_dalloca deploy_unit.cu_context ==> allocas_below_fmp final) /\
         !H. P H ==>
           gas_origin_ptr_path
             (DF H,imm_len_mods mods,
              gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context,
              deploy_unit.cu_context,fn,[]) (s,G,tn) [] (Halt final,G',tn')` by
      (POP_ASSUM_LIST (K ALL_TAC) >>
       rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
       `?G' tn'. !D. ptr_safe_run D (imm_len_mods mods) tail_fuel
          deploy_unit.cu_context fn [] G tn s ==>
          gas_path_ptr D (imm_len_mods mods) deploy_unit.cu_context fn []
            G tn s 0 G' tn' (Halt final) /\
          (ctx_has_dalloca deploy_unit.cu_context ==> allocas_below_fmp final)` by
         (irule ctorDeployMemoryRunPtrFrameRetTheory.halting_tail_gas_path_ptr_uniform >>
          conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
          conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
          qexistsl_tac [`bb`,`pre`,`ret`] >> rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
       qexistsl_tac [`G'`,`tn'`] >> conj_tac
       >- (safe_exit `DF H0` >> FIRST_ASSUM ACCEPT_TAC) >>
       qx_gen_tac `H` >> disch_tac >> safe_exit `DF H` >>
       irule fragGasOriginPtrExecTheory.gas_zero_paths_joint >>
       simp[exit_result_def] >> rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)
  end;
(* Use the actual pre-copy state for both the linked snapshot and the
   padded bytes.  The memory execution and byte execution have the same halt. *)
val linked_ctor_epilogue_frame_fields_tac =
  `body_ce.ce_is_ctor = ctor_ce.ce_is_ctor /\
   body_ce.ce_imm_alloca = ctor_ce.ce_imm_alloca /\
   body_ce.ce_modules = ctor_ce.ce_modules /\
   body_ce.ce_module_vars = ctor_ce.ce_module_vars` by
    (qpat_assum `same_frame ctor_ce body_ce` mp_tac >>
     simp[NoAsms, bodySimTheory.same_frame_def, compile_env_component_equality]) >>
  pop_assum (map_every assume_tac o CONJUNCTS);

val linked_ctor_epilogue_terminal_tac =
  drule_all_then (qx_choose_then `tail_bb` (map_every assume_tac o CONJUNCTS))
    immutableDeployExecutionTheory.compile_constructor_epilogue_code_placement >>
  qpat_assum `compile_constructor_epilogue _ _ _ epi = ((),se)`
    (mp_tac o MATCH_MP immutableDeployExecutionTheory.compile_constructor_epilogue_terminal_shape) >>
  disch_then (qx_choosel_then [`ep_pre`,`ep_id`,`ep_dst`,`ep_sz`]
     (map_every assume_tac o CONJUNCTS)) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
             ~is_terminator i.inst_opcode) ep_pre` by
    (pure_rewrite_tac [EVERY_MEM] >> qx_gen_tac `epi_inst` >> disch_tac >>
     qpat_assum `EVERY (\i. MEM i.inst_opcode _) ep_pre`
       (qspec_then `epi_inst` mp_tac o PURE_REWRITE_RULE [EVERY_MEM]) >>
     BETA_TAC >> impl_tac >- FIRST_ASSUM ACCEPT_TAC >>
     simp[NoAsms, MEM] >> strip_tac >> simp[is_terminator_def]);

val linked_ctor_epilogue_halt_tac =
  drule_all_then (qx_choosel_then [`ep_final`,`ep_codepos`] (map_every assume_tac o CONJUNCTS))
    ctorDeployLoweringFrameRetTheory.compile_constructor_epilogue_padded_gas_path >>
  drule_all_then (qx_choose_then `ep_mem_final` assume_tac)
    ctorDeployMemoryRunMemFrameRetTheory.constructor_epilogue_zero_path_mem >>
  drule fragGasPathMemTheory.gas_path_mem_exec >>
  simp[NoAsms, exit_result_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `ep_fuel` (map_every assume_tac o CONJUNCTS))) >>
  `ep_mem_final = ep_final` by
    (qpat_assum `gas_path _ fn s 0 (Halt ep_mem_final)` mp_tac >>
     qpat_assum `gas_path _ fn s 0 (Halt ep_final)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[ctorDeployLoweringFrameRetTheory.gas_path_halt_unique]) >>
  qpat_x_assum `ep_mem_final = ep_final` SUBST_ALL_TAC;

val linked_ctor_epilogue_run_tac =
  `LENGTH runtime_bc <= LENGTH (assemble prog')` by
    (qpat_assum `DROP off (assemble prog') = runtime_bc` (SUBST1_TAC o SYM) >>
     simp[listTheory.LENGTH_DROP]) >>
  `LENGTH runtime_bc + imm_len_mods mods < dimword (:256)` by
    (qpat_assum `LENGTH runtime_bc <= LENGTH (assemble prog')` mp_tac >>
     qpat_assum `LENGTH (assemble prog') < 65536` mp_tac >>
     qpat_assum `imm_len_mods mods + _ + _ <= w2n fmp` mp_tac >>
     qpat_assum `w2n fmp < 2 ** 254` mp_tac >>
     simp[NoAsms, wordsTheory.dimword_def, venomLayoutTheory.dimindex_256] >>
     decide_tac) >>
  `!(H0 : (bool # bytes32 # type_value) list # num list) body_ce body_src s epi se.
     compile_constructor_epilogue (LENGTH runtime_bc) (imm_len_mods mods) imm epi = ((),se) /\
     fn_has_code epi se fn /\ fn_inst_ids_distinct fn /\ ~block_is_terminated epi /\
     same_frame ctor_ce body_ce /\ ctor_ce.ce_is_ctor /\
     (imm_len_mods mods <> 0 ==>
        ctor_ce.ce_imm_alloca = SOME imm /\ (!x. imm = Var x ==> not_fresh_at epi x)) /\
     stmt_state_rel H0 deploy_unit.cu_context fn body_ce cx body_src s /\
     immutable_frame_mods fn body_ce cx body_src s /\
     ~s.vs_halted /\ s.vs_current_bb = epi.cs_current_bb /\
     s.vs_inst_idx = LENGTH epi.cs_current_insts ==>
     ?final codepos fuel tail_bb pre ret.
       gas_path_mem deploy_unit.cu_context fn s 0 (Halt final) /\
       run_from fuel deploy_unit.cu_context fn s = Halt final /\
       mem_safe_run fuel deploy_unit.cu_context fn s /\
       lookup_block s.vs_current_bb fn.fn_blocks = SOME tail_bb /\
       isPREFIX (pre ++ [ret]) (DROP s.vs_inst_idx tail_bb.bb_instructions) /\
       EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
                  ~is_terminator i.inst_opcode) pre /\ ret.inst_opcode = RETURN /\
       FLOOKUP s.vs_labels "runtime_begin" = SOME codepos /\ final.vs_halted /\
       final.vs_returndata =
         TAKE (LENGTH runtime_bc)
           (DROP (w2n codepos) s.vs_code ++ REPLICATE (LENGTH runtime_bc) 0w) ++
         TAKE (imm_len_mods mods) (s.vs_memory ++ REPLICATE (imm_len_mods mods) 0w) /\
       final.vs_accounts = s.vs_accounts /\ final.vs_transient = s.vs_transient /\
       final.vs_logs = s.vs_logs /\ final.vs_outcomes = s.vs_outcomes /\
       final.vs_requests = s.vs_requests /\ final.vs_pending_deletions = s.vs_pending_deletions /\
       final.vs_call_ctx = s.vs_call_ctx /\ final.vs_tx_ctx = s.vs_tx_ctx /\
       final.vs_block_ctx = s.vs_block_ctx /\ final.vs_data_section = s.vs_data_section /\
       final.vs_immutables = s.vs_immutables /\ final.vs_code = s.vs_code /\
       final.vs_labels = s.vs_labels /\
       immutables_rel_mods ctor_ce cx.txn.target ctor_ce.ce_is_ctor body_src s` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     linked_ctor_epilogue_frame_fields_tac >>
     `body_ce.ce_is_ctor /\ (imm_len_mods mods <> 0 ==>
         body_ce.ce_imm_alloca = SOME imm /\ (!x. imm = Var x ==> not_fresh_at epi x))` by
       (conj_tac >- simp[] >> disch_tac >> first_x_assum drule >> simp[]) >>
     `immutables_rel_mods ctor_ce cx.txn.target ctor_ce.ce_is_ctor body_src s` by
       (qpat_assum `immutable_frame_mods fn body_ce cx body_src s`
          (mp_tac o cj 1 o PURE_REWRITE_RULE [bodyFullPostsModsTheory.immutable_frame_mods_def]) >>
        simp[immutables_rel_mods_def, immutables_rel_def]) >>
     linked_ctor_epilogue_terminal_tac >>
     linked_ctor_epilogue_halt_tac >>
     qexistsl_tac [`ep_final`,`ep_codepos`,`ep_fuel`,`tail_bb`,`ep_pre`,
                   `mk_inst ep_id RETURN [ep_dst;ep_sz] []`] >>
     rpt conj_tac >> FIRST [FIRST_ASSUM ACCEPT_TAC,
       qpat_assum `emitted_insts epi se = _` (fn code =>
         qpat_assum `isPREFIX (emitted_insts epi se) _` (ACCEPT_TAC o PURE_REWRITE_RULE [code])),
       simp[NoAsms, mk_inst_def]]);

(* Keep the source observation and the marked execution at the same raw entry. *)
fun linked_ctor_replay_source_tac frame =
  qabbrev_tac `body_src = es0 with outcomes := SOME (MAP SND (call_trace ^frame))` >>
  qabbrev_tac `source_finish = \res (s:evaluation_state).
    case res of
       INR HaltException => INL (finalize_pending_deletions
         (abstract_machine_from_state am_c.sources am_c.exports am_c.layouts s), s.requests)
     | INR (ReturnException v) =>
         (case safe_cast NoneTV v of NONE => INR (Error (TypeError "ext cast ret"))
          | SOME _ => INL (finalize_pending_deletions
              ((abstract_machine_from_state am_c.sources am_c.exports am_c.layouts s)
                with sources updated_by CONS (tx.target,mods)), s.requests))
     | INR exc => INR exc
     | INL () => INL (finalize_pending_deletions
         ((abstract_machine_from_state am_c.sources am_c.exports am_c.layouts s)
           with sources updated_by CONS (tx.target,mods)), s.requests)` >>
  `!gs res src. eval_stmts cx raw_body (body_src with gas_obs := gs) = (res,src) ==>
       load_contract_trace (SOME (MAP SND (call_trace ^frame))) gs am tx mods exps =
         (source_finish res src,src.storage_trace)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!orc gs res st. eval_stmts _ raw_body _ = (res,st) ==> _`
       (qspecl_then [`SOME (MAP SND (call_trace ^frame))`,`gs`,`res`,`src`] mp_tac) >>
     qpat_assum `Abbrev (cx = deploy_evaluation_context_mods mods am tx)`
       (fn c => PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] c)]) >>
     simp[NoAsms, Abbr `body_src`, Abbr `source_finish`,
          vyperStateTheory.evaluation_state_fupdcanon] >>
     qpat_assum `eval_stmts cx raw_body _ = (res,src)`
       (fn ev => simp[NoAsms, SIMP_RULE (srw_ss()) [Abbr `body_src`,
          vyperStateTheory.evaluation_state_fupdcanon] ev]));

(* Keep the source execution where it is needed for the selected
   correctness replay; the gas consumer only needs the trace. *)
fun linked_ctor_replay_eval_projection retain_eval readings =
  if retain_eval then
    `(!tail. eval_stmts cx raw_body
       (body_src with gas_obs := gas_explicit marks ^readings ++ tail) =
       (res,ee with gas_obs := tail)) /\ `
  else [];

(* The zero-mark prefix is replayed at the very same body state and ghosts. *)
fun linked_ctor_replay_prefix_goal_tac retain_eval frame =
  Q.SUBGOAL_THEN (`!root ent G0 tn0 Q R.
    ent.vs_gas_readings = root.vs_gas_readings /\
    (!gs. eval_stmts cx cpkg6 (body_src with gas_obs := gs) =
          eval_stmts cx raw_body (body_src with gas_obs := gs)) /\
    (!H. gas_origin_ptr_path (linked_ret_DF H,imm_len_mods mods,
          gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context,
          deploy_unit.cu_context,fn,[]) (root,FEMPTY,entry_taint) [] (OK ent,G0,tn0)) /\
    gas_outcome_full_mods (linked_ret_DF,imm_len_mods mods,
      gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context,
      deploy_unit.cu_context,fn,[]) mods cx (initial_state am [])
      (eval_stmts cx cpkg6) (body_src,ent,G0,tn0) Q R ==>
    ?marks.
      ((?H leaf pg G tn finish.
           gas_origin_ptr_focus (linked_ret_DF H,imm_len_mods mods,
             gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context,
             deploy_unit.cu_context,fn,[]) (root,FEMPTY,entry_taint) marks
             (leaf,pg,G,tn,finish)) /\
       ((!tail. ~deploy_storage_ok_mods mods exps am tx (MAP SND (call_trace ^frame))
             (gas_explicit marks root.vs_gas_readings ++ tail)) \/
        (!tail. deploy_source_exempt_mods mods
            (load_contract (SOME (MAP SND (call_trace ^frame)))
              (gas_explicit marks root.vs_gas_readings ++ tail) am tx mods exps)))) \/
      (?res ee r G' tn'.
        ` @ linked_ctor_replay_eval_projection retain_eval ``root.vs_gas_readings`` @ `
        (!tail. load_contract_trace (SOME (MAP SND (call_trace ^frame)))
          (gas_explicit marks root.vs_gas_readings ++ tail) am tx mods exps =
          (source_finish res (ee with gas_obs := tail),ee.storage_trace)) /\
        storage_trace_domain cx (initial_state am []) ee.storage_trace /\
        !H. valid_horizon cx (initial_state am []) H ee.storage_trace ==>
          gas_origin_ptr_path (linked_ret_DF H,imm_len_mods mods,
            gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context,
            deploy_unit.cu_context,fn,[]) (root,FEMPTY,entry_taint) marks (r,G',tn') /\
          ((?t. r = OK t /\ Q H res (ee with gas_obs := []) G' tn' t) \/
           (exit_result r /\ create_size_exit_ok deploy_unit.cu_context res r /\
            R H res (ee with gas_obs := []) (G',tn') r)))`)
    (mk_asm "linked_ctor_replay_prefix");

val linked_ctor_replay_prefix_tac = linked_ctor_replay_prefix_goal_tac false;

val linked_ctor_focus_prepend_tac =
  rename1 `gas_origin_ptr_focus (linked_ret_DF chosen_horizon,_,_,_,_,_)
                  (ent,G0,tn0) marks (focus_fn,focus_pg,focus_g,focus_tn,focus_end)` >>
  qpat_assum `gas_origin_ptr_focus _ (ent,G0,tn0) _ _` (fn focus =>
    qpat_assum `!H. gas_origin_ptr_path _ _ [] (OK ent,G0,tn0)`
      (qspec_then `chosen_horizon` (fn pre =>
        qexistsl_tac [`chosen_horizon`,`focus_fn`,`focus_pg`,`focus_g`,`focus_tn`,`focus_end`] >>
        mp_tac (MATCH_MP (cj 2 fragGasOriginPtrTheory.gas_origin_ptr_focus_rules)
          (CONJ pre focus)) >> simp[NoAsms])));

fun linked_ctor_replay_prefix_open_tac frame =
  map_every qx_gen_tac [`root`,`ent`,`G0`,`tn0`,`Q`,`R`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!gs res src. eval_stmts cx cpkg6 (body_src with gas_obs := gs) = (res,src) ==>
       load_contract_trace (SOME (MAP SND (call_trace ^frame))) gs am tx mods exps =
         (source_finish res src,src.storage_trace)` by
    (qpat_assum `!gs. eval_stmts cx cpkg6 _ = _`
       (fn agree => PURE_REWRITE_TAC [agree]) >> FIRST_ASSUM ACCEPT_TAC) >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (qx_choose_then `marks`
      (DISJ_CASES_THEN2 strip_assume_tac
        (DISJ_CASES_THEN2
          (qx_choosel_then [`body_res`,`body_end`,`body_out`,`body_prov`,`body_taint`]
            (map_every assume_tac o CONJUNCTS))
          strip_assume_tac)) o
      PURE_REWRITE_RULE [gasOutcomeFullModsTheory.gas_outcome_full_mods_def]) >>
  qexists_tac `marks`;

fun linked_ctor_replay_bad_tac frame =
  disj1_tac >> conj_tac >- linked_ctor_focus_prepend_tac >> disj1_tac >>
  qx_gen_tac `tail` >>
  qpat_assum `gas_bad_storage_at _ _ _ _ _ _`
    (qspec_then `tail` mp_tac o PURE_REWRITE_RULE [gasStorageTheory.gas_bad_storage_at_def]) >>
  qpat_assum `ent.vs_gas_readings = root.vs_gas_readings`
    (fn readings => PURE_REWRITE_TAC [readings]) >>
  Cases_on `eval_stmts cx cpkg6 (body_src with gas_obs :=
                gas_explicit marks root.vs_gas_readings ++ tail)` >>
  rename1 `_ = (res,ee)` >>
  simp[NoAsms] >> disch_tac >>
  `load_contract_trace (SOME (MAP SND (call_trace ^frame)))
     (gas_explicit marks root.vs_gas_readings ++ tail) am tx mods exps =
       (source_finish res ee,ee.storage_trace)` by
    (qpat_assum `!gs res src. eval_stmts cx cpkg6 _ = _ ==> _`
      (drule_then ACCEPT_TAC)) >>
  qpat_assum `~storage_trace_domain cx _ ee.storage_trace` mp_tac >>
  qpat_assum `load_contract_trace _ _ am tx mods exps = _` (fn trace =>
    simp[NoAsms, deploy_storage_ok_mods_def, deploy_storage_trace_mods_def, LET_THM,
      trace, Abbr `cx`, storage_trace_domain_def, valid_horizon_def,
      storage_trace_horizon_def, storage_observations_ok_def, EVERY_MEM,
      AC CONJ_ASSOC CONJ_COMM]);

val linked_ctor_replay_exempt_open_tac =
  disj1_tac >> conj_tac >- linked_ctor_focus_prepend_tac >> disj2_tac >>
  drule gasExemptCertModsTheory.gas_exempt_cert_execution_mods >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!f : evaluation_state -> unit evaluation_result. !st err ss.
     vyperState$ignore_bind f (vyperState$return ()) st = (INR (Error err),ss) ==>
     f st = (INR (Error err),ss)` by
    (POP_ASSUM_LIST (K ALL_TAC) >>
     simp[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, AllCaseEqs()] >> metis_tac[]);

val linked_ctor_replay_exempt_eval_tac =
  qx_gen_tac `tail` >>
  qpat_assum `!tail. ignore_bind _ _ _ = _` (qspec_then `tail` mp_tac) >>
  qpat_assum `ent.vs_gas_readings = root.vs_gas_readings`
    (fn readings => PURE_REWRITE_TAC [readings]) >> disch_tac >>
  qpat_assum `!f st err ss. vyperState$ignore_bind _ _ _ = _ ==> _`
    (drule_then assume_tac);

val linked_ctor_replay_exempt_finish_tac =
  qpat_assum `!gs res src. eval_stmts cx cpkg6 _ = _ ==> _`
    (drule_then (fn trace => simp[NoAsms, load_contract_def, trace,
       deploy_source_exempt_mods_def]));

val linked_ctor_replay_exempt_error_tac =
  qpat_assum `Abbrev (source_finish = _)` (fn fin =>
    qpat_assum `unspecified_behaviour_exempt_mods mods _` (fn ex =>
      simp[NoAsms, REWRITE_RULE [markerTheory.Abbrev_def] fin,ex]));

val linked_ctor_replay_started_tac =
  disj2_tac >> qexistsl_tac [`body_res`,`body_end`,`body_out`,`body_prov`,`body_taint`];

val linked_ctor_replay_eval_tac =
  qpat_assum `!gs. eval_stmts cx cpkg6 _ = _` (fn agree =>
    qpat_assum `ent.vs_gas_readings = root.vs_gas_readings` (fn readings =>
      qpat_assum `!tail. eval_stmts cx cpkg6 _ = (_,body_end with gas_obs := tail)`
        (ACCEPT_TAC o PURE_REWRITE_RULE [agree,readings])));

val linked_ctor_replay_trace_tac =
  qx_gen_tac `tail` >>
  qpat_assum `!tail. eval_stmts cx cpkg6 _ = (_,body_end with gas_obs := tail)`
    (qspec_then `tail` (fn run =>
       qpat_assum `ent.vs_gas_readings = root.vs_gas_readings`
         (fn readings =>
           qpat_assum `!gs res src. eval_stmts cx cpkg6 _ = _ ==> _`
             (fn trace => mp_tac (MATCH_MP trace (REWRITE_RULE [readings] run)))))) >>
  simp[NoAsms];

val linked_ctor_replay_path_tac =
  (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >>
  qx_gen_tac `replay_h` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (ent,G0,tn0) _ _ /\ _`
    (qspec_then `replay_h` mp_tac) >>
  (impl_tac >- (FIRST_ASSUM ACCEPT_TAC ORELSE FAIL_TAC "replay horizon")) >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  conj_tac >- (
    qpat_assum `!H. gas_origin_ptr_path _ _ [] (OK ent,G0,tn0)`
      (qspec_then `replay_h` (mp_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_append)) >>
    simp[NoAsms] >> disch_then irule >>
    (FIRST_ASSUM ACCEPT_TAC ORELSE FAIL_TAC "replay append")) >>
  (FIRST_ASSUM ACCEPT_TAC ORELSE FAIL_TAC "replay post");

(* Place the common constructor tail at the actual exit block. *)
val linked_ctor_install_epilogue_exit_tac =
  `st_epilogue = st_exit` by
    (qpat_assum `_ st_exit = ((),st_epilogue)` mp_tac >>
     simp[NoAsms, comp_return_def]);

val linked_ctor_install_epilogue_placement_tac =
  `st_epilogue.cs_current_bb = exit_lbl /\ st_epilogue.cs_current_insts = [] /\
   st_epilogue.cs_next_var = sj.cs_next_var` by
    (qpat_assum `st_epilogue = st_exit` SUBST1_TAC >>
     drule_then (fn th => simp[NoAsms,th]) emitHelperPropsTheory.new_block_props) >>
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  `fn_has_code st_epilogue st_final fn /\ ~block_is_terminated st_epilogue` by
    simp[block_is_terminated_def] >>
  pop_assum (map_every assume_tac o CONJUNCTS);

val linked_ctor_install_epilogue_reserved_tac =
  `local_ptrs_reserved ce1 st2` by
    (qpat_assum `compile_register_constructor_args ce_before_registration (build_positional_args _ _) 0 0 st1 = _`
       (mp_then Any mp_tac entryLocalsTheory.compile_register_constructor_args_reserved) >>
     (impl_tac >-
       (qpat_assum `!n l. FLOOKUP ce_before_registration.ce_vars n = SOME l ==> _` mp_tac >>
        qpat_assum `!id p sz. FLOOKUP ce_before_registration.ce_vars id <> SOME (PtrVar (Var p) sz)` mp_tac >>
        qpat_assum `!x. ce_before_registration.ce_imm_alloca = SOME (Var x) ==> _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[entryLocalsTheory.build_positional_args_FST] >> metis_tac[])) >>
     disch_then (ACCEPT_TAC o CONJUNCT1));

val linked_ctor_install_epilogue_fresh_tac =
  `sa.cs_next_var = st2.cs_next_var` by
    drule_then (ACCEPT_TAC o cj 4) emitHelperPropsTheory.fresh_label_props >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (qpat_assum `compile_stmts _ NoLoop NoneT cpkg6 sa = ((),sb)` mp_tac >>
     qspecl_then [`ctor_ce`,`NoLoop`,`NoneT`,`cpkg6`] mp_tac
       (cj 2 stmtLoweringMonoTheory.compile_stmt_cs_mono) >>
     simp[NoAsms, cs_mono_def, exprLoweringPropsTheory.ci_mono_def] >> metis_tac[]) >>
  `sj.cs_next_var = sb.cs_next_var` by
    (qpat_assum `_ sb = ((),sj)` mp_tac >> IF_CASES_TAC >>
     simp[NoAsms, comp_return_def] >>
     disch_then (ACCEPT_TAC o cj 5 o MATCH_MP emitHelperPropsTheory.emit_inst_extends)) >>
  `imm_len_mods mods <> 0 ==> ctor_ce.ce_imm_alloca = SOME imm` by
    (qpat_assum `ctor_ce = _` SUBST1_TAC >> simp[NoAsms]) >>
  `ctor_ce.ce_imm_alloca = ce1.ce_imm_alloca` by
    simp[NoAsms, Abbr `ctor_ce`] >>
  `st2.cs_next_var <= st_epilogue.cs_next_var` by
    (qpat_assum `sa.cs_next_var <= sb.cs_next_var` mp_tac >>
     simp[]) >>
  `!x. ctor_ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at st_epilogue x` by
    (qx_gen_tac `x` >> disch_tac >>
     `ce1.ce_imm_alloca = SOME (Var x)` by
       (qpat_assum `ctor_ce.ce_imm_alloca = ce1.ce_imm_alloca`
          (fn th => pure_rewrite_tac[GSYM th]) >> FIRST_ASSUM ACCEPT_TAC) >>
     `not_fresh_at st2 x` by
       drule_all_then ACCEPT_TAC exprLoweringPropsTheory.local_ptrs_reserved_imm_base >>
     drule_all_then ACCEPT_TAC loweringShapeDefsTheory.not_fresh_at_mono);

val linked_ctor_install_epilogue_static_tac =
  `imm_len_mods mods <> 0 ==>
    ctor_ce.ce_imm_alloca = SOME imm /\ (!x. imm = Var x ==> not_fresh_at st_epilogue x)` by
    (disch_tac >>
     qpat_assum `imm_len_mods mods <> 0 ==> ctor_ce.ce_imm_alloca = SOME imm`
       (drule_then assume_tac) >>
     conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
     qx_gen_tac `x` >> disch_tac >>
     qpat_assum `!x. ctor_ce.ce_imm_alloca = SOME (Var x) ==> _` irule >> simp[]);

val linked_ctor_install_epilogue_entry_tac =
  map_every qx_gen_tac [`body_ce`,`st0`,`src`,`s`,`G0`,`tn0`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `s.vs_current_bb = st_epilogue.cs_current_bb /\
   s.vs_inst_idx = LENGTH st_epilogue.cs_current_insts` by simp[] >>
  pop_assum (map_every assume_tac o CONJUNCTS);

val linked_ctor_install_epilogue_horizon_tac =
  qabbrev_tac `P = \H. valid_horizon cx st0 H src.storage_trace` >>
  `P (storage_trace_horizon src.storage_trace)` by
    simp[Abbr `P`, GSYM vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H src.storage_trace ==> _`
    (qspec_then `storage_trace_horizon src.storage_trace` mp_tac) >>
  (impl_tac >- simp[GSYM vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "epilogue_entry_state_rel")
    (map_every assume_tac o CONJUNCTS));

val linked_ctor_install_epilogue_run_tac =
  asm "linked_epilogue_raw"
    (qspecl_then [`storage_trace_horizon src.storage_trace`,`body_ce`,`src`,`s`,`st_epilogue`,`st_final`] mp_tac) >>
  impl_tac;

val linked_ctor_install_epilogue_run_result_tac =
  disch_then (qx_choosel_then [`tail_final`,`tail_codepos`,`tail_fuel`,`tail_bb`,`tail_pre`,`tail_ret`]
    (map_every assume_tac o CONJUNCTS));

val linked_ctor_install_epilogue_zero_code_tac =
  drule_all_then (qx_choose_then `bb` (map_every assume_tac o CONJUNCTS))
    immutableDeployExecutionTheory.compile_constructor_epilogue_code_placement >>
  qabbrev_tac `eid = st_epilogue.cs_next_id` >>
  qabbrev_tac `buf = "%" ++ toString st_epilogue.cs_next_var` >>
  `isPREFIX
     [mk_inst eid ALLOCA [Lit (n2w (LENGTH runtime_bc))] [buf];
      mk_inst (eid + 1) CODECOPY [Var buf; Label "runtime_begin"; Lit (n2w (LENGTH runtime_bc))] [];
      mk_inst (eid + 2) RETURN [Var buf; Lit (n2w (LENGTH runtime_bc))] []]
     (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `compile_constructor_epilogue _ _ _ st_epilogue = _`
       (mp_tac o REWRITE_RULE []) >>
     qpat_assum `imm_len_mods mods = 0` (fn th => simp[NoAsms,th]) >>
     disch_then (fn cmp =>
       qpat_assum `isPREFIX (emitted_insts st_epilogue st_final) _`
         (mp_tac o REWRITE_RULE [MATCH_MP immutableDeployExecutionTheory.compile_constructor_epilogue_zero_insts cmp])) >>
     simp[NoAsms, Abbr `eid`, Abbr `buf`]) >>
  ntac 3
    (qpat_x_assum `isPREFIX (_::_) (DROP _ _)`
       (strip_assume_tac o MATCH_MP fragGasSeqAbortTheory.instruction_prefix_cursor)) >>
  `MEM (mk_inst eid ALLOCA [Lit (n2w (LENGTH runtime_bc))] [buf]) (fn_insts fn)` by
    (irule fragFuelTheory.lookup_block_get_instruction_fn_insts >>
     qexistsl_tac [`bb`,`s.vs_inst_idx`,`s.vs_current_bb`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC);

val linked_ctor_install_epilogue_zero_tac =
  `LENGTH runtime_bc < dimword (:256)` by
    (qpat_assum `LENGTH runtime_bc + imm_len_mods mods < dimword (:256)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `body_ce.ce_is_ctor` by
    (qpat_assum `same_frame ctor_ce body_ce` mp_tac >>
     qpat_assum `ctor_ce.ce_is_ctor` mp_tac >>
     simp[NoAsms, bodySimTheory.same_frame_def, compile_env_component_equality]) >>
  qpat_assum `!body_ce D H ee s G tn bb id buf. _ ==> !fuel. _`
    (qspecl_then [`body_ce`,`linked_ret_DF H`,`H`,`src`,`s`,`G0`,`tn0`,`bb`,`eid`,`buf`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
  disch_then (qspec_then `tail_fuel` ACCEPT_TAC);

val linked_ctor_install_epilogue_positive_tac =
  `0 < imm_len_mods mods` by decide_tac >>
  qpat_assum `!D ctx fn body_ce ctor_ce cx ee H G tn rt cap imm epi se s fuel final codepos. _ ==> _`
    irule;

val linked_ctor_install_epilogue_ptr_goal =
  sg `!H. P H ==> ptr_safe_run (linked_ret_DF H) (imm_len_mods mods) tail_fuel
     deploy_unit.cu_context fn [] G0 tn0 s`;

val linked_ctor_install_epilogue_ptr_setup_tac =
  qx_gen_tac `H` >> simp[NoAsms, Abbr `P`] >> disch_tac >>
  qpat_assum `!H. valid_horizon cx st0 H src.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- FIRST_ASSUM ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS);

val linked_ctor_install_epilogue_ptr_fresh_tac =
  `ctor_ce.ce_imm_alloca = SOME imm /\ (!x. imm = Var x ==> not_fresh_at st_epilogue x)` by
    (qpat_assum `imm_len_mods mods <> 0 ==> _ /\ _` (drule_then ACCEPT_TAC)) >>
  pop_assum (map_every assume_tac o CONJUNCTS);

val linked_ctor_install_epilogue_endpoint_tac =
  qpat_assum `!P DF H0 pre ret s tail_fuel G tn bb final. _ ==> _`
    (qspecl_then [`P`,`linked_ret_DF`,`storage_trace_horizon src.storage_trace`,`tail_pre`,`tail_ret`,
                 `s`,`tail_fuel`,`G0`,`tn0`,`tail_bb`,`tail_final`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`tail_prov`,`tail_taint`] (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`tail_final`,`tail_prov`,`tail_taint`,`tail_codepos`] >>
  rpt (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >>
  qpat_assum `!H. P H ==> gas_origin_ptr_path _ _ _ _` mp_tac >>
  simp[NoAsms, Abbr `P`];

val linked_ctor_install_epilogue_open_tac =
  qpat_assum `(!body_ce st0 src sx G0 tn0. _ ==> _) ==> frame_ret_ok_full_mods _ _ _ _ _ _` mp_tac >>
  impl_keep_tac;

(* The terminal installation fields shared by explicit return and fallthrough. *)
val linked_ctor_terminal_install_tac =
  qabbrev_tac `installed = \(H : (bool # bytes32 # type_value) list # num list) (src:evaluation_state) r.
    ?before final codepos.
      r = Halt final /\ final.vs_halted /\
      state_rel H fn ctor_ce cx src before /\
      immutables_rel_mods ctor_ce cx.txn.target T src before /\
      FLOOKUP before.vs_labels "runtime_begin" = SOME codepos /\
      final.vs_returndata =
        TAKE (LENGTH runtime_bc) (DROP (w2n codepos) before.vs_code ++ REPLICATE (LENGTH runtime_bc) 0w) ++
        TAKE (imm_len_mods mods) (before.vs_memory ++ REPLICATE (imm_len_mods mods) 0w) /\
      final.vs_accounts = before.vs_accounts /\ final.vs_transient = before.vs_transient /\
      final.vs_logs = before.vs_logs /\ final.vs_outcomes = before.vs_outcomes /\
      final.vs_requests = before.vs_requests /\ final.vs_pending_deletions = before.vs_pending_deletions /\
      final.vs_call_ctx = before.vs_call_ctx /\ final.vs_tx_ctx = before.vs_tx_ctx /\
      final.vs_block_ctx = before.vs_block_ctx /\ final.vs_data_section = before.vs_data_section /\
      final.vs_immutables = before.vs_immutables /\ final.vs_code = before.vs_code /\
      final.vs_labels = before.vs_labels`;

val linked_ctor_terminal_exit_goal_tac =
  Q.SUBGOAL_THEN `!H res src (gt : (string, num # num) fmap # taint) r.
    (!tail. stmt_exit_ptr (\v ee gt r. v = NoneV /\ installed H ee r)
                          (src with gas_obs := tail) res gt r) /\
    halt_exit H cx (src with gas_obs := []) res r ==>
    (res = INR (ReturnException NoneV) /\ installed H (src with <|gas_obs := []; scopes := []|>) r) \/
    (res = INR HaltException /\ ?final. r = Halt final /\ final.vs_returndata = [] /\
       halt_rel H cx (src with gas_obs := []) final) \/
    (?err final abort. res = INR err /\ r = Abort abort final /\ expr_exit res r)`
    (mk_asm "linked_ctor_classify_exit");

val linked_ctor_terminal_exit_open_tac =
  map_every qx_gen_tac [`post_h`,`post_res`,`post_src`,`post_gt`,`post_out`] >>
  strip_tac >>
  qpat_assum `!tail. stmt_exit_ptr _ _ _ _ _` (fn post =>
    qpat_assum `halt_exit _ _ _ _ _` (fn halt =>
      POP_ASSUM_LIST (K ALL_TAC) >>
      qspec_then `[]` mp_tac post >> mp_tac halt)) >>
  simp[NoAsms, bodyPtrDefsTheory.stmt_exit_ptr_def, exprSimDefsTheory.halt_exit_def,
       vyperStateTheory.evaluation_state_fupdcanon] >> rpt strip_tac;

val linked_ctor_terminal_exit_expr_tac =
  disj2_tac >>
  Cases_on `post_out` >> Cases_on `post_res` >>
  gvs[exprSimDefsTheory.expr_exit_def] >>
  rename1 `expr_exit (INR ex) _` >> Cases_on `ex` >>
  gvs[exprSimDefsTheory.expr_exit_def] >>
  rename1 `expr_exit (INR (Error err)) _` >> Cases_on `err` >>
  gvs[exprSimDefsTheory.expr_exit_def];

(* Fallthrough executes the placed jump and then the same epilogue as Return NONE. *)
val linked_ctor_fallthrough_goal_tac =
  sg `!body_ce src landed body_g body_tn.
    same_frame ctor_ce body_ce /\
    emit_inst JMP [Label exit_lbl] [] sb = ((),sj) /\ fn_has_code sb sj fn /\
    ~landed.vs_halted /\ landed.vs_current_bb = sb.cs_current_bb /\
    landed.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (ctx_has_dalloca deploy_unit.cu_context ==> allocas_below_fmp landed) /\
    storage_trace_domain cx (initial_state am []) src.storage_trace /\
    (!H. valid_horizon cx (initial_state am []) H src.storage_trace ==>
         stmt_state_rel H deploy_unit.cu_context fn body_ce cx src landed /\
         immutable_frame_mods fn body_ce cx src landed /\
         ghost_inv_at_mods (linked_ret_DF H) (imm_len_mods mods) NONE body_ce cx src body_g body_tn landed) ==>
    ?final tail_g tail_tn.
      !H. valid_horizon cx (initial_state am []) H src.storage_trace ==>
          gas_origin_ptr_path
            (linked_ret_DF H,imm_len_mods mods,
             gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context,deploy_unit.cu_context,fn,[])
            (landed,body_g,body_tn) [] (Halt final,tail_g,tail_tn) /\
          installed H (src with scopes := []) (Halt final)`;

val linked_ctor_fallthrough_open_tac =
  map_every qx_gen_tac [`fall_ce`,`fall_src`,`landed`,`fall_G`,`fall_tn`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `fall_jump = jump_to exit_lbl landed` >>
  `~fall_jump.vs_halted /\ fall_jump.vs_current_bb = exit_lbl /\ fall_jump.vs_inst_idx = 0` by
    (qpat_assum `~landed.vs_halted` mp_tac >>
     simp[NoAsms, Abbr `fall_jump`, jump_to_def]) >>
  pop_assum (map_every assume_tac o CONJUNCTS);

val linked_ctor_fallthrough_fmp_goal_tac =
  sg `(ctx_has_dalloca deploy_unit.cu_context ==> allocas_below_fmp fall_jump)`;

val linked_ctor_fallthrough_fmp_tac =
  simp[NoAsms, Abbr `fall_jump`, allocas_below_fmp_def, jump_to_def] >>
  qpat_assum `ctx_has_dalloca _ ==> allocas_below_fmp landed`
    (ACCEPT_TAC o REWRITE_RULE [allocas_below_fmp_def]);

val linked_ctor_fallthrough_inv_goal_tac =
  sg `!H. valid_horizon cx (initial_state am []) H fall_src.storage_trace ==>
      stmt_state_rel H deploy_unit.cu_context fn fall_ce cx fall_src fall_jump /\
      immutable_frame_mods fn fall_ce cx fall_src fall_jump /\
      ghost_inv_at_mods (linked_ret_DF H) (imm_len_mods mods) NONE fall_ce cx fall_src fall_G fall_tn fall_jump`;

val linked_ctor_fallthrough_inv_tac =
  qx_gen_tac `jump_h` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ landed /\ _`
    (qspec_then `jump_h` (drule_then (map_every assume_tac o CONJUNCTS)));

val linked_ctor_fallthrough_state_tac =
  simp[NoAsms, Abbr `fall_jump`, exprLoweringPropsTheory.stmt_state_rel_jump_to] >>
  FIRST_ASSUM ACCEPT_TAC;

val linked_ctor_fallthrough_imm_tac =
  `immutable_frame_mods fn fall_ce cx fall_src fall_jump =
   immutable_frame_mods fn fall_ce cx fall_src landed` by
    simp[NoAsms, Abbr `fall_jump`, jump_to_def, bodyFullPostsModsTheory.immutable_frame_mods_def,
         immutables_rel_mods_def, immutable_alloca_sep_mods_def, immutables_rel_def,
         exprLoweringPropsTheory.immutable_alloca_sep_def, local_region_def, lookup_var_def] >>
  pop_assum SUBST1_TAC >> FIRST_ASSUM ACCEPT_TAC;

val linked_ctor_fallthrough_ghost_tac =
  `ghost_inv_at_mods (linked_ret_DF jump_h) (imm_len_mods mods) NONE fall_ce cx fall_src fall_G fall_tn fall_jump =
   ghost_inv_at_mods (linked_ret_DF jump_h) (imm_len_mods mods) NONE fall_ce cx fall_src fall_G fall_tn landed` by
    simp[NoAsms, Abbr `fall_jump`, jump_to_def, bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def,
         bodyPtrDefsTheory.ptr_covers_def, bodyPtrDefsTheory.stor_taint_ok_at_def,
         lookup_var_def, allocas_from_def, bodyPtrDefsTheory.return_buf_ptr_def] >>
  pop_assum SUBST1_TAC >> FIRST_ASSUM ACCEPT_TAC;

val linked_ctor_fallthrough_epilogue_tac =
  qpat_assum `!body_ce st0 src sx G0 tn0. _ ==> ?final G' tn' codepos. _`
    (qspecl_then [`fall_ce`,`initial_state am []`,`fall_src`,`fall_jump`,`fall_G`,`fall_tn`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`fall_final`,`tail_G`,`tail_tn`,`fall_codepos`]
    (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`fall_final`,`tail_G`,`tail_tn`] >>
  qx_gen_tac `fall_h` >> disch_tac;

val linked_ctor_fallthrough_jmp_goal_tac =
  sg `gas_origin_ptr_path
       (linked_ret_DF fall_h,imm_len_mods mods,
        gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context,deploy_unit.cu_context,fn,[])
        (landed,fall_G,fall_tn) [] (OK fall_jump,fall_G,fall_tn)`;

val linked_ctor_fallthrough_jmp_tac =
  `allocas_from (imm_len_mods mods) landed` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ landed /\ _`
       (drule_then (mp_tac o cj 3)) >>
     simp[NoAsms, bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def] >>
     strip_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  simp[NoAsms, Abbr `fall_jump`] >> irule fragGasEmitCtrlTheory.emit_jmp_origin_ptr >>
  reverse (rpt conj_tac)
  >- (qexistsl_tac [`sb`,`sj`] >> rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  FIRST_ASSUM ACCEPT_TAC;

val linked_ctor_fallthrough_append_tac =
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (fall_jump,fall_G,fall_tn) [] _`
    (drule_then (fn tail =>
      qpat_assum `gas_origin_ptr_path _ (landed,fall_G,fall_tn) [] _`
        (fn jump => mp_tac (MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_append jump) >>
          simp[NoAsms,tail])));

val linked_ctor_fallthrough_install_tac =
  simp[NoAsms, Abbr `installed`] >> qexistsl_tac [`fall_jump`,`fall_codepos`] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ fall_jump /\ _`
    (qspec_then `fall_h` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  (conj_tac >- FIRST_ASSUM ACCEPT_TAC);

val linked_ctor_fallthrough_install_state_tac =
  irule stmtSimReturnTheory.constructor_exit_state_rel >>
  qexists_tac `fall_ce` >>
  rpt (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >>
  qpat_assum `stmt_state_rel _ _ _ fall_ce _ _ fall_jump`
    (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [exprLoweringPropsTheory.stmt_state_rel_def]);

val linked_ctor_fallthrough_install_imm_tac =
  `ctor_ce.ce_modules = fall_ce.ce_modules /\
   ctor_ce.ce_module_vars = fall_ce.ce_module_vars /\ fall_ce.ce_is_ctor` by
    (qpat_assum `same_frame ctor_ce fall_ce`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [bodySimTheory.same_frame_def]) >>
     qpat_assum `ctor_ce.ce_is_ctor` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[compile_env_component_equality] >> strip_tac >> simp[]) >>
  qpat_assum `immutable_frame_mods _ _ _ _ fall_jump`
    (mp_tac o CONJUNCT1 o REWRITE_RULE [bodyFullPostsModsTheory.immutable_frame_mods_def]) >>
  qpat_assum `fall_ce.ce_is_ctor`
    (fn ctor => simp[NoAsms, ctor, immutables_rel_mods_def, immutables_rel_def]) >>
  qpat_assum `ctor_ce.ce_modules = fall_ce.ce_modules` (fn modules =>
    qpat_assum `ctor_ce.ce_module_vars = fall_ce.ce_module_vars` (fn locs =>
      PURE_REWRITE_TAC [modules, locs])) >> simp[NoAsms];

(* Normalize the running replay branch at the body fragment's landing and exit posts. *)
val linked_ctor_terminal_replay_goal_tac =
  Q.SUBGOAL_THEN `!root marks res ee out G tn Q R.
    storage_trace_domain cx (initial_state am []) ee.storage_trace /\
    (if block_is_terminated sb then comp_return () else emit_inst JMP [Label exit_lbl] [])
      sb = ((),sj) /\ fn_has_code sb sj fn /\
    (!H t. Q H res (ee with gas_obs := []) G tn t ==>
       stmt_lands NoLoop sb res t /\ ~t.vs_halted /\ ~block_is_terminated sb /\
       cenv_top_ext ctor_ce ce_end ee.scopes /\
       stmt_state_rel H deploy_unit.cu_context fn ce_end cx (ee with gas_obs := []) t /\
       immutable_frame_mods fn ce_end cx (ee with gas_obs := []) t /\
       (ctx_has_dalloca deploy_unit.cu_context ==> allocas_below_fmp t) /\
       ghost_inv_at_mods (linked_ret_DF H) (imm_len_mods mods) NONE ce_end cx
            (ee with gas_obs := []) G tn t) /\
    (!H. R H res (ee with gas_obs := []) (G,tn) out ==>
       (!tail. stmt_exit_ptr (\v src gt r. v = NoneV /\ installed H src r)
                      (ee with gas_obs := tail) res (G,tn) out) /\
       halt_exit H cx (ee with gas_obs := []) res out) /\
    (!H. valid_horizon cx (initial_state am []) H ee.storage_trace ==>
       gas_origin_ptr_path (linked_ret_DF H,imm_len_mods mods,
         gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context,deploy_unit.cu_context,fn,[])
         (root,FEMPTY,entry_taint) marks (out,G,tn) /\
       ((?t. out = OK t /\ Q H res (ee with gas_obs := []) G tn t) \/
        exit_result out /\ create_size_exit_ok deploy_unit.cu_context res out /\
        R H res (ee with gas_obs := []) (G,tn) out)) ==>
    ?terminal end_g end_tn. exit_result terminal /\
      create_size_exit_ok deploy_unit.cu_context res terminal /\
      !H. valid_horizon cx (initial_state am []) H ee.storage_trace ==>
        gas_origin_ptr_path (linked_ret_DF H,imm_len_mods mods,
          gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context,deploy_unit.cu_context,fn,[])
          (root,FEMPTY,entry_taint) marks (terminal,end_g,end_tn) /\
        ((res = INL () \/ res = INR (ReturnException NoneV)) /\
           installed H (ee with <|gas_obs := []; scopes := []|>) terminal \/
         (res = INR HaltException /\ ?final. terminal = Halt final /\
            final.vs_returndata = [] /\ halt_rel H cx (ee with gas_obs := []) final) \/
         (?err final abort. res = INR err /\ terminal = Abort abort final /\ expr_exit res terminal))`
    (mk_asm "linked_ctor_terminal_replay");

val linked_ctor_terminal_replay_open_tac =
  map_every qx_gen_tac [`replay_root`,`replay_marks`,`replay_res`,`replay_src`,
                     `replay_out`,`replay_G`,`replay_tn`,`replay_Q`,`replay_R`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx (initial_state am []) (storage_trace_horizon replay_src.storage_trace)
     replay_src.storage_trace` by
    (PURE_REWRITE_TAC [GSYM vyperStorageFootprintTheory.storage_trace_domain_def] >>
     FIRST_ASSUM ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ (replay_out,replay_G,replay_tn) /\ _`
    (qspec_then `storage_trace_horizon replay_src.storage_trace` mp_tac) >>
  (impl_tac >- FIRST_ASSUM ACCEPT_TAC) >>
  disch_then (DISJ_CASES_THEN2
    (qx_choose_then `replay_landed` (map_every assume_tac o CONJUNCTS))
    (map_every assume_tac o CONJUNCTS) o CONJUNCT2);

val linked_ctor_terminal_replay_exit_tac =
  qexistsl_tac [`replay_out`,`replay_G`,`replay_tn`] >>
  ntac 2 (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >>
  qx_gen_tac `replay_h` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ (replay_out,replay_G,replay_tn) /\ _`
    (qspec_then `replay_h` (drule_then (CONJUNCTS_THEN2 assume_tac (mk_asm "replay_alts")))) >>
  (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >>
  asm_x "replay_alts" (DISJ_CASES_THEN2
    (qx_choose_then `impossible` (mp_tac o CONJUNCT1))
    (assume_tac o CONJUNCT2 o CONJUNCT2))
  >- (disch_then (fn eq =>
        qpat_assum `exit_result replay_out`
          (fn ex => mp_tac (REWRITE_RULE [eq,exit_result_def] ex))) >> simp[]) >>
  qpat_assum `!H. replay_R H _ _ _ _ ==> _`
    (qspec_then `replay_h` (drule_then (mk_asm "linked_ctor_at_exit")));

val linked_ctor_terminal_replay_exit_close_tac =
  asm "linked_ctor_classify_exit" (fn classify =>
    asm "linked_ctor_at_exit" (mp_tac o MATCH_MP classify)) >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[];

val linked_ctor_terminal_replay_landed_tac =
  qpat_x_assum `replay_out = OK replay_landed` SUBST_ALL_TAC >>
  `!H. valid_horizon cx (initial_state am []) H replay_src.storage_trace ==>
    gas_origin_ptr_path (linked_ret_DF H,imm_len_mods mods,
         gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context,deploy_unit.cu_context,fn,[])
         (replay_root,FEMPTY,entry_taint) replay_marks (OK replay_landed,replay_G,replay_tn) /\
    replay_Q H replay_res (replay_src with gas_obs := []) replay_G replay_tn replay_landed` by
    (qx_gen_tac `hr` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ (OK replay_landed,_,_) /\ _`
       (qspec_then `hr` (drule_then mp_tac)) >>
     simp[NoAsms, exit_result_def]);

val linked_ctor_terminal_replay_land_fields_tac =
  qpat_assum `!H t. replay_Q H _ _ _ _ t ==> _`
    (qspecl_then [`storage_trace_horizon replay_src.storage_trace`,`replay_landed`] (drule_then assume_tac)) >>
  qpat_x_assum `stmt_lands NoLoop sb replay_res replay_landed /\ _`
    (strip_assume_tac o PURE_REWRITE_RULE [loweringPostsTheory.stmt_lands_def,
          stmtLoweringTheory.loop_ctx_distinct]) >>
  qpat_assum `cenv_top_ext ctor_ce ce_end _`
    (assume_tac o MATCH_MP bodySimTheory.cenv_top_ext_same_frame) >>
  `emit_inst JMP [Label exit_lbl] [] sb = ((),sj)` by
    (qpat_assum `(if block_is_terminated sb then _ else _) sb = _` mp_tac >>
     qpat_assum `~block_is_terminated sb` (fn nt => simp[NoAsms,nt]));

val linked_ctor_terminal_replay_land_epilogue_tac =
  qpat_assum `!body_ce src landed body_g body_tn. _ ==> ?final tail_g tail_tn. _`
    (qspecl_then [`ce_end`,`replay_src with gas_obs := []`,`replay_landed`,`replay_G`,`replay_tn`] mp_tac) >>
  PURE_REWRITE_TAC [vyperStateTheory.evaluation_state_accfupds] >>
  (impl_tac >- (rpt (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >>
    qx_gen_tac `land_h` >> disch_tac >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ (OK replay_landed,_,_) /\ replay_Q _ _ _ _ _ _`
      (qspec_then `land_h` (drule_then (assume_tac o CONJUNCT2))) >>
    qpat_assum `!H t. replay_Q H _ _ _ _ t ==> _`
      (qspecl_then [`land_h`,`replay_landed`] (drule_then strip_assume_tac)) >>
    rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`terminal_state`,`terminal_G`,`terminal_tn`] assume_tac) >>
  qexistsl_tac [`Halt terminal_state`,`terminal_G`,`terminal_tn`] >>
  simp[NoAsms, exit_result_def] >> qx_gen_tac `replay_h` >> disch_tac;

val linked_ctor_terminal_replay_land_close_tac =
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ (OK replay_landed,_,_) /\ replay_Q _ _ _ _ _ _`
    (qspec_then `replay_h` (drule_then (assume_tac o CONJUNCT1))) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ (replay_landed,replay_G,replay_tn) [] _ /\ _`
    (qspec_then `replay_h` (drule_then strip_assume_tac)) >>
  (conj_tac >-
    (qpat_assum `gas_origin_ptr_path _ (replay_landed,replay_G,replay_tn) [] (Halt terminal_state,_,_)`
       (fn tail =>
         qpat_assum `gas_origin_ptr_path _ _ replay_marks (OK replay_landed,replay_G,replay_tn)`
           (qspecl_then [`replay_landed`,`replay_G`,`replay_tn`,`[]`] mp_tac o
            MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
         simp[NoAsms,tail]))) >>
  disj1_tac >>
  (conj_tac >- (disj1_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
  simp[NoAsms, vyperStateTheory.evaluation_state_fupdcanon] >> FIRST_ASSUM ACCEPT_TAC;

(* Specialize the replay to the actual stmt_frag_full_mods posts. *)
val linked_ctor_native_source_tac =
  `(body_src:evaluation_state).gas_obs = []` by
    (qpat_assum `Abbrev (body_src = _)`
       (PURE_REWRITE_TAC o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `es0 = unpaid with accounts := _` SUBST1_TAC >>
     simp[NoAsms, Abbr `unpaid`, vyperInterpreterTheory.initial_state_def,
          vyperStateTheory.evaluation_state_accfupds]) >>
  `body_src with gas_obs := [] = body_src` by
    (qpat_assum `body_src.gas_obs = []` (fn obs =>
       simp[NoAsms, obs, vyperStateTheory.evaluation_state_component_equality]));

val linked_ctor_native_posts_tac =
  qabbrev_tac `native_ret = \H v (ee:evaluation_state) (gt : (string,num # num) fmap # taint) r.
    v = NoneV /\ installed H ee r` >>
  qabbrev_tac `native_R = \H res (ee:evaluation_state) gt r.
    (!tail. stmt_exit_ptr (native_ret H) (ee with gas_obs := tail) res gt r) /\
    halt_exit H cx ee res r /\
    (ctx_has_dalloca deploy_unit.cu_context ==>
     !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s)`;

val linked_ctor_native_land_tac =
  qabbrev_tac `native_Q = \(ent:venom_state) G0 tn0 H res (ee:evaluation_state) G tn t.
    ?body_ce. stmt_lands NoLoop sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ body_ce = ce_end) /\
      cenv_top_ext ctor_ce body_ce ee.scopes /\
      stmt_state_rel H deploy_unit.cu_context fn body_ce cx ee t /\
      immutable_frame_mods fn body_ce cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame NONE body_ce sb t /\ alloca_history fn t /\
      return_buf_sep NONE body_ce ee t /\
      (ctx_has_dalloca deploy_unit.cu_context ==> allocas_below_fmp t) /\
      ent.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (linked_ret_DF H) (imm_len_mods mods) NONE body_ce cx ee G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x ent = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP ent.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
                                 op_taint tn (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame ctor_ce body_src sa ent body_ce ee t /\
      (!aid off sz i.
         FLOOKUP ent.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
         (!n b sz'. local_region ctor_ce body_src.scopes ent n b sz' ==>
                    off + sz <= b \/ b + sz' <= off) /\
         off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem)`;

fun linked_ctor_native_replay_projection_goal_tac retain_eval frame =
  Q.SUBGOAL_THEN (`!root ent G0 tn0.
    ent.vs_gas_readings = root.vs_gas_readings /\
    (!gs. eval_stmts cx cpkg6 (body_src with gas_obs := gs) =
          eval_stmts cx raw_body (body_src with gas_obs := gs)) /\
    (!H. gas_origin_ptr_path (linked_ret_DF H,imm_len_mods mods,
          gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context,
          deploy_unit.cu_context,fn,[]) (root,FEMPTY,entry_taint) [] (OK ent,G0,tn0)) /\
    gas_outcome_full_mods (linked_ret_DF,imm_len_mods mods,
       gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context,
       deploy_unit.cu_context,fn,[]) mods cx (initial_state am [])
       (eval_stmts cx cpkg6) (body_src,ent,G0,tn0) (native_Q ent G0 tn0) native_R ==>
    ?marks.
      ((?H leaf pg G tn finish.
           gas_origin_ptr_focus (linked_ret_DF H,imm_len_mods mods,
             gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context,
             deploy_unit.cu_context,fn,[]) (root,FEMPTY,entry_taint) marks
             (leaf,pg,G,tn,finish)) /\
       ((!tail. ~deploy_storage_ok_mods mods exps am tx (MAP SND (call_trace ^frame))
             (gas_explicit marks root.vs_gas_readings ++ tail)) \/
        (!tail. deploy_source_exempt_mods mods
            (load_contract (SOME (MAP SND (call_trace ^frame)))
              (gas_explicit marks root.vs_gas_readings ++ tail) am tx mods exps)))) \/
      (?res ee terminal G' tn'.
        ` @ linked_ctor_replay_eval_projection retain_eval ``root.vs_gas_readings`` @ `
        (!tail. load_contract_trace (SOME (MAP SND (call_trace ^frame)))
          (gas_explicit marks root.vs_gas_readings ++ tail) am tx mods exps =
          (source_finish res (ee with gas_obs := tail),ee.storage_trace)) /\
        storage_trace_domain cx (initial_state am []) ee.storage_trace /\
        exit_result terminal /\
        create_size_exit_ok deploy_unit.cu_context res terminal /\
        !H. valid_horizon cx (initial_state am []) H ee.storage_trace ==>
          gas_origin_ptr_path (linked_ret_DF H,imm_len_mods mods,
            gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context,
            deploy_unit.cu_context,fn,[]) (root,FEMPTY,entry_taint) marks (terminal,G',tn') /\
          ((res = INL () \/ res = INR (ReturnException NoneV)) /\
             installed H (ee with <|gas_obs := []; scopes := []|>) terminal \/
           (res = INR HaltException /\ ?final. terminal = Halt final /\
              final.vs_returndata = [] /\ halt_rel H cx (ee with gas_obs := []) final) \/
           (?err final abort. res = INR err /\ terminal = Abort abort final /\ expr_exit res terminal)))`)
    (mk_asm "linked_ctor_native_replay");

val linked_ctor_native_replay_goal_tac = linked_ctor_native_replay_projection_goal_tac false;

val linked_ctor_native_replay_open_tac =
  map_every qx_gen_tac [`nat_root`,`nat_ent`,`nat_G0`,`nat_tn0`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  asm_x "linked_ctor_replay_prefix" (drule_all_then
    (qx_choose_then `nat_marks` (DISJ_CASES_THEN2 assume_tac
      (qx_choosel_then [`nat_res`,`nat_src`,`nat_out`,`nat_G`,`nat_tn`]
        (map_every assume_tac o CONJUNCTS))))) >>
  qexists_tac `nat_marks`;

val linked_ctor_native_replay_terminal_tac =
  disj2_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ nat_marks (nat_out,nat_G,nat_tn) /\ _`
    (fn path => asm_x "linked_ctor_terminal_replay" (fn end_rule => mp_then Any mp_tac end_rule path)) >>
  impl_tac;

val linked_ctor_native_replay_premises_tac =
  rpt (conj_tac >- FIRST_ASSUM ACCEPT_TAC);

val linked_ctor_native_replay_q_tac =
  simp[NoAsms, Abbr `native_Q`, vyperStateTheory.evaluation_state_accfupds] >>
  rpt gen_tac >> disch_then (qx_choose_then `native_ce` (map_every assume_tac o CONJUNCTS)) >>
  `nat_res = INL ()` by
    (qpat_assum `stmt_lands NoLoop _ nat_res _` mp_tac >>
     simp[NoAsms, loweringPostsTheory.stmt_lands_def, stmtLoweringTheory.loop_ctx_distinct]) >>
  qpat_assum `nat_res = INL () ==> ~block_is_terminated sb /\ native_ce = ce_end`
    (drule_then (CONJUNCTS_THEN2 assume_tac SUBST_ALL_TAC)) >>
  rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC;

val linked_ctor_native_replay_r_tac =
  simp[NoAsms, Abbr `native_R`, Abbr `native_ret`, vyperStateTheory.evaluation_state_fupdcanon];

val linked_ctor_native_replay_close_tac =
  disch_then (qx_choosel_then [`nat_terminal`,`nat_end_g`,`nat_end_tn`]
    (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`nat_res`,`nat_src`,`nat_terminal`,`nat_end_g`,`nat_end_tn`] >>
  rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC;

(* Project the padded reading prefix of each selected raw run.  Only a
   storage-valid, non-exempt observation needs an optimized witness. *)
fun linked_accepted_correct_mask_post_tac sites selected slots unused markf =
  PURE_REWRITE_TAC [gas_readings_rel_def] >>
  MATCH_MP_TAC
    (Q.INST [`sites` |-> sites, `selected` |-> selected,
             `slots` |-> slots, `unused` |-> unused, `markf` |-> markf]
       (SPEC_ALL (INST_TYPE [alpha |-> ``:string # num``]
         gasMaskProjectionTheory.gas_mask_projection_padded))) >>
  conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
  conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
  qx_gen_tac `raw` >> disch_tac >> BETA_TAC >>
  qpat_assum `!raw. LIST_REL _ _ raw ==> (?rest. _ = _ ++ rest) /\ !suffix. _`
    (qspec_then `raw` mp_tac) >>
  impl_tac >- FIRST_ASSUM ACCEPT_TAC >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
  qx_gen_tac `suffix` >> disch_tac >>
  qpat_assum `!suffix. deploy_storage_ok_mods mods exps am tx os _ ==> _`
    (qspec_then `suffix` mp_tac) >>
  impl_tac >- FIRST_ASSUM ACCEPT_TAC >>
  disch_then (DISJ_CASES_THEN2 assume_tac
    (qx_choosel_then [`chosen_dead`, `chosen_raw_fuel`] strip_assume_tac))
  >- (disj1_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  disj2_tac >>
  qpat_assum `ctx_sim chosen_dead deploy_unit.cu_context _ _ vs`
    (mp_tac o PURE_REWRITE_RULE [ctx_sim_def]) >>
  disch_then (qspec_then `chosen_raw_fuel` mp_tac) >>
  impl_tac >- FIRST_ASSUM ACCEPT_TAC >>
  disch_then (qx_choose_then `chosen_opt_fuel` assume_tac) >>
  qexists_tac `chosen_opt_fuel` >>
  conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
  conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
  qpat_assum `!u. dead_result_rel chosen_dead _ u ==> deploy_post _ u` irule >>
  FIRST_ASSUM ACCEPT_TAC;

(* The allocated pointer retains one recorded site and a bounded dirty set. *)
val linked_alloc_site_tac =
  `!(H : (bool # bytes32 # type_value) list # num list) ctx func cenv cx es s s1 G tn PG id n out.
     stmt_state_rel H ctx func cenv cx es s /\
     MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
     n < dimword (:256) /\
     step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 ==>
     ?b dirty.
       FLOOKUP s1.vs_allocas id = SOME (b,n) /\
       b+n < dimword (:256) /\
       lookup_var out s1 = SOME (n2w b) /\
       step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1 =
         G |+ (out,(b,n)) /\
       step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn =
         tn with <|t_var := tn.t_var |+ (out,{}); t_mem := tn.t_mem UNION dirty|> /\
       dirty SUBSET {i | b <= i /\ i < b+n}` by
    (rpt gen_tac >> strip_tac >>
     metis_tac [exprSimPtrLiteralBufferTheory.literal_ptr_alloca_ghost]);

val linked_add_site_tac =
  `!PG G tn id src dst off v s site.
     FLOOKUP G src = SOME site ==>
     step_prov PG G (mk_inst id ADD [Var src; Lit off] [dst])
       (update_var dst v s) = G |+ (dst,site) /\
     step_taint (mk_inst id ADD [Var src; Lit off] [dst]) s
       (update_var dst v s) tn = tn with t_var := tn.t_var |+ (dst,{})` by
    (rpt gen_tac >> strip_tac >>
     metis_tac [exprSimPtrLiteralOpsTheory.literal_add_ghost]);

(* The copied suffix can only observe taint from below the allocation floor. *)
val linked_positive_epilogue_suffix_tac =
  `!b rt cap (tm:num -> bool) tm1 tm2 p.
     (!j. j < cap /\ j IN tm ==> p j) /\
     (!j. j < cap ==> (j IN tm1 <=> j IN tm)) /\
     (!j. j < cap ==> (b + rt + j IN tm2 <=> j IN tm1)) ==>
     !i. i < rt + cap /\ b + i IN (tm2 DIFF {k | b <= k /\ k < b + rt}) ==>
         rt <= i /\ p (i - rt)` by
    (POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >> strip_tac >> gen_tac >>
     disch_then (CONJUNCTS_THEN2 assume_tac (mp_tac o REWRITE_RULE [pred_setTheory.IN_DIFF])) >>
     disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >> simp[NoAsms] >> strip_tac >>
     `rt <= i /\ i - rt < cap /\ b + rt + (i - rt) = b + i` by decide_tac >>
     qpat_assum `!j. j < cap ==> (b + rt + j IN tm2 <=> j IN tm1)`
       (qspec_then `i - rt` mp_tac) >>
     qpat_assum `b + rt + (i - rt) = b + i` (fn th => PURE_REWRITE_TAC [th]) >>
     qpat_assum `!j. j < cap ==> (j IN tm1 <=> j IN tm)`
       (qspec_then `i - rt` mp_tac) >>
     qpat_assum `!j. j < cap /\ j IN tm ==> p j` (qspec_then `i - rt` mp_tac) >> simp[]);

(* Project only the two frontier inequalities for the dynamic-allocation check. *)
val linked_epilogue_below_fmp_tac =
  `!C f u. alloca_inv u /\ fmp_room C f u /\ ctx_has_dalloca C ==>
      allocas_below_fmp u` by
    (POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >> strip_tac >>
     `u.vs_alloca_next <= w2n u.vs_initial_fmp /\
      w2n u.vs_initial_fmp <= w2n u.vs_fmp` by
       (qpat_x_assum `fmp_room C f u`
          (mp_tac o PURE_REWRITE_RULE [exprLoweringPropsTheory.fmp_room_def]) >>
        simp[] >> strip_tac >> decide_tac) >>
     PURE_REWRITE_TAC [allocas_below_fmp_def] >>
     conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
     rpt gen_tac >> strip_tac >>
     drule_all allocaSiteResourceTheory.alloca_site_registered_below >> decide_tac);

val linked_epilogue_alloca_resources_tac =
  `!(H : (bool # bytes32 # type_value) list # num list) C f c cx e s cap id n out.
     stmt_state_rel H C f c cx e s /\
     MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts f) /\
     n < dimword (:256) /\ allocas_from cap s /\ cap <= s.vs_alloca_next ==>
     ?u b. step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
           lookup_var out u = SOME (n2w b) /\ FLOOKUP u.vs_allocas id = SOME (b,n) /\
           cap <= b /\ b + n < dimword (:256) /\ allocas_from cap u /\
           (ctx_has_dalloca C ==> allocas_below_fmp u)` by
    (qpat_assum `!C f u. alloca_inv u /\ fmp_room C f u /\ ctx_has_dalloca C ==> _`
       (fn th => POP_ASSUM_LIST (K (assume_tac th))) >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `stmt_state_rel H C f c cx e s`
       (fn th => map_every (fn r => assume_tac (MATCH_MP r th))
          [stateRelProjTheory.stmt_state_rel_alloca_room,
           stateRelProjTheory.stmt_state_rel_fmp_room,
           bodyMemBopRestWordPathTheory.rest_word_state_alloca_inv]) >>
     qmatch_asmsub_abbrev_tac `MEM ainst (fn_insts f)` >>
     `ainst.inst_id = id /\ ainst.inst_opcode = ALLOCA /\
      ainst.inst_operands = [Lit (n2w n)] /\ ainst.inst_outputs = [out]` by
       simp[NoAsms, Abbr `ainst`, mk_inst_def] >>
     `!b sz. FLOOKUP s.vs_allocas ainst.inst_id = SOME (b,sz) ==> sz = w2n (n2w n : bytes32)` by
       (drule stateRelProjTheory.stmt_state_rel_alloca_size >>
        disch_then (qspecl_then [`ainst`, `n2w n`] mp_tac) >> simp[]) >>
     drule_all allocaSiteResourceTheory.alloca_site_execute >>
     disch_then (qx_choose_then `u` (qx_choose_then `b` strip_assume_tac)) >>
     `allocas_from cap u` by
       (drule_all decoderAllocationBoundsPtrTheory.exec_alloca_preserves_allocas_from >>
        disch_then ACCEPT_TAC) >>
     `fmp_room C f u` by
       (drule_all exprLoweringPropsTheory.fmp_room_exec_alloca >> disch_then ACCEPT_TAC) >>
     `u.vs_alloca_next < dimword (:256)` by
       (qpat_assum `alloca_room C f u`
          (ACCEPT_TAC o MATCH_MP exprLoweringPropsTheory.alloca_room_next_lt)) >>
     `w2n (n2w n : bytes32) = n` by simp[] >>
     `FLOOKUP u.vs_allocas id = SOME (b,n)` by
       (qpat_assum `FLOOKUP u.vs_allocas ainst.inst_id = SOME _` mp_tac >>
        qpat_assum `ainst.inst_id = id` (fn eq => PURE_REWRITE_TAC [eq]) >>
        qpat_assum `w2n (n2w n : bytes32) = n` (fn eq => PURE_REWRITE_TAC [eq]) >>
        disch_then ACCEPT_TAC) >>
     `cap <= b` by
       (qpat_assum `allocas_from cap u` (mp_tac o PURE_REWRITE_RULE [allocas_from_def]) >>
        disch_then (qspecl_then [`id`, `b`, `n`] mp_tac) >> simp[]) >>
     `b + n < dimword (:256)` by decide_tac >>
     qexistsl_tac [`u`, `b`] >>
     conj_tac >-
       (qpat_assum `exec_alloca ainst s _ = OK u` mp_tac >>
        simp[NoAsms, Abbr `ainst`, mk_inst_def, step_inst_base_opcode_eqs, eval_operand_def]) >>
     rpt (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >> disch_tac >>
     qpat_assum `!C f u. alloca_inv u /\ fmp_room C f u /\ _ ==> _`
       (qspecl_then [`C`, `f`, `u`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC);

val linked_epilogue_alloca_frame_tac =
  `!id n out s u. step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
      u.vs_current_bb = s.vs_current_bb /\ u.vs_inst_idx = s.vs_inst_idx /\
      u.vs_halted = s.vs_halted /\ u.vs_labels = s.vs_labels /\
      u.vs_code = s.vs_code /\ u.vs_data_section = s.vs_data_section /\
      u.vs_memory = s.vs_memory /\ u.vs_requests = s.vs_requests /\
      u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
      u.vs_transient = s.vs_transient /\ u.vs_immutables = s.vs_immutables /\
      (!op. op <> Var out ==> eval_operand op u = eval_operand op s)` by
    (POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >> strip_tac >>
     drule bodyPtrMakeArrayAllocBufferTheory.literal_alloca_static_frame >> strip_tac >>
     qpat_assum `step_inst_base _ s = OK u`
       (assume_tac o SIMP_RULE (srw_ss()) [mk_inst_def, step_inst_base_opcode_eqs, eval_operand_def]) >>
     `!op. op <> Var out ==> eval_operand op u = eval_operand op s` by
       (drule stmtSimDeclPathTheory.exec_alloca_operand_frame >> simp[mk_inst_def]) >>
     `u.vs_inst_idx = s.vs_inst_idx /\ u.vs_code = s.vs_code /\
      u.vs_requests = s.vs_requests` by
       (qpat_assum `exec_alloca _ s _ = OK u`
          (fn th => POP_ASSUM_LIST (K (mp_tac th))) >>
        simp[exec_alloca_def, mk_inst_def, AllCaseEqs()] >>
        rpt strip_tac >> gvs[update_var_def]) >>
     rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC);

(* The terminal state and the pointer check use the same RETURN step. *)
val linked_positive_epilogue_return_step_tac =
  `!ctx fn fuel cap n b G tn4 ret buf s4 sh.
     ret.inst_opcode = RETURN /\ ret.inst_operands = [Var buf; Lit (n2w n)] /\
     eval_operand (Var buf) s4 = SOME (n2w b) /\
     w2n (n2w b : bytes32) = b /\ w2n (n2w n : bytes32) = n /\
     FLOOKUP G buf = SOME (b,n) /\ op_taint tn4 (Var buf) = {} /\
     sh = halt_state (set_returndata (mem_bytes_at b n s4.vs_memory) s4) ==>
     step_inst fuel ctx ret s4 = Halt sh /\ access_ok cap G fn ret s4 /\
     taint_ok fn tn4 ret s4 /\
     (step_taint ret s4 sh tn4).t_stor = tn4.t_stor /\
     (step_taint ret s4 sh tn4).t_trans = tn4.t_trans /\
     ret_taint tn4 ret s4 = {i | i < n /\ b + i IN tn4.t_mem}` by
    (POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >>
     disch_then (map_every assume_tac o CONJUNCTS) >> rpt conj_tac
     >- (simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
         qpat_assum `ret.inst_opcode = RETURN`
           (fn h => PURE_REWRITE_TAC [MATCH_MP
             (valOf (List.find (fn th => can (MATCH_MP th) h)
                (CONJUNCTS venomExecSemanticsTheory.step_inst_base_opcode_eqs))) h]) >>
         simp[Excl "w2n_n2w", cj 1 venomStateTheory.eval_operand_def,
              valueEncodingDefsTheory.mem_bytes_at_def])
     >- (simp[Excl "w2n_n2w", access_ok_def, source_memory_read_ranges_def,
              source_memory_write_ranges_def, memory_range_of_operands_def,
              memLocDefsTheory.mem_read_ops_def, cj 1 venomStateTheory.eval_operand_def] >>
         rw[] >> fs[])
     >- (simp[taint_ok_def] >> qx_gen_tac `op` >>
         Cases_on `op = Var buf` >> Cases_on `op = Lit (n2w n)` >> gvs[op_taint_def])
     >- simp[step_taint_def, store_taint_def, adopt_reset_def]
     >- simp[step_taint_def, store_taint_def, adopt_reset_def] >>
     simp[Excl "w2n_n2w", ret_taint_def, cj 1 venomStateTheory.eval_operand_def]);

val linked_positive_epilogue_return_tac =
  `!D ctx fn fuel cap rt b G tn tn4 ret buf s s4 sh body_ce ctor_ce codepos tm1 tm2.
     ret.inst_opcode = RETURN /\ ret.inst_operands = [Var buf; Lit (n2w (rt + cap))] /\
     eval_operand (Var buf) s4 = SOME (n2w b) /\
     w2n (n2w b : bytes32) = b /\ w2n (n2w (rt + cap) : bytes32) = rt + cap /\
     FLOOKUP G buf = SOME (b,rt + cap) /\ op_taint tn4 (Var buf) = {} /\
     sh = halt_state (set_returndata (mem_bytes_at b (rt + cap) s4.vs_memory) s4) /\
     allocas_from cap s4 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s4) /\
     stor_taint_ok_at D tn s /\ D.d_imm = K UNIV /\
     tn4.t_stor = tn.t_stor /\ tn4.t_trans = tn.t_trans /\
     s4.vs_call_ctx = s.vs_call_ctx /\ s4.vs_accounts = s.vs_accounts /\
     s4.vs_transient = s.vs_transient /\
     body_ce.ce_modules = ctor_ce.ce_modules /\ body_ce.ce_module_vars = ctor_ce.ce_module_vars /\
     D.d_ret = (\r. {i | rt <= i /\ imm_section_dead_mods ctor_ce (DROP rt r) (i - rt)}) /\
     sh.vs_returndata =
       TAKE rt (DROP (w2n (codepos:bytes32)) s.vs_code ++ REPLICATE rt 0w) ++
       TAKE cap (s.vs_memory ++ REPLICATE cap 0w) /\
     (!j. j < cap /\ j IN tn.t_mem ==> imm_section_dead_mods body_ce (mem_bytes_at 0 cap s.vs_memory) j) /\
     (!j. j < cap ==> (j IN tm1 <=> j IN tn.t_mem)) /\
     (!j. j < cap ==> (b + rt + j IN tm2 <=> j IN tm1)) /\
     tn4.t_mem = tm2 DIFF {k | b <= k /\ k < b + rt} ==>
     step_inst fuel ctx ret s4 = Halt sh /\ ptr_inst_ok D cap fuel ctx fn G tn4 ret s4` by
    (qpat_assum `!ctx fn fuel cap n b G tn4 ret buf s4 sh.
         _ ==> step_inst fuel ctx ret s4 = Halt sh /\ _` mp_tac >>
     qpat_assum `!b rt cap tm tm1 tm2 p. _ ==> !i. _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     disch_then (mk_asm "return_suffix") >> disch_then (mk_asm "return_step") >>
     rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     asm "return_step"
       (qspecl_then [`ctx`,`fn`,`fuel`,`cap`,`rt+cap`,`b`,`G`,`tn4`,`ret`,`buf`,`s4`,`sh`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
     `DROP rt sh.vs_returndata = mem_bytes_at 0 cap s.vs_memory` by
       (qpat_assum `sh.vs_returndata = _` (fn th => PURE_REWRITE_TAC [th]) >>
        simp[listTheory.DROP_APPEND2, listTheory.LENGTH_TAKE_EQ,
             valueEncodingDefsTheory.mem_bytes_at_def]) >>
     `!j. j < cap /\ j IN tn.t_mem ==>
          imm_section_dead_mods ctor_ce (mem_bytes_at 0 cap s.vs_memory) j` by
       (qpat_assum `!j. j < cap /\ j IN tn.t_mem ==> imm_section_dead_mods body_ce _ j` mp_tac >>
        PURE_REWRITE_TAC [bodyInvSplitTheory.imm_section_dead_mods_def] >>
        asm_rewrite_tac []) >>
     `!i. i < rt + cap /\ b + i IN tn4.t_mem ==>
          rt <= i /\ imm_section_dead_mods ctor_ce (DROP rt sh.vs_returndata) (i - rt)` by
       (qpat_assum `DROP rt sh.vs_returndata = _` (fn th => PURE_REWRITE_TAC [th]) >>
        qpat_assum `tn4.t_mem = _` (fn th => PURE_REWRITE_TAC [th]) >>
        asm "return_suffix"
          (qspecl_then [`b`,`rt`,`cap`,`tn.t_mem`,`tm1`,`tm2`,
                       `\j. imm_section_dead_mods ctor_ce (mem_bytes_at 0 cap s.vs_memory) j`]
             (MATCH_MP_TAC o BETA_RULE)) >>
        rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     `sh.vs_call_ctx = s.vs_call_ctx /\ sh.vs_accounts = s.vs_accounts /\
      sh.vs_transient = s.vs_transient` by
       (qpat_assum `sh = halt_state _` (fn th => PURE_REWRITE_TAC [th]) >>
        simp[venomStateTheory.halt_state_def, venomStateTheory.set_returndata_def]) >>
     qpat_x_assum `sh = halt_state _` kall_tac >>
     qpat_x_assum `sh.vs_returndata = _` kall_tac >>
     qpat_x_assum `tn4.t_mem = _` kall_tac >>
     `ret_taint tn4 ret s4 SUBSET D.d_ret sh.vs_returndata` by
       (qpat_assum `ret_taint tn4 ret s4 = _` (fn th => PURE_REWRITE_TAC [th]) >>
        qpat_assum `D.d_ret = _` (fn th => PURE_REWRITE_TAC [th]) >>
        qpat_assum `!i. i < rt + cap /\ b + i IN tn4.t_mem ==> _` mp_tac >>
        simp[NoAsms, pred_setTheory.SUBSET_DEF]) >>
     qpat_x_assum `D.d_ret = _` kall_tac >>
     qpat_x_assum `ret_taint tn4 ret s4 = _` kall_tac >>
     qpat_assum `stor_taint_ok_at D tn s`
       (strip_assume_tac o PURE_REWRITE_RULE [bodyPtrDefsTheory.stor_taint_ok_at_def]) >>
     asm_rewrite_tac [ptr_inst_ok_def] >> simp[]) >>
  pop_assum (mk_asm "positive_return");

(* MCOPY reads the fixed immutable region but writes into the allocated site. *)
val linked_positive_epilogue_mcopy_checks_tac =
  `!fn G tn s id tmp imm b rt cap.
     eval_operand (Var tmp) s = SOME (n2w (b + rt)) /\
     eval_operand imm s = SOME 0w /\
     w2n (n2w (b + rt) : bytes32) = b + rt /\
     w2n (n2w cap : bytes32) = cap /\
     FLOOKUP G tmp = SOME (b,rt + cap) /\ op_prov G imm = NONE /\
     op_taint tn (Var tmp) = {} /\ op_taint tn imm = {} ==>
     step_inst_base (mk_inst id MCOPY [Var tmp;imm;Lit (n2w cap)] []) s =
       OK (mcopy (b + rt) 0 cap s) /\
     access_ok cap G fn (mk_inst id MCOPY [Var tmp;imm;Lit (n2w cap)] []) s /\
     taint_ok fn tn (mk_inst id MCOPY [Var tmp;imm;Lit (n2w cap)] []) s` by
    (POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >> strip_tac >>
     fs[eval_operand_def, ptrDisciplineTheory.op_taint_def] >>
     conj_tac
     >- simp[mk_inst_def, step_inst_base_opcode_eqs, eval_operand_def] >>
     conj_tac
     >- (simp[ptrDisciplineTheory.access_ok_def, source_memory_read_ranges_def,
              source_memory_write_ranges_def, sized_source_write_range_def,
              memLocDefsTheory.mem_write_ops_def, memLocDefsTheory.mem_read_ops_def,
              mk_inst_def, eval_operand_def] >> rw[] >> fs[]) >>
     simp[ptrDisciplineTheory.taint_ok_def, mk_inst_def, ptrDisciplineTheory.op_taint_def] >>
     gen_tac >> Cases_on `op = Var tmp` >> Cases_on `op = imm` >>
     Cases_on `op = Lit (n2w cap)` >> gvs[]);

val linked_positive_epilogue_mcopy_ghost_tac =
  `!PG G tn s id tmp imm b rt cap u tn'.
     eval_operand (Var tmp) s = SOME (n2w (b + rt)) /\
     eval_operand imm s = SOME 0w /\
     w2n (n2w (b + rt) : bytes32) = b + rt /\
     w2n (n2w cap : bytes32) = cap /\
     u = mcopy (b + rt) 0 cap s /\
     tn' = step_taint (mk_inst id MCOPY [Var tmp;imm;Lit (n2w cap)] []) s u tn ==>
     step_prov PG G (mk_inst id MCOPY [Var tmp;imm;Lit (n2w cap)] []) u = G /\
     tn'.t_var = tn.t_var /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
     (!j. j < cap ==> (b + rt + j IN tn'.t_mem <=> j IN tn.t_mem))` by
    (POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >> strip_tac >>
     `eval_operand (Lit (n2w cap)) s = SOME (n2w cap)` by simp[eval_operand_def] >>
     qpat_assum `eval_operand (Var tmp) s = SOME _`
       (mp_then (Pat `eval_operand dst _ = _`) mp_tac fragExecPtrTheory.mcopy_operand_ghost_frame) >>
     disch_then (fn th => qpat_assum `eval_operand imm s = SOME _`
       (mp_then (Pat `eval_operand src _ = _`) mp_tac th)) >>
     disch_then (fn th => qpat_assum `eval_operand (Lit _) s = SOME _`
       (mp_then (Pat `eval_operand count_op _ = _`) mp_tac th)) >>
     disch_then (qspecl_then [`PG`, `G`, `tn`, `id`] mp_tac) >>
     simp[] >> strip_tac >>
     simp[pred_setTheory.IN_DIFF] >> rpt strip_tac >>
     `b + rt + j < b + rt + cap` by decide_tac >> simp[]);

val linked_positive_epilogue_mcopy_frames_tac =
  `!s b rt cap u s'.
     u = mcopy (b + rt) 0 cap s /\ s' = u with vs_inst_idx := SUC s.vs_inst_idx ==>
     u.vs_requests = s.vs_requests /\ s'.vs_requests = s.vs_requests /\
     s'.vs_current_bb = s.vs_current_bb /\ s'.vs_prev_bb = s.vs_prev_bb /\
     s'.vs_inst_idx = SUC s.vs_inst_idx /\ s'.vs_halted = s.vs_halted /\
     s'.vs_accounts = s.vs_accounts /\ s'.vs_transient = s.vs_transient /\
     s'.vs_immutables = s.vs_immutables /\ s'.vs_call_ctx = s.vs_call_ctx /\
     s'.vs_labels = s.vs_labels /\ s'.vs_code = s.vs_code /\
     s'.vs_vars = s.vs_vars /\ s'.vs_allocas = s.vs_allocas /\
     s'.vs_alloca_next = s.vs_alloca_next /\ s'.vs_fmp = s.vs_fmp /\
     s'.vs_initial_fmp = s.vs_initial_fmp /\
     (allocas_from cap s' <=> allocas_from cap s) /\
     (allocas_below_fmp s' <=> allocas_below_fmp s)` by
    (POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >> strip_tac >>
     simp[mcopy_def, write_memory_with_expansion_def,
          ptrDisciplineTheory.allocas_from_def, ptrDisciplineTheory.allocas_below_fmp_def]);

(* The base step and ghost updates refer to the same pre-increment state. *)
val linked_positive_epilogue_codecopy_tac =
  `!id buf rt cap b label lo fn PG G tn s i u next.
    i = mk_inst (id + 3) CODECOPY [Var buf; Label "runtime_begin"; Lit (n2w rt)] [] /\
    u = write_memory_with_expansion b
          (TAKE rt (DROP (w2n label) s.vs_code ++ REPLICATE rt 0w)) s /\
    next = u with vs_inst_idx := SUC s.vs_inst_idx /\
    b + (rt + cap) < dimword (:256) /\
    FLOOKUP G buf = SOME (b,rt + cap) /\
    eval_operand (Var buf) s = SOME (n2w b) /\
    FLOOKUP s.vs_labels "runtime_begin" = SOME label /\
    op_taint tn (Var buf) = {} ==>
    step_inst_base i s = OK u /\ access_ok lo G fn i s /\ taint_ok fn tn i s /\
    step_prov PG G i u = G /\
    step_taint i s u tn = tn with t_mem := tn.t_mem DIFF {k | b <= k /\ k < b+rt} /\
    u.vs_requests = s.vs_requests /\ u.vs_current_bb = s.vs_current_bb /\
    next.vs_inst_idx = SUC s.vs_inst_idx /\ next.vs_current_bb = s.vs_current_bb /\
    next.vs_halted = s.vs_halted /\ next.vs_requests = s.vs_requests /\
    next.vs_code = s.vs_code /\ next.vs_labels = s.vs_labels /\
    next.vs_alloca_next = s.vs_alloca_next /\ next.vs_allocas = s.vs_allocas /\
    next.vs_fmp = s.vs_fmp /\ next.vs_initial_fmp = s.vs_initial_fmp /\
    next.vs_call_ctx = s.vs_call_ctx /\ next.vs_accounts = s.vs_accounts /\
    next.vs_transient = s.vs_transient /\ next.vs_immutables = s.vs_immutables /\
    eval_operand (Var buf) next = SOME (n2w b)` by
    (POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >> strip_tac >>
     `b < dimword (:256) /\ rt < dimword (:256)` by decide_tac >>
     `w2n (n2w b : bytes32) = b /\ w2n (n2w rt : bytes32) = rt` by
       simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
     `eval_operand (Label "runtime_begin") s = SOME label /\
      eval_operand (Lit (n2w rt)) s = SOME (n2w rt)` by simp[eval_operand_def] >>
     `step_inst_base i s = OK u` by
       simp[mk_inst_def, step_inst_base_opcode_eqs] >>
     `i.inst_opcode = CODECOPY /\
      i.inst_operands = [Var buf; Label "runtime_begin"; Lit (n2w rt)] /\
      i.inst_outputs = []` by simp[mk_inst_def] >>
     `op_taint tn (Label "runtime_begin") = {} /\ op_taint tn (Lit (n2w rt)) = {}` by
       simp[op_taint_def] >>
     `b <= w2n (n2w b : bytes32) /\
      w2n (n2w b : bytes32) + w2n (n2w rt : bytes32) <= b + (rt + cap)` by simp[] >>
     `access_ok lo G fn i s /\ taint_ok fn tn i s` by
       (drule_all lowerDloadPtrExpansionTheory.dload_codecopy_safe >> simp[]) >>
     `step_prov PG G i u = G /\
      step_taint i s u tn = tn with t_mem := tn.t_mem DIFF {k | b <= k /\ k < b+rt}` by
       (drule_all lowerDloadPtrExpansionTransportTheory.dload_codecopy_state_ghost >> simp[]) >>
     simp[instIdxIndepTheory.eval_op_inst_idx,
          venomMemPropsTheory.eval_operand_write_memory_with_expansion] >>
     simp[write_memory_with_expansion_def]);

(* With unchanged requests an ordinary instruction needs only its local
   checks and the continuation at the stepped provenance and taint. *)
val linked_epilogue_ptr_next_tac =
  `!D lo fuel ctx fn G tn bb s i u.
     get_instruction bb s.vs_inst_idx = SOME i /\
     i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
     step_inst_base i s = OK u /\ u.vs_requests = s.vs_requests /\
     access_ok lo G fn i s /\ taint_ok fn tn i s /\
     allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
     ptr_safe_block D lo fuel ctx fn [] (step_prov [] G i u)
       (step_taint i s u tn) bb (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
     ptr_safe_block D lo fuel ctx fn [] G tn bb s` by
    (POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     `step_inst fuel ctx i s = OK u` by
       simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
     drule_all ptrSafeRunTheory.ptr_safe_block_step >>
     disch_then (fn th => pure_once_rewrite_tac [th]) >>
     drule_all ptrSafeRunTheory.ghost_step_non_invoke >>
     disch_then (fn th => pure_rewrite_tac [th]) >>
     simp[ptrSafeRunTheory.ptr_safe_step_def, ptrSafeRunTheory.ptr_inst_ok_def]);

val linked_epilogue_ptr_halt_tac =
  `!D lo fuel ctx fn G tn bb s i sh.
     get_instruction bb s.vs_inst_idx = SOME i /\
     i.inst_opcode <> INVOKE /\ step_inst_base i s = Halt sh /\
     access_ok lo G fn i s /\ taint_ok fn tn i s /\
     allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
     (step_taint i s sh tn).t_stor SUBSET
       D.d_stor sh.vs_call_ctx.cc_address
         (sh.vs_accounts sh.vs_call_ctx.cc_address).storage /\
     (step_taint i s sh tn).t_trans SUBSET
       D.d_trans sh.vs_call_ctx.cc_address
         (sh.vs_transient sh.vs_call_ctx.cc_address) /\
     (step_taint i s sh tn).t_imm SUBSET D.d_imm sh.vs_immutables /\
     ret_taint tn i s SUBSET D.d_ret sh.vs_returndata ==>
     ptr_safe_block D lo fuel ctx fn [] G tn bb s` by
    (POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     simp[Once ptrSafeRunTheory.ptr_safe_block_def,
          ptrSafeRunTheory.ptr_safe_step_def, ptrSafeRunTheory.ptr_inst_ok_def,
          venomExecSemanticsTheory.step_inst_non_invoke]);

(* The positive tail is checked at the very PC and fuel of its padded run. *)
val linked_positive_epilogue_goal =
  sg `!D ctx fn body_ce ctor_ce cx ee (H : (bool # bytes32 # type_value) list # num list)
       G tn rt cap imm epi se s fuel final codepos.
     0 < cap /\ rt + cap < dimword (:256) /\
     compile_constructor_epilogue rt cap imm epi = ((),se) /\
     fn_has_code epi se fn /\ ~block_is_terminated epi /\
     s.vs_current_bb = epi.cs_current_bb /\ s.vs_inst_idx = LENGTH epi.cs_current_insts /\
     stmt_state_rel H ctx fn body_ce cx ee s /\ ghost_inv_at_mods D cap NONE body_ce cx ee G tn s /\
     same_frame ctor_ce body_ce /\ ctor_ce.ce_imm_alloca = SOME imm /\
     (!x. imm = Var x ==> not_fresh_at epi x) /\
     D.d_imm = K UNIV /\
     D.d_ret = (\r. {i | rt <= i /\ imm_section_dead_mods ctor_ce (DROP rt r) (i - rt)}) /\
     FLOOKUP s.vs_labels "runtime_begin" = SOME codepos /\
     run_from fuel ctx fn s = Halt final /\
     final.vs_returndata =
       TAKE rt (DROP (w2n codepos) s.vs_code ++ REPLICATE rt 0w) ++
       TAKE cap (s.vs_memory ++ REPLICATE cap 0w) ==>
     ptr_safe_run D cap fuel ctx fn [] G tn s`;

val linked_positive_epilogue_setup_tac =
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (qx_choose_then `bb` (map_every assume_tac o CONJUNCTS))
    immutableDeployExecutionTheory.compile_constructor_epilogue_code_placement >>
  drule_all_then assume_tac immutableDeployExecutionTheory.compile_constructor_epilogue_positive_insts >>
  qabbrev_tac `id = epi.cs_next_id` >>
  qabbrev_tac `buf = "%" ++ toString epi.cs_next_var` >>
  qabbrev_tac `tmp = "%" ++ toString (epi.cs_next_var + 1)` >>
  qabbrev_tac `i0 = mk_inst id ALLOCA [Lit (n2w (rt+cap))] [buf]` >>
  qabbrev_tac `i1 = mk_inst (id+1) ADD [Var buf; Lit (n2w rt)] [tmp]` >>
  qabbrev_tac `i2 = mk_inst (id+2) MCOPY [Var tmp; imm; Lit (n2w cap)] []` >>
  qabbrev_tac `i3 = mk_inst (id+3) CODECOPY [Var buf; Label "runtime_begin"; Lit (n2w rt)] []` >>
  qabbrev_tac `i4 = mk_inst (id+4) RETURN [Var buf; Lit (n2w (rt+cap))] []` >>
  `isPREFIX [i0;i1;i2;i3;i4] (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `emitted_insts epi se = _` (fn code =>
       qpat_assum `isPREFIX (emitted_insts epi se) _`
         (mp_tac o PURE_REWRITE_RULE [code])) >>
     simp[Abbr `i0`, Abbr `i1`, Abbr `i2`, Abbr `i3`, Abbr `i4`,
          Abbr `id`, Abbr `buf`, Abbr `tmp`]) >>
  ntac 5
    (qpat_x_assum `isPREFIX (_::_) (DROP _ _)`
       (strip_assume_tac o MATCH_MP fragGasSeqAbortTheory.instruction_prefix_cursor)) >>
  `MEM i0 (fn_insts fn)` by
    (irule fragFuelTheory.lookup_block_get_instruction_fn_insts >>
     qexistsl_tac [`bb`,`s.vs_inst_idx`,`s.vs_current_bb`] >> simp[]);

val linked_positive_epilogue_entry_tac =
  linked_ctor_epilogue_frame_fields_tac >>
  `body_ce.ce_imm_alloca = SOME imm` by simp[] >>
  qpat_assum `ghost_inv_at_mods D cap NONE body_ce cx ee G tn s`
    (map_every assume_tac o List.drop o (fn ths => (ths,3)) o CONJUNCTS o
     PURE_REWRITE_RULE [bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> simp[]) >>
  `eval_operand imm s = SOME 0w` by
    (qpat_assum `stmt_state_rel H ctx fn body_ce cx ee s`
       (qspec_then `imm` mp_tac o cj 1 o
        PURE_REWRITE_RULE [exprLoweringPropsTheory.immutable_base_zero_alt] o
        MATCH_MP stateRelProjTheory.stmt_state_rel_immutable_base_zero) >>
     simp[] >> Cases_on `imm` >> simp[NoAsms, eval_operand_def, lookup_var_def]);

val linked_positive_epilogue_imm_ghost_goal = sg `op_prov G imm = NONE /\ op_taint tn imm = {}`;
val linked_positive_epilogue_imm_ghost_tac =
  Cases_on `imm` >> simp[NoAsms, op_prov_def, op_taint_def] >>
  rename1 `FLOOKUP G x = NONE` >>
  qpat_assum `!x. cap <> 0 /\ body_ce.ce_imm_alloca = SOME (Var x) ==> _`
    (qspec_then `x` mp_tac) >>
  (impl_tac >- (conj_tac >- decide_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
  simp[NoAsms, op_taint_def];

val linked_positive_epilogue_fresh_tac =
  `buf <> tmp /\ imm <> Var buf /\ imm <> Var tmp` by
    (simp[Abbr `buf`, Abbr `tmp`, ASCIInumbersTheory.toString_11] >>
     conj_tac >> strip_tac >>
     qpat_assum `!x. imm = Var x ==> not_fresh_at epi x` drule >>
     simp[NoAsms, not_fresh_at_def, ASCIInumbersTheory.toString_11]);

val linked_positive_epilogue_alloc_tac =
  `MEM (mk_inst id ALLOCA [Lit (n2w (rt+cap))] [buf]) (fn_insts fn)` by
    (qpat_assum `MEM i0 (fn_insts fn)` mp_tac >> simp[Abbr `i0`]) >>
  qpat_assum `!H C f c cx e s cap id n out. _ ==> ?u b. _`
    (qspecl_then [`H`,`ctx`,`fn`,`body_ce`,`cx`,`ee`,`s`,`cap`,`id`,`rt+cap`,`buf`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC));

val linked_positive_epilogue_open_alloc_tac =
  disch_then (qx_choosel_then [`u0`,`b0`] (map_every assume_tac o CONJUNCTS)) >>
  qabbrev_tac `s1 = u0 with vs_inst_idx := SUC s.vs_inst_idx`;

val linked_positive_epilogue_alloc_ghost_tac =
  qpat_assum `!id n out s u. step_inst_base (mk_inst _ ALLOCA _ _) s = OK u ==> _`
    (qspecl_then [`id`,`rt+cap`,`buf`,`s`,`u0`] mp_tac) >>
  (impl_tac >- FIRST_ASSUM ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!H ctx func cenv cx es s s1 G tn PG id n out. _ ==> ?b dirty. _`
    (qspecl_then [`H`,`ctx`,`fn`,`body_ce`,`cx`,`ee`,`s`,`u0`,`G`,`tn`,`[]`,`id`,`rt+cap`,`buf`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
  disch_then (qx_choose_then `b` (qx_choose_then `dirty` (map_every assume_tac o CONJUNCTS))) >>
  `b0 = b` by
    (qpat_assum `FLOOKUP u0.vs_allocas id = SOME (b0,_)` mp_tac >> simp[]) >>
  qpat_x_assum `b0 = b` SUBST_ALL_TAC >>
  qabbrev_tac `G1 = G |+ (buf,(b,rt+cap))` >>
  qabbrev_tac `tn1 = tn with <|t_var := tn.t_var |+ (buf,{}); t_mem := tn.t_mem UNION dirty|>` >>
  `step_inst_base i0 s = OK u0 /\ step_prov [] G i0 u0 = G1 /\ step_taint i0 s u0 tn = tn1` by
    (simp[Abbr `i0`, Abbr `G1`, Abbr `tn1`] >> rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC);

val linked_positive_epilogue_after_alloc_goal =
  sg `get_instruction bb s1.vs_inst_idx = SOME i1 /\ eval_operand (Var buf) s1 = SOME (n2w b)`;
val linked_positive_epilogue_after_alloc_proof =
  qpat_assum `get_instruction bb (SUC s.vs_inst_idx) = SOME i1` mp_tac >>
  qpat_assum `lookup_var buf u0 = SOME _` mp_tac >>
  simp[NoAsms, Abbr `s1`, eval_operand_def, lookup_var_def];
val linked_positive_epilogue_after_alloc_tac =
  `eval_operand imm s1 = SOME 0w` by
    (qpat_assum `!op. op <> Var buf ==> eval_operand op u0 = eval_operand op s`
       (qspec_then `imm` mp_tac) >> simp[Abbr `s1`, instIdxIndepTheory.eval_op_inst_idx]) >>
  `allocas_from cap s1` by
    (qpat_assum `allocas_from cap u0` mp_tac >> simp[NoAsms, Abbr `s1`, allocas_from_def]) >>
  `(allocas_below_fmp s1 <=> allocas_below_fmp u0)` by
    simp[NoAsms, Abbr `s1`, allocas_below_fmp_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s1` by simp[] >>
  `FLOOKUP G1 buf = SOME (b,rt+cap) /\ op_taint tn1 (Var buf) = {}` by
    simp[Abbr `G1`, Abbr `tn1`, finite_mapTheory.FLOOKUP_UPDATE, op_taint_def] >>
  `b < dimword (:256) /\ b+rt < dimword (:256) /\ cap < dimword (:256)` by
    (qpat_assum `b + (rt+cap) < dimword (:256)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `w2n (n2w b : bytes32) = b /\ w2n (n2w (b+rt) : bytes32) = b+rt /\
   w2n (n2w cap : bytes32) = cap /\ w2n (n2w (rt+cap) : bytes32) = rt+cap` by simp[];

val linked_positive_epilogue_add_tac =
  qabbrev_tac `u1 = update_var tmp (n2w (b+rt)) s1` >>
  qabbrev_tac `s2 = u1 with vs_inst_idx := SUC s1.vs_inst_idx` >>
  `step_inst_base i1 s1 = OK u1` by
    simp[Abbr `i1`, Abbr `u1`, mk_inst_def, step_inst_base_opcode_eqs,
         exec_pure2_def, eval_operands_def, cj 1 eval_operand_def, wordsTheory.word_add_n2w] >>
  qabbrev_tac `G2 = G1 |+ (tmp,(b,rt+cap))` >>
  qabbrev_tac `tn2 = tn1 with t_var := tn1.t_var |+ (tmp,{})` >>
  `step_prov [] G1 i1 u1 = G2 /\ step_taint i1 s1 u1 tn1 = tn2` by
    (qpat_assum `!PG G tn id src dst off v s site. FLOOKUP G src = SOME site ==> _`
       (qspecl_then [`[]`,`G1`,`tn1`,`id+1`,`buf`,`tmp`,`n2w rt`,`n2w (b+rt)`,`s1`,`(b,rt+cap)`] mp_tac) >>
     (impl_tac >- FIRST_ASSUM ACCEPT_TAC) >>
     simp[Abbr `i1`, Abbr `u1`, Abbr `G2`, Abbr `tn2`]) >>
  `u1.vs_requests = s1.vs_requests /\ s2.vs_inst_idx = SUC s1.vs_inst_idx /\
   s2.vs_call_ctx = s1.vs_call_ctx /\ s2.vs_accounts = s1.vs_accounts /\
   s2.vs_transient = s1.vs_transient /\ s2.vs_labels = s1.vs_labels /\
   (allocas_from cap s2 <=> allocas_from cap s1) /\
   (allocas_below_fmp s2 <=> allocas_below_fmp s1)` by
    simp[NoAsms, Abbr `u1`, Abbr `s2`, update_var_def, allocas_from_def, allocas_below_fmp_def] >>
  `s1.vs_inst_idx = SUC s.vs_inst_idx` by simp[NoAsms, Abbr `s1`] >>
  `get_instruction bb s2.vs_inst_idx = SOME i2` by
    (qpat_assum `get_instruction bb (SUC (SUC s.vs_inst_idx)) = SOME i2` mp_tac >>
     qpat_assum `s2.vs_inst_idx = _` (fn a =>
       qpat_assum `s1.vs_inst_idx = _` (fn b => simp[NoAsms,a,b]))) >>
  `allocas_from cap s2 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s2)` by
    (qpat_assum `allocas_from cap s2 <=> allocas_from cap s1` (fn a =>
       qpat_assum `allocas_below_fmp s2 <=> allocas_below_fmp s1` (fn b =>
         pure_rewrite_tac[a,b])) >> rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  `eval_operand (Var buf) s2 = SOME (n2w b) /\ eval_operand (Var tmp) s2 = SOME (n2w (b+rt))` by
    (qpat_assum `eval_operand (Var buf) s1 = SOME _` mp_tac >>
     qpat_assum `buf <> tmp` mp_tac >>
     simp[NoAsms, Abbr `s2`, Abbr `u1`, update_var_def, eval_operand_def, lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE]);

val linked_positive_epilogue_after_add_tac =
  `eval_operand imm s2 = SOME 0w /\ op_prov G2 imm = NONE /\ op_taint tn2 imm = {}` by
    (qpat_assum `eval_operand imm s1 = _` mp_tac >>
     qpat_assum `op_prov G imm = NONE` mp_tac >>
     qpat_assum `op_taint tn imm = {}` mp_tac >>
     qpat_assum `imm <> Var buf` mp_tac >> qpat_assum `imm <> Var tmp` mp_tac >>
     Cases_on `imm` >> simp[NoAsms, Abbr `s2`, Abbr `u1`, Abbr `G2`, Abbr `tn2`,
          Abbr `G1`, Abbr `tn1`, update_var_def, eval_operand_def, lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE, op_prov_def, op_taint_def]) >>
  `FLOOKUP G2 buf = SOME (b,rt+cap) /\ FLOOKUP G2 tmp = SOME (b,rt+cap) /\
   op_taint tn2 (Var buf) = {} /\ op_taint tn2 (Var tmp) = {}` by
    (qpat_assum `FLOOKUP G1 buf = _` mp_tac >> qpat_assum `op_taint tn1 (Var buf) = {}` mp_tac >>
     qpat_assum `buf <> tmp` mp_tac >>
     simp[NoAsms, Abbr `G2`, Abbr `tn2`, op_taint_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  `tn2.t_stor = tn.t_stor /\ tn2.t_trans = tn.t_trans` by
    simp[Abbr `tn2`, Abbr `tn1`] >>
  `!j. j < cap ==> (j IN tn2.t_mem <=> j IN tn.t_mem)` by
    (qpat_assum `dirty SUBSET _` mp_tac >>
     simp[NoAsms, Abbr `tn2`, Abbr `tn1`, pred_setTheory.SUBSET_DEF] >>
     disch_then (mk_asm "dirty_range") >> gen_tac >> disch_tac >>
     `j NOTIN dirty` by
       (strip_tac >> asm "dirty_range" drule >>
        qpat_assum `j < cap` mp_tac >> qpat_assum `cap <= b` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> decide_tac) >> simp[]);

val linked_positive_epilogue_mcopy_tac =
  qabbrev_tac `u2 = mcopy (b+rt) 0 cap s2` >>
  qabbrev_tac `s3 = u2 with vs_inst_idx := SUC s2.vs_inst_idx` >>
  qabbrev_tac `tn3 = step_taint i2 s2 u2 tn2` >>
  `step_inst_base i2 s2 = OK u2 /\ access_ok cap G2 fn i2 s2 /\ taint_ok fn tn2 i2 s2` by
    (qpat_assum `!fn G tn s id tmp imm b rt cap. _ ==> step_inst_base _ _ = OK _ /\ _`
       (qspecl_then [`fn`,`G2`,`tn2`,`s2`,`id+2`,`tmp`,`imm`,`b`,`rt`,`cap`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
     simp[NoAsms, Abbr `i2`, Abbr `u2`]) >>
  `step_prov [] G2 i2 u2 = G2 /\ tn3.t_var = tn2.t_var /\
   tn3.t_stor = tn2.t_stor /\ tn3.t_trans = tn2.t_trans /\
   (!j. j < cap ==> (b+rt+j IN tn3.t_mem <=> j IN tn2.t_mem))` by
    (qpat_assum `!PG G tn s id tmp imm b rt cap u tn'. _ ==> step_prov _ _ _ _ = G /\ _`
       (qspecl_then [`[]`,`G2`,`tn2`,`s2`,`id+2`,`tmp`,`imm`,`b`,`rt`,`cap`,`u2`,`tn3`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE simp[NoAsms, Abbr `i2`, Abbr `u2`, Abbr `tn3`]))) >>
     simp[NoAsms, Abbr `i2`]);

val linked_positive_epilogue_after_mcopy_tac =
  qpat_assum `!s b rt cap u s'. _ ==> u.vs_requests = s.vs_requests /\ _`
    (qspecl_then [`s2`,`b`,`rt`,`cap`,`u2`,`s3`] mp_tac) >>
  (impl_tac >- simp[NoAsms, Abbr `u2`, Abbr `s3`]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `get_instruction bb s3.vs_inst_idx = SOME i3` by
    (qpat_assum `get_instruction bb (SUC (SUC (SUC s.vs_inst_idx))) = SOME i3` mp_tac >>
     qpat_assum `s3.vs_inst_idx = _` (fn a => qpat_assum `s2.vs_inst_idx = _` (fn b =>
       qpat_assum `s1.vs_inst_idx = _` (fn c => simp[NoAsms,a,b,c])))) >>
  `allocas_from cap s3 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s3)` by
    (qpat_assum `allocas_from cap s3 <=> allocas_from cap s2` (fn a =>
       qpat_assum `allocas_below_fmp s3 <=> allocas_below_fmp s2` (fn b =>
         pure_rewrite_tac[a,b])) >> rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  `eval_operand (Var buf) s3 = SOME (n2w b)` by
    (qpat_assum `eval_operand (Var buf) s2 = SOME _` mp_tac >>
     qpat_assum `s3.vs_vars = _` (fn th => simp[NoAsms, th, eval_operand_def, lookup_var_def])) >>
  `op_taint tn3 (Var buf) = {}` by
    (qpat_assum `op_taint tn2 (Var buf) = {}` mp_tac >>
     qpat_assum `tn3.t_var = _` (fn th => simp[NoAsms, th, op_taint_def])) >>
  `s1.vs_labels = s.vs_labels` by
    (qpat_assum `u0.vs_labels = s.vs_labels` mp_tac >> simp[NoAsms, Abbr `s1`]) >>
  `FLOOKUP s3.vs_labels "runtime_begin" = SOME codepos` by
    (qpat_assum `s3.vs_labels = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `s2.vs_labels = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `s1.vs_labels = _` (fn th => pure_rewrite_tac[th]) >> FIRST_ASSUM ACCEPT_TAC);

fun linked_ep_fields pats tac =
  let fun collect [] ths = tac ths
        | collect (p::ps) ths = qpat_assum p (fn th => collect ps (th::ths))
  in collect pats [] end;

val linked_positive_epilogue_codecopy_join_tac =
  qabbrev_tac `u3 = write_memory_with_expansion b
    (TAKE rt (DROP (w2n codepos) s3.vs_code ++ REPLICATE rt 0w)) s3` >>
  qabbrev_tac `s4 = u3 with vs_inst_idx := SUC s3.vs_inst_idx` >>
  qpat_assum `!id buf rt cap b label lo fn PG G tn s i u next. _ ==> step_inst_base i s = OK u /\ _`
     (qspecl_then [`id`,`buf`,`rt`,`cap`,`b`,`codepos`,`cap`,`fn`,`[]`,`G2`,`tn3`,`s3`,`i3`,`u3`,`s4`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE simp[NoAsms, Abbr `i3`, Abbr `u3`, Abbr `s4`]))) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `tn4 = tn3 with t_mem := tn3.t_mem DIFF {k | b <= k /\ k < b+rt}` >>
  `step_taint i3 s3 u3 tn3 = tn4` by
    (qpat_assum `step_taint i3 s3 u3 tn3 = _` mp_tac >> simp[NoAsms, Abbr `tn4`]) >>
  `op_taint tn4 (Var buf) = {}` by
    (qpat_assum `op_taint tn3 (Var buf) = {}` mp_tac >> simp[NoAsms, Abbr `tn4`, op_taint_def]) >>
  `tn4.t_stor = tn.t_stor /\ tn4.t_trans = tn.t_trans /\
   tn4.t_mem = tn3.t_mem DIFF {k | b <= k /\ k < b+rt}` by
    linked_ep_fields [`tn3.t_stor = _`, `tn2.t_stor = _`, `tn3.t_trans = _`, `tn2.t_trans = _`]
      (fn ths => simp ([NoAsms, Abbr `tn4`] @ ths));

val linked_positive_epilogue_after_codecopy_tac =
  `s4.vs_call_ctx = s.vs_call_ctx /\ s4.vs_accounts = s.vs_accounts /\ s4.vs_transient = s.vs_transient` by
    linked_ep_fields [`s4.vs_call_ctx = _`, `s3.vs_call_ctx = _`, `s2.vs_call_ctx = _`, `u0.vs_call_ctx = _`,
       `s4.vs_accounts = _`, `s3.vs_accounts = _`, `s2.vs_accounts = _`, `u0.vs_accounts = _`,
       `s4.vs_transient = _`, `s3.vs_transient = _`, `s2.vs_transient = _`, `u0.vs_transient = _`]
       (fn ths => pure_rewrite_tac ths >> simp[NoAsms, Abbr `s1`] >> simp (NoAsms :: ths)) >>
  `get_instruction bb s4.vs_inst_idx = SOME i4` by
    (qpat_assum `get_instruction bb (SUC (SUC (SUC (SUC s.vs_inst_idx)))) = SOME i4` mp_tac >>
     linked_ep_fields [`s4.vs_inst_idx = _`,`s3.vs_inst_idx = _`,`s2.vs_inst_idx = _`,`s1.vs_inst_idx = _`]
       (fn ths => simp (NoAsms :: ths))) >>
  `allocas_from cap s4 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s4)` by
    (conj_tac >- (qpat_assum `allocas_from cap s3` mp_tac >>
       linked_ep_fields [`s4.vs_allocas = _`] (fn ths => simp ([NoAsms, allocas_from_def] @ ths))) >>
     disch_tac >> qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s3` drule >>
     linked_ep_fields [`s4.vs_allocas = _`,`s4.vs_fmp = _`,`s4.vs_initial_fmp = _`]
       (fn ths => pure_rewrite_tac [allocas_below_fmp_def] >>
         pure_rewrite_tac ths >> simp[NoAsms]));

val linked_positive_epilogue_run_halt_tac =
  `i0.inst_opcode <> INVOKE /\ ~is_terminator i0.inst_opcode /\
   i1.inst_opcode <> INVOKE /\ ~is_terminator i1.inst_opcode /\
   i2.inst_opcode <> INVOKE /\ ~is_terminator i2.inst_opcode /\
   i3.inst_opcode <> INVOKE /\ ~is_terminator i3.inst_opcode /\
   i4.inst_opcode <> INVOKE /\ i4.inst_opcode = RETURN /\
   i4.inst_operands = [Var buf; Lit (n2w (rt+cap))]` by
    simp[NoAsms, Abbr `i0`, Abbr `i1`, Abbr `i2`, Abbr `i3`, Abbr `i4`, mk_inst_def, is_terminator_def] >>
  qabbrev_tac `sh = halt_state (set_returndata (mem_bytes_at b (rt+cap) s4.vs_memory) s4)` >>
  qpat_assum `!ctx fn fuel cap n b G tn4 ret buf s4 sh. _ ==> step_inst fuel ctx ret s4 = Halt sh /\ _`
    (qspecl_then [`ctx`,`fn`,`fuel`,`cap`,`rt+cap`,`b`,`G2`,`tn4`,`i4`,`buf`,`s4`,`sh`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE simp[NoAsms, Abbr `sh`]))) >>
  disch_then (map_every assume_tac o CONJUNCTS);

val linked_positive_epilogue_identify_halt_tac =
  `step_inst fuel ctx i0 s = OK u0 /\ step_inst fuel ctx i1 s1 = OK u1 /\
   step_inst fuel ctx i2 s2 = OK u2 /\ step_inst fuel ctx i3 s3 = OK u3` by
    (simp[step_inst_non_invoke] >> rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  `exec_block fuel ctx bb s4 = Halt sh` by
    (qpat_assum `get_instruction bb s4.vs_inst_idx = SOME i4`
       (fn th => pure_once_rewrite_tac [MATCH_MP (SPEC_ALL fnBlockBodyHelpersTheory.exec_block_step) th]) >>
     simp[]) >>
  `exec_block fuel ctx bb s3 = exec_block fuel ctx bb s4` by
    linked_ep_fields [`get_instruction bb s3.vs_inst_idx = SOME i3`, `step_inst fuel ctx i3 s3 = OK u3`,
                      `~is_terminator i3.inst_opcode`] (fn ths =>
      simp ([NoAsms, Abbr `s4`, blockSimHelpersTheory.exec_block_step] @ ths)) >>
  `exec_block fuel ctx bb s2 = exec_block fuel ctx bb s3` by
    linked_ep_fields [`get_instruction bb s2.vs_inst_idx = SOME i2`, `step_inst fuel ctx i2 s2 = OK u2`,
                      `~is_terminator i2.inst_opcode`] (fn ths =>
      simp ([NoAsms, Abbr `s3`, blockSimHelpersTheory.exec_block_step] @ ths)) >>
  `exec_block fuel ctx bb s1 = exec_block fuel ctx bb s2` by
    linked_ep_fields [`get_instruction bb s1.vs_inst_idx = SOME i1`, `step_inst fuel ctx i1 s1 = OK u1`,
                      `~is_terminator i1.inst_opcode`] (fn ths =>
      simp ([NoAsms, Abbr `s2`, blockSimHelpersTheory.exec_block_step] @ ths)) >>
  `exec_block fuel ctx bb s = exec_block fuel ctx bb s1` by
    linked_ep_fields [`get_instruction bb s.vs_inst_idx = SOME i0`, `step_inst fuel ctx i0 s = OK u0`,
                      `~is_terminator i0.inst_opcode`] (fn ths =>
      simp ([NoAsms, Abbr `s1`, blockSimHelpersTheory.exec_block_step] @ ths)) >>
  `final = sh` by
    (qpat_assum `run_from fuel ctx fn s = Halt final` mp_tac >>
     linked_ep_fields [`lookup_block s.vs_current_bb fn.fn_blocks = SOME bb`,
       `exec_block fuel ctx bb s = _`, `exec_block fuel ctx bb s1 = _`, `exec_block fuel ctx bb s2 = _`,
       `exec_block fuel ctx bb s3 = _`, `exec_block fuel ctx bb s4 = _`] (fn ths =>
       simp ([NoAsms, run_from_def] @ ths))) >>
  qpat_x_assum `final = sh` SUBST_ALL_TAC;

val linked_positive_epilogue_return_check_tac =
  asm "positive_return"
    (qspecl_then [`D`,`ctx`,`fn`,`fuel`,`cap`,`rt`,`b`,`G2`,`tn`,`tn4`,`i4`,`buf`,
       `s`,`s4`,`sh`,`body_ce`,`ctor_ce`,`codepos`,`(tn2:taint).t_mem`,`(tn3:taint).t_mem`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE simp[NoAsms, Abbr `sh`]))) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `step_inst_base i4 s4 = Halt sh` by
    (qpat_assum `step_inst fuel ctx i4 s4 = Halt sh` mp_tac >>
     qpat_assum `i4.inst_opcode <> INVOKE`
       (fn th => simp[NoAsms, step_inst_non_invoke, th]));

val linked_positive_epilogue_scalar_checks_tac =
  `ptrSafeRun$ptr_safe_step D cap fuel ctx fn [] G tn i0 s` by
    (simp[NoAsms, Abbr `i0`] >> irule ctorDeployMemoryRunPtrPrefixStepsTheory.prefix_alloca_ptr_step >>
     rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  `access_ok cap G fn i0 s /\ taint_ok fn tn i0 s` by
    (qpat_assum `ptrSafeRun$ptr_safe_step D cap fuel ctx fn [] G tn i0 s` mp_tac >>
     simp[NoAsms, ptrSafeRunTheory.ptr_safe_step_def, ptrSafeRunTheory.ptr_inst_ok_def] >>
     strip_tac >> simp[]) >>
  `ptr_inst_ok D 0 fuel ctx fn G1 tn1 i1 s1` by
    (simp[NoAsms, Abbr `i1`] >> irule exprSimPtrLiteralOpsTheory.literal_add_ptr_inst_ok >>
     rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  `access_ok cap G1 fn i1 s1 /\ taint_ok fn tn1 i1 s1` by
    (qpat_assum `ptr_inst_ok D 0 fuel ctx fn G1 tn1 i1 s1`
       (strip_assume_tac o PURE_REWRITE_RULE [ptrSafeRunTheory.ptr_inst_ok_def]) >>
     reverse conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
     simp[NoAsms, Abbr `i1`, access_ok_def, mk_inst_def,
          source_memory_write_ranges_def, source_memory_read_ranges_def,
          memLocDefsTheory.mem_write_ops_def, memLocDefsTheory.mem_read_ops_def]) >>
  `step_taint i2 s2 u2 tn2 = tn3` by simp[NoAsms, Abbr `tn3`];

fun linked_positive_epilogue_next (g,tn,s,i,u) next ghosts =
  qpat_assum `!D lo fuel ctx fn G tn bb s i u.
     get_instruction bb s.vs_inst_idx = SOME i /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode /\ _ ==> ptr_safe_block D lo fuel ctx fn [] G tn bb s`
    (qspecl_then [`D`,`cap`,`fuel`,`ctx`,`fn`,g,tn,`bb`,s,i,u] MATCH_MP_TAC) >>
  rpt (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >>
  linked_ep_fields ghosts pure_rewrite_tac >>
  qpat_assum next (fn th => pure_rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]);

val linked_positive_epilogue_begin_block_tac =
  qpat_assum `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb`
    (fn th => simp[NoAsms, ptrSafeRunTheory.ptr_safe_run_def, th]);

val linked_positive_epilogue_finish_block_tac =
  qpat_assum `ptr_inst_ok D cap fuel ctx fn G2 tn4 i4 s4` mp_tac >>
  linked_ep_fields [`step_inst fuel ctx i4 s4 = Halt sh`, `i4.inst_opcode <> INVOKE`]
    (fn ths => simp (NoAsms :: ptrSafeRunTheory.ptr_inst_ok_def :: ths)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!D lo fuel ctx fn G tn bb s i sh.
     get_instruction bb s.vs_inst_idx = SOME i /\ i.inst_opcode <> INVOKE /\
     step_inst_base i s = Halt sh /\ _ ==> ptr_safe_block D lo fuel ctx fn [] G tn bb s`
    (qspecl_then [`D`,`cap`,`fuel`,`ctx`,`fn`,`G2`,`tn4`,`bb`,`s4`,`i4`,`sh`] MATCH_MP_TAC) >>
  rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE simp[NoAsms]);

(* Constant expressions excluding SHA256 can read a cell but have no
   risky accesses. *)
val linked_ctor_replacement_no_risky_tac =
  `(!e. constant_expr mods e /\ no_sha256_expr e ==>
      ~MEM vyperSubscriptOverlap$RiskyAcc (vyperSubscriptOverlap$accesses_expr e)) /\
   (!es. EVERY (constant_expr mods) es /\ no_sha256_exprs es ==>
      ~MEM vyperSubscriptOverlap$RiskyAcc (vyperSubscriptOverlap$accesses_exprs es)) /\
   (!fs. EVERY (constant_expr mods) (MAP SND fs) /\ no_sha256_fields fs ==>
      ~MEM vyperSubscriptOverlap$RiskyAcc
        (vyperSubscriptOverlap$accesses_named_exprs fs))` by
    (POP_ASSUM_LIST (K ALL_TAC) >>
     ho_match_mp_tac constSubstCorrectTheory.const_local_refs_ind >>
     simp[constant_expr_def, constSubstTheory.no_sha256_expr_def,
          vyperSubscriptOverlapTheory.accesses_expr_def, SF ETA_ss] >>
     rpt strip_tac >> gvs[SF ETA_ss] >>
     Cases_on `bi` >>
     gvs[constant_builtin_def, vyperSubscriptOverlapTheory.risky_builtin_def]);

val linked_ctor_replacement_access_tac =
  sg `!e. constant_expr mods e /\ no_sha256_expr e /\
       (!a. MEM a (vyperSubscriptOverlap$accesses_expr e) ==>
         a = vyperSubscriptOverlap$RiskyAcc) ==>
       vyperSubscriptOverlap$accesses_expr e = []` >-
    (qpat_assum `!e. constant_expr mods e /\ no_sha256_expr e ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> disch_tac >>
     `!accs. ~MEM vyperSubscriptOverlap$RiskyAcc accs /\
         (!a. MEM a accs ==> a = vyperSubscriptOverlap$RiskyAcc) ==> accs = []` by
       (POP_ASSUM_LIST (K ALL_TAC) >> Cases >>
        simp[DISJ_IMP_THM, FORALL_AND_THM] >> metis_tac[]) >>
     qx_gen_tac `closed_replacement` >> disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `!accs. _ ==> accs = []`
       (qspec_then `vyperSubscriptOverlap$accesses_expr closed_replacement` mp_tac) >>
     qpat_assum `!e. constant_expr mods e /\ no_sha256_expr e ==> _`
       (qspec_then `closed_replacement` mp_tac) >>
     simp[]);

(* Replay a checked replacement in any observation state, given the
   per-module folds into the constructor's immutable cells. *)
val linked_ctor_constant_replacement_tac =
  sg `!cells.
    (!src ts. MEM (src,ts) mods ==>
      ?A. constants_fold_module mods cells src ts FEMPTY = SOME A /\
          A SUBMAP get_source_immutables src cells) /\
    EVERY (no_sha256_expr o SND) (consts_env_mods mods) /\
    EVERY (no_neg_exp_expr o SND) (consts_env_mods mods) ==>
    !src id r. ALOOKUP (consts_env_mods mods) (src,id) = SOME r ==>
    ?ts vis init ty slot tv v.
      ALOOKUP mods src = SOME ts /\
      MEM (VariableDecl vis (Constant init) id ty slot) ts /\
      expr_type r = ty /\ constant_expr mods r /\
      vyperSubscriptOverlap$accesses_expr r = [] /\
      evaluate_type (get_tenv cx) ty = SOME tv /\
      FLOOKUP (get_source_immutables src cells) id = SOME (tv,v) /\
      !st. eval_expr cx r st = (INL (Value v),st)` >-
    (`get_tenv cx = type_env_all_modules mods` by
       drule_then ACCEPT_TAC vyperTypeConstantFoldTheory.get_tenv_sources >>
     qpat_assum `get_tenv cx = _` mp_tac >>
     qpat_assum `check_contract T _ _ mods = SOME deploy_art` mp_tac >>
     qpat_assum `!e. constant_expr mods e /\ no_sha256_expr e /\ _ ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> ntac 3 disch_tac >>
     qx_gen_tac `fold_cells` >> disch_then (map_every assume_tac o CONJUNCTS) >>
     map_every qx_gen_tac [`cell_src`,`cell_id`,`replacement`] >> disch_tac >>
     drule_all linkedConstantReplacementValueTheory.checked_linked_constant_replacement_value >>
     disch_then (qx_choosel_then [`decls`,`decl_vis`,`decl_init`,`decl_ty`,
                                  `decl_slot`,`value_ty`,`cell_value`]
       (map_every assume_tac o CONJUNCTS)) >>
     `no_sha256_expr replacement` by
       (qpat_assum `ALOOKUP (consts_env_mods mods) (cell_src,cell_id) = SOME replacement`
          (assume_tac o MATCH_MP alistTheory.ALOOKUP_MEM) >>
        qpat_assum `EVERY (no_sha256_expr o SND) _`
          (qspec_then `((cell_src,cell_id),replacement)` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
        simp[]) >>
     `vyperSubscriptOverlap$accesses_expr replacement = []` by
       (qpat_assum `!e. constant_expr mods e /\ no_sha256_expr e /\ _ ==> _`
          (qspec_then `replacement` mp_tac) >> simp[]) >>
     `well_typed_expr (artifact_env deploy_art mods NONE) replacement` by
       (drule_all linkedConstantReplacementTypingTheory.checked_linked_constant_replacements_typed >>
        disch_then (qspec_then `NONE` ACCEPT_TAC)) >>
     `(artifact_env deploy_art mods NONE).type_defs = type_env_all_modules mods` by
       simp[NoAsms, artifact_env_def] >>
     `!st. eval_expr cx replacement st = (INL (Value cell_value),st)` by
       drule_all_then ACCEPT_TAC linkedConstantReplacementEvalTheory.eval_closed_constant_expr >>
     qexistsl_tac [`decls`,`decl_vis`,`decl_init`,`decl_ty`,`decl_slot`,`value_ty`,`cell_value`] >>
     asm_rewrite_tac[]);

val linked_positive_epilogue_alloc_producers_tac =
  POP_ASSUM_LIST (K ALL_TAC) >>
  linked_alloc_site_tac >> linked_add_site_tac >>
  linked_positive_epilogue_mcopy_checks_tac >> linked_positive_epilogue_mcopy_ghost_tac >>
  linked_positive_epilogue_mcopy_frames_tac;

val linked_positive_epilogue_copy_producers_tac =
  linked_positive_epilogue_suffix_tac >> linked_positive_epilogue_codecopy_tac >>
  linked_positive_epilogue_return_step_tac >> linked_positive_epilogue_return_tac;

val linked_positive_epilogue_run_producers_tac =
  linked_epilogue_ptr_next_tac >> linked_epilogue_ptr_halt_tac >>
  linked_epilogue_below_fmp_tac >> linked_epilogue_alloca_resources_tac >> linked_epilogue_alloca_frame_tac;

val linked_ctor_decode_unconditional_tac =
  `!target. supported_stmts_expr_exists (expr_abi_decode_target_root target) cpkg6 ==>
     EXISTS (occurs_abi_decode_target target o SND) mods` by
    (qpat_assum `_ ==> !target. supported_stmts_expr_exists _ cpkg6 ==> _` mp_tac >>
     impl_tac
     >- (qpat_assum `!target. (!env e. _ ==> supported_expr_exists _ _ ==> _) /\ _` mp_tac >>
         qpat_assum `!key r target. ALOOKUP (consts_env_mods mods) key = SOME r ==> _` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> metis_tac[]) >>
     disch_then ACCEPT_TAC);

val linked_ctor_support_unconditional_tac =
  `!key r. ALOOKUP (consts_env_mods mods) key = SOME r ==>
      constant_expr mods r /\ vyperSubscriptOverlap$accesses_expr r = []` by
    (qpat_assum `!cells. _ ==> !src id r. ALOOKUP (consts_env_mods mods) (src,id) = SOME r ==> _`
       (qspec_then `cells` mp_tac) >>
     (impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
     POP_ASSUM_LIST (K ALL_TAC) >> disch_tac >>
     map_every qx_gen_tac [`key`,`replacement`] >> PairCases_on `key` >>
     metis_tac[]) >>
  `subst_consts_stmts_mods (consts_env_mods mods) cpkg6 = cpkg6` by
    (qpat_assum `_ ==> subst_consts_stmts_mods _ cpkg6 = cpkg6` irule >>
     FIRST_ASSUM ACCEPT_TAC) >>
  `?bindings. supported_stmts tops' bindings cpkg6` by
    (qpat_assum `_ ==> ?bindings. supported_stmts tops' bindings cpkg6` irule >>
     conj_tac >> FIRST_ASSUM ACCEPT_TAC);

(* The lookup certificate selects one entry root per qualified key.  A
   later observation need agree only on these roots, not on whole tables. *)
val linked_ctor_constant_roots_tac =
  let
    fun hit k =
      qpat_assum `!src id r. ALOOKUP (consts_env_mods mods) (src,id) = SOME r ==> _`
        (drule_then k)
  in
    sg `!root_cells src_es env.
      (!src ts. MEM (src,ts) mods ==>
        ?A. constants_fold_module mods root_cells src ts FEMPTY = SOME A /\
            A SUBMAP get_source_immutables src root_cells) /\
      (!src id r. ALOOKUP (consts_env_mods mods) (src,id) = SOME r ==>
        ?ts vis init ty slot tv v.
          ALOOKUP mods src = SOME ts /\
          MEM (VariableDecl vis (Constant init) id ty slot) ts /\
          expr_type r = ty /\ constant_expr mods r /\
          vyperSubscriptOverlap$accesses_expr r = [] /\
          evaluate_type (get_tenv cx) ty = SOME tv /\
          FLOOKUP (get_source_immutables src root_cells) id = SOME (tv,v) /\
          !st. eval_expr cx r st = (INL (Value v),st)) /\
      ALOOKUP src_es.immutables cx.txn.target = SOME root_cells /\
      constSubstCorrect$frame_maps env deploy_art /\
      env.toplevel_vtypes = deploy_art.cta_toplevel_vtypes /\
      env.type_defs = get_tenv cx /\ state_well_typed src_es ==>
      body_const_cells_agree_mods mods cx env src_es` >-
    (qpat_assum `check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME deploy_art` mp_tac >>
     qpat_assum `ALOOKUP cx.sources cx.txn.target = SOME mods` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> ntac 2 disch_tac >>
     map_every qx_gen_tac [`root_cells`,`src_es`,`env`] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qabbrev_tac `roots =
       MAP (\(src,id). (cx.txn.target,src,id,
                      THE (FLOOKUP (get_source_immutables src root_cells) id)))
           (MAP FST (consts_env_mods mods))` >>
     `contract_namespaces_ok F mods` by
       drule_then ACCEPT_TAC check_contract_runtime_namespaces >>
     `imms_well_typed root_cells` by
       drule_all_then ACCEPT_TAC vyperTypeEnvTheory.state_well_typed_immutables_ALOOKUP >>
     (sg `!addr src id tv v. MEM (addr,src,id,tv,v) roots ==>
       addr = cx.txn.target /\ declared_constant mods src id /\
       FLOOKUP (get_source_immutables src root_cells) id = SOME (tv,v)` >-
       (rpt gen_tac >> simp[NoAsms, Abbr `roots`, MEM_MAP, pairTheory.EXISTS_PROD] >>
        disch_then strip_assume_tac >> gvs[] >>
        `ALOOKUP (consts_env_mods mods) (src,id) <> NONE` by
          (simp[NoAsms, alistTheory.ALOOKUP_NONE, MEM_MAP, pairTheory.EXISTS_PROD] >>
           goal_assum (drule_at Any)) >>
        Cases_on `ALOOKUP (consts_env_mods mods) (src,id)` >- fs[] >>
        hit strip_assume_tac >>
        conj_tac >- metis_tac[declared_constant_def, alistTheory.ALOOKUP_MEM] >>
        gvs[])) >>
     rewrite_tac[bodyFullPredsModsTheory.body_const_cells_agree_mods_def] >>
     qexistsl_tac [`roots`,`deploy_art`,`root_cells`] >> simp[] >>
     rpt conj_tac
     >- (rpt gen_tac >> strip_tac >>
         qpat_assum `!addr src id tv v. MEM (addr,src,id,tv,v) roots ==> _`
           (drule_then strip_assume_tac) >>
         simp[constSubstCorrectTheory.checked_frame_context_def] >>
         qexists_tac `cx.in_deploy` >> first_assum ACCEPT_TAC)
     >- (map_every qx_gen_tac [`src`,`id`,`r`] >> disch_tac >>
         hit (qx_choosel_then [`ts`,`vis`,`init`,`ty`,`slot`,`tv`,`v`]
                (map_every assume_tac o CONJUNCTS)) >>
         `MEM (cx.txn.target,src,id,tv,v) roots` by
           (simp[NoAsms, Abbr `roots`, MEM_MAP, pairTheory.EXISTS_PROD] >>
            conj_tac >- simp[] >> qexists_tac `r` >>
            drule_then ACCEPT_TAC alistTheory.ALOOKUP_MEM) >>
         `value_has_type tv v` by
           drule_all_then (ACCEPT_TAC o CONJUNCT1) vyperTypeEnvTheory.imms_well_typed_get_source_immutables >>
         `declared_constant mods src id` by
           (simp[declared_constant_def] >>
            qexistsl_tac [`ts`,`vis`,`init`,`ty`,`slot`] >> simp[alistTheory.ALOOKUP_MEM]) >>
         `FLOOKUP env.bare_globals (src,id) = SOME ty` by
           (qpat_assum `constSubstCorrect$frame_maps env deploy_art`
              (assume_tac o CONJUNCT1 o REWRITE_RULE [constSubstCorrectTheory.frame_maps_def]) >>
            drule_then (assume_tac o CONJUNCT1) check_contract_nonsig_maps >>
            simp[] >> irule build_contract_type_artifact_bare_globals_complete >>
            metis_tac[]) >>
         `FLOOKUP deploy_art.cta_toplevel_vtypes (src,id) = SOME (Type ty)` by
           (qpat_assum `check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME deploy_art`
              (mp_then Any mp_tac vyperTypeContractStaticMapsTheory.check_contract_bare_global_toplevel_vtype) >>
            disch_then (qspecl_then [`vis`,`ty`,`ts`,`src`,`Constant init`,`slot`,`id`] mp_tac) >>
            simp[]) >>
         asm_rewrite_tac[] >> qexistsl_tac [`Value v`,`v`] >>
         conj_tac
         >- (simp[constSubstCorrectTheory.const_result_at_def,
                  vyperStateTheory.subscripts_type_def, vyperStateTheory.evaluate_subscripts_def] >>
             qexistsl_tac [`tv`,`v`] >> simp[]) >>
         conj_tac >- simp[constSubstCorrectTheory.const_result_at_def] >>
         qx_gen_tac `st` >> disch_tac >> conj_tac >- (
           `MEM (src,ts) mods` by drule_then ACCEPT_TAC alistTheory.ALOOKUP_MEM >>
           `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
             drule_all_then ACCEPT_TAC contract_namespaces_ok_module_toplevel_vtype_keys >>
           `find_var_decl_by_name id ts = NONE` by
             drule_all_then ACCEPT_TAC find_var_decl_by_name_NONE_Constant >>
           qpat_assum `constSubstCorrect$const_cells_agree roots st`
             (mp_tac o REWRITE_RULE [constSubstCorrectTheory.const_cells_agree_def]) >>
           disch_then (qspecl_then [`cx.txn.target`,`src`,`id`,`tv`,`v`] mp_tac) >>
           simp[] >> strip_tac >>
           simp[vyperStateTheory.lookup_global_def, vyperContextTheory.get_module_code_def,
                vyperStateTheory.get_immutables_def, vyperStateTheory.get_address_immutables_def,
                vyperStateTheory.bind_def, vyperStateTheory.lift_option_type_def,
                vyperStateTheory.return_def]) >>
         simp[]) >>
     simp[constSubstCorrectTheory.const_cells_agree_def] >> rpt gen_tac >> strip_tac >>
     qpat_assum `!addr src id tv v. MEM (addr,src,id,tv,v) roots ==> _`
       (drule_then strip_assume_tac) >>
     qexists_tac `root_cells` >> simp[])
  end;

(* Specialize the fold and replacement facts to the cells at es0. *)
val linked_ctor_constant_entry_tac =
  sg `!env src_es.
    constSubstCorrect$frame_maps env deploy_art /\
    env.toplevel_vtypes = deploy_art.cta_toplevel_vtypes /\
    env.type_defs = get_tenv cx /\ state_well_typed src_es /\
    src_es.immutables = es0.immutables ==>
    body_const_cells_agree_mods mods cx env src_es` >-
  (map_every qx_gen_tac [`env`,`src_es`] >>
   disch_then (map_every assume_tac o CONJUNCTS) >>
   `ALOOKUP src_es.immutables cx.txn.target = SOME cells` by
     (qpat_assum `src_es.immutables = es0.immutables` SUBST1_TAC >>
      first_assum ACCEPT_TAC) >>
   qpat_assum `!fold_cells. _ ==> !src id r.
       ALOOKUP (consts_env_mods mods) (src,id) = SOME r ==> _`
     (qspec_then `cells` mp_tac) >>
   (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
   qpat_assum `!root_cells src_es env. _ ==>
       body_const_cells_agree_mods mods cx env src_es`
     (qspecl_then [`cells`,`src_es`,`env`] mp_tac) >>
   (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
   disch_then ACCEPT_TAC);

(* Byte supports and covers must come from the same checked decoder endpoint. *)
val linked_ctor_registered_ghost_goal =
  sg `!actual Gbody tnbody tnpre t src.
    src.scopes = [scope] /\
    allocas_from (imm_len_mods mods) actual /\ imm_len_mods mods <= actual.vs_alloca_next /\
    imm_len_mods mods <= t.vs_alloca_next /\
    tnpre.t_mem = {} /\ tnpre.t_stor = {} /\ tnpre.t_trans = {} /\ tnpre.t_imm = {} /\
    (!i. i < t.vs_alloca_next /\ i IN tnbody.t_mem ==> i IN tnpre.t_mem) /\
    tnbody.t_stor = tnpre.t_stor /\ tnbody.t_trans = tnpre.t_trans /\ tnbody.t_imm = tnpre.t_imm /\
    op_prov Gbody imm = NONE /\ op_taint tnbody imm = {} /\
    (!j. j < LENGTH src_args ==> ?entry d B.
       imm_len_mods mods <= d /\
       lookup_scopes (FST (EL j src_args)) [scope] = SOME entry /\
       local_region ctor_ce [scope] actual (FST (EL j src_args)) d
         (type_memory_bytes ce_before_registration (SND (EL j src_args))) /\
       (?p. FLOOKUP ctor_ce.ce_vars (FST (EL j src_args)) =
         SOME (PtrVar (Var p) (type_memory_bytes ce_before_registration (SND (EL j src_args)))) /\
         ptr_covers Gbody tnbody p actual (type_memory_bytes ce_before_registration (SND (EL j src_args)))) /\
       FINITE B /\ DISJOINT B tnbody.t_mem /\
       (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
         val_in_memory entry.type entry.value d mem)) ==>
    !H. ghost_inv_at_mods (linked_ret_DF H) (imm_len_mods mods) NONE ctor_ce cx src Gbody tnbody actual`;

val linked_ctor_registered_ghost_open_tac =
  rpt gen_tac >> disch_then
    (fn th => case rev (CONJUNCTS th) of
       supports :: frame => map_every assume_tac (rev frame) >> mk_asm "checked_formal_supports" supports
     | [] => NO_TAC) >> gen_tac >>
  pure_rewrite_tac[bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def] >>
  reverse conj_tac;

val linked_ctor_registered_ghost_frame_tac =
  qpat_assum `ctor_ce.ce_is_ctor /\ ctor_ce.ce_return_pc = NONE /\ _` (fn ret =>
  let val rpc = cj 2 ret in
  qpat_assum `tnbody.t_stor = tnpre.t_stor` (fn stor =>
  qpat_assum `tnbody.t_trans = tnpre.t_trans` (fn trans =>
  qpat_assum `tnbody.t_imm = tnpre.t_imm` (fn im =>
  qpat_assum `tnpre.t_stor = {}` (fn stor0 =>
  qpat_assum `tnpre.t_trans = {}` (fn trans0 =>
  qpat_assum `tnpre.t_imm = {}` (fn im0 =>
    simp[NoAsms, rpc, stor, trans, im, stor0, trans0, im0,
         bodyPtrDefsTheory.return_buf_ptr_def, bodyPtrDefsTheory.stor_taint_ok_at_def]))))))
  end);

val linked_ctor_registered_ghost_low_tac =
  rpt gen_tac >> strip_tac >>
  `i < t.vs_alloca_next` by decide_tac >>
  qpat_assum `!i. i < t.vs_alloca_next /\ i IN tnbody.t_mem ==> _`
    (drule_all_then mp_tac) >>
  qpat_assum `tnpre.t_mem = {}` (fn h => simp[NoAsms,h]);

val linked_ctor_registered_ghost_imm_tac =
  qx_gen_tac `x` >> strip_tac >>
      `ctor_ce.ce_imm_alloca = SOME imm` by
        (qpat_assum `imm_len_mods mods <> 0 ==> ctor_ce.ce_imm_alloca = SOME imm`
           (drule_then ACCEPT_TAC)) >>
      `imm = Var x` by
        (qpat_assum `ctor_ce.ce_imm_alloca = SOME imm` mp_tac >>
         qpat_assum `ctor_ce.ce_imm_alloca = SOME (Var x)` (fn h => simp[NoAsms,h])) >>
      qpat_assum `imm = Var x` (fn h =>
        qpat_assum `op_prov Gbody imm = NONE` (fn p =>
        qpat_assum `op_taint tnbody imm = {}` (fn q =>
          mp_tac (PURE_REWRITE_RULE [h,op_prov_def] p) >>
          simp[NoAsms,PURE_REWRITE_RULE [h] q])));

val linked_ctor_registered_ghost_lookup_tac =
  map_every qx_gen_tac [`name`,`entry`,`p`,`sz`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!n l. FLOOKUP ctor_ce.ce_vars n = SOME l ==> MEM n (MAP FST src_args)`
    (drule_then (mp_tac o PURE_REWRITE_RULE [listTheory.MEM_EL, listTheory.LENGTH_MAP])) >>
  disch_then (qx_choose_then `j` strip_assume_tac) >>
  qpat_x_assum `name = EL j (MAP FST src_args)` mp_tac >>
  qpat_assum `j < LENGTH src_args` (fn h => simp[NoAsms,h,listTheory.EL_MAP]) >>
  disch_then SUBST_ALL_TAC;

val linked_ctor_registered_ghost_support_tac =
  asm "checked_formal_supports" (drule_then strip_assume_tac);

val linked_ctor_registered_ghost_scope_tac =
  qpat_assum `src.scopes = [scope]` SUBST_ALL_TAC >>
  qpat_assum `lookup_scopes (FST (EL j src_args)) [scope] = SOME entry` mp_tac >>
  qpat_assum `lookup_scopes (FST (EL j src_args)) [scope] = SOME _` mp_tac >>
  qpat_assum `FLOOKUP ctor_ce.ce_vars (FST (EL j src_args)) = SOME (PtrVar (Var p) sz)` mp_tac >>
  qpat_assum `FLOOKUP ctor_ce.ce_vars (FST (EL j src_args)) =
    SOME (PtrVar _ (type_memory_bytes ce_before_registration (SND (EL j src_args))))` mp_tac >>
  qpat_assum `ptr_covers Gbody tnbody _ actual
    (type_memory_bytes ce_before_registration (SND (EL j src_args)))` mp_tac >>
  qpat_assum `local_region ctor_ce [scope] actual (FST (EL j src_args)) _ _` mp_tac >>
  qpat_assum `DISJOINT _ tnbody.t_mem` mp_tac >>
  qpat_assum `!mem. _ ==> val_in_memory _ _ _ mem` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> gvs[local_region_def];

val linked_ctor_registered_ghost_bytes_tac =
  gen_tac >> disch_tac >>
  qpat_assum `!mem. _ ==> val_in_memory _ _ _ mem` irule >>
  fs[bodyPtrDefsTheory.mem_agree_outside_def, pred_setTheory.IN_DISJOINT] >>
  metis_tac[];

(* Transport the immutable operand on the suffix's old-variable frame. *)
val linked_ctor_registered_imm_transport_tac =
  `!x. imm = Var x ==> not_fresh_at st1 x` by
    (qpat_assum `!x. ce_before_registration.ce_imm_alloca = SOME (Var x) ==> _` mp_tac >>
     qpat_assum `ce_before_registration = cpkg0 with ce_imm_alloca := _` SUBST1_TAC >>
     qpat_assum `(if imm_len_mods mods > 0 then _ else _) st_pay = (imm,st1)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `imm_len_mods mods > 0` >> simp[comp_return_def]) >>
  `!Gpre tnpre Gbody tnbody.
      op_prov Gpre imm = NONE /\ op_taint tnpre imm = {} /\
      (!x. not_fresh_at st1 x ==> FLOOKUP Gbody x = FLOOKUP Gpre x /\
          op_taint tnbody (Var x) = op_taint tnpre (Var x)) ==>
      op_prov Gbody imm = NONE /\ op_taint tnbody imm = {}` by
    (qpat_assum `!x. imm = Var x ==> not_fresh_at st1 x` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `imm` >> simp[op_prov_def,op_taint_def] >>
     disch_tac >> rpt gen_tac >> strip_tac >> res_tac >> simp[]);

val linked_ctor_registered_return_buf_tac =
  `ce1.ce_return_buf = ce_before_registration.ce_return_buf` by
    (qpat_assum `!pos ce off size cs ce' cs'. compile_register_constructor_args ce pos off size cs = _ ==> _`
       (drule_then (mp_tac o AP_TERM ``\ce:compile_env. ce.ce_return_buf``)) >>
     simp[NoAsms]) >>
  `ce_base.ce_return_buf = NONE` by
    (qpat_assum `Abbrev (ce_base = _)`
       (PURE_REWRITE_TAC o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     simp[NoAsms,build_compile_env_unit_def,LET_THM,pairTheory.ELIM_UNCURRY]) >>
  `ctor_ce.ce_return_buf = NONE` by
    (qpat_assum `ce1.ce_return_buf = ce_before_registration.ce_return_buf` (fn reg =>
     qpat_assum `ce_before_registration = _ with ce_imm_alloca := _` (fn pre =>
     qpat_assum `cpkg0 = _` (fn pkg =>
     qpat_assum `ce_base.ce_return_buf = NONE` (fn base =>
       simp[NoAsms,Abbr `ctor_ce`,reg,pre,pkg,base])))));

val linked_ctor_registered_control_goal =
  sg `!actual src. alloca_history fn actual /\
     (ctx_has_dalloca deploy_unit.cu_context ==> allocas_below_fmp actual) /\
     ~actual.vs_halted /\ actual.vs_current_bb = st2.cs_current_bb /\
     actual.vs_inst_idx = LENGTH st2.cs_current_insts ==>
     ret_pc_ok ctor_ce sa actual /\
     (!x sz. ctor_ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
     return_buf_frame NONE ctor_ce sa actual /\ return_buf_sep NONE ctor_ce src actual /\
     alloca_history fn actual /\
     (ctx_has_dalloca deploy_unit.cu_context ==> allocas_below_fmp actual) /\
     ~actual.vs_halted /\ actual.vs_current_bb = sa.cs_current_bb /\
     actual.vs_inst_idx = LENGTH sa.cs_current_insts`;

val linked_ctor_registered_control_tac =
    qpat_assum `ctor_ce.ce_is_ctor /\ ctor_ce.ce_return_pc = NONE /\ _` (mp_tac o cj 2) >>
     qpat_assum `ctor_ce.ce_return_buf = NONE` mp_tac >>
     qpat_assum `fresh_label "ctor_exit" st2 = (exit_lbl,sa)`
       (fn h => let val props = MATCH_MP emitHelperPropsTheory.fresh_label_props h in
         mp_tac (cj 1 props) >> mp_tac (cj 3 props) end) >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rpt disch_tac >>
     simp[loweringPostsTheory.ret_pc_ok_def,loweringPostsTheory.return_buf_frame_def,
          bodySimFullTheory.return_buf_sep_def];

(* Classify active dynamic allocations in every function of the linked unit. *)
val linked_ctor_dalloca_windows_tac =
  `!callee bb. MEM callee deploy_unit.cu_context.ctx_functions /\ MEM bb callee.fn_blocks ==>
      dalloca_windows (\chunk k. raw_call_dalloca_chunk chunk k \/
        create_copy_dalloca_chunk chunk k \/ create_blueprint_dalloca_chunk chunk k)
        bb.bb_instructions` by
    (qpat_assum `lower_vyper_deploy_unit_mods mods exps rpolicy runtime_bc = SOME deploy_unit` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> disch_tac >>
     drule_at (Pat `lower_vyper_deploy_unit_mods _ _ _ _ = _`)
       (Q.INST [`window` |-> `\chunk k. raw_call_dalloca_chunk chunk k \/
           create_copy_dalloca_chunk chunk k \/ create_blueprint_dalloca_chunk chunk k`]
         linkedDeployDallocaWindowsTheory.lower_vyper_deploy_unit_dalloca_windows_mods) >>
     simp[]) >>
  `!callee. MEM callee deploy_unit.cu_context.ctx_functions ==> ALL_DISTINCT (fn_labels callee)` by
    (qpat_assum `lowering_context_ok deploy_unit.cu_context`
       (mp_tac o CONJUNCT1 o MATCH_MP vyperCompilerTheory.lowering_context_ok_bridge) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[EVERY_MEM]) >>
  `!callee i s. MEM callee deploy_unit.cu_context.ctx_functions /\
     active_inst callee i s /\ i.inst_opcode = DALLOCA ==>
     raw_call_dalloca_window callee i s \/ create_copy_dalloca_window callee i s \/
     create_blueprint_dalloca_window callee i s` by
    (map_every qx_gen_tac [`callee`,`i`,`s`] >> disch_then (map_every assume_tac o CONJUNCTS) >>
     match_mp_tac runtimePeakMemoryCodeTheory.active_inst_dalloca_windows_with_blueprint >>
     `ALL_DISTINCT (fn_labels callee)` by
       (qpat_assum `!f. MEM f deploy_unit.cu_context.ctx_functions ==> ALL_DISTINCT _`
         (drule_then ACCEPT_TAC)) >>
     `!bb. MEM bb callee.fn_blocks ==> dalloca_windows
       (\chunk k. raw_call_dalloca_chunk chunk k \/ create_copy_dalloca_chunk chunk k \/
         create_blueprint_dalloca_chunk chunk k) bb.bb_instructions` by
       (qpat_assum `!f bb. MEM f deploy_unit.cu_context.ctx_functions /\ _ ==> _`
         (qspec_then `callee` mp_tac) >> simp[]) >>
     rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC);

val linked_ctor_raw_headroom_tac =
  `!vi. account_code_lengths_ok vi.vs_accounts /\ ~vi.vs_halted /\
     vi.vs_fmp = vi.vs_initial_fmp /\ w2n vi.vs_initial_fmp < 2 ** 254 /\
     LENGTH vi.vs_outcomes < 2 ** 64 /\ outcomes_accounts_typed (SOME vi.vs_outcomes) /\
     LENGTH vi.vs_call_ctx.cc_calldata < 2 ** 64 ==>
     !callee inst s. raw_reachable vi deploy_unit.cu_context callee inst s ==>
       dalloca_fmp_headroom inst s` by
    (qx_gen_tac `vi` >> disch_then (map_every assume_tac o CONJUNCTS) >>
     mp_tac (Q.INST [`ctx` |-> `deploy_unit.cu_context`, `vi` |-> `vi`]
       runtimePeakMemoryProofTheory.raw_headroom_from_dalloca_windows) >>
     impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     disch_then ACCEPT_TAC);

fun linked_ctor_variant_headroom_tac frame =
  `account_code_lengths_ok vs.vs_accounts /\ vs.vs_call_ctx.cc_calldata = [] /\
    ~vs.vs_halted /\ vs.vs_outcomes = MAP SND (call_trace ^frame)` by
    (qpat_assum `Abbrev (vs = _)` (mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `deploy_state_rel_mods mods exps (assemble prog') am tx ^frame` mp_tac >>
     qpat_assum `machine_well_typed am` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     strip_tac >> rewrite_tac[deploy_state_rel_mods_def] >> strip_tac >> strip_tac >>
     simp[opt_entry_state_own_def,entry_venom_state_def,init_venom_state_def,
          loweringBudgetAccountCodesTheory.initial_account_codes_after_transfer]) >>
  (sg `!vi. raw_variant fmp vi vs /\ LENGTH (call_trace ^frame) < 2 ** 64 ==>
     !callee inst s. raw_reachable vi deploy_unit.cu_context callee inst s ==>
       dalloca_fmp_headroom inst s` >-
    (qx_gen_tac `vi` >> disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `!v. account_code_lengths_ok v.vs_accounts /\ _ ==> _`
       (qspec_then `vi` mp_tac) >>
     reverse impl_tac >- (disch_then ACCEPT_TAC) >>
     (sg `vi.vs_fmp = fmp /\ vi.vs_initial_fmp = fmp /\
          vi.vs_accounts = vs.vs_accounts /\ vi.vs_halted = vs.vs_halted /\
          vi.vs_outcomes = vs.vs_outcomes /\ vi.vs_call_ctx = vs.vs_call_ctx` >-
       (qpat_assum `raw_variant fmp vi vs` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp[raw_variant_def,gas_variant_def,venom_state_component_equality] >>
        strip_tac >> gvs[] >> metis_tac[])) >>
     map_every (fn p => qpat_assum p (fn th => PURE_REWRITE_TAC [th]))
       [`vi.vs_fmp = fmp`, `vi.vs_initial_fmp = fmp`,
        `vi.vs_accounts = vs.vs_accounts`, `vi.vs_halted = vs.vs_halted`,
        `vi.vs_outcomes = vs.vs_outcomes`, `vi.vs_call_ctx = vs.vs_call_ctx`] >>
     qpat_assum `account_code_lengths_ok vs.vs_accounts` mp_tac >>
     qpat_assum `vs.vs_call_ctx.cc_calldata = []` mp_tac >>
     qpat_assum `~vs.vs_halted` mp_tac >>
     qpat_assum `vs.vs_outcomes = MAP SND (call_trace ^frame)` mp_tac >>
     qpat_assum `LENGTH (call_trace ^frame) < 2 ** 64` mp_tac >>
     qpat_assum `outcomes_accounts_typed (SOME (MAP SND (call_trace ^frame)))` mp_tac >>
     qpat_assum `w2n fmp < 2 ** 254` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[]));

(* A checked root-to-body path transfers the raw-root resource bound to all
   fragment-reachable instructions, including those in invoked functions. *)
val linked_ctor_registered_headroom_goal =
  sg `!vi actual.
     fn_entry_label fn = SOME "__deploy" /\
     gas_path deploy_unit.cu_context fn
       (vi with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>) 0 (OK actual) /\
     (ctx_has_dalloca deploy_unit.cu_context ==>
       !callee inst s. raw_reachable vi deploy_unit.cu_context callee inst s ==>
         dalloca_fmp_headroom inst s) ==>
     !callee inst s. frag_reachable deploy_unit.cu_context fn actual callee inst s ==>
       dalloca_fmp_headroom inst s`;

val linked_ctor_registered_headroom_setup_tac =
  map_every qx_gen_tac [`vi`,`actual`] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!bb label. lookup_block label fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0` by
    (rpt gen_tac >> disch_tac >>
     drule_all_then ACCEPT_TAC acceptedContextPhiTheory.lowering_context_ok_block_phi) >>
  qabbrev_tac `root = vi with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>` >>
  `?bb. lookup_block "__deploy" fn.fn_blocks = SOME bb` by
    (qpat_assum `fn_entry_label fn = SOME "__deploy"` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `fn.fn_blocks` >>
     simp[venomInstTheory.fn_entry_label_def,venomInstTheory.entry_block_def,
          venomInstTheory.lookup_block_def,listTheory.FIND_thm]) >>
  pop_assum strip_assume_tac >>
  `enters_block fn root root` by
    (qpat_assum `!bb label. lookup_block label fn.fn_blocks = SOME bb ==> _`
       (drule_then assume_tac) >>
     simp[enters_block_def,Abbr `root`,eval_phis_no_phi,venom_state_fupdfupds]);

val linked_ctor_registered_headroom_transfer_tac =
  `!i. active_inst fn i root ==> raw_reachable vi deploy_unit.cu_context fn i root` by
    (qpat_assum `deploy_unit.cu_context.ctx_entry = SOME "__deploy"` mp_tac >>
     qpat_assum `lookup_function "__deploy" deploy_unit.cu_context.ctx_functions = SOME fn` mp_tac >>
     qpat_assum `fn_entry_label fn = SOME "__deploy"` mp_tac >>
     qpat_assum `enters_block fn root root` mp_tac >>
     qpat_assum `Abbrev (root = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> rpt gen_tac >> disch_tac >>
     metis_tac[CONJUNCT1 contextRawReachableTheory.raw_reachable_rules]) >>
  `!i. active_inst fn i actual ==> raw_reachable vi deploy_unit.cu_context fn i actual` by
    (qpat_assum `gas_path deploy_unit.cu_context fn root 0 (OK actual)` mp_tac >>
     qpat_assum `!bb label. lookup_block label fn.fn_blocks = SOME bb ==> _` mp_tac >>
     qpat_assum `!i. active_inst fn i root ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> gen_tac >> disch_tac >>
     metis_tac[deployBodyReachabilityTheory.raw_reachable_gas_path]) >>
  map_every qx_gen_tac [`callee`,`inst`,`s`] >> disch_tac >>
  Cases_on `ctx_has_dalloca deploy_unit.cu_context`
  >- (qpat_assum `ctx_has_dalloca deploy_unit.cu_context ==> _` mp_tac >>
      qpat_assum `ctx_has_dalloca deploy_unit.cu_context` mp_tac >>
      qpat_assum `!i. active_inst fn i actual ==> _` mp_tac >>
      qpat_assum `frag_reachable deploy_unit.cu_context fn actual callee inst s` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
      metis_tac[deployBodyReachabilityTheory.raw_reachable_through_fragment]) >>
  `MEM fn deploy_unit.cu_context.ctx_functions` by
    drule_then ACCEPT_TAC venomInstTheory.lookup_function_MEM >>
  `MEM callee deploy_unit.cu_context.ctx_functions /\ MEM inst (fn_insts callee)` by
    (qpat_assum `MEM fn deploy_unit.cu_context.ctx_functions` mp_tac >>
     qpat_assum `frag_reachable deploy_unit.cu_context fn actual callee inst s` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[contextRawReachableTheory.frag_reachable_members]) >>
  simp[unitTransformDefsTheory.dalloca_fmp_headroom_def] >> disch_tac >>
  `ctx_has_dalloca deploy_unit.cu_context` by
    (simp[NoAsms,ctx_has_dalloca_def,listTheory.EXISTS_MEM] >>
     qexists_tac `callee` >> simp[] >> qexists_tac `inst` >> simp[]) >>
  fs[];

(* The trace bound is a supplied premise for gas sufficiency, not a fact
   about every funded frame. The path and reachable states share one root. *)
fun linked_ctor_frame_headroom_tac frame =
  `!vi actual.
     LENGTH (call_trace ^frame) < 2 ** 64 /\ raw_variant fmp vi vs /\
     fn_entry_label fn = SOME "__deploy" /\
     gas_path deploy_unit.cu_context fn
       (vi with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>) 0 (OK actual) ==>
     !callee inst s. frag_reachable deploy_unit.cu_context fn actual callee inst s ==>
       dalloca_fmp_headroom inst s` by
    (map_every qx_gen_tac [`vi`,`actual`] >> disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `!vi actual. fn_entry_label fn = SOME "__deploy" /\ _ ==> _`
       (qspecl_then [`vi`,`actual`] mp_tac) >>
     (impl_tac >-
       (conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
        conj_tac >- FIRST_ASSUM ACCEPT_TAC >> disch_tac >>
        qpat_assum `!vi. raw_variant fmp vi vs /\ LENGTH (call_trace ^frame) < 2 ** 64 ==> _`
          (qspec_then `vi` mp_tac) >>
        (impl_tac >- (conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >> disch_then ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  pop_assum (mk_asm "linked_registered_headroom");

(* The raw and substituted source bodies agree for every observation of
   this frame; use the same root package for replacement and cell agreement. *)
val linked_registered_body_source_replay_goal =
  Q.SUBGOAL_THEN `!gs. eval_stmts cx cpkg6 (body_src with gas_obs := gs) =
        eval_stmts cx raw_body (body_src with gas_obs := gs)` assume_tac;

val linked_registered_body_source_replay_tac =
  qx_gen_tac `gs` >>
     `body_const_cells_agree_mods mods cx env (body_src with gas_obs := gs)` by
       (qpat_assum `!gs. env_consistent env cx (body_src with gas_obs := gs) /\ _`
          (qspec_then `gs` (assume_tac o CONJUNCT2)) >>
        qpat_assum `!env src_es. _ ==> body_const_cells_agree_mods mods cx env src_es` irule >>
        rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE
          (qpat_assum `get_tenv cx = type_env_all_modules mods` (fn th =>
             simp[NoAsms, Abbr `body_src`,th]) >> TRY (FIRST_ASSUM ACCEPT_TAC)))) >>
     qpat_x_assum `body_const_cells_agree_mods mods cx env _`
       (qx_choosel_then [`roots`,`art`,`entry_imms`] (map_every assume_tac o CONJUNCTS) o
        PURE_REWRITE_RULE [bodyFullPredsModsTheory.body_const_cells_agree_mods_def]) >>
     qpat_assum `cpkg6 = subst_consts_stmts_mods _ raw_body` SUBST1_TAC >>
     irule linkedConstReplayTheory.const_subst_eval_stmts_mods;

val linked_registered_body_source_witness_tac =
  reverse conj_tac >-
   (qexistsl_tac [`art`,`env`,`mods`,`NoneT`,`roots`] >>
    rpt conj_tac >> FIRST [FIRST_ASSUM ACCEPT_TAC,
      qpat_assum `contract_namespaces_ok T mods`
        (ACCEPT_TAC o cj 2 o PURE_REWRITE_RULE [contract_namespaces_ok_def]),
      qpat_assum `type_stmts env NoneT raw_body = SOME raw_env'` (fn th => simp[NoAsms,th])]) >>
  qpat_assum `check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art`
    (mp_then (Pat `check_contract _ _ _ _ = _`) mp_tac
      constSubstModsCorrectTheory.const_subst_blueprint_literal_offset_mods) >>
  disch_then irule >> FIRST_ASSUM ACCEPT_TAC;

(* Execute the paired body at the one endpoint selected by the checked
   registration path.  The source base observation is empty; the outcome
   computes the readings consumed by the body from the registered machine. *)
fun linked_registered_body_goal_tac frame =
  Q.SUBGOAL_THEN `!vi. raw_variant fmp vi vs /\ LENGTH (call_trace ^frame) < 2 ** 64 ==>
    ?actual Gbody tnbody.
      actual.vs_gas_readings = vi.vs_gas_readings /\
      (!H. gas_origin_ptr_path (linked_ret_DF H,imm_len_mods mods,
          gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context,
          deploy_unit.cu_context,fn,[])
          (vi with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>,
           FEMPTY,entry_taint) [] (OK actual,Gbody,tnbody)) /\
      gas_outcome_full_mods (linked_ret_DF,imm_len_mods mods,
          gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context,
          deploy_unit.cu_context,fn,[]) mods cx (initial_state am [])
          (eval_stmts cx cpkg6) (body_src,actual,Gbody,tnbody)
          (native_Q actual Gbody tnbody) native_R`
    (mk_asm "linked_ctor_registered_body");

val linked_registered_body_open_tac =
  qx_gen_tac `vi` >> disch_then (map_every assume_tac o CONJUNCTS) >>
  asm "linked_ctor_checked_entry" (drule_then
    (qx_choosel_then [`actual`,`Gbody`,`tnbody`] (map_every assume_tac o CONJUNCTS))) >>
  qexistsl_tac [`actual`,`Gbody`,`tnbody`] >>
  conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
  conj_tac >-
    (qx_gen_tac `H` >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ _ [] (OK actual,Gbody,tnbody)`
       (qspecl_then [`linked_ret_DF H`,
          `gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context`] ACCEPT_TAC));

val linked_registered_body_local_ptr_goal =
  Q.SUBGOAL_THEN `local_ptrs_reserved ctor_ce st2` assume_tac;

val linked_registered_body_local_ptr_tac =
  qpat_assum `Abbrev (ctor_ce = _)`
    (PURE_REWRITE_TAC o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `local_ptrs_reserved ce1 st2` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  pure_rewrite_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def,
       compileEnvTheory.compile_env_accfupds] >> simp_tac bool_ss [];

val linked_registered_body_local_ptr_sa_tac =
  `local_ptrs_reserved ctor_ce sa` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `st2` >> rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE simp[]));

val linked_registered_body_state_tac =
  asm "linked_registered_state_frame" (qspecl_then [`vi`,`actual`,`[]`] mp_tac) >> impl_tac;

val linked_registered_body_state_premises_tac =
  rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `!inst b sz n. MEM inst (fn_insts fn) /\ _ ==> sz = w2n n`
       (drule_all_then ACCEPT_TAC)));

val linked_registered_body_source_empty_tac =
  qpat_assum `body_src with gas_obs := [] = body_src` (PURE_REWRITE_TAC o single);

val linked_registered_body_state_close_tac =
  linked_registered_body_source_empty_tac >>
  disch_then (mk_asm "linked_body_state_frame") >>
  qpat_assum `!gs. gas_admissible (eval_stmts cx cpkg6) _ _` (qspec_then `[]` mp_tac) >>
  linked_registered_body_source_empty_tac >> disch_tac;

val linked_registered_body_control_tac =
  qpat_assum `!actual src. alloca_history fn actual /\ _ ==> ret_pc_ok ctor_ce sa actual /\ _`
    (qspecl_then [`actual`,`body_src`] mp_tac) >>
  (impl_tac >-
    (rpt conj_tac >> FIRST [FIRST_ASSUM ACCEPT_TAC,
       qpat_assum `ctx_has_dalloca deploy_unit.cu_context ==> allocas_below_fmp actual /\ _`
         (ACCEPT_TAC o DISCH_ALL o CONJUNCT1 o UNDISCH),
       drule_then (fn th => simp[th]) emitHelperPropsTheory.fresh_label_props])) >>
  disch_then (map_every assume_tac o CONJUNCTS);

val linked_registered_body_headroom_tac =
  `gas_path deploy_unit.cu_context fn
     (vi with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>)
     0 (OK actual)` by
     (qpat_assum `gas_path_mem deploy_unit.cu_context fn _ 0 (OK actual)`
        (ACCEPT_TAC o CONJUNCT1 o MATCH_MP fragGasPathMemTheory.gas_path_mem_exec)) >>
  asm "linked_registered_headroom" (qspecl_then [`vi`,`actual`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >> disch_tac;

val linked_registered_body_ghost_goal =
  Q.SUBGOAL_THEN `!H. ghost_inv_at_mods (linked_ret_DF H) (imm_len_mods mods) NONE
    ctor_ce cx body_src Gbody tnbody actual` (mk_asm "linked_body_ghost");

val linked_registered_body_ghost_open_tac =
  qabbrev_tac `src = body_src` >>
  `src.scopes = [scope]` by
    (simp[NoAsms, Abbr `src`, Abbr `body_src`] >> FIRST_ASSUM ACCEPT_TAC) >>
  qx_gen_tac `H` >> pure_rewrite_tac[bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def] >>
  reverse conj_tac;

val linked_registered_body_ghost_frame_tac =
  qpat_assum `ctor_ce.ce_is_ctor /\ ctor_ce.ce_return_pc = NONE /\ _`
    (assume_tac o cj 2) >>
  rpt conj_tac >> FIRST
    [FIRST_ASSUM ACCEPT_TAC,
     linked_ctor_registered_ghost_imm_tac,
     (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_assum `!i. i < imm_len_mods mods ==> i NOTIN tnbody.t_mem`
        (drule_then (fn th => qpat_assum `i IN tnbody.t_mem`
          (fn mem => mp_tac th >> simp[NoAsms,mem])))),
     (map_every (fn q => qpat_assum q mp_tac)
        [`ctor_ce.ce_return_pc = NONE`,`tnbody.t_stor = {}`,
         `tnbody.t_trans = {}`,`tnbody.t_imm = {}`] >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp[bodyPtrDefsTheory.return_buf_ptr_def, bodyPtrDefsTheory.stor_taint_ok_at_def])];

val linked_registered_body_formals_tac =
  qpat_assum `!j. j < LENGTH src_args ==> ?entry d B. _` (mk_asm "checked_formal_supports") >>
  linked_ctor_registered_ghost_lookup_tac >> linked_ctor_registered_ghost_support_tac >>
  qpat_assum `Abbrev (ctor_ce = _)` (fn h =>
    qpat_assum `FLOOKUP ctor_ce.ce_vars (FST (EL j src_args)) = SOME (PtrVar (Var p) sz)`
      (assume_tac o SIMP_RULE (srw_ss()) [REWRITE_RULE [markerTheory.Abbrev_def] h])) >>
  qpat_assum `src.scopes = [scope]` SUBST_ALL_TAC >>
  qpat_assum `local_region ce1 [scope] actual _ _ _`
    (mp_tac o PURE_REWRITE_RULE [local_region_def]) >>
  qpat_assum `FLOOKUP ce1.ce_vars (FST (EL j src_args)) = SOME (PtrVar (Var p) sz)` mp_tac >>
  rename1 `ptr_covers Gbody tnbody covered actual _` >>
  qpat_assum `FLOOKUP ce1.ce_vars (FST (EL j src_args)) = SOME (PtrVar (Var covered) _)` mp_tac >>
  qpat_assum `lookup_scopes (FST (EL j src_args)) [scope] = SOME entry` mp_tac >>
  qpat_assum `lookup_scopes (FST (EL j src_args)) [scope] = SOME _` mp_tac >>
  qpat_assum `ptr_covers Gbody tnbody _ actual _` mp_tac >>
  qpat_assum `DISJOINT _ tnbody.t_mem` mp_tac >>
  qpat_assum `!mem. _ ==> val_in_memory _ _ _ mem` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> gvs[];

val linked_registered_body_static_tac =
  linked_registered_body_local_ptr_sa_tac >>
  `MEM fn deploy_unit.cu_context.ctx_functions` by
    drule_then ACCEPT_TAC venomInstTheory.lookup_function_MEM >>
  `ctx_inst_ids_distinct deploy_unit.cu_context` by
    drule_then (ACCEPT_TAC o CONJUNCT1) vyperCompilerTheory.lowering_context_ok_static_integrity >>
  `~block_is_terminated st1` by
    drule_all_then ACCEPT_TAC ctorDeployLoweringEntryPrefixTheory.deploy_ctor_pre_register_unterminated >>
  `~block_is_terminated st2` by
    drule_all_then ACCEPT_TAC ctorDeployLoweringEntryStaticTheory.deploy_ctor_register_args_open >>
  `~block_is_terminated sa` by
    (qpat_assum `fresh_label "ctor_exit" st2 = (exit_lbl,sa)`
       (fn h => PURE_REWRITE_TAC [block_is_terminated_def,
           cj 3 (MATCH_MP emitHelperPropsTheory.fresh_label_props h)]) >>
     qpat_assum `~block_is_terminated st2`
       (ACCEPT_TAC o PURE_REWRITE_RULE [block_is_terminated_def]));

val linked_registered_body_apply_tac =
  asm "linked_ctor_body_frag" (qspec_then `[]` mp_tac) >>
  pure_rewrite_tac[bodyFullPostsModsTheory.stmt_frag_full_mods_def] >>
  disch_then (qspecl_then [`initial_state am []`,`sa`,`sb`,`sa`,`shadow_sb`,
                          `actual`,`Gbody`,`tnbody`,`ce_end`] mp_tac) >>
  linked_registered_body_source_empty_tac >> impl_tac;

val linked_registered_body_apply_premises_tac =
  rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE
    (qx_gen_tac `H` >> disch_tac >>
     asm "linked_body_state_frame" (qspec_then `H` (drule_then strip_assume_tac)) >>
     asm "linked_body_ghost" (qspec_then `H` assume_tac) >>
     rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC));

val linked_registered_body_apply_close_tac =
  qpat_assum `contract_inv mods exps deploy_unit.cu_context ctor_ce cx`
    (PURE_REWRITE_TAC o single o MATCH_MP bodyInvCodePropsTheory.contract_inv_cenv_modules) >>
  simp[NoAsms, Abbr `native_Q`, Abbr `native_R`, Abbr `native_ret`, Abbr `installed`];

(* Prepend the very path that selected the body witness and run the
   native consumer without weakening its focus and terminal alternatives. *)
fun linked_registered_terminal_projection_goal_tac retain_eval frame =
  let val root = ``vi with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>``
      val label = if retain_eval then "linked_ctor_registered_terminal_eval"
                  else "linked_ctor_registered_terminal"
  in Q.SUBGOAL_THEN (`!vi. raw_variant fmp vi vs /\ LENGTH (call_trace ^frame) < 2 ** 64 ==>
    ?marks.
      ((?H leaf pg G tn finish.
           gas_origin_ptr_focus (linked_ret_DF H,imm_len_mods mods,
             gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context,
             deploy_unit.cu_context,fn,[]) (^root,FEMPTY,entry_taint) marks
             (leaf,pg,G,tn,finish)) /\
       ((!tail. ~deploy_storage_ok_mods mods exps am tx (MAP SND (call_trace ^frame))
             (gas_explicit marks vi.vs_gas_readings ++ tail)) \/
        (!tail. deploy_source_exempt_mods mods
            (load_contract (SOME (MAP SND (call_trace ^frame)))
              (gas_explicit marks vi.vs_gas_readings ++ tail) am tx mods exps)))) \/
      (?res ee terminal G' tn'.
        ` @ linked_ctor_replay_eval_projection retain_eval ``vi.vs_gas_readings`` @ `
        (!tail. load_contract_trace (SOME (MAP SND (call_trace ^frame)))
          (gas_explicit marks vi.vs_gas_readings ++ tail) am tx mods exps =
          (source_finish res (ee with gas_obs := tail),ee.storage_trace)) /\
        storage_trace_domain cx (initial_state am []) ee.storage_trace /\
        exit_result terminal /\
        create_size_exit_ok deploy_unit.cu_context res terminal /\
        !H. valid_horizon cx (initial_state am []) H ee.storage_trace ==>
          gas_origin_ptr_path (linked_ret_DF H,imm_len_mods mods,
            gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context,
            deploy_unit.cu_context,fn,[]) (^root,FEMPTY,entry_taint) marks (terminal,G',tn') /\
          ((res = INL () \/ res = INR (ReturnException NoneV)) /\
             installed H (ee with <|gas_obs := []; scopes := []|>) terminal \/
           (res = INR HaltException /\ ?final. terminal = Halt final /\
              final.vs_returndata = [] /\ halt_rel H cx (ee with gas_obs := []) final) \/
           (?err final abort. res = INR err /\ terminal = Abort abort final /\ expr_exit res terminal)))`)
    (mk_asm label)
  end;

val linked_registered_terminal_goal_tac = linked_registered_terminal_projection_goal_tac false;

val linked_registered_terminal_tac =
  qx_gen_tac `vi` >> disch_tac >>
  asm "linked_ctor_registered_body" (qspec_then `vi` mp_tac) >>
  (impl_tac >- FIRST_ASSUM ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`actual`,`Gbody`,`tnbody`]
    (map_every assume_tac o CONJUNCTS)) >>
  asm "linked_ctor_native_replay" (qspecl_then
    [`vi with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>`,
     `actual`,`Gbody`,`tnbody`] mp_tac) >>
  pure_rewrite_tac[venom_state_accfupds] >> impl_tac;

val linked_registered_terminal_premises_tac =
  rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC;

(* Interpret the selected source observation at its raw terminal. *)
val linked_raw_post_goal_tac =
  Q.SUBGOAL_THEN `!v m tail res ee terminal Gend tnend.
    raw_variant fmp v vs /\
    (!tail. load_contract_trace (SOME os) (gas_explicit m v.vs_gas_readings ++ tail)
      am tx mods exps = (source_finish res (ee with gas_obs := tail),ee.storage_trace)) /\
    storage_trace_domain cx (initial_state am []) ee.storage_trace /\
    (!H. valid_horizon cx (initial_state am []) H ee.storage_trace ==>
       gas_origin_ptr_path (linked_ret_DF H,imm_len_mods mods,
         gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context,
         deploy_unit.cu_context,fn,[])
         (v with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>,
          FEMPTY,entry_taint) m (terminal,Gend,tnend) /\
       ((res = INL () \/ res = INR (ReturnException NoneV)) /\
          installed H (ee with <|gas_obs := []; scopes := []|>) terminal \/
        (res = INR HaltException /\ ?final. terminal = Halt final /\
           final.vs_returndata = [] /\ halt_rel H cx (ee with gas_obs := []) final) \/
        (?err final abort. res = INR err /\ terminal = Abort abort final /\ expr_exit res terminal))) /\
    eval_stmts cx raw_body (body_src with gas_obs := gas_explicit m v.vs_gas_readings ++ tail) =
      (res,ee with gas_obs := tail) /\
    deploy_storage_ok_mods mods exps am tx os (gas_explicit m v.vs_gas_readings ++ tail) /\
    ~deploy_source_exempt_mods mods
      (load_contract (SOME os) (gas_explicit m v.vs_gas_readings ++ tail) am tx mods exps) ==>
    storage_trace_horizon (deploy_storage_trace_mods (SOME os)
      (gas_explicit m v.vs_gas_readings ++ tail) am tx mods exps) =
      storage_trace_horizon ee.storage_trace /\
    valid_horizon cx (initial_state am []) (storage_trace_horizon ee.storage_trace) ee.storage_trace /\
    deploy_post (gas_explicit m v.vs_gas_readings ++ tail) terminal`
    (mk_asm "linked_raw_post");

val linked_raw_post_observation_tac =
  map_every qx_gen_tac [`v`,`m`,`tail`,`res`,`ee`,`terminal`,`Gend`,`tnend`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `obs = gas_explicit m v.vs_gas_readings ++ tail` >>
  qpat_assum `!tail. load_contract_trace _ _ am tx mods exps = _`
    (qspec_then `tail` (fn trace =>
       qpat_assum `Abbrev (obs = _)` (fn ob =>
         assume_tac (PURE_REWRITE_RULE
           [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] ob)] trace)))) >>
  `deploy_storage_trace_mods (SOME os) obs am tx mods exps = ee.storage_trace` by
    (qpat_assum `load_contract_trace (SOME os) obs am tx mods exps = _`
       (fn trace => simp[NoAsms, deploy_storage_trace_mods_def, trace])) >>
  `valid_horizon cx (initial_state am []) (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`deploy_storage_ok_mods mods exps am tx os _`,
        `storage_trace_domain cx (initial_state am []) ee.storage_trace`] >>
     qpat_assum `Abbrev (obs = _)` (fn ob =>
       PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] ob)]) >>
     qpat_assum `deploy_storage_trace_mods (SOME os) obs am tx mods exps = ee.storage_trace`
       (fn trace => simp[NoAsms, trace, Abbr `cx`, deploy_storage_ok_mods_def,
                        storage_trace_domain_def, valid_horizon_def,
                        storage_trace_horizon_def, storage_observations_ok_def, EVERY_MEM])) >>
  conj_tac >- simp[] >> conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
  qpat_assum `!H. valid_horizon cx (initial_state am []) H ee.storage_trace ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- FIRST_ASSUM ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "linked_raw_post_path") mp_tac) >>
  qpat_assum `load_contract_trace (SOME os) obs am tx mods exps = _` (fn trace =>
    qpat_assum `deploy_storage_trace_mods (SOME os) obs am tx mods exps = ee.storage_trace`
      (fn strace => simp[NoAsms, Abbr `deploy_post`, load_contract_def, trace, strace]));

val linked_raw_post_abort_tac =
  disch_then (qx_choosel_then [`err`,`abort_final`,`why`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `terminal = Abort why abort_final` SUBST_ALL_TAC >>
  qpat_x_assum `res = INR err` SUBST_ALL_TAC >>
  qpat_assum `expr_exit _ _` mp_tac >>
  namedCases_on `err` ["e","msg","","","val",""] >>
  simp[NoAsms, Abbr `source_finish`, exprSimDefsTheory.expr_exit_def]
  >- (Cases_on `e` >> simp[NoAsms, exprSimDefsTheory.expr_exit_def]) >>
  Cases_on `why` >> simp[NoAsms];

val linked_raw_post_halt_tac =
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `halt_final` (CONJUNCTS_THEN2 SUBST_ALL_TAC
      (map_every assume_tac o CONJUNCTS)))) >>
  `MEM tx.target ee.pending_deletions` by
    (qpat_assum `eval_stmts cx raw_body _ = (res,ee with gas_obs := tail)`
       (fn ev => qpat_assum `res = INR HaltException` (fn h =>
          mp_tac (MATCH_MP evalNoHaltTheory.eval_stmts_halt_pending_deletions
            (PURE_REWRITE_RULE [h] ev)))) >>
     simp[NoAsms, Abbr `cx`, deploy_evaluation_context_mods_def, initial_evaluation_context_def]) >>
  `ALOOKUP am_c.sources tx.target = NONE` by
    (qpat_assum `evaluate_all_constants _ _ _ _ = SOME am_c`
       (mp_tac o CONJUNCT1 o MATCH_MP
         vyperTypeDeploymentMachineTheory.evaluate_all_constants_preserves_machine_static_components) >>
     qpat_assum `am0 = _` (fn a0 => simp[NoAsms, a0]) >>
     disch_then SUBST1_TAC >> FIRST_ASSUM ACCEPT_TAC) >>
  qpat_assum `halt_rel _ cx _ halt_final`
    (mp_tac o PURE_REWRITE_RULE [halt_rel_def, accounts_rel_def]) >>
  qpat_assum `cx.txn.target = tx.target` (fn target => simp[NoAsms, target]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `res = INR HaltException` (fn h =>
    qpat_assum `ALOOKUP am_c.sources tx.target = NONE` (fn fresh =>
      simp[NoAsms, h, Abbr `source_finish`, finalize_pending_deletions_def,
           abstract_machine_from_state_def, fresh])) >>
  conj_tac >-
    (qpat_assum `ee.pending_deletions = halt_final.vs_pending_deletions` (SUBST1_TAC o SYM) >>
     qpat_assum `cx.txn.target = tx.target` (fn target =>
       irule (REWRITE_RULE [target] (Q.SPEC `cx` accounts_agree_process_deletions))) >>
     FIRST_ASSUM ACCEPT_TAC) >>
  rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE
    (qpat_assum `ee.pending_deletions = halt_final.vs_pending_deletions` (SUBST1_TAC o SYM) >>
     FIRST_ASSUM ACCEPT_TAC));

val linked_raw_post_install_open_tac =
  disch_then (CONJUNCTS_THEN2 (mk_asm "linked_raw_post_returns") mp_tac) >>
  simp[NoAsms, Abbr `installed`] >>
  disch_then (qx_choosel_then [`before`,`final`,`codepos`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `terminal = Halt final` SUBST1_TAC >>
  qabbrev_tac `rh = storage_trace_horizon ee.storage_trace`;

val linked_raw_post_install_source_tac =
  (* The source install branches have the same machine and request list. *)
  qabbrev_tac `raw_installed = finalize_pending_deletions
    ((abstract_machine_from_state am_c.sources am_c.exports am_c.layouts ee)
      with sources updated_by CONS (tx.target,mods))` >>
  `safe_cast NoneTV NoneV = SOME NoneV` by EVAL_TAC >>
  `source_finish res (ee with gas_obs := tail) = INL (raw_installed,ee.requests)` by
    (qpat_assum `safe_cast NoneTV NoneV = SOME NoneV` (fn cast =>
       asm "linked_raw_post_returns" (DISJ_CASES_THEN (fn res =>
         simp[NoAsms, res, cast, Abbr `source_finish`, Abbr `raw_installed`,
              vyperInterpreterTheory.abstract_machine_from_state_gas_obs])))) >>
  qpat_assum `source_finish res (ee with gas_obs := tail) = _` (fn fin =>
    qpat_assum `Abbrev (raw_installed = _)` (fn inst =>
      simp[NoAsms, fin, REWRITE_RULE [markerTheory.Abbrev_def] inst,
           finalize_pending_deletions_def, abstract_machine_from_state_def]));

val linked_raw_post_install_effects_tac =
  qpat_assum `cx.txn.target = tx.target` (fn tgt =>
    qpat_assum `state_rel _ fn ctor_ce cx _ before`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [tgt] o MATCH_MP
        accountsRelPropsTheory.state_rel_accounts)) >>
  qpat_assum `cx.txn.target = tx.target` (fn tgt =>
    qpat_assum `state_rel _ fn ctor_ce cx _ before`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [tgt, sourceLogFramesTheory.logs_rel_eq] o
        (fn th => LIST_CONJ [cj 8 th,cj 11 th]) o PURE_REWRITE_RULE [state_rel_def])) >>
  qpat_assum `final.vs_pending_deletions = before.vs_pending_deletions` (fn del =>
    qpat_assum `ee.pending_deletions = before.vs_pending_deletions` (fn edel =>
      qpat_assum `final.vs_accounts = before.vs_accounts` (fn acc =>
        qpat_assum `final.vs_transient = before.vs_transient` (fn trans =>
          qpat_assum `final.vs_logs = before.vs_logs` (fn logs =>
            qpat_assum `final.vs_requests = before.vs_requests` (fn rqs =>
              PURE_REWRITE_TAC [del,GSYM edel,acc,trans,logs,rqs])))))) >>
  conj_tac;

val linked_raw_post_install_accounts_tac =
  `accounts_agree rh tx.target (process_deletions ee.pending_deletions ee.accounts)
      (process_deletions ee.pending_deletions before.vs_accounts)` by
    (qpat_assum `cx.txn.target = tx.target` (fn target =>
       irule (REWRITE_RULE [target] (Q.SPEC `cx` accounts_agree_process_deletions))) >>
     FIRST_ASSUM ACCEPT_TAC) >>
  Cases_on `MEM tx.target ee.pending_deletions`
  >- (qpat_assum `MEM tx.target ee.pending_deletions` (fn mem =>
        simp[NoAsms, MATCH_MP process_deletions_update_mem mem]) >> FIRST_ASSUM ACCEPT_TAC) >>
  `(lookup_account tx.target before.vs_accounts).code = (lookup_account tx.target ee.accounts).code` by
    (qpat_assum `accounts_agree rh tx.target ee.accounts before.vs_accounts` (fn agr =>
       qpat_assum `cx.txn.target = tx.target` (fn target =>
         mp_tac (MATCH_MP (REWRITE_RULE [target] (Q.SPEC `cx` accounts_agree_lookup)) agr))) >>
     disch_then (qspec_then `tx.target` (ACCEPT_TAC o cj 2))) >>
  `!A a. update_account a (lookup_account a A) A = A` by
    rw[FUN_EQ_THM, vfmStateTheory.update_account_def,
       vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM] >>
  qpat_assum `~MEM tx.target ee.pending_deletions` (fn mem =>
    qpat_assum `(lookup_account tx.target before.vs_accounts).code = _` (fn code =>
      qpat_assum `!A a. update_account a (lookup_account a A) A = A` (fn upd =>
        simp[NoAsms, MATCH_MP vfmProgTheory.lookup_account_process_deletions_other mem,
             GSYM code, upd]))) >>
  FIRST_ASSUM ACCEPT_TAC;

val linked_raw_post_install_runtime_tac =
  `v.vs_code = vs.vs_code /\ v.vs_labels = vs.vs_labels` by
    (qpat_assum `raw_variant fmp v vs`
       (mp_tac o Q.AP_TERM `\s. (s.vs_code,s.vs_labels)` o
        PURE_REWRITE_RULE [raw_variant_def, gas_variant_def]) >> simp[NoAsms]) >>
  pop_assum (map_every assume_tac o CONJUNCTS);

val linked_raw_post_install_path_fields_tac =
  `final.vs_code = v.vs_code /\ final.vs_labels = v.vs_labels` by
    (asm "linked_raw_post_path" (mp_tac o MATCH_MP fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec) >>
     qpat_assum `terminal = Halt final` (fn term => simp[NoAsms, term, exit_result_def]) >>
     disch_then (qx_choose_then `efuel` (fn th =>
       mp_tac (MATCH_MP ctorDeployLoweringHaltCodeTheory.run_from_halt_code (cj 1 th)))) >>
     simp[NoAsms]) >>
  pop_assum (map_every assume_tac o CONJUNCTS);

val linked_raw_post_install_label_tac =
  `before.vs_code = assemble prog' ++ vs.vs_data_section /\ codepos = n2w off` by
    (qpat_assum `final.vs_code = before.vs_code` (fn bcode =>
        qpat_assum `final.vs_code = v.vs_code` (fn fcode =>
          qpat_assum `v.vs_code = vs.vs_code` (fn vcode =>
            simp[NoAsms, GSYM bcode, fcode, vcode]))) >>
     conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
     qpat_assum `FLOOKUP before.vs_labels "runtime_begin" = SOME codepos` mp_tac >>
     qpat_assum `final.vs_labels = before.vs_labels`
       (fn eq => PURE_REWRITE_TAC [GSYM eq]) >>
     map_every (fn q => qpat_assum q (fn eq => PURE_REWRITE_TAC [eq]))
       [`final.vs_labels = v.vs_labels`, `v.vs_labels = vs.vs_labels`] >>
     qpat_assum `FLOOKUP (lo_reloc prog prog') "runtime_begin" = SOME off`
       (fn label_eq => simp[NoAsms, Abbr `vs`, opt_entry_state_own_def,
         finite_mapTheory.FLOOKUP_o_f, label_eq])) >>
  pop_assum (map_every assume_tac o CONJUNCTS);

val linked_raw_post_install_slice_tac =
  `DROP (w2n codepos) before.vs_code = runtime_bc ++ vs.vs_data_section` by
    (qpat_assum `before.vs_code = _` SUBST1_TAC >>
     `w2n codepos = off` by
       (qpat_assum `codepos = n2w off` SUBST1_TAC >>
        qpat_assum `off < dimword (:256)` (fn bound => simp[NoAsms, bound, wordsTheory.w2n_n2w])) >>
     qpat_assum `w2n codepos = off` SUBST1_TAC >>
     qpat_assum `off <= LENGTH (assemble prog')` (fn bound =>
       qpat_assum `DROP off (assemble prog') = runtime_bc` (fn slice =>
         simp[NoAsms, MATCH_MP listTheory.DROP_APPEND1 bound, slice]))) >>
  sg `TAKE (LENGTH runtime_bc)
      (DROP (w2n codepos) before.vs_code ++ REPLICATE (LENGTH runtime_bc) 0w) = runtime_bc`;

val linked_raw_post_install_slice_finish_tac =
  qpat_assum `DROP (w2n codepos) before.vs_code = _` SUBST1_TAC >>
  PURE_REWRITE_TAC [GSYM listTheory.APPEND_ASSOC, rich_listTheory.TAKE_LENGTH_APPEND];

val linked_raw_post_install_cells_tac =
  `ALOOKUP (body_src with gas_obs := obs).immutables cx.txn.target = SOME cells` by
    (qpat_assum `ALOOKUP es0.immutables cx.txn.target = SOME cells`
       (fn cell => simp[NoAsms, Abbr `body_src`, cell])) >>
  qpat_assum `Abbrev (obs = _)` (fn ob =>
    qpat_assum `eval_stmts cx raw_body _ = (res,ee with gas_obs := tail)`
      (fn ev => assume_tac (PURE_REWRITE_RULE [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] ob)] ev))) >>
  `IS_SOME (ALOOKUP ee.immutables cx.txn.target)` by
    (qpat_assum `eval_stmts cx raw_body (body_src with gas_obs := obs) = _`
       (qspec_then `cx.txn.target` mp_tac o MATCH_MP
        vyperEvalPreservesImmutablesDomTheory.eval_stmts_preserves_immutables_addr_dom) >>
     qpat_assum `ALOOKUP (body_src with gas_obs := obs).immutables cx.txn.target = SOME cells`
       (fn cell => simp[NoAsms, cell])) >>
  qpat_assum `IS_SOME (ALOOKUP ee.immutables cx.txn.target)`
    (qx_choose_then `end_cells` assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  qpat_assum `eval_stmts cx raw_body (body_src with gas_obs := obs) = _`
    (mk_asm "linked_raw_post_preserves_tv" o CONJUNCT2 o CONJUNCT2 o
       PURE_REWRITE_RULE [vyperEvalPreservesScopesTheory.preserves_tv_def] o
       MATCH_MP (cj 2 vyperEvalPreservesScopesTheory.eval_preserves_tv)) >>
  `!src id tv v. FLOOKUP (get_source_immutables src cells) id = SOME (tv,v) ==>
     ?v'. FLOOKUP (get_source_immutables src end_cells) id = SOME (tv,v')` by
    (asm "linked_raw_post_preserves_tv" mp_tac >>
     qpat_assum `ALOOKUP (body_src with gas_obs := obs).immutables cx.txn.target = SOME cells` (fn s0 =>
       qpat_assum `ALOOKUP ee.immutables cx.txn.target = SOME end_cells` (fn s1 =>
         simp[NoAsms, s0,s1])));

val linked_raw_post_install_section_tac =
  qabbrev_tac `section = mem_bytes_at 0 (imm_len_mods mods) before.vs_memory` >>
  qexists_tac `section` >> conj_tac
  >- (qpat_assum `final.vs_returndata = _` SUBST1_TAC >>
      qpat_assum `TAKE (LENGTH runtime_bc) _ = runtime_bc` (fn rt =>
        simp[NoAsms, rt, Abbr `section`, valueEncodingDefsTheory.mem_bytes_at_def])) >>
  qpat_assum `cx.txn.target = tx.target` (fn tgt =>
    qpat_assum `ALOOKUP ee.immutables cx.txn.target = SOME end_cells` (fn cell =>
      simp[NoAsms, account_immutables_def, REWRITE_RULE [tgt] cell,
           immutables_section_rel_mods_def])) >>
  conj_tac >- simp[NoAsms, Abbr `section`] >>
  map_every qx_gen_tac [`sid`,`nm`,`ioff`,`isz`] >> disch_tac >>
  qpat_assum `immutable_section_layout_mods mods ctor_ce`
    (fn th => map_every assume_tac (List.take
      (CONJUNCTS (PURE_REWRITE_RULE [immutable_section_layout_mods_def] th),2))) >>
  qpat_assum `!src name off size. immutable_region_mods mods src name off size ==> off + size <= _`
    (drule_then assume_tac) >>
  `FLOOKUP ctor_ce.ce_module_vars (sid,nm) = SOME (ImmutableLoc ioff)` by
    (qpat_assum `!src name off. FLOOKUP ctor_ce.ce_module_vars (src,name) = _ <=> _`
       (qspecl_then [`sid`,`nm`,`ioff`] (fn th => PURE_REWRITE_TAC [th])) >>
     qexists_tac `isz` >> FIRST_ASSUM ACCEPT_TAC) >>
  qpat_assum `immutables_section_rel_mods mods cells _`
    (drule_then (qx_choosel_then [`cell_tv`,`entry_val`] (map_every assume_tac o CONJUNCTS)) o
     cj 2 o PURE_REWRITE_RULE [immutables_section_rel_mods_def]) >>
  qpat_assum `!src id tv v. FLOOKUP (get_source_immutables src cells) id = SOME (tv,v) ==> _`
    (drule_then (qx_choose_then `end_val` assume_tac)) >>
  qexistsl_tac [`cell_tv`,`end_val`];

val linked_raw_post_install_module_tac =
  qpat_assum `immutable_region_mods mods sid nm ioff isz`
    (strip_assume_tac o PURE_REWRITE_RULE [immutable_region_mods_def]) >>
  qpat_assum `contract_inv mods exps deploy_unit.cu_context ctor_ce cx`
    (fn ctr => qpat_assum `ALOOKUP mods sid = SOME _`
       (mk_asm "linked_raw_post_module" o SUBS
          [SYM (MATCH_MP bodyInvCodePropsTheory.contract_inv_cenv_modules ctr)]));

val linked_raw_post_install_imm_tac =
  qpat_assum `immutables_rel_mods ctor_ce cx.txn.target T _ before`
    (fn im => asm "linked_raw_post_module" (fn m =>
       mp_tac (MATCH_MP (PURE_REWRITE_RULE [immutables_rel_mods_def] im) m))) >>
  qpat_assum `ALOOKUP ee.immutables cx.txn.target = SOME end_cells` (fn cell =>
    simp[NoAsms, immutables_rel_def, cell]) >>
  disch_then (qspecl_then [`nm`,`cell_tv`,`end_val`,`ioff`] mp_tac);

val linked_raw_post_install_imm_finish_tac =
  (impl_tac >- (conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS);

val linked_raw_post_install_bytes_window_tac =
  `mem_bytes_at ioff (type_memory_size cell_tv) section =
    mem_bytes_at ioff (type_memory_size cell_tv) before.vs_memory` by
    (qpat_assum `type_memory_size cell_tv = isz` SUBST1_TAC >>
     `ioff + isz <= LENGTH section` by
       (qpat_assum `ioff + isz <= imm_len_mods mods` (fn bd =>
          simp[NoAsms, Abbr `section`, bd])) >>
     qpat_assum `ioff + isz <= LENGTH section`
       (fn bd => PURE_REWRITE_TAC [MATCH_MP valueEncodingDefsTheory.mem_bytes_at_bounded bd]) >>
     qpat_assum `Abbrev (section = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `ioff + isz <= imm_len_mods mods` (fn bd =>
       simp[NoAsms, MATCH_MP abiCanonicalHeadSizeTheory.mem_bytes_at_window bd]));

val linked_raw_post_install_bytes_tac =
  rpt (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >>
  conj_tac
  >- (qpat_assum `val_in_memory cell_tv end_val ioff before.vs_memory`
        (fn vm => mp_tac (MATCH_MP (SIMP_RULE bool_ss [GSYM AND_IMP_INTRO]
          (cj 1 valueEncodingProofsTheory.val_in_memory_mem_agree_proof)) vm)) >>
      disch_then irule >>
      rpt conj_tac >> FIRST [FIRST_ASSUM ACCEPT_TAC,
        drule_then ACCEPT_TAC (cj 1 loweringSliceTheory.immutable_admissible_val_wf),
        qpat_assum `mem_bytes_at ioff _ section = _` (ACCEPT_TAC o SYM)]) >>
  qpat_assum `mem_bytes_at ioff _ section = _` SUBST1_TAC >> FIRST_ASSUM ACCEPT_TAC;

(* A completed path supplies full-run checks, unlike a focused prefix. *)
val linked_correct_exit_goal =
  Q.SUBGOAL_THEN `!v m H terminal G' tn'.
    raw_variant fmp v vs /\ code_layout_valid vs /\ exit_result terminal /\
    gas_origin_ptr_path (linked_ret_DF H,imm_len_mods mods,
      gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context,
      deploy_unit.cu_context,fn,[])
      (v with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>,
       FEMPTY,entry_taint) m (terminal,G',tn') ==>
    (?fr. run_context fr deploy_unit.cu_context v = terminal /\
          terminates (run_context fr deploy_unit.cu_context v)) /\
    o1_pre_walk_inv (linked_ret_DF H) deploy_unit.cu_context v /\
    mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                       s.vs_code = vs.vs_code /\ s.vs_data_section = vs.vs_data_section)
      deploy_unit.cu_context v /\
    o1_safe_upto (linked_ret_DF H) (imm_len_mods mods)
      (MIN (LENGTH m) (LENGTH v.vs_gas_readings)) deploy_unit.cu_context v /\
    (?fuel. MAP (\key. key IN gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context)
      (gas_events_blocks fuel deploy_unit.cu_context fn
        (v with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>)) = m)`
    (mk_asm "linked_correct_exit_inputs");

val linked_correct_exit_root_tac =
  map_every qx_gen_tac [`v`,`m`,`H`,`terminal`,`G'`,`tn'`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `exit_root = v with <|vs_prev_bb := NONE; vs_current_bb := "__deploy";
                                   vs_inst_idx := 0|>` >>
  `exit_root.vs_current_bb = "__deploy" /\ exit_root.vs_inst_idx = 0 /\
    exit_root with vs_inst_idx := 0 = exit_root` by
    simp[NoAsms, Abbr `exit_root`, venom_state_fupdfupds] >>
  (Q.SUBGOAL_THEN `?bb. lookup_block "__deploy" fn.fn_blocks = SOME bb`
    (qx_choose_then `exit_bb` assume_tac) >-
    (qpat_assum `fn_entry_label fn = SOME "__deploy"` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `fn.fn_blocks` >>
     simp[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def,
          venomInstTheory.lookup_block_def, listTheory.FIND_thm])) >>
  `phi_prefix_length exit_bb.bb_instructions = 0` by
    drule_all_then ACCEPT_TAC acceptedContextPhiTheory.lowering_context_ok_block_phi;

val linked_correct_exit_run_tac =
  `!s. terminal <> OK s` by
    (qpat_assum `exit_result terminal` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `terminal` >> simp[exit_result_def]) >>
  qpat_assum `gas_origin_ptr_path _ (exit_root,_,_) m (terminal,_,_)`
    (mp_tac o MATCH_MP fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec) >>
  qpat_assum `!s. terminal <> OK s` (fn neq =>
    qpat_assum `exit_result terminal` (fn ex => simp[NoAsms, neq, ex])) >>
  disch_then (qx_choose_then `fr` strip_assume_tac) >>
  `!e. run_from fr deploy_unit.cu_context fn exit_root <> Error e` by
    (qpat_assum `run_from fr _ _ _ = terminal` SUBST1_TAC >>
     drule_then ACCEPT_TAC exit_result_not_error) >>
  `run_context (SUC fr) deploy_unit.cu_context v = terminal` by
    (qspecl_then [`SUC fr`,`deploy_unit.cu_context`,`v`,`"__deploy"`,`fn`,`"__deploy"`]
       mp_tac run_context_run_blocks >>
     (impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
     qpat_assum `Abbrev (exit_root = _)`
       (fn root => PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] root)]) >>
     disch_then SUBST1_TAC >>
     qspecl_then [`fr`,`deploy_unit.cu_context`,`fn`,`exit_root`,`exit_bb`]
       mp_tac run_blocks_run_from_no_phi >> asm_rewrite_tac[]) >>
  conj_tac
  >- (qexists_tac `SUC fr` >> asm_rewrite_tac[] >>
      qpat_assum `exit_result terminal` mp_tac >> Cases_on `terminal` >>
      simp[NoAsms, exit_result_def, terminates_def]);

val linked_correct_exit_blocks_tac =
  `!fuel. mem_safe_run fuel deploy_unit.cu_context fn exit_root` by
    (irule mem_safe_run_all_fuel >> qexists_tac `fr` >>
     conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  `!fuel. ptr_safe_run (linked_ret_DF H) (imm_len_mods mods) fuel
      deploy_unit.cu_context fn [] FEMPTY entry_taint exit_root` by
    (irule fragExecPtrTheory.ptr_safe_run_all_fuel >> qexists_tac `fr` >>
     conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  `lookup_block exit_root.vs_current_bb fn.fn_blocks = SOME exit_bb` by
    asm_rewrite_tac[] >>
  `eval_phis exit_root exit_bb.bb_instructions = OK exit_root` by
    (irule eval_phis_no_phi >> FIRST_ASSUM ACCEPT_TAC) >>
  `!fuel. mem_safe_run fuel deploy_unit.cu_context fn (exit_root with vs_inst_idx := 0)` by
    asm_rewrite_tac[];

val linked_correct_exit_mem_blocks_tac =
  `!fuel. mem_safe_blocks fuel deploy_unit.cu_context fn exit_root` by
     drule_all_then ACCEPT_TAC entryDispatchMemTheory.mem_safe_blocks_no_phi;

val linked_correct_exit_ptr_blocks_tac =
  `!fuel. ptr_safe_blocks (linked_ret_DF H) (imm_len_mods mods) fuel
      deploy_unit.cu_context fn [] FEMPTY entry_taint exit_root` by
     drule_all_then ACCEPT_TAC entryDispatchPtrTheory.ptr_safe_blocks_from_phi_free_run;

val linked_correct_exit_memory_goal =
  Q.SUBGOAL_THEN `raw_unit_memory_ok deploy_unit.cu_context v /\
      ptr_discipline (imm_len_mods mods) deploy_unit.cu_context v /\
      taint_within (linked_ret_DF H) deploy_unit.cu_context v /\
      mem_inv dload_offset_ok deploy_unit.cu_context v /\
      mem_inv dload_headroom_ok deploy_unit.cu_context v`
    (map_every assume_tac o CONJUNCTS);

val linked_correct_exit_memory_entry_tac =
  `v = vs with <|vs_fmp := fmp; vs_initial_fmp := fmp;
                  vs_gas_readings := v.vs_gas_readings|>` by
    (qpat_assum `raw_variant fmp v vs`
       (mp_tac o PURE_REWRITE_RULE [raw_variant_def, gas_variant_def]) >>
     simp[NoAsms, venom_state_component_equality] >> strip_tac >>
     qpat_assum `fmp = v.vs_initial_fmp` (fn h =>
       qpat_assum `fmp = v.vs_fmp` (ACCEPT_TAC o TRANS (SYM h)))) >>
  `v.vs_alloca_next = vs.vs_alloca_next /\ v.vs_initial_fmp = fmp /\ v.vs_fmp = fmp /\
   v.vs_code = vs.vs_code /\ v.vs_data_section = vs.vs_data_section /\
   v.vs_labels = vs.vs_labels` by
    (qpat_assum `v = vs with <|vs_fmp := fmp; vs_initial_fmp := fmp;
                            vs_gas_readings := v.vs_gas_readings|>` SUBST1_TAC >>
     simp[NoAsms]) >>
  `code_layout_valid v` by
    (qpat_assum `code_layout_valid vs` mp_tac >>
     qpat_assum `v.vs_code = vs.vs_code` (fn code =>
       qpat_assum `v.vs_data_section = vs.vs_data_section` (fn data =>
         qpat_assum `v.vs_labels = vs.vs_labels` (fn labels =>
           pure_rewrite_tac[code_layout_valid_def, code, data, labels]))) >>
     disch_then ACCEPT_TAC) >>
  qpat_x_assum `v = vs with <|vs_fmp := fmp; vs_initial_fmp := fmp;
                             vs_gas_readings := v.vs_gas_readings|>` kall_tac;

val linked_correct_exit_memory_tac =
  let fun memory_from rule =
    mp_tac (Q.INST [`dunit` |-> `deploy_unit`,`vs` |-> `v`,
        `D` |-> `linked_ret_DF (H : (bool # bytes32 # type_value) list # num list)`,
        `func` |-> `fn`] (SPEC_ALL rule)) >>
    qpat_assum `Abbrev (exit_root = _)`
      (fn root => PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] root)]) >>
    asm_rewrite_tac[arithmeticTheory.LESS_EQ_REFL] >>
    disch_then irule >> FIRST_ASSUM ACCEPT_TAC
  in Cases_on `ctx_has_dalloca deploy_unit.cu_context`
     >- memory_from deploy_selected_memory_from_checked_mods >>
     memory_from deploy_selected_memory_mods
  end;

val linked_correct_exit_prewalk_tac =
  `mem_inv raw_mem_ok deploy_unit.cu_context v` by
    (qpat_assum `raw_unit_memory_ok deploy_unit.cu_context v` mp_tac >>
     simp[NoAsms, unitTransformDefsTheory.raw_unit_memory_ok_def, mem_inv_def, raw_mem_ok_def]) >>
  `fmp_free_ctx deploy_unit.cu_context` by drule_all_then ACCEPT_TAC source_fmp_free >>
  conj_tac
  >- (irule o1_source_pre_walk_inv >>
      rpt (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >>
      rewrite_tac[o1_src_inv_def] >> rpt conj_tac >>
      (FIRST_ASSUM ACCEPT_TAC ORELSE (qexists_tac `imm_len_mods mods` >> asm_rewrite_tac[])));

val linked_correct_exit_dload_tac =
  conj_tac
  >- (qspecl_then [`deploy_unit.cu_context`,`"__deploy"`,`fn`,`"__deploy"`,`v`]
        mp_tac lowered_unit_dload_in_section >>
      qpat_assum `Abbrev (exit_root = _)`
        (fn root => PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] root)]) >>
      (impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
      disch_then (mk_asm "exit_dload") >>
      rewrite_tac[mem_inv_raw_reachable] >> BETA_TAC >> conj_tac
      >- (qexistsl_tac [`"__deploy"`,`fn`,`"__deploy"`] >> asm_rewrite_tac[]) >>
      rpt gen_tac >> disch_tac >> conj_tac
      >- asm "exit_dload" (drule_then ACCEPT_TAC) >>
      drule_then strip_assume_tac o1SafeUptoTheory.raw_reachable_code_data >> asm_rewrite_tac[]);

val linked_correct_exit_cut_tac =
  conj_tac
  >- (rewrite_tac[o1SafeUptoTheory.o1_safe_upto_def, o1SafeUptoTheory.o1_ptr_safe_upto_def] >>
      rpt conj_tac >> FIRST
      [FIRST_ASSUM ACCEPT_TAC,
       match_mp_tac (SPEC_ALL o1SafeUptoTheory.ptr_discipline_upto_whole) >> FIRST_ASSUM ACCEPT_TAC,
       match_mp_tac (SPEC_ALL o1SafeUptoTheory.taint_within_upto_whole) >> FIRST_ASSUM ACCEPT_TAC,
       rpt gen_tac >> disch_then (assume_tac o CONJUNCT1) >> conj_tac
       >- (qpat_assum `mem_inv raw_mem_ok _ v`
            (drule_then ACCEPT_TAC o CONJUNCT2 o REWRITE_RULE [mem_inv_raw_reachable])) >>
       qpat_assum `mem_inv dload_offset_ok _ v`
         (drule_then ACCEPT_TAC o CONJUNCT2 o REWRITE_RULE [mem_inv_raw_reachable])]);

val linked_correct_exit_events_tac =
  qpat_assum `gas_origin_ptr_path _ (exit_root,_,_) m (terminal,_,_)`
    (assume_tac o CONJUNCT1 o MATCH_MP (SPEC_ALL fragGasOriginPtrTheory.gas_origin_ptr_path_projections)) >>
  qpat_assum `Abbrev (exit_root = _)`
    (fn root => PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] root)]) >>
  drule_at (Pat `gas_origin_path _ _ _ _ _ _ _`)
    fragGasOriginEventsTheory.gas_origin_path_entry_events >>
  disch_then (qspec_then `exit_bb` mp_tac) >> asm_rewrite_tac[];

val linked_correct_exit_producer_goal =
  Q.SUBGOAL_THEN `!v m H terminal G' tn'.
    raw_variant fmp v vs /\ code_layout_valid vs /\ exit_result terminal /\
    gas_origin_ptr_path (linked_ret_DF H,imm_len_mods mods,
      gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context,
      deploy_unit.cu_context,fn,[])
      (v with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>,
       FEMPTY,entry_taint) m (terminal,G',tn') /\
    dead_wf (linked_ret_DF H) ==>
    ?D fuel extra. dead_wf D /\
      (fin = asm_opt_finalizer ==> !callee inst s.
        raw_reachable v deploy_unit.cu_context callee inst s /\
        gas_cut (MIN (LENGTH m) (LENGTH v.vs_gas_readings)) v s ==>
        inst_dload_in_section inst s) /\
      o1_safe_upto D (imm_len_mods mods) (MIN (LENGTH m) (LENGTH v.vs_gas_readings))
        deploy_unit.cu_context v /\
      MAP (\key. key IN gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context)
        (gas_events_blocks fuel deploy_unit.cu_context fn
          (v with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>)) =
        m ++ extra`
    (mk_asm "linked_correct_exit_producer");

val linked_correct_exit_producer_tac =
  map_every qx_gen_tac [`v`,`m`,`H`,`terminal`,`G'`,`tn'`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  asm "linked_correct_exit_inputs" (drule_all_then strip_assume_tac) >>
  rename1 `MAP _ (gas_events_blocks exit_event_fuel _ _ _) = m` >>
  qexistsl_tac [`linked_ret_DF H`, `exit_event_fuel`, `[]`] >>
  conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
  conj_tac
  >- (disch_tac >> rpt gen_tac >> disch_then (assume_tac o CONJUNCT1) >>
      qpat_assum `mem_inv (\_ _ i s. inst_dload_in_section i s /\ _) _ v`
        (drule_then (ACCEPT_TAC o CONJUNCT1) o CONJUNCT2 o
         SIMP_RULE bool_ss [mem_inv_raw_reachable])) >>
  asm_rewrite_tac[listTheory.APPEND_NIL];

(* Preserve the compatibility interface without choosing a second replay. *)
val linked_registered_terminal_forget_eval_tac =
  qx_gen_tac `vi` >> disch_tac >>
  asm "linked_ctor_registered_terminal_eval" (qspec_then `vi` mp_tac) >>
  (impl_tac >- FIRST_ASSUM ACCEPT_TAC) >>
  disch_then (qx_choose_then `replay_marks` (DISJ_CASES_THEN2 assume_tac
    (qx_choosel_then [`replay_res`,`replay_src`,`terminal`,`replay_G`,`replay_tn`]
      (CONJUNCTS_THEN2 (K ALL_TAC) assume_tac)))) >>
  qexists_tac `replay_marks` >- (disj1_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  disj2_tac >>
  qexistsl_tac [`replay_res`,`replay_src`,`terminal`,`replay_G`,`replay_tn`] >>
  FIRST_ASSUM ACCEPT_TAC;

(* Fixed-observation transport up to the linked dead return mask. *)
val linked_correctness_abort_transport_tac =
  `!gs H a s u'.
     H = storage_trace_horizon (deploy_storage_trace_mods (SOME os) gs am tx mods exps) /\
     deploy_post gs (Abort a s) /\ dead_result_rel (linked_ret_DF H) (Abort a s) u' ==>
     deploy_post gs u'` by
    (map_every qx_gen_tac [`gs`,`H`,`a`,`s`,`u'`] >>
     disch_then (CONJUNCTS_THEN2 (K ALL_TAC) mp_tac) >>
     namedCases_on `u'` ["st","p","a' s'","ir st","msg"] >>
     simp[NoAsms, dead_result_rel_def, Abbr `deploy_post`] >>
     Cases_on `load_contract (SOME os) gs am tx mods exps` >> simp[] >>
     rename1 `INR exc` >> Cases_on `exc` >> Cases_on `a` >> Cases_on `a'` >> simp[]);

val linked_correctness_halt_cases_tac =
  `!gs H p u'.
     deploy_post gs (Halt p) /\ dead_result_rel (linked_ret_DF H) (Halt p) u' ==>
     ?installed rqs p'. load_contract (SOME os) gs am tx mods exps = INL (installed,rqs) /\
                        u' = Halt p'` by
    (map_every qx_gen_tac [`gs`,`H`,`p`,`u'`] >>
     namedCases_on `u'` ["st","p'","a s","ir st","msg"] >>
     simp[NoAsms, dead_result_rel_def, Abbr `deploy_post`] >>
     namedCases_on `load_contract (SOME os) gs am tx mods exps` ["loaded","exc"] >>
     simp[NoAsms] >> PairCases_on `loaded` >> simp[NoAsms]);

val linked_correctness_halt_accounts_setup_tac =
  qabbrev_tac `raw_accounts = if ALOOKUP installed.sources tx.target = NONE
    then p.vs_accounts else update_account tx.target
      (lookup_account tx.target p.vs_accounts with
         code := (lookup_account tx.target installed.accounts).code) p.vs_accounts` >>
  qabbrev_tac `opt_accounts = if ALOOKUP installed.sources tx.target = NONE
    then p'.vs_accounts else update_account tx.target
      (lookup_account tx.target p'.vs_accounts with
         code := (lookup_account tx.target installed.accounts).code) p'.vs_accounts` >>
  Q.SUBGOAL_THEN `accounts_agree_except (linked_ret_DF H) raw_accounts opt_accounts` assume_tac;

val linked_correctness_halt_accounts_mask_tac =
  qpat_assum `Abbrev (raw_accounts = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `Abbrev (opt_accounts = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  Cases_on `ALOOKUP installed.sources tx.target = NONE`
  >- (qpat_assum `ALOOKUP installed.sources tx.target = NONE` (fn src => simp[NoAsms, src]) >>
      qpat_assum `accounts_agree_except _ p.vs_accounts p'.vs_accounts` ACCEPT_TAC) >>
  qpat_assum `accounts_agree_except _ p.vs_accounts p'.vs_accounts` mp_tac >>
  qpat_assum `ALOOKUP installed.sources tx.target <> NONE`
    (fn src => simp[NoAsms, src, accounts_agree_except_def]) >>
  disch_tac >> qx_gen_tac `a` >>
  qpat_assum `!a. _ /\ storage_agree_except _ _ _` (qspec_then `a` mp_tac) >>
  Cases_on `a = tx.target`
  >- (qpat_assum `a = tx.target`
        (fn addr => simp[NoAsms, addr, vfmStateTheory.update_account_def,
                         vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM,
                         vfmStateTheory.account_state_component_equality])) >>
  qpat_assum `a <> tx.target`
    (fn addr => simp[NoAsms, addr, vfmStateTheory.update_account_def,
                     combinTheory.APPLY_UPDATE_THM]);

val linked_correctness_halt_accounts_compose_tac =
  `accounts_agree_except (linked_ret_DF H)
      (process_deletions p'.vs_pending_deletions raw_accounts)
      (process_deletions p'.vs_pending_deletions opt_accounts)` by
    (irule e2eCompositionTheory.accounts_agree_except_process_deletions >>
     qpat_assum `accounts_agree_except _ raw_accounts opt_accounts` ACCEPT_TAC) >>
  irule accounts_agree_storage_dead_trans >>
  qexists_tac `process_deletions p'.vs_pending_deletions raw_accounts`;

val linked_correctness_halt_accounts_storage_tac =
  qpat_assum `accounts_agree_except _ (process_deletions _ _) _`
    (assume_tac o PURE_REWRITE_RULE [accounts_agree_except_def]) >>
  rpt conj_tac
  >- (qx_gen_tac `a` >> qpat_assum `!a. _ /\ storage_agree_except _ _ _`
        (ACCEPT_TAC o CONJUNCT1 o Q.SPEC `a`))
  >- (qx_gen_tac `a` >> disch_tac >>
      qpat_assum `!a. _ /\ storage_agree_except _ _ _`
        (mp_tac o CONJUNCT2 o Q.SPEC `a`) >>
      qpat_assum `a <> tx.target` (fn addr =>
        simp[NoAsms, addr, Abbr `linked_ret_DF`, storage_agree_except_empty]))
  >- (qpat_assum `!a. _ /\ storage_agree_except _ _ _`
        (mp_tac o CONJUNCT2 o Q.SPEC `tx.target`) >>
      simp[NoAsms, Abbr `linked_ret_DF`, storage_agree_except_storage_dead]) >>
  qpat_assum `p.vs_pending_deletions = p'.vs_pending_deletions` (SUBST1_TAC o SYM) >>
  qpat_assum `accounts_agree H tx.target installed.accounts _` ACCEPT_TAC;

val linked_correctness_halt_transient_tac =
  irule transient_agree_storage_dead_trans >> qexists_tac `p.vs_transient` >>
  qpat_assum `transient_agree_except _ p.vs_transient p'.vs_transient`
    (assume_tac o PURE_REWRITE_RULE [transient_agree_except_def]) >>
  rpt conj_tac
  >- (qx_gen_tac `a` >> disch_tac >>
      qpat_assum `!a. storage_agree_except _ _ _` (qspec_then `a` mp_tac) >>
      qpat_assum `a <> tx.target` (fn addr =>
        simp[NoAsms, addr, Abbr `linked_ret_DF`, storage_agree_except_empty]))
  >- (qpat_assum `!a. storage_agree_except _ _ _` (qspec_then `tx.target` mp_tac) >>
      simp[NoAsms, Abbr `linked_ret_DF`, storage_agree_except_storage_dead]) >>
  qpat_assum `transient_agree H tx.target installed.tStorage _` ACCEPT_TAC;

val linked_correctness_request_storage_rules =
  [request_agree_except_def, accounts_agree_except_def, transient_agree_except_def];

val linked_correctness_halt_requests_tac =
  qpat_assum `LIST_REL (request_agree H tx.target) rqs p.vs_requests`
    (strip_assume_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
  qpat_assum `LIST_REL (request_agree_except _) p.vs_requests p'.vs_requests`
    (strip_assume_tac o REWRITE_RULE [LIST_REL_EL_EQN]) >>
  rewrite_tac[LIST_REL_EL_EQN] >> conj_tac >- simp[] >>
  qx_gen_tac `n` >> disch_tac >>
  irule (SIMP_RULE (srw_ss())
    (vyperLoweringCorrectTheory.external_call_dead_def :: linked_correctness_request_storage_rules)
    request_agree_dead_trans) >>
  qexists_tac `EL n p.vs_requests` >>
  `n < LENGTH p.vs_requests` by
    (qpat_assum `LENGTH rqs = LENGTH p.vs_requests` (SUBST1_TAC o SYM) >>
     qpat_assum `n < LENGTH rqs` ACCEPT_TAC) >>
  qpat_assum `!n. n < LENGTH rqs ==> request_agree _ _ _ _` (qspec_then `n` mp_tac) >>
  qpat_assum `!n. n < LENGTH p.vs_requests ==> request_agree_except _ _ _`
    (qspec_then `n` mp_tac) >>
  qpat_assum `n < LENGTH rqs` (fn src_lt =>
    qpat_assum `n < LENGTH p.vs_requests` (fn raw_lt =>
      simp (NoAsms :: src_lt :: raw_lt :: Abbr `linked_ret_DF` ::
            linked_correctness_request_storage_rules))) >>
  rpt strip_tac >> FIRST_ASSUM ACCEPT_TAC;

val linked_correctness_halt_bytes_tac =
  qpat_assum `if ALOOKUP installed.sources tx.target = NONE then _ else _` mp_tac >>
  Cases_on `ALOOKUP installed.sources tx.target = NONE`
  >- (qpat_assum `ALOOKUP installed.sources tx.target = NONE` (fn src => simp[NoAsms, src]) >>
      disch_then (map_every assume_tac o CONJUNCTS) >> conj_tac
      >- (qpat_assum `LENGTH p.vs_returndata = LENGTH p'.vs_returndata` mp_tac >>
          qpat_assum `p.vs_returndata = []` (fn ret => simp[NoAsms, ret])) >>
      qpat_assum `p.vs_pending_deletions = p'.vs_pending_deletions` (SUBST1_TAC o SYM) >>
      qpat_assum `MEM tx.target p.vs_pending_deletions` ACCEPT_TAC) >>
  qpat_assum `ALOOKUP installed.sources tx.target <> NONE` (fn src => simp[NoAsms, src]) >>
  disch_then (qx_choose_then `sec` strip_assume_tac);

val linked_correctness_halt_suffix_goal =
  Q.SUBGOAL_THEN `?sec'. p'.vs_returndata = runtime_bc ++ sec' /\
    LENGTH sec' = LENGTH sec /\
    !j. j < LENGTH sec /\ ~imm_section_dead_mods ctor_ce sec j ==> EL j sec' = EL j sec`
    (qx_choose_then `sec'` strip_assume_tac);

val linked_correctness_halt_suffix_rule_tac =
  qspecl_then [`runtime_bc`, `sec`, `p'.vs_returndata`,
               `imm_section_dead_mods ctor_ce sec`] mp_tac
    ctorDeployDeadTheory.append_agree_except_suffix >> impl_tac;

val linked_correctness_halt_length_tac =
  qpat_assum `p.vs_returndata = runtime_bc ++ sec` (fn ret =>
    qpat_assum `LENGTH p.vs_returndata = LENGTH p'.vs_returndata`
      (ACCEPT_TAC o REWRITE_RULE [ret] o SYM));

val linked_correctness_halt_live_bytes_tac =
  qx_gen_tac `i` >> disch_tac >>
  qpat_assum `!i. _ ==> EL i p.vs_returndata = EL i p'.vs_returndata`
    (qspec_then `i` mp_tac) >>
  qpat_assum `p.vs_returndata = runtime_bc ++ sec` (fn ret =>
    simp[NoAsms, ret, Abbr `linked_ret_DF`, rich_listTheory.DROP_LENGTH_APPEND]) >>
  disch_then irule >>
  qpat_assum `i < LENGTH (runtime_bc ++ sec) /\ _`
    (ACCEPT_TAC o SIMP_RULE (srw_ss()) []);

val linked_correctness_halt_transport_goal =
  Q.SUBGOAL_THEN `!gs H installed rqs p p'.
     H = storage_trace_horizon (deploy_storage_trace_mods (SOME os) gs am tx mods exps) /\
     load_contract (SOME os) gs am tx mods exps = INL (installed,rqs) /\
     deploy_post gs (Halt p) /\ dead_result_rel (linked_ret_DF H) (Halt p) (Halt p') ==>
     accounts_agree H tx.target installed.accounts
       (process_deletions p'.vs_pending_deletions
         (if ALOOKUP installed.sources tx.target = NONE then p'.vs_accounts
          else update_account tx.target
            (lookup_account tx.target p'.vs_accounts with
               code := (lookup_account tx.target installed.accounts).code) p'.vs_accounts)) /\
     transient_agree H tx.target installed.tStorage p'.vs_transient /\
     installed.logs = p'.vs_logs /\ LIST_REL (request_agree H tx.target) rqs p'.vs_requests /\
     (if ALOOKUP installed.sources tx.target = NONE then
        p'.vs_returndata = [] /\ MEM tx.target p'.vs_pending_deletions
      else ?sec sec'. p.vs_returndata = runtime_bc ++ sec /\
        immutables_section_rel_mods mods (account_immutables installed tx.target) sec /\
        p'.vs_returndata = runtime_bc ++ sec' /\ LENGTH sec' = LENGTH sec /\
        !j. j < LENGTH sec /\ ~imm_section_dead_mods ctor_ce sec j ==> EL j sec' = EL j sec)`
    assume_tac;

val linked_correctness_halt_transport_setup_tac =
  map_every qx_gen_tac [`gs`,`H`,`installed`,`rqs`,`p`,`p'`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `load_contract (SOME os) gs am tx mods exps = INL (installed,rqs)` (fn load =>
    qpat_assum `H = storage_trace_horizon _` (fn hor =>
      qpat_x_assum `deploy_post gs (Halt p)` mp_tac >>
      simp[NoAsms, Abbr `deploy_post`, load, GSYM hor])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `dead_result_rel _ _ _`
    (map_every assume_tac o CONJUNCTS o SIMP_RULE (srw_ss()) [dead_result_rel_def]);

(* Select marks once per raw entry. Both the focus producer and the
   observation certificate below use this same selection. *)
fun linked_correctness_mark_selection_tac terminal_label =
  asm terminal_label
    (qx_choose_then `select_marks` (mk_asm "linked_selected_terminal") o
     CONV_RULE (BINDER_CONV RIGHT_IMP_EXISTS_CONV THENC SKOLEM_CONV)) >>
  qabbrev_tac `raw_entry = \gs. vs with <|vs_gas_readings := gs;
      vs_fmp := fmp; vs_initial_fmp := fmp|>` >>
  qabbrev_tac `markf = \gs. select_marks (raw_entry gs)` >>
  `!gs. raw_variant fmp (raw_entry gs) vs /\ (raw_entry gs).vs_gas_readings = gs` by
    simp[NoAsms, Abbr `raw_entry`, raw_variant_def, gas_variant_def,
         venom_state_component_equality];

val linked_correctness_static_focus_tac =
  `FLOOKUP vs.vs_labels "code_end" = SOME (n2w (LENGTH (assemble prog')))` by
    (qpat_assum `FLOOKUP (lo_reloc prog prog') "code_end" = SOME _`
       (fn lab => simp[NoAsms, Abbr `vs`, opt_entry_state_own_def,
                     finite_mapTheory.FLOOKUP_o_f, lab])) >>
  `!bs. constructor_args_encode_mods mods tx bs ==> LENGTH bs < 2 ** 128` by
    (gen_tac >> strip_tac >>
     drule_all constructor_args_size_bounded_mods >> simp[NoAsms]) >>
  `code_layout_valid vs` by
    (mp_tac (Q.INST [`es` |-> `es`, `cplan` |-> `cplan`] deploy_entry_code_layout_mods) >>
     impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     simp[NoAsms, Abbr `vs`, code_layout_valid_def]) >>
  `o1_run_state_ok vs` by simp[o1_run_state_ok_def] >>
  `w2n vs.vs_initial_fmp <= w2n fmp` by
    (qpat_assum `w2n (opt_entry_state_own prog prog' cplan es).vs_initial_fmp <= w2n fmp`
       mp_tac >> simp[NoAsms, Abbr `vs`]) >>
  `LENGTH vs.vs_data_section < dimword (:256) DIV 2` by
    (MATCH_MP_TAC (Q.INST [`vs` |-> `vs`, `prefix` |-> `assemble prog'`]
       e2eCorrectnessTheory.data_section_length_bound) >>
     rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC);

fun linked_correctness_selected_tac readings =
  qpat_assum `!gs. raw_variant fmp (raw_entry gs) vs /\ _`
    (qspec_then readings (map_every assume_tac o CONJUNCTS)) >>
  asm "linked_selected_terminal" (qspec_then (`raw_entry (` @ readings @ `)`) mp_tac) >>
  (impl_tac >- (conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
  qpat_assum `Abbrev (markf = _)` (fn th =>
    PURE_REWRITE_TAC [GSYM (BETA_RULE (Q.AP_THM
      (REWRITE_RULE [markerTheory.Abbrev_def] th) readings))]) >>
  qpat_assum (`(raw_entry (` @ readings @ `)).vs_gas_readings = ` @ readings)
    (fn th => PURE_REWRITE_TAC [th]) >>
  qpat_assum `Abbrev (os = MAP SND (call_trace es))`
    (PURE_REWRITE_TAC o single o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]);

(* A focus needs only the checks at its own GAS cut.  Use the root's
   allocation and DLOAD budgets rather than assuming a complete run. *)
val linked_focus_entry_static_tac =
  `ptr_ok_check deploy_unit.cu_context` by
    (qpat_assum `lowering_context_ok deploy_unit.cu_context`
       (mp_tac o REWRITE_RULE [lowering_context_ok_def]) >>
     simp[NoAsms]) >>
  drule_then assume_tac ptrOkCheckTheory.ptr_ok_check_sound >>
  `EVERY (\f. ALL_DISTINCT (fn_labels f)) deploy_unit.cu_context.ctx_functions` by
    (qpat_assum `lowering_context_ok deploy_unit.cu_context`
       (mp_tac o CONJUNCT1 o MATCH_MP lowering_context_ok_bridge) >>
     simp[NoAsms, listTheory.EVERY_MEM]) >>
  `fmp_free_ctx deploy_unit.cu_context` by
    (irule o1PipelineComposeTheory.source_fmp_free >>
     goal_assum (drule_at Any) >> FIRST_ASSUM ACCEPT_TAC) >>
  (Q.SUBGOAL_THEN `?bb. lookup_block "__deploy" fn.fn_blocks = SOME bb`
     (qx_choose_then `focus_entry_bb` assume_tac) >-
    (qpat_assum `fn_entry_label fn = SOME "__deploy"` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `fn.fn_blocks` >>
     simp[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def,
          venomInstTheory.lookup_block_def,listTheory.FIND_thm]));

val linked_focus_entry_phi_goal = sg `phi_prefix_length focus_entry_bb.bb_instructions = 0`;

val linked_focus_entry_phi_tac =
  qpat_assum `lowering_context_ok deploy_unit.cu_context` mp_tac >>
  qpat_assum `lookup_function "__deploy" deploy_unit.cu_context.ctx_functions = SOME fn` mp_tac >>
  qpat_assum `lookup_block "__deploy" fn.fn_blocks = SOME focus_entry_bb` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
  metis_tac[acceptedContextPhiTheory.lowering_context_ok_block_phi];

val linked_focus_entry_budget_tac =
  `imm_len_mods mods + unit_alloca_budget deploy_unit.cu_context +
     32 * ctx_dload_count deploy_unit.cu_context < dimword (:256)` by
    (qpat_assum `imm_len_mods mods + _ + _ <= w2n fmp` mp_tac >>
     qpat_assum `w2n fmp < 2 ** 254` mp_tac >>
     simp[NoAsms, wordsTheory.dimword_def, venomLayoutTheory.dimindex_256] >> decide_tac);

(* The return mask is determined by the live bytes of each declared region. *)
val linked_focus_dead_regions_goal =
  sg `!sec j. imm_section_dead_mods ctor_ce sec j <=>
    ?src id off ty tv. immutable_region_mods mods src id off (type_memory_size tv) /\
      FLOOKUP env.bare_globals (src,id) = SOME ty /\
      evaluate_type (get_tenv cx) ty = SOME tv /\ mem_dead_bytes sec off tv j`;

val linked_focus_dead_regions_tac =
  qpat_assum `!gs. expr_sim_inv_mods mods ctor_ce cx env _`
    (qspec_then `([]:bytes32 list)` mp_tac) >>
  qpat_assum `contract_inv mods exps deploy_unit.cu_context ctor_ce cx` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> ntac 2 disch_tac >> rpt gen_tac >>
  drule_all_then MATCH_ACCEPT_TAC immutableRegionDeadPropsTheory.imm_section_dead_mods_regions;

val linked_focus_dead_layout_tac =
  qpat_assum `immutable_section_layout_mods mods ctor_ce`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [immutable_section_layout_mods_def]);

val linked_focus_dead_region_goal =
  sg `!sec src id off ty tv j.
    immutable_region_mods mods src id off (type_memory_size tv) /\
    FLOOKUP env.bare_globals (src,id) = SOME ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
    off <= j /\ j < off + type_memory_size tv /\ imm_section_dead_mods ctor_ce sec j ==>
    mem_dead_bytes sec off tv j`;

val linked_focus_dead_region_tac =
  qpat_assum `!sec j. imm_section_dead_mods ctor_ce sec j <=> _` mp_tac >>
  qpat_assum `!src id off. FLOOKUP ctor_ce.ce_module_vars (src,id) = SOME (ImmutableLoc off) <=> _`
    mp_tac >>
  qpat_assum `!src id off size src' id' off' size'. _ ==> loweringStateRelDefs$regions_disjoint _ _ _ _`
    mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> ntac 3 disch_tac >>
  map_every qx_gen_tac [`sec`,`src`,`id`,`off`,`ty`,`tv`,`j`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!sec j. imm_section_dead_mods ctor_ce sec j <=> _`
    (qspecl_then [`sec`,`j`] (fn iff =>
      qpat_x_assum `imm_section_dead_mods ctor_ce sec j`
        (qx_choosel_then [`src'`,`id'`,`off'`,`ty'`,`tv'`]
          (map_every assume_tac o CONJUNCTS) o REWRITE_RULE [iff]))) >>
  `off' <= j /\ j < off' + type_memory_size tv'` by
    (qpat_assum `mem_dead_bytes sec off' tv' j`
       (MATCH_ACCEPT_TAC o MATCH_MP (CONJUNCT1 ctorDeployDeadSectionTheory.mem_dead_bytes_range))) >>
  `(src,id) = (src',id')` by
    (CCONTR_TAC >>
     qpat_assum `!src id off size src' id' off' size'. _ ==> loweringStateRelDefs$regions_disjoint _ _ _ _`
       (qspecl_then [`src`,`id`,`off`,`type_memory_size tv`,
                     `src'`,`id'`,`off'`,`type_memory_size tv'`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
     simp[NoAsms, loweringStateRelDefsTheory.regions_disjoint_def] >>
     qpat_assum `off <= j` mp_tac >> qpat_assum `off' <= j` mp_tac >>
     qpat_assum `j < off + type_memory_size tv` mp_tac >>
     qpat_assum `j < off' + type_memory_size tv'` mp_tac >> decide_tac) >>
  `off = off'` by
    (`FLOOKUP ctor_ce.ce_module_vars (src,id) = SOME (ImmutableLoc off)` by
       (qpat_assum `!src id off. FLOOKUP ctor_ce.ce_module_vars (src,id) = SOME (ImmutableLoc off) <=> _`
          (qspecl_then [`src`,`id`,`off`] (irule o snd o EQ_IMP_RULE)) >>
        qexists_tac `type_memory_size tv` >> FIRST_ASSUM ACCEPT_TAC) >>
     `FLOOKUP ctor_ce.ce_module_vars (src',id') = SOME (ImmutableLoc off')` by
       (qpat_assum `!src id off. FLOOKUP ctor_ce.ce_module_vars (src,id) = SOME (ImmutableLoc off) <=> _`
          (qspecl_then [`src'`,`id'`,`off'`] (irule o snd o EQ_IMP_RULE)) >>
        qexists_tac `type_memory_size tv'` >> FIRST_ASSUM ACCEPT_TAC) >>
     map_every (fn q => qpat_assum q mp_tac)
       [`FLOOKUP ctor_ce.ce_module_vars (src,id) = SOME (ImmutableLoc off)`,
        `FLOOKUP ctor_ce.ce_module_vars (src',id') = SOME (ImmutableLoc off')`,
        `(src,id) = (src',id')`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[pairTheory.PAIR_EQ] >> rpt disch_tac >> gvs[]) >>
  `tv = tv'` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`FLOOKUP env.bare_globals (src,id) = SOME ty`,
        `FLOOKUP env.bare_globals (src',id') = SOME ty'`,
        `evaluate_type (get_tenv cx) ty = SOME tv`,
        `evaluate_type (get_tenv cx) ty' = SOME tv'`, `(src,id) = (src',id')`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> gvs[]) >>
  asm_rewrite_tac[];

val linked_focus_dead_section_goal =
  sg `!sec1 sec2. LENGTH sec2 = LENGTH sec1 /\
    (!j. j < LENGTH sec1 /\ ~imm_section_dead_mods ctor_ce sec1 j ==> EL j sec2 = EL j sec1) ==>
    imm_section_dead_mods ctor_ce sec2 = imm_section_dead_mods ctor_ce sec1`;

val linked_focus_dead_section_setup_tac =
  qpat_assum `!sec j. imm_section_dead_mods ctor_ce sec j <=> _` mp_tac >>
  qpat_assum `!sec src id off ty tv j. _ ==> mem_dead_bytes sec off tv j` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> ntac 2 disch_tac >>
  map_every qx_gen_tac [`sec1`,`sec2`] >> disch_then (map_every assume_tac o CONJUNCTS);

val linked_focus_dead_section_frame_goal =
  sg `!src id off ty tv.
     immutable_region_mods mods src id off (type_memory_size tv) /\
     FLOOKUP env.bare_globals (src,id) = SOME ty /\ evaluate_type (get_tenv cx) ty = SOME tv ==>
     mem_dead_bytes sec2 off tv = mem_dead_bytes sec1 off tv`;

val linked_focus_dead_section_frame_tac =
  map_every qx_gen_tac [`src`,`id`,`off`,`ty`,`tv`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule ctorDeployDeadSectionTheory.mem_dead_bytes_frame >> simp[] >>
  qx_gen_tac `j` >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!j. _ /\ ~imm_section_dead_mods ctor_ce sec1 j ==> _`
    (qspec_then `j` irule) >> simp[] >>
  qpat_assum `!sec src id off ty tv j. _ ==> mem_dead_bytes sec off tv j`
    (qspecl_then [`sec1`,`src`,`id`,`off`,`ty`,`tv`,`j`] mp_tac) >> simp[];

val linked_focus_dead_section_finish_tac =
  simp[NoAsms, FUN_EQ_THM] >> qx_gen_tac `j` >>
  qpat_assum `!sec j. imm_section_dead_mods ctor_ce sec j <=> _`
    (PURE_REWRITE_TAC o single) >>
  qpat_assum `!src id off ty tv. _ ==> mem_dead_bytes sec2 off tv = _`
    (mp_tac o REWRITE_RULE [FUN_EQ_THM]) >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[];

val linked_focus_dead_wf_goal =
  Q.SUBGOAL_THEN `!H. dead_wf (linked_ret_DF H)` (mk_asm "linked_correctness_dead_wf");

val linked_focus_dead_wf_tac =
  qpat_assum `!sec1 sec2. _ ==> imm_section_dead_mods ctor_ce sec2 = _` mp_tac >>
  qpat_assum `Abbrev (linked_ret_DF = _)`
    (PURE_REWRITE_TAC o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  POP_ASSUM_LIST (K ALL_TAC) >> disch_tac >>
  qx_gen_tac `H` >> simp[dead_wf_def] >> rpt conj_tac
  >- (qx_gen_tac `a` >> rpt gen_tac >> Cases_on `a = tx.target` >>
      simp[storage_agree_except_storage_dead] >> strip_tac >>
      drule storage_agree_storage_dead >> simp[])
  >- (qx_gen_tac `a` >> rpt gen_tac >> Cases_on `a = tx.target` >>
      simp[storage_agree_except_storage_dead] >> strip_tac >>
      drule storage_agree_storage_dead >> simp[]) >>
  map_every qx_gen_tac [`r1`,`r2`] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `imm_section_dead_mods ctor_ce (DROP (LENGTH runtime_bc) r2) =
   imm_section_dead_mods ctor_ce (DROP (LENGTH runtime_bc) r1)` suffices_by simp[NoAsms] >>
  qpat_assum `!sec1 sec2. _ ==> imm_section_dead_mods ctor_ce sec2 = _` irule >>
  simp[] >> rpt strip_tac >>
  qpat_assum `!i. _ ==> EL i r1 = EL i r2`
    (qspec_then `j + LENGTH runtime_bc` mp_tac) >>
  simp[listTheory.EL_DROP];

val linked_focus_producer_goal =
  Q.SUBGOAL_THEN `!v m H leaf pg G tn finish.
    raw_variant fmp v vs /\
    gas_origin_ptr_focus (linked_ret_DF H,imm_len_mods mods,
      gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context,
      deploy_unit.cu_context,fn,[])
      (v with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>,
       FEMPTY,entry_taint) m (leaf,pg,G,tn,finish) ==>
    ?D fuel extra. dead_wf D /\
      (fin = asm_opt_finalizer ==>
       !callee inst s. raw_reachable v deploy_unit.cu_context callee inst s /\
         gas_cut (MIN (LENGTH m) (LENGTH v.vs_gas_readings)) v s ==>
         inst_dload_in_section inst s) /\
      o1_safe_upto D (imm_len_mods mods) (MIN (LENGTH m) (LENGTH v.vs_gas_readings))
        deploy_unit.cu_context v /\
      MAP (\key. key IN gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context)
        (gas_events_blocks fuel deploy_unit.cu_context fn
          (v with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>)) =
        m ++ extra` (mk_asm "linked_correctness_focus_producer");

val linked_focus_variant_tac =
  map_every qx_gen_tac [`v`,`m`,`H`,`leaf`,`pg`,`G`,`tn`,`focus_finish`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `v.vs_fmp = fmp /\ v.vs_initial_fmp = fmp /\
   v.vs_alloca_next = vs.vs_alloca_next /\ code_layout_valid v` by
    (qpat_assum `raw_variant fmp v vs` mp_tac >>
     qpat_assum `code_layout_valid vs` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[raw_variant_def, gas_variant_def, code_layout_valid_def,
          venom_state_component_equality] >> strip_tac >> strip_tac >> gvs[]) >>
  `v.vs_alloca_next = imm_len_mods mods` by simp[] >>
  `imm_len_mods mods <= v.vs_alloca_next` by simp[] >>
  `w2n v.vs_initial_fmp <= w2n v.vs_fmp` by simp[];

val linked_focus_headroom_goal = sg `mem_inv dload_headroom_ok deploy_unit.cu_context v`;

val linked_focus_headroom_tac =
  map_every (fn q => qpat_assum q mp_tac)
    [`lowering_context_ok deploy_unit.cu_context`,
     `deploy_unit.cu_context.ctx_entry = SOME "__deploy"`,
     `lookup_function "__deploy" deploy_unit.cu_context.ctx_functions = SOME fn`,
     `v.vs_alloca_next = imm_len_mods mods`, `v.vs_initial_fmp = fmp`,
     `imm_len_mods mods + unit_alloca_budget deploy_unit.cu_context +
       32 * ctx_dload_count deploy_unit.cu_context < dimword (:256)`,
     `imm_len_mods mods + unit_alloca_budget deploy_unit.cu_context +
       32 * ctx_dload_count deploy_unit.cu_context <= w2n fmp`] >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
  metis_tac[ctorDeployMemoryFrontierTheory.lowered_unit_dload_headroom_ok_from];

fun linked_focus_check_rule_tac th =
  drule_at (Pat `gas_origin_ptr_focus _ _ _ _`)
    (Q.INST [`P` |-> `\nm. set (vyperCompiler$ctx_ptr_param_list deploy_unit.cu_context nm)`] th) >>
  disch_then (qspecl_then [`"__deploy"`,`deploy_unit`] mp_tac);

val linked_focus_safe_tac =
  linked_focus_check_rule_tac fragGasOriginPtrSafeUptoTheory.gas_origin_ptr_focus_o1_safe_upto;

val linked_focus_dload_tac =
  linked_focus_check_rule_tac fragGasOriginPtrSafeUptoTheory.gas_origin_ptr_focus_dload_upto;

val linked_focus_events_tac =
  drule_then assume_tac fragGasOriginPtrTheory.gas_origin_ptr_focus_origin >>
  drule_at (Pat `gas_origin_focus _ _ _ _ _ _`)
    fragGasOriginEventsTheory.gas_origin_focus_entry_events_prefix >>
  disch_then (qspec_then `focus_entry_bb` mp_tac) >>
  (impl_tac >-
    (simp[NoAsms, venom_state_accfupds] >> rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`focus_fuel`,`focus_extra`] assume_tac);

val linked_focus_producer_witness_tac =
  qexistsl_tac [`linked_ret_DF H`,`focus_fuel`,`focus_extra`] >>
  (conj_tac >- asm "linked_correctness_dead_wf" MATCH_ACCEPT_TAC);

val linked_focus_dload_apply_tac =
  disch_tac >> map_every qx_gen_tac [`focus_callee`,`focus_inst`,`focus_state`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  asm "linked_focus_dload_rule"
    (qspecl_then [`focus_callee`,`focus_inst`,`focus_state`] irule);

val linked_correctness_slot_packet_goal =
  Q.SUBGOAL_THEN
    `(!gs. ?D fuel extra.
       dead_wf D /\
       (fin = asm_opt_finalizer ==>
          !f inst s. raw_reachable ((raw_entry:bytes32 list -> venom_state) gs)
            deploy_unit.cu_context f inst s /\
            o1SafeUpto$gas_cut (MIN (LENGTH (markf gs)) (LENGTH gs)) (raw_entry gs) s ==>
            inst_dload_in_section inst s) /\
       o1SafeUpto$o1_safe_upto D (imm_len_mods mods) (MIN (LENGTH (markf gs)) (LENGTH gs))
         deploy_unit.cu_context (raw_entry gs) /\
       MAP (\key. key IN gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context)
         (gas_events_blocks fuel deploy_unit.cu_context fn
           ((raw_entry gs) with <|vs_prev_bb := NONE; vs_current_bb := "__deploy";
                                  vs_inst_idx := 0|>)) = markf gs ++ extra) ==>
     ?slots sites unused.
       LENGTH slots = LENGTH sites /\
       PERM (MAP THE (FILTER IS_SOME slots) ++ unused) (gas_readings es) /\
       !raw. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) slots raw ==>
         (?rest. MAP (\key. key IN gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context)
                    sites = markf (raw ++ [0w]) ++ rest) /\
         !D. (?fr. terminates (run_context fr deploy_unit.cu_context (raw_entry (raw ++ [0w])))) /\
             dead_wf D /\
             o1_pre_walk_inv D deploy_unit.cu_context (raw_entry (raw ++ [0w])) /\
             (fin = asm_opt_finalizer ==>
                mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                          s.vs_code = vs.vs_code /\ s.vs_data_section = vs.vs_data_section)
                  deploy_unit.cu_context (raw_entry (raw ++ [0w]))) ==>
             !exit_fin.
               (exit_fin = asm_opt_finalizer ==>
                  mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                            s.vs_code = vs.vs_code /\ s.vs_data_section = vs.vs_data_section)
                    deploy_unit.cu_context (raw_entry (raw ++ [0w]))) ==>
               ctx_sim D deploy_unit.cu_context deploy_out.po_unit.cu_context
                 (raw_entry (raw ++ [0w])) vs /\
               ctx_abort_rq D deploy_unit.cu_context deploy_out.po_unit.cu_context
                 (raw_entry (raw ++ [0w])) vs /\
               (exit_fin = asm_opt_finalizer ==>
                  code_end_offset_ok (raw_reachable vs) deploy_out.po_unit.cu_context) /\
               o1_lowered_inv deploy_out.po_unit.cu_context vs`
    (mk_asm "linked_correctness_slot_packet");

fun linked_correctness_slot_match pat next rule =
  qpat_assum pat (mp_then (Pat pat) next rule);

val linked_correctness_slot_apply_tac =
  qpat_assum `gas_readings (shadow_root es) = gas_readings es`
    (PURE_REWRITE_TAC o single o SYM) >>
  qpat_assum `Abbrev (raw_entry = _)`
    (PURE_REWRITE_TAC o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  BETA_TAC >>
  disch_then (mk_asm "slot_input") >>
  linked_correctness_slot_match `o1PipelineCorrect$o1_pipeline rpolicy deploy_unit = _`
    mp_tac (Q.INST [`nm` |-> `"__deploy"`]
      gasFocusPacketPipelineStagesTheory.focus_packet_pipeline_stages) >>
  (impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`slot_pre`,`slot_t`,`slot_t'`,`slot_stage`]
    (map_every assume_tac o CONJUNCTS));

(* The actual finalizer selects the slots and replay once. The replay arm does
   not constrain the finalizer used for the separate exit argument. *)
fun linked_correctness_slot_use pat =
  disch_then (linked_correctness_slot_match pat mp_tac);

val linked_correctness_slot_select_tac =
  linked_correctness_slot_match `o1PipelineCorrect$o1_pipeline rpolicy deploy_unit = _`
    mp_tac (INST_TYPE [alpha |-> ``:bool``]
      gasFocusPrefixDriverTheory.focus_finalizer_select_replay_own) >>
  linked_correctness_slot_use `codegen_asm_entry_rel_reloc _ _ _ vs _` >>
  linked_correctness_slot_use `fin IN accepted_finalizers` >>
  disch_then (fn rule =>
    qpat_assum `lookup_function "__deploy" deploy_unit.cu_context.ctx_functions = SOME fn`
      (mp_then (Pat `lookup_function _ _ = _`) mp_tac rule)) >>
  disch_then (fn rule => qpat_assum `fn_entry_label fn = SOME "__deploy"`
    (mp_then (Pat `fn_entry_label _ = _`) mp_tac rule)) >>
  linked_correctness_slot_use `run_callee_first _ _ _ _ slot_t = SOME (_,slot_t')` >>
  linked_correctness_slot_use `slot_stage 9 = deploy_out.po_unit.cu_context` >>
  disch_then (fn rule => qpat_assum `run_call (shadow_root es) = SOME (sr,sg)`
    (mp_then (Pat `run_call _ = _`) mp_tac rule)) >>
  disch_then (fn rule => mp_tac (BETA_RULE
    (Q.INST [`markf` |-> `markf`, `lo` |-> `imm_len_mods mods`, `fmp` |-> `fmp`,
      `project` |-> `\key. key IN gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context`]
      (SPEC_ALL rule))));

val linked_correctness_slot_select_premises_tac =
  rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE
    (asm "slot_input" mp_tac >> simp[NoAsms, venom_state_fupdfupds] >> NO_TAC) ORELSE
    (qpat_assum `~vs.vs_call_ctx.cc_static` (fn th => simp[NoAsms, th]) >> NO_TAC) ORELSE
    (disch_tac >> rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE
       (qpat_assum `deploy_unit.cu_data_segment = _` (fn th => simp[NoAsms, th])))));

val linked_correctness_slot_filling_tac =
  disch_then (qx_choosel_then [`slot_values`,`slot_sites`,`slot_unused`]
    (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`slot_values`,`slot_sites`,`slot_unused`] >>
  (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >>
  (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >>
  qx_gen_tac `raw` >> disch_tac >>
  qpat_assum `!raw. LIST_REL _ slot_values raw ==> _`
    (qspecl_then [`raw`] (drule_then (map_every assume_tac o CONJUNCTS))) >>
  (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >>
  qx_gen_tac `D` >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!D. _ ==> (?orc. _) \/ _` (qspec_then `D` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
  disch_then (DISJ_CASES_THEN2
    (qx_choose_then `orc` (map_every assume_tac o CONJUNCTS))
    (fn static => qpat_assum `~vs.vs_call_ctx.cc_static`
      (fn nonstatic => CONTR_TAC (MP (NOT_ELIM nonstatic) (CONJUNCT1 static)))));

val linked_correctness_slot_exit_tac =
  qx_gen_tac `exit_fin` >> disch_tac >>
  linked_correctness_slot_match `o1PipelineCorrect$o1_pipeline rpolicy deploy_unit = _`
    mp_tac gasFocusReplayExitTheory.focus_v3_exit_from_replay_for >>
  linked_correctness_slot_use `run_pipeline_stages _ _ deploy_unit _ = SOME (slot_pre,slot_t)` >>
  disch_then (fn rule => qpat_assum `slot_pre.cu_context.ctx_entry = SOME "__deploy"`
    (mp_then (Pat `_.cu_context.ctx_entry = _`) mp_tac rule)) >>
  linked_correctness_slot_use `generate_context_plan deploy_out.po_unit.cu_context = SOME cplan` >>
  linked_correctness_slot_use `o1_pre_walk_inv D deploy_unit.cu_context _` >>
  linked_correctness_slot_use `!fuel. gas_res_rel (run_context fuel (slot_stage 7) _)
                                       (ev_context orc fuel (slot_stage 7) vs)` >>
  disch_then (qspec_then `exit_fin` mp_tac);

val linked_correctness_slot_exit_premises_tac =
  rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE
    (disch_tac >> rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE
      (qpat_assum `exit_fin = asm_opt_finalizer ==> mem_inv _ _ _`
        (drule_then ACCEPT_TAC)))));

(* A raw constructor section can be transferred through dead-byte changes
   once the source cell types are known to be their declared types. *)
val linked_correctness_section_goal =
  sg `!imms sec sec'.
    immutables_section_rel_mods mods imms sec /\ LENGTH sec' = LENGTH sec /\
    (!j. j < LENGTH sec /\ ~imm_section_dead_mods ctor_ce sec j ==>
         EL j sec' = EL j sec) /\
    (!src id ty tv v. FLOOKUP env.bare_globals (src,id) = SOME ty /\
      FLOOKUP (get_source_immutables src imms) id = SOME (tv,v) ==>
      evaluate_type (get_tenv cx) ty = SOME tv) ==>
    immutables_section_rel_mods mods imms sec'`;

val linked_correctness_section_setup_tac =
  qpat_assum `contract_inv mods exps _ ctor_ce cx` mp_tac >>
  qpat_assum `!gs. expr_sim_inv_mods mods ctor_ce cx env _`
    (qspec_then `[]` mp_tac) >>
  POP_ASSUM_LIST (K ALL_TAC) >> ntac 2 disch_tac >>
  qpat_assum `contract_inv mods exps _ ctor_ce cx`
    (map_every assume_tac o CONJUNCTS o
     PURE_REWRITE_RULE [immutable_section_layout_mods_def] o
     MATCH_MP contract_inv_immutable_section_layout) >>
  drule_all_then assume_tac immutableRegionDeadPropsTheory.imm_section_dead_mods_regions >>
  map_every qx_gen_tac [`imms`, `sec`, `sec'`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `immutables_section_rel_mods mods imms sec`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [immutables_section_rel_mods_def]) >>
  pure_rewrite_tac[immutables_section_rel_mods_def] >> conj_tac
  >- simp[] >>
  map_every qx_gen_tac [`ssrc`, `sid`, `soff`, `width`] >> disch_tac >>
  qpat_assum `!src id off size. immutable_region_mods mods src id off size ==> ?tv v. _`
    (drule_then (qx_choosel_then [`stv`,`sv`] (map_every assume_tac o CONJUNCTS))) >>
  drule_all_then (qx_choosel_then [`stops`,`sty`,`decltv`] (assume_tac o cj 2))
    immutableRegionTypingPropsTheory.immutable_region_mods_type >>
  `evaluate_type (get_tenv cx) sty = SOME stv` by
    (qpat_assum `!src id ty tv v. FLOOKUP env.bare_globals (src,id) = SOME ty /\ _ ==> _`
       (drule_all_then ACCEPT_TAC)) >>
  qpat_x_assum `type_memory_size stv = width` (SUBST_ALL_TAC o SYM) >>
  `soff + type_memory_size stv <= LENGTH sec` by
    (qpat_assum `LENGTH sec = imm_len_mods mods` SUBST1_TAC >>
     qpat_assum `!src id off size. immutable_region_mods mods src id off size ==> _ <= _`
       (drule_then ACCEPT_TAC));

val linked_correctness_section_offset_tac =
  qpat_assum `!src id off. FLOOKUP ctor_ce.ce_module_vars (src,id) = _ <=> _`
    (fn layout =>
       map_every (fn args => qspecl_then args
         (assume_tac o snd o EQ_IMP_RULE) layout)
         [[`ssrc`,`sid`,`soff`], [`ssrc`,`sid`,`doff`]]) >>
  `FLOOKUP ctor_ce.ce_module_vars (ssrc,sid) = SOME (ImmutableLoc soff)` by
    (qpat_assum `_ ==> FLOOKUP ctor_ce.ce_module_vars (ssrc,sid) = SOME (ImmutableLoc soff)` irule >>
     qexists_tac `type_memory_size stv` >> FIRST_ASSUM ACCEPT_TAC) >>
  `FLOOKUP ctor_ce.ce_module_vars (ssrc,sid) = SOME (ImmutableLoc doff)` by
    (qpat_assum `_ ==> FLOOKUP ctor_ce.ce_module_vars (ssrc,sid) = SOME (ImmutableLoc doff)` irule >>
     qexists_tac `type_memory_size dtv` >> FIRST_ASSUM ACCEPT_TAC) >>
  `doff = soff` by
    (qpat_assum `FLOOKUP ctor_ce.ce_module_vars (ssrc,sid) = SOME (ImmutableLoc doff)` mp_tac >>
     qpat_assum `FLOOKUP ctor_ce.ce_module_vars (ssrc,sid) = SOME (ImmutableLoc soff)`
       (fn loc => simp[NoAsms, loc, compileEnvTheory.var_location_11])) >>
  `dty = sty` by
    (qpat_assum `FLOOKUP env.bare_globals (ssrc,sid) = SOME dty` mp_tac >>
     qpat_assum `FLOOKUP env.bare_globals (ssrc,sid) = SOME sty`
       (fn lookup => simp[NoAsms, lookup])) >>
  qpat_x_assum `dty = sty` SUBST_ALL_TAC >>
  `dtv = stv` by
    (qpat_assum `evaluate_type (get_tenv cx) sty = SOME dtv` mp_tac >>
     qpat_assum `evaluate_type (get_tenv cx) sty = SOME stv`
       (fn eval => simp[NoAsms, eval])) >>
  qpat_x_assum `dtv = stv` SUBST_ALL_TAC >>
  qpat_x_assum `doff = soff` SUBST_ALL_TAC >>
  qpat_assum `~mem_dead_bytes sec soff stv j` (irule o NOT_ELIM) >>
  FIRST_ASSUM ACCEPT_TAC;

val linked_correctness_section_live_goal =
  sg `!j. soff <= j /\ j < soff + type_memory_size stv /\
          ~mem_dead_bytes sec soff stv j ==> EL j sec' = EL j sec`;

val linked_correctness_section_live_tac =
  qx_gen_tac `j` >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `j < LENGTH sec` by decide_tac >>
  `~imm_section_dead_mods ctor_ce sec j` suffices_by
    (disch_tac >>
     qpat_assum `!j. j < LENGTH sec /\ ~imm_section_dead_mods ctor_ce sec j ==> _`
       (qspec_then `j` (drule_all_then ACCEPT_TAC))) >>
  strip_tac >>
  qpat_assum `!sec j. imm_section_dead_mods ctor_ce sec j <=> _`
    (qspecl_then [`sec`, `j`] (fn regions =>
       qpat_x_assum `imm_section_dead_mods ctor_ce sec j`
         (qx_choosel_then [`ds`,`di`,`doff`,`dty`,`dtv`]
            (map_every assume_tac o CONJUNCTS) o PURE_REWRITE_RULE [regions]))) >>
  Cases_on `(ds,di) = (ssrc,sid)`;

val linked_correctness_section_same_key_tac =
  qpat_x_assum `(ds,di) = (ssrc,sid)`
    (map_every SUBST_ALL_TAC o CONJUNCTS o PURE_REWRITE_RULE [pairTheory.PAIR_EQ]) >>
  linked_correctness_section_offset_tac;

val linked_correctness_section_other_key_tac =
  qpat_assum `!src id off size src' id' off' size'. _ ==>
               loweringStateRelDefs$regions_disjoint off size off' size'`
    (qspecl_then [`ds`,`di`,`doff`,`type_memory_size dtv`,
                  `ssrc`,`sid`,`soff`,`type_memory_size stv`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
  rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >> disch_tac >>
  drule_then strip_assume_tac (cj 1 ctorDeployDeadSectionTheory.mem_dead_bytes_range) >>
  decide_tac;

val linked_correctness_section_frame_tac =
  qexistsl_tac [`stv`,`sv`] >>
  conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
  conj_tac >- FIRST_ASSUM ACCEPT_TAC >> simp[NoAsms] >>
  conj_tac;

val linked_correctness_section_memory_tac =
  MATCH_MP_TAC (Q.INST [`tenv` |-> `get_tenv cx`, `ty` |-> `sty`, `sec1` |-> `sec`]
    ctorDeployDeadSectionRelTheory.section_evaluated_value_memory_frame) >>
  asm_rewrite_tac[];

val linked_correctness_section_mask_tac =
  MATCH_MP_TAC (Q.INST [`b1` |-> `mem_bytes_at soff (type_memory_size stv) sec`]
    ctorDeployDeadSectionRelTheory.section_used_mask_transport) >>
  simp[valueEncodingPropsTheory.LENGTH_mem_bytes_at];

val linked_correctness_section_slice_tac =
  qx_gen_tac `k` >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `soff + k < LENGTH sec /\ soff + k < LENGTH sec'` by decide_tac >>
  simp[valueEncodingProofsTheory.EL_mem_bytes_at];

val linked_correctness_section_support_tac =
  qpat_assum `!j. soff <= j /\ j < soff + type_memory_size stv /\ _ ==> _`
    MATCH_MP_TAC >>
  conj_tac >- decide_tac >> conj_tac >- decide_tac >>
  SUBST1_TAC (Q.SPECL [`k`, `soff`] arithmeticTheory.ADD_COMM) >>
  MATCH_MP_TAC (Q.INST [`tenv` |-> `get_tenv cx`, `ty` |-> `sty`, `v` |-> `sv`]
    ctorDeployDeadSectionRelTheory.section_evaluated_value_mask_support) >>
  asm_rewrite_tac[];

(* A declared immutable exists at entry; evaluation preserves the type of
   that same qualified cell even when its value changes. *)
val linked_correctness_installed_type_goal =
  Q.SUBGOAL_THEN `!obs installed rqs src id ty tv v.
    load_contract (SOME (MAP SND (call_trace es))) obs am tx mods exps =
      INL (installed,rqs) /\
    FLOOKUP env.bare_globals (src,id) = SOME ty /\
    FLOOKUP (get_source_immutables src (account_immutables installed tx.target)) id =
      SOME (tv,v) ==>
    evaluate_type (get_tenv cx) ty = SOME tv`
    (mk_asm "linked_correctness_installed_type");

val linked_correctness_installed_type_run_tac =
  map_every qx_gen_tac [`obs`,`installed`,`rqs`,`src`,`id`,`ty`,`tv`,`v`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `eval_stmts cx raw_body (body_src with gas_obs := obs)` >>
  rename1 `eval_stmts cx raw_body _ = (res,ee)` >>
  qpat_assum `!gs res src. eval_stmts cx raw_body _ = _ ==> _`
    (drule_then (fn tr =>
      qpat_assum `load_contract _ obs am tx mods exps = INL (installed,rqs)`
        (assume_tac o SIMP_RULE (srw_ss()) [load_contract_def,tr]))) >>
  qpat_assum `eval_stmts cx raw_body _ = (res,ee)`
    (assume_tac o MATCH_MP vyperEvalPreservesScopesTheory.eval_stmts_preserves_tv);

val linked_correctness_installed_type_map_tac =
  `installed.immutables = ee.immutables` by
    (qpat_assum `source_finish res ee = INL (installed,rqs)` mp_tac >>
     Cases_on `res` >>
     simp[NoAsms, Abbr `source_finish`, AllCaseEqs()] >>
     strip_tac >>
     qpat_assum `finalize_pending_deletions _ = installed` (SUBST1_TAC o SYM) >>
     simp[NoAsms, vyperInterpreterTheory.abstract_machine_from_state_def]);

val linked_correctness_installed_type_entry_tac =
  `env_immutables_consistent env cx (body_src with gas_obs := obs)` by
    (`(body_src with gas_obs := obs).immutables = es0.immutables` by
       simp[NoAsms, Abbr `body_src`] >>
     qpat_assum `(body_src with gas_obs := obs).immutables = es0.immutables`
       (PURE_REWRITE_TAC o single o MATCH_MP
          vyperTypeInitialStateTheory.env_immutables_consistent_immutables_cong) >>
     qpat_assum `env_consistent env cx es0`
       (ACCEPT_TAC o cj 3 o PURE_REWRITE_RULE [vyperTypeInvariantsTheory.env_consistent_def])) >>
  qpat_assum `env_immutables_consistent env cx _`
    (fn h => let val clauses = PURE_REWRITE_RULE [vyperTypeInvariantsTheory.env_immutables_consistent_def] h
             in map_every assume_tac [cj 1 clauses, cj 2 clauses] end) >>
  (Q.SUBGOAL_THEN `?tv0 v0. FLOOKUP (get_source_immutables src
      (case ALOOKUP (body_src with gas_obs := obs).immutables cx.txn.target of
         SOME m => m | NONE => [])) id = SOME (tv0,v0)`
      (qx_choosel_then [`tv0`,`v0`] assume_tac) >-
    (qpat_assum `!src id ty. FLOOKUP env.bare_globals _ = _ ==> _`
       (drule_then mp_tac) >> simp[NoAsms, optionTheory.IS_SOME_EXISTS, GSYM pairTheory.EXISTS_PROD]));

val linked_correctness_installed_type_finish_tac =
  `evaluate_type (get_tenv cx) ty = SOME tv0` by
    (qpat_assum `!src id ty tv v. FLOOKUP env.bare_globals _ = _ /\ _ ==> _`
       (drule_all_then ACCEPT_TAC)) >>
  Q.SUBGOAL_THEN `?v1. FLOOKUP (get_source_immutables src
      (account_immutables installed tx.target)) id = SOME (tv0,v1)`
    (qx_choose_then `v1` mp_tac) >-
    (qpat_assum `cx.txn.target = tx.target` (SUBST1_TAC o SYM) >>
     qpat_assum `installed.immutables = ee.immutables` (fn map_eq =>
       simp[NoAsms, account_immutables_def, vyperStateTheory.empty_immutables_def, map_eq]) >>
     irule vyperTypeEnvPreservationTheory.preserves_tv_immutables_type_preserved >>
     qexistsl_tac [`body_src with gas_obs := obs`,`v0`] >>
     conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  qpat_assum `FLOOKUP (get_source_immutables src (account_immutables installed tx.target)) id = SOME (tv,v)`
    (fn cell => qpat_assum `evaluate_type (get_tenv cx) ty = SOME tv0` (fn typ =>
       simp[NoAsms,cell,typ]));

Resume e2e_deploy_correctness_mods[linked_present_deploy_accepted_value_body]:
  (linked_positive_epilogue_goal >-
    (linked_positive_epilogue_alloc_producers_tac >> linked_positive_epilogue_copy_producers_tac >>
     linked_positive_epilogue_run_producers_tac >>
     linked_positive_epilogue_setup_tac >> linked_positive_epilogue_entry_tac >>
     (linked_positive_epilogue_imm_ghost_goal >- linked_positive_epilogue_imm_ghost_tac) >>
     linked_positive_epilogue_fresh_tac >> linked_positive_epilogue_alloc_tac >>
     linked_positive_epilogue_open_alloc_tac >> linked_positive_epilogue_alloc_ghost_tac >>
     (linked_positive_epilogue_after_alloc_goal >- linked_positive_epilogue_after_alloc_proof) >>
     linked_positive_epilogue_after_alloc_tac >> linked_positive_epilogue_add_tac >>
     linked_positive_epilogue_after_add_tac >> linked_positive_epilogue_mcopy_tac >>
     linked_positive_epilogue_after_mcopy_tac >> linked_positive_epilogue_codecopy_join_tac >>
     linked_positive_epilogue_after_codecopy_tac >> linked_positive_epilogue_run_halt_tac >> linked_positive_epilogue_identify_halt_tac >>
     linked_positive_epilogue_return_check_tac >> linked_positive_epilogue_scalar_checks_tac >>
     linked_positive_epilogue_begin_block_tac >>
     linked_positive_epilogue_next (`G`,`tn`,`s`,`i0`,`u0`) `Abbrev (s1 = _)`
       [`step_prov [] G i0 u0 = G1`,`step_taint i0 s u0 tn = tn1`] >>
     linked_positive_epilogue_next (`G1`,`tn1`,`s1`,`i1`,`u1`) `Abbrev (s2 = _)`
       [`step_prov [] G1 i1 u1 = G2`,`step_taint i1 s1 u1 tn1 = tn2`] >>
     linked_positive_epilogue_next (`G2`,`tn2`,`s2`,`i2`,`u2`) `Abbrev (s3 = _)`
       [`step_prov [] G2 i2 u2 = G2`,`step_taint i2 s2 u2 tn2 = tn3`] >>
     linked_positive_epilogue_next (`G2`,`tn3`,`s3`,`i3`,`u3`) `Abbrev (s4 = _)`
       [`step_prov [] G2 i3 u3 = G2`,`step_taint i3 s3 u3 tn3 = tn4`] >>
     linked_positive_epilogue_finish_block_tac)) >>
  linked_ctor_active_contract_tac >>
  linked_ctor_checker_calls_tac >>
  linked_ctor_struct_args_tac >>
  linked_ctor_rewritten_supported_stmts_tac >>
  linked_ctor_decode_expr_reflect_tac >>
  linked_ctor_decode_occurrence_tac >>
  linked_ctor_subst_idempotent_tac >>
  linked_ctor_registration_fields_tac >>
  linked_ctor_package_fields_tac >>
  linked_ctor_transport_contract_tac >>
  linked_ctor_stmts_env_code_tac >>
  linked_ctor_conditional_body_tac >>
  (linked_ctor_return_fields_goal_tac >- linked_ctor_return_fields_tac) >>
  linked_ctor_return_fragment_tac
  >- (linked_ctor_return_open_fragment_tac >>
      (linked_ctor_return_jump_entry_tac >- linked_ctor_return_jmp_code_tac) >>
      (linked_ctor_return_landing_tac >- linked_ctor_return_alloca_tac) >>
      (linked_ctor_return_inv_goal_tac >- linked_ctor_return_inv_tac) >>
      linked_ctor_return_epilogue_tac >> linked_ctor_return_outcome_tac >>
      (conj_tac >- ((linked_ctor_return_prepend_tac >- linked_ctor_return_jmp_path_tac) >>
                    linked_ctor_return_append_tac)) >>
      linked_ctor_return_post_tac) >>
  linked_ctor_constant_guards_tac >>
  linked_ctor_constant_cells_tac >>
  linked_ctor_constant_folds_tac >>
  linked_ctor_error_annotation_tac >>
  linked_ctor_error_resolution_tac >>
  linked_ctor_custom_errors_tac >>
  (linked_ctor_zero_epilogue_ptr_goal >-
   (linked_ctor_zero_epilogue_setup_tac >> linked_ctor_zero_epilogue_alloc_tac >>
    linked_ctor_zero_epilogue_alloc_step_tac >> linked_ctor_zero_epilogue_alloc_exec_tac >>
    linked_ctor_zero_epilogue_alloc_fmp_tac >>
    linked_ctor_zero_epilogue_alloc_frame_tac >>
    linked_ctor_zero_epilogue_copy_tac >> linked_ctor_zero_epilogue_return_tac)) >>
  linked_ctor_uniform_marked_tail_tac >>
  linked_ctor_epilogue_run_tac >>
  pop_assum (mk_asm "linked_epilogue_raw") >>
  linked_ctor_replacement_no_risky_tac >>
  linked_ctor_replacement_access_tac >>
  linked_ctor_constant_replacement_tac >>
  linked_ctor_constant_roots_tac >>
  linked_ctor_constant_entry_tac >>
  linked_ctor_checked_entry_env_tac >>
  linked_ctor_immutable_guards_tac >>
  linked_ctor_source_well_typed_tac >>
  linked_ctor_source_scope_tac >>
  linked_ctor_source_accounts_tac >>
  linked_ctor_send_value_tac >>
  linked_ctor_paid_accounts_tac >>
  linked_ctor_env_consistency_tac >>
  linked_ctor_bare_globals_layout_tac
  >- (linked_ctor_bare_globals_layout_setup_tac >>
      linked_ctor_bare_globals_regions_tac >>
      linked_ctor_bare_globals_layout_head_tac >>
      (conj_tac >- (linked_ctor_bare_globals_disjoint_tac >>
                    linked_ctor_bare_globals_disjoint_finish_tac)) >>
      linked_ctor_bare_globals_modules_tac) >>
  linked_ctor_alloc_env_tac >>
  linked_ctor_typed_allocation_tac >>
  linked_ctor_register_domain_tac >>
  linked_ctor_formal_domain_tac >>
  linked_ctor_post_registration_domain_tac >>
  linked_ctor_registration_map_tac >>
  linked_ctor_registered_pointers_tac >>
  linked_ctor_formal_pointers_tac >>
  linked_ctor_formal_types_tac >>
  linked_correctness_abort_transport_tac >>
  linked_correctness_halt_cases_tac >>
  (linked_correctness_halt_transport_goal >-
   (linked_correctness_halt_transport_setup_tac >>
    (conj_tac >- ((linked_correctness_halt_accounts_setup_tac >-
                   linked_correctness_halt_accounts_mask_tac) >>
                  linked_correctness_halt_accounts_compose_tac >>
                  linked_correctness_halt_accounts_storage_tac)) >>
    (conj_tac >- linked_correctness_halt_transient_tac) >>
    (conj_tac >- simp[]) >>
    (conj_tac >- linked_correctness_halt_requests_tac) >>
    linked_correctness_halt_bytes_tac >>
    (linked_correctness_halt_suffix_goal >-
     (linked_correctness_halt_suffix_rule_tac >-
      ((conj_tac >- linked_correctness_halt_length_tac) >>
       linked_correctness_halt_live_bytes_tac) >>
      disch_then ACCEPT_TAC)) >>
    map_every qexists_tac [`sec`, `sec'`] >> rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
  linked_ctor_expr_metadata_tac >>
  linked_ctor_struct_fields_tac >>
  linked_ctor_flags_tac >>
  linked_ctor_flag_fold_tac >>
  linked_ctor_flag_index_helpers_tac >>
  linked_ctor_flag_namespace_tac >>
  linked_ctor_flag_member_tac >>
  (linked_ctor_const_name_free_tac >- (linked_ctor_const_name_free_body_tac >>
    (linked_ctor_const_key_tac >- linked_ctor_const_key_member_tac) >>
    linked_ctor_access_free_root_tac >> linked_ctor_subst_expr_roots_tac >>
    linked_ctor_subst_stmt_roots_tac)) >>
  linked_ctor_stmts_exprs_ok_tac >>
  linked_ctor_source_observation_tac ``es:execution_state`` >>
  linked_ctor_observed_env_tac ``es:execution_state`` >>
  linked_ctor_return_decl_tac >>
  (linked_ctor_return_miss_goal >- linked_ctor_return_miss_tac) >>
  linked_ctor_return_key_member_tac >>
  (linked_ctor_return_hit_goal >- linked_ctor_return_hit_tac) >>
  linked_ctor_return_checked_keys_tac >>
  linked_ctor_return_mod_key_tac >>
  (linked_ctor_return_mods_goal >- linked_ctor_return_mods_tac) >>
  linked_ctor_return_types_tac >>
  (linked_ctor_bare_endpoint_tac >- linked_ctor_bare_endpoint_proof_tac) >>
  linked_ctor_bare_slot_source_tac >>
  linked_ctor_bare_slot_frame_tac >>
  (linked_ctor_bare_classify_tac >-
   (linked_ctor_bare_classify_prefix_tac >> linked_ctor_bare_classify_checker_tac)) >>
  linked_ctor_bare_slot_cleanup_tac >>
  linked_ctor_bare_placement_tac >>
  (linked_ctor_immutable_region_type_goal_tac >-
   (linked_ctor_immutable_region_type_tac >>
    (linked_ctor_immutable_region_open_tac >- linked_ctor_immutable_region_lookup_tac) >>
    linked_ctor_immutable_region_size_tac)) >>
  linked_ctor_checked_storage_tables_tac >>
  linked_ctor_checked_map_projections_tac >>
  linked_ctor_checked_place_tables_tac >>
  linked_ctor_checked_bare_hash_tac >>
  linked_deploy_registration_inputs_tac >>
  (linked_deploy_registration_replay_entry_tac >-
    (qx_gen_tac `vi` >> disch_tac >>
     linked_deploy_registration_prefix_tac >>
     linked_deploy_registration_decode_tac >>
     linked_deploy_registration_path_tac >>
     linked_deploy_registration_replay_bytes_tac >>
     linked_deploy_registration_replay_finish_tac)) >>
  linked_ctor_builder_src_other_tac >>
  linked_ctor_builder_src_absent_tac >>
  linked_ctor_builder_src_decl_tac >>
  linked_ctor_builder_mods_absent_tac >>
  linked_ctor_builder_mods_var_tac >>
  linked_ctor_builder_mods_hash_tac >>
  linked_ctor_builder_decl_tac >>
  linked_ctor_decode_unconditional_tac >>
  linked_ctor_support_unconditional_tac >>
  linked_ctor_install_epilogue_exit_tac >>
  linked_ctor_install_epilogue_placement_tac >>
  linked_ctor_install_epilogue_reserved_tac >>
  linked_ctor_install_epilogue_fresh_tac >>
  linked_ctor_registered_imm_transport_tac >>
  linked_ctor_registered_return_buf_tac >>
  (linked_ctor_registered_control_goal >- linked_ctor_registered_control_tac) >>
  linked_ctor_dalloca_windows_tac >>
  linked_ctor_raw_headroom_tac >>
  linked_ctor_variant_headroom_tac ``es:execution_state`` >>
  (linked_ctor_registered_headroom_goal >-
   (linked_ctor_registered_headroom_setup_tac >> linked_ctor_registered_headroom_transfer_tac)) >>
  linked_ctor_frame_headroom_tac ``es:execution_state`` >>
  (linked_ctor_registered_ghost_goal >-
   (linked_ctor_registered_ghost_open_tac
    >- (linked_ctor_registered_ghost_frame_tac >> rpt conj_tac
        >- linked_ctor_registered_ghost_low_tac
        >- linked_ctor_registered_ghost_imm_tac >> FIRST_ASSUM ACCEPT_TAC) >>
    linked_ctor_registered_ghost_lookup_tac >> linked_ctor_registered_ghost_support_tac >>
    linked_ctor_registered_ghost_scope_tac >> linked_ctor_registered_ghost_bytes_tac)) >>
  linked_ctor_install_epilogue_static_tac >>
  (linked_ctor_install_epilogue_open_tac >-
   (linked_ctor_install_epilogue_entry_tac >> linked_ctor_install_epilogue_horizon_tac >>
    (linked_ctor_install_epilogue_run_tac >-
     (rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE asm "epilogue_entry_state_rel" ACCEPT_TAC))) >>
    linked_ctor_install_epilogue_run_result_tac >>
    (linked_ctor_install_epilogue_ptr_goal >-
      (linked_ctor_install_epilogue_ptr_setup_tac >> Cases_on `imm_len_mods mods = 0`
       >- (linked_ctor_install_epilogue_zero_code_tac >> linked_ctor_install_epilogue_zero_tac) >>
       linked_ctor_install_epilogue_ptr_fresh_tac >> linked_ctor_install_epilogue_positive_tac >>
       conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
       conj_tac >- simp[NoAsms, Abbr `linked_ret_DF`] >>
       qexistsl_tac [`H`,`body_ce`,`tail_codepos`,`ctor_ce`,`cx`,`src`,`st_epilogue`,
                    `tail_final`,`imm`,`LENGTH runtime_bc`,`st_final`] >>
       rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE simp[NoAsms, Abbr `linked_ret_DF`]))) >>
    linked_ctor_install_epilogue_endpoint_tac)) >>
  disch_tac >>
  linked_ctor_expr_roots_join_tac >>
  linked_ctor_expr_table_join_tac >>
  linked_ctor_expr_layout_join_tac >>
  (linked_ctor_observed_expr_inv_tac ``es:execution_state`` >-
   (linked_ctor_observed_expr_project_tac ``es:execution_state`` >>
    linked_ctor_observed_expr_finish_tac)) >>
  linked_ctor_body_except_frame_tac ``es:execution_state`` >>
  linked_ctor_body_at_return_frame_tac >>
  linked_ctor_subst_control_tac >>
  linked_ctor_source_admissible_tac ``es:execution_state`` >>
  linked_ctor_paired_env_tac >>
  linked_ctor_body_dead_low_tac >>
  (linked_correctness_section_goal >-
   (linked_correctness_section_setup_tac >>
    (linked_correctness_section_live_goal >-
     (linked_correctness_section_live_tac
      >- linked_correctness_section_same_key_tac >>
      linked_correctness_section_other_key_tac)) >>
    (linked_correctness_section_frame_tac >- linked_correctness_section_memory_tac) >>
    linked_correctness_section_mask_tac >> linked_correctness_section_slice_tac >>
    linked_correctness_section_support_tac)) >>
  linked_entry_machine_slots_tac >>
  (linked_entry_machine_parts_goal_tac ``es:execution_state`` >-
   (map_every qx_gen_tac [`vi`,`actual`,`gs`,`H`] >>
    disch_then (map_every assume_tac o CONJUNCTS) >>
    qabbrev_tac `entry_src = es0 with <|gas_obs := gs;
      outcomes := SOME (MAP SND (call_trace es))|>` >>
    linked_entry_machine_variant_tac >>
    linked_entry_machine_frame_tac ``es:execution_state`` >>
    linked_entry_machine_world_tac ``es:execution_state`` >>
    (sg `call_ctx_rel cx.txn actual.vs_call_ctx actual.vs_tx_ctx actual.vs_block_ctx` >-
      (linked_entry_machine_call_fields_tac ``es:execution_state`` >>
       linked_entry_machine_call_hashes_tac ``es:execution_state``)) >>
    `actual.vs_call_ctx.cc_address = cx.txn.target` by linked_entry_machine_address_tac >>
    rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE linked_entry_machine_conjuncts_tac))) >>
  linked_entry_immutable_tac ``es:execution_state`` >>
  (linked_checked_ctor_entry_goal >-
   (linked_checked_ctor_root_tac >> linked_checked_ctor_root_empty_tac >>
    linked_checked_ctor_root_bound_tac >>
    (linked_checked_ctor_prepare_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
    linked_checked_ctor_open_prepared_tac >> linked_checked_ctor_prepared_tac >>
    linked_checked_ctor_suffix_inputs_tac >>
    (linked_checked_ctor_suffix_tac >- linked_checked_ctor_suffix_premises_tac) >>
    linked_checked_ctor_suffix_open_tac >>
    (linked_checked_ctor_join_origin_goal >- linked_checked_ctor_join_origin_tac) >>
    linked_checked_ctor_join_mem_tac >>
    linked_checked_ctor_cursor_tac >> linked_checked_ctor_end_fmp_tac >>
    linked_checked_ctor_low_tac >> linked_checked_ctor_bytes_tac >>
    (linked_checked_ctor_formal_regions_goal >- linked_checked_ctor_formal_regions_tac) >>
    linked_checked_ctor_region_tac >> linked_checked_ctor_imm_tac >>
    linked_checked_ctor_finish_tac)) >>
  linked_ctor_paid_fields_tac >>
  linked_ctor_paid_backends_tac ``es:execution_state`` >>
  linked_ctor_entry_storage_tac ``es:execution_state`` >>
  linked_registered_state_frame_tac ``es:execution_state`` >>
  linked_ctor_replay_source_tac ``es:execution_state`` >>
  (linked_correctness_installed_type_goal >-
   (linked_correctness_installed_type_run_tac >>
    linked_correctness_installed_type_map_tac >>
    linked_correctness_installed_type_entry_tac >>
    linked_correctness_installed_type_finish_tac)) >>
  (linked_ctor_replay_prefix_goal_tac true ``es:execution_state`` >-
    (reverse (linked_ctor_replay_prefix_open_tac ``es:execution_state`` >-
       linked_ctor_replay_bad_tac ``es:execution_state``) >-
    (linked_ctor_replay_exempt_open_tac >> linked_ctor_replay_exempt_eval_tac >>
     linked_ctor_replay_exempt_finish_tac >> linked_ctor_replay_exempt_error_tac) >>
     linked_ctor_replay_started_tac >>
     (conj_tac >- linked_ctor_replay_eval_tac) >>
     (conj_tac >- linked_ctor_replay_trace_tac) >>
     linked_ctor_replay_path_tac)) >>
  linked_ctor_terminal_install_tac >>
  (linked_ctor_terminal_exit_goal_tac >-
   (linked_ctor_terminal_exit_open_tac
    >~ [`expr_exit post_res _`] >- linked_ctor_terminal_exit_expr_tac >>
    simp[])) >>
  (linked_ctor_fallthrough_goal_tac >-
   (linked_ctor_fallthrough_open_tac >>
    (linked_ctor_fallthrough_fmp_goal_tac >- linked_ctor_fallthrough_fmp_tac) >>
    (linked_ctor_fallthrough_inv_goal_tac >-
      (linked_ctor_fallthrough_inv_tac >>
       (conj_tac >- linked_ctor_fallthrough_state_tac) >>
       (conj_tac >- linked_ctor_fallthrough_imm_tac) >>
       linked_ctor_fallthrough_ghost_tac)) >>
    linked_ctor_fallthrough_epilogue_tac >>
    (conj_tac >-
     ((linked_ctor_fallthrough_jmp_goal_tac >- linked_ctor_fallthrough_jmp_tac) >>
      linked_ctor_fallthrough_append_tac)) >>
    linked_ctor_fallthrough_install_tac >>
    (conj_tac >- linked_ctor_fallthrough_install_state_tac) >>
    (conj_tac >- linked_ctor_fallthrough_install_imm_tac) >>
    rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
  (linked_ctor_terminal_replay_goal_tac >-
   (reverse linked_ctor_terminal_replay_open_tac >-
      (linked_ctor_terminal_replay_exit_tac >> linked_ctor_terminal_replay_exit_close_tac) >>
    linked_ctor_terminal_replay_landed_tac >>
    linked_ctor_terminal_replay_land_fields_tac >>
    linked_ctor_terminal_replay_land_epilogue_tac >>
    linked_ctor_terminal_replay_land_close_tac)) >>
  linked_ctor_native_source_tac >> linked_ctor_native_posts_tac >> linked_ctor_native_land_tac >>
  (linked_ctor_native_replay_projection_goal_tac true ``es:execution_state`` >-
   (linked_ctor_native_replay_open_tac >- (disj1_tac >> FIRST_ASSUM ACCEPT_TAC) >>
    (linked_ctor_native_replay_terminal_tac >-
     (linked_ctor_native_replay_premises_tac >>
      (conj_tac >- linked_ctor_native_replay_q_tac) >>
      linked_ctor_native_replay_r_tac)) >>
    linked_ctor_native_replay_close_tac)) >>
  (linked_registered_body_source_replay_goal >-
   (linked_registered_body_source_replay_tac >> linked_registered_body_source_witness_tac)) >>
  (linked_registered_body_goal_tac ``es:execution_state`` >-
   (linked_registered_body_open_tac >>
    (linked_registered_body_local_ptr_goal >-
     linked_registered_body_local_ptr_tac) >>
    linked_registered_body_static_tac >>
    (linked_registered_body_state_tac >- linked_registered_body_state_premises_tac) >>
    linked_registered_body_state_close_tac >>
    linked_registered_body_control_tac >> linked_registered_body_headroom_tac >>
    (linked_registered_body_ghost_goal >-
     (linked_registered_body_ghost_open_tac >- linked_registered_body_ghost_frame_tac >>
      linked_registered_body_formals_tac >> linked_ctor_registered_ghost_bytes_tac)) >>
    (linked_registered_body_apply_tac >- linked_registered_body_apply_premises_tac) >>
    linked_registered_body_apply_close_tac)) >>
  (linked_registered_terminal_projection_goal_tac true ``es:execution_state`` >-
   ((linked_registered_terminal_tac >- linked_registered_terminal_premises_tac) >>
    disch_then ACCEPT_TAC)) >>
  (linked_registered_terminal_goal_tac ``es:execution_state`` >-
   linked_registered_terminal_forget_eval_tac) >>
  (linked_correct_exit_goal >-
   (linked_correct_exit_root_tac >> linked_correct_exit_run_tac >>
    linked_correct_exit_blocks_tac >> linked_correct_exit_mem_blocks_tac >>
    linked_correct_exit_ptr_blocks_tac >> linked_correct_exit_memory_entry_tac >>
    (linked_correct_exit_memory_goal >- linked_correct_exit_memory_tac) >>
    linked_correct_exit_prewalk_tac >> linked_correct_exit_dload_tac >>
    linked_correct_exit_cut_tac >> linked_correct_exit_events_tac)) >>
  (linked_correct_exit_producer_goal >- linked_correct_exit_producer_tac) >>
  linked_correctness_mark_selection_tac "linked_ctor_registered_terminal_eval" >>
  linked_correctness_static_focus_tac >>
  (linked_raw_post_goal_tac >-
   (linked_raw_post_observation_tac >>
    (reverse (disch_then (DISJ_CASES_THEN2 mp_tac (DISJ_CASES_THEN2 mp_tac mp_tac)))
      >- linked_raw_post_abort_tac
      >- linked_raw_post_halt_tac) >>
    linked_raw_post_install_open_tac >> linked_raw_post_install_source_tac >>
    (linked_raw_post_install_effects_tac >- linked_raw_post_install_accounts_tac) >>
    rpt (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >>
    linked_raw_post_install_runtime_tac >> linked_raw_post_install_path_fields_tac >>
    linked_raw_post_install_label_tac >>
    (linked_raw_post_install_slice_tac >-
     (linked_raw_post_install_slice_finish_tac >> REFL_TAC)) >>
    linked_entry_immutable_section_tac >> linked_raw_post_install_cells_tac >>
    linked_raw_post_install_section_tac >> linked_raw_post_install_module_tac >>
    linked_raw_post_install_imm_tac >>
    linked_raw_post_install_imm_finish_tac >> linked_raw_post_install_bytes_window_tac >>
    linked_raw_post_install_bytes_tac)) >>

  linked_focus_entry_static_tac >>
  (linked_focus_entry_phi_goal >- linked_focus_entry_phi_tac) >>
  linked_focus_entry_budget_tac >>
  (linked_focus_dead_regions_goal >- linked_focus_dead_regions_tac) >>
  linked_focus_dead_layout_tac >>
  (linked_focus_dead_region_goal >- linked_focus_dead_region_tac) >>
  (linked_focus_dead_section_goal >-
    (linked_focus_dead_section_setup_tac >>
     (linked_focus_dead_section_frame_goal >- linked_focus_dead_section_frame_tac) >>
     linked_focus_dead_section_finish_tac)) >>
  (linked_focus_dead_wf_goal >- linked_focus_dead_wf_tac) >>
  (linked_focus_producer_goal >-
    (linked_focus_variant_tac >>
     (linked_focus_headroom_goal >- linked_focus_headroom_tac) >>
     linked_focus_safe_tac >>
     (impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >> disch_tac >>
     linked_focus_dload_tac >> disch_then (mk_asm "linked_focus_dload_rule") >>
     linked_focus_events_tac >>
     linked_focus_producer_witness_tac >>
     (conj_tac >-
       (linked_focus_dload_apply_tac >> rpt conj_tac >>
        (FIRST_ASSUM ACCEPT_TAC ORELSE (qexists_tac `focus_callee` >> FIRST_ASSUM ACCEPT_TAC)))) >>
     conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>

  `unit_alloca_budget deploy_unit.cu_context +
    32 * ctx_dload_count deploy_unit.cu_context <= w2n fmp` by
    (qpat_assum `imm_len_mods mods + _ + _ <= w2n fmp` mp_tac >> decide_tac) >>
  (linked_correctness_slot_packet_goal >-
   (linked_correctness_slot_apply_tac >> linked_correctness_slot_select_tac >>
    (impl_tac >- linked_correctness_slot_select_premises_tac) >>
    linked_correctness_slot_filling_tac >> linked_correctness_slot_exit_tac >>
    (impl_tac >- linked_correctness_slot_exit_premises_tac) >> disch_then ACCEPT_TAC)) >>
  asm "linked_correctness_slot_packet" mp_tac >>
  (impl_tac >-
   (qx_gen_tac `gs` >> linked_correctness_selected_tac `gs` >>
    disch_then (DISJ_CASES_THEN2 mp_tac mp_tac)
    >- (disch_then (CONJUNCTS_THEN2
          (qx_choosel_then [`focus_h`,`focus_leaf`,`focus_pg`,`focus_g`,`focus_tn`,`focus_finish`]
             assume_tac) (K ALL_TAC)) >>
        asm "linked_correctness_focus_producer"
          (qspecl_then [`raw_entry gs`,`markf gs`,`focus_h`,`focus_leaf`,`focus_pg`,
                        `focus_g`,`focus_tn`,`focus_finish`] mp_tac) >>
        asm_rewrite_tac[]) >>
    disch_then (qx_choosel_then [`res`,`ee`,`terminal`,`Gend`,`tnend`]
      (map_every assume_tac o CONJUNCTS)) >>
    `valid_horizon cx (initial_state am []) (storage_trace_horizon ee.storage_trace)
       ee.storage_trace` by
      (qpat_assum `storage_trace_domain cx (initial_state am []) ee.storage_trace`
        (ACCEPT_TAC o PURE_REWRITE_RULE [storage_trace_domain_def])) >>
    qpat_assum `!H. valid_horizon cx (initial_state am []) H ee.storage_trace ==> _`
      (drule_then (assume_tac o CONJUNCT1)) >>
    asm "linked_correct_exit_producer"
      (qspecl_then [`raw_entry gs`,`markf gs`,`storage_trace_horizon ee.storage_trace`,
                    `terminal`,`Gend`,`tnend`] mp_tac) >>
    (impl_tac >- (rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE
      asm "linked_correctness_dead_wf" MATCH_ACCEPT_TAC))) >>
    asm_rewrite_tac[])) >>
  disch_then (qx_choosel_then [`slots`,`sites`,`unused`]
    (map_every assume_tac o CONJUNCTS)) >>
  `!obs H terminal u. exit_result terminal /\
     H = storage_trace_horizon (deploy_storage_trace_mods (SOME os) obs am tx mods exps) /\
     deploy_post obs terminal /\ dead_result_rel (linked_ret_DF H) terminal u ==>
     deploy_post obs u` by
    (map_every qx_gen_tac [`obs`,`H`,`terminal`,`u`] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     (Q.SUBGOAL_THEN `(?a p. terminal = Abort a p) \/ (?p. terminal = Halt p)` mp_tac >-
       (qpat_assum `deploy_post obs terminal` mp_tac >>
        simp[NoAsms, Abbr `deploy_post`] >>
        namedCases_on `load_contract (SOME os) obs am tx mods exps` ["loaded","exc"]
        >- (PairCases_on `loaded` >> Cases_on `terminal` >> simp[NoAsms]) >>
        Cases_on `exc` >> Cases_on `terminal` >> simp[NoAsms] >>
        rename1 `case ab of Revert_abort => _ | ExHalt_abort => _` >>
        Cases_on `ab` >> simp[NoAsms])) >>
     disch_then (DISJ_CASES_THEN2 (qx_choosel_then [`a`,`p`] SUBST_ALL_TAC)
                                 (qx_choose_then `p` SUBST_ALL_TAC))
     >- (qpat_assum `!gs H a s u'. _ /\ deploy_post gs (Abort a s) /\ _ ==> _`
           (qspecl_then [`obs`,`H`,`a`,`p`,`u`] mp_tac) >>
         (impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
     qpat_assum `!gs H p u'. deploy_post gs (Halt p) /\ _ ==> ?installed rqs p'. _ /\ u' = Halt p'`
       (qspecl_then [`obs`,`H`,`p`,`u`] mp_tac) >>
     (impl_tac >- (conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
     disch_then (qx_choosel_then [`installed_am`,`source_rqs`,`opt_post`]
       (CONJUNCTS_THEN2 assume_tac SUBST_ALL_TAC)) >>
     qpat_assum `!gs H ia rqs p p'. _ ==> accounts_agree H _ ia.accounts _ /\ _`
       (qspecl_then [`obs`,`H`,`installed_am`,`source_rqs`,`p`,`opt_post`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `load_contract (SOME os) obs am tx mods exps = INL (installed_am,source_rqs)` (fn ld =>
       qpat_assum `H = storage_trace_horizon _` (fn hor =>
         simp[NoAsms, Abbr `deploy_post`, ld, GSYM hor])) >>
     rpt (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >>
     Cases_on `ALOOKUP installed_am.sources tx.target = NONE` >>
     pop_assum (fn src => simp[NoAsms, src] >>
       qpat_x_assum `if ALOOKUP installed_am.sources tx.target = NONE then _ else _`
         (mp_tac o SIMP_RULE bool_ss [src]))
     >- simp[NoAsms] >>
     disch_then (qx_choosel_then [`sec`,`sec'`] (map_every assume_tac o CONJUNCTS)) >>
     qexists_tac `sec'` >> conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
     qpat_assum `!imms sec sec'. _ ==> immutables_section_rel_mods mods imms sec'`
       (qspecl_then [`account_immutables installed_am tx.target`,`sec`,`sec'`] mp_tac) >>
     (impl_tac >- (rpt (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >> rpt gen_tac >>
       disch_then (map_every assume_tac o CONJUNCTS) >>
       qpat_assum `Abbrev (os = MAP SND (call_trace es))` (fn os_eq =>
         asm "linked_correctness_installed_type"
           (drule_all_then ACCEPT_TAC o PURE_REWRITE_RULE
             [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] os_eq)])))) >>
     disch_then ACCEPT_TAC) >>
  (`!raw. LIST_REL (\slot w. slot = NONE \/ slot = SOME w) slots raw ==>
      (?rest. MAP (\key. key IN gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context)
                 sites = markf (raw ++ [0w]) ++ rest) /\
      !suffix. deploy_storage_ok_mods mods exps am tx os
          (gas_explicit (markf (raw ++ [0w])) (raw ++ [0w]) ++ suffix) ==>
        deploy_source_exempt_mods mods (load_contract (SOME os)
          (gas_explicit (markf (raw ++ [0w])) (raw ++ [0w]) ++ suffix) am tx mods exps) \/
        ?D fr. ctx_sim D deploy_unit.cu_context deploy_out.po_unit.cu_context
                   (raw_entry (raw ++ [0w])) vs /\
               terminates (run_context fr deploy_unit.cu_context (raw_entry (raw ++ [0w]))) /\
               o1_lowered_inv deploy_out.po_unit.cu_context vs /\
               code_end_offset_ok (raw_reachable vs) deploy_out.po_unit.cu_context /\
               !u. dead_result_rel D
                      (run_context fr deploy_unit.cu_context (raw_entry (raw ++ [0w]))) u ==>
                   deploy_post (gas_explicit (markf (raw ++ [0w])) (raw ++ [0w]) ++ suffix) u` by
    (qx_gen_tac `raw` >> disch_tac >>
     qpat_assum `!raw. LIST_REL _ slots raw ==> (?rest. MAP _ sites = _ ++ rest) /\ _`
       (qspec_then `raw` (drule_then (CONJUNCTS_THEN2 assume_tac (mk_asm "linked_fixed_fill")))) >>
     conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
     qx_gen_tac `tail` >> disch_tac >>
     qabbrev_tac `obs = gas_explicit (markf (raw ++ [0w])) (raw ++ [0w]) ++ tail` >>
     Cases_on `deploy_source_exempt_mods mods (load_contract (SOME os) obs am tx mods exps)`
     >- (disj1_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     disj2_tac >> linked_correctness_selected_tac `raw ++ [0w]` >>
     disch_then (DISJ_CASES_THEN2 mp_tac mp_tac)
     >- (disch_then (CONJUNCTS_THEN2 (K ALL_TAC) (DISJ_CASES_THEN
           (qspec_then `tail` mp_tac))) >>
         qpat_assum `Abbrev (obs = _)`
           (PURE_REWRITE_TAC o single o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
         simp[] >> FIRST_ASSUM ACCEPT_TAC) >>
     disch_then (qx_choosel_then [`res`,`ee`,`terminal`,`Gend`,`tnend`]
       (map_every assume_tac o CONJUNCTS)) >>
     asm "linked_raw_post"
       (qspecl_then [`raw_entry (raw ++ [0w])`,`markf (raw ++ [0w])`,`tail`,
                     `res`,`ee`,`terminal`,`Gend`,`tnend`] mp_tac) >>
     qpat_assum `(raw_entry (raw ++ [0w])).vs_gas_readings = _`
       (PURE_REWRITE_TAC o single) >>
     qpat_assum `Abbrev (obs = _)`
       (PURE_REWRITE_TAC o single o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     (impl_tac >- (rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE
       qpat_assum `Abbrev (obs = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
       qpat_assum `!tail. eval_stmts cx raw_body (body_src with gas_obs := _ ++ tail) =
                            (res,ee with gas_obs := tail)` (qspec_then `tail` ACCEPT_TAC)))) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qabbrev_tac `Hsel = storage_trace_horizon ee.storage_trace` >>
     qpat_assum `!H. valid_horizon cx (initial_state am []) H ee.storage_trace ==> _`
       (qspec_then `Hsel` mp_tac) >>
     (impl_tac >- simp[Abbr `Hsel`]) >>
     disch_then (assume_tac o CONJUNCT1) >>
     asm "linked_correct_exit_inputs"
       (qspecl_then [`raw_entry (raw ++ [0w])`,`markf (raw ++ [0w])`,`Hsel`,
                     `terminal`,`Gend`,`tnend`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
     disch_then (CONJUNCTS_THEN2
       (qx_choose_then `fr` (map_every assume_tac o CONJUNCTS))
       (map_every assume_tac o CONJUNCTS)) >>
     asm "linked_fixed_fill" (qspec_then `linked_ret_DF Hsel` mp_tac) >>
     (impl_tac >-
       (conj_tac >- (qexists_tac `fr` >> FIRST_ASSUM ACCEPT_TAC) >>
        conj_tac >- asm "linked_correctness_dead_wf" MATCH_ACCEPT_TAC >>
        conj_tac >- FIRST_ASSUM ACCEPT_TAC >> disch_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
     disch_then (qspec_then `asm_opt_finalizer` mp_tac) >>
     simp_tac bool_ss [] >>
     (impl_tac >- FIRST_ASSUM ACCEPT_TAC) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qexistsl_tac [`linked_ret_DF Hsel`,`fr`] >>
     rpt (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >>
     qpat_assum `run_context fr deploy_unit.cu_context _ = terminal`
       (PURE_REWRITE_TAC o single) >>
     gen_tac >> disch_tac >>
     qpat_assum `!obs H terminal u. _ ==> deploy_post obs u`
       (qspecl_then [`obs`,`Hsel`,`terminal`,`u`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >>
       (FIRST_ASSUM ACCEPT_TAC ORELSE simp[Abbr `Hsel`]))) >>
     disch_then ACCEPT_TAC)) >>
  linked_accepted_correct_mask_post_tac
    `sites` `\key. key IN gas_explicit_sites deploy_unit.cu_context shadow_unit.cu_context`
    `slots` `unused` `markf`
QED

Resume e2e_deploy_correctness_mods[linked_empty_deploy_s4]:
  qabbrev_tac `D = <|d_stor := K (K {}); d_trans := K (K {});
                       d_imm := K {}; d_ret := K {}|>` >>
  `dead_wf D` by simp[Abbr `D`, dead_wf_def] >>
  `FLOOKUP vs.vs_labels "code_end" = SOME (n2w (LENGTH (assemble prog')))` by
    (qpat_assum `FLOOKUP (lo_reloc prog prog') "code_end" = SOME (LENGTH (assemble prog'))`
       (fn lab => simp[NoAsms, Abbr `vs`, opt_entry_state_own_def,
                     finite_mapTheory.FLOOKUP_o_f, lab])) >>
  `code_layout_valid vs` by
    (PURE_REWRITE_TAC [code_layout_valid_def] >>
     conj_tac >- (qexists_tac `assemble prog'` >> FIRST_ASSUM ACCEPT_TAC) >>
     simp[] >>
     qpat_assum `LENGTH (assemble prog') < 65536` mp_tac >>
     simp[NoAsms, wordsTheory.dimword_def, venomLayoutTheory.dimindex_256] >>
     decide_tac) >>
  `o1_run_state_ok vs` by simp[o1_run_state_ok_def] >>
  `w2n vs.vs_initial_fmp <= w2n fmp` by
    (qpat_assum `w2n (opt_entry_state_own prog prog' cplan es).vs_initial_fmp <= w2n fmp`
       mp_tac >> simp[NoAsms, Abbr `vs`]) >>
  `LENGTH vs.vs_data_section < dimword (:256) DIV 2` by
    simp[wordsTheory.dimword_def, venomLayoutTheory.dimindex_256] >>
  `!vi. raw_variant fmp vi vs ==>
    raw_unit_memory_ok deploy_unit.cu_context vi /\
    ptr_discipline (imm_len_mods mods) deploy_unit.cu_context vi /\
    taint_within D deploy_unit.cu_context vi /\
    mem_inv dload_offset_ok deploy_unit.cu_context vi /\
    mem_inv dload_headroom_ok deploy_unit.cu_context vi /\
    mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                             s.vs_code = vi.vs_code /\ s.vs_data_section = vi.vs_data_section)
      deploy_unit.cu_context vi /\
    ?post. run_context 1 deploy_unit.cu_context vi = Halt post /\
      post.vs_returndata = runtime_bc ++ REPLICATE (imm_len_mods mods) 0w /\
      post.vs_accounts = vs.vs_accounts /\ post.vs_transient = vs.vs_transient /\
      post.vs_logs = vs.vs_logs /\ post.vs_pending_deletions = vs.vs_pending_deletions /\
      post.vs_requests = vs.vs_requests` by
    (gen_tac >> strip_tac >>
     `vi = vs with <|vs_fmp := fmp; vs_initial_fmp := fmp;
                         vs_gas_readings := vi.vs_gas_readings|>` by
       (qpat_assum `raw_variant fmp vi vs`
          (mp_tac o PURE_REWRITE_RULE [raw_variant_def, gas_variant_def]) >>
        simp[NoAsms, venom_state_component_equality] >> strip_tac >>
        qpat_assum `fmp = vi.vs_initial_fmp` (fn h =>
          qpat_assum `fmp = vi.vs_fmp` (ACCEPT_TAC o TRANS (SYM h)))) >>
     `code_layout_valid vi /\ vi.vs_fmp = vi.vs_initial_fmp /\
      vi.vs_alloca_next = imm_len_mods mods` by
       (qpat_assum `vi = _` SUBST1_TAC >>
        qpat_assum `code_layout_valid vs` mp_tac >>
        simp[NoAsms, code_layout_valid_def] >> strip_tac >>
        qpat_assum `vs.vs_alloca_next = imm_len_mods mods` ACCEPT_TAC) >>
     mp_tac (Q.INST [`unit` |-> `deploy_unit`, `rp` |-> `rpolicy`,
         `vs` |-> `vi`, `off` |-> `off`]
       (SPEC_ALL linked_empty_deploy_target)) >>
     impl_tac >- (qpat_assum `vi = _` SUBST1_TAC >> simp[]) >>
     disch_then (qx_choosel_then [`vfn`, `vpost`] strip_assume_tac) >>
     mp_tac (Q.INST [`dunit` |-> `deploy_unit`, `vs` |-> `vi`, `D` |-> `D`,
        `func` |-> `vfn`] (SPEC_ALL deploy_selected_memory_mods)) >>
     impl_tac >-
       (rpt conj_tac >>
        FIRST [FIRST_ASSUM ACCEPT_TAC,
               qpat_assum `!D fuel. ptr_safe_blocks D _ fuel _ vfn _ _ _ _`
                 (qspec_then `D` ACCEPT_TAC),
               qpat_assum `vi.vs_fmp = vi.vs_initial_fmp`
                 (fn th => simp[NoAsms, th])]) >>
     disch_then strip_assume_tac >>
     `mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                     s.vs_code = vi.vs_code /\ s.vs_data_section = vi.vs_data_section)
        deploy_unit.cu_context vi` by
       (qspecl_then [`deploy_unit.cu_context`,`"__deploy"`,`vfn`,`"__deploy"`,`vi`]
          mp_tac lowered_unit_dload_in_section >>
        impl_tac >- asm_rewrite_tac[] >>
        simp[mem_inv_raw_reachable] >> strip_tac >> rpt gen_tac >> disch_tac >>
        conj_tac
        >- first_x_assum (drule_then ACCEPT_TAC) >>
        drule_then ACCEPT_TAC o1SafeUptoTheory.raw_reachable_code_data) >>
     `vi.vs_accounts = vs.vs_accounts /\ vi.vs_transient = vs.vs_transient /\
      vi.vs_logs = vs.vs_logs /\ vi.vs_pending_deletions = vs.vs_pending_deletions /\
      vi.vs_requests = vs.vs_requests` by
       (qpat_assum `vi = vs with <|vs_fmp := fmp; vs_initial_fmp := fmp;
                                  vs_gas_readings := vi.vs_gas_readings|>` mp_tac >>
        simp[NoAsms, venom_state_component_equality]) >>
     asm_rewrite_tac[] >> qexists_tac `vpost` >>
     asm_rewrite_tac[]) >>
  `code_end_offset_ok (raw_reachable vs) deploy_out.po_unit.cu_context` by
    (qspecl_then [`D`, `imm_len_mods mods`, `rpolicy`, `deploy_unit`,
                  `deploy_out`, `vs`, `fmp`]
       mp_tac o1StaticPipelineCorrectTheory.o1_pipeline_code_end_offset_ok_static_abort >>
     impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     disch_then (qx_choose_then `vcode` strip_assume_tac) >>
     qpat_assum `!vi. raw_variant _ vi vs ==> _` (drule_then strip_assume_tac) >>
     qpat_x_assum `_ ==> code_end_offset_ok _ _ /\ _` mp_tac >>
     impl_tac >- asm_rewrite_tac[] >>
     disch_then (CONJUNCTS_THEN2 assume_tac (K ALL_TAC)) >>
     qpat_x_assum `code_end_offset_ok (\_ _ _ _. _) _` mp_tac >>
     simp_tac bool_ss [code_end_offset_ok_def, in_static_abort_prefix_def] >>
     metis_tac[replay_exit_raw_call_ctx]) >>
  qspecl_then [`D`, `imm_len_mods mods`, `rpolicy`, `deploy_unit`,
                `deploy_out`, `vs`, `fmp`]
    mp_tac o1PipelineCorrectTheory.run_venom_pipeline_correct >>
  impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  disch_then (qx_choose_then `vrun` strip_assume_tac) >>
  qpat_assum `!vi. raw_variant _ vi vs ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `_ ==> ctx_sim D _ _ vrun vs /\ _` mp_tac >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then strip_assume_tac >>
  qpat_x_assum `ctx_sim D _ _ vrun vs` (mp_tac o REWRITE_RULE [ctx_sim_def]) >>
  disch_then (qspec_then `1` mp_tac) >>
  simp[terminates_def] >>
  disch_then (qx_choose_then `opt_fuel` assume_tac) >>
  suspend "linked_empty_deploy_post"
QED

Resume e2e_deploy_correctness_mods[linked_empty_deploy_post]:
  rename1 `run_context 1 deploy_unit.cu_context vrun = Halt raw` >>
  `?post. run_context opt_fuel deploy_out.po_unit.cu_context vs = Halt post /\
    post.vs_returndata = runtime_bc ++ REPLICATE (imm_len_mods mods) 0w /\
    post.vs_accounts = vs.vs_accounts /\ post.vs_transient = vs.vs_transient /\
    post.vs_logs = vs.vs_logs /\ post.vs_pending_deletions = vs.vs_pending_deletions /\
    post.vs_requests = []` by
    (Cases_on `run_context opt_fuel deploy_out.po_unit.cu_context vs` >>
     qpat_x_assum `dead_result_rel D (Halt raw) _`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [dead_result_rel_def]) >>
     rename1 `accounts_agree_except D raw.vs_accounts post.vs_accounts` >>
     `raw.vs_accounts = post.vs_accounts` by
       (qpat_assum `accounts_agree_except _ raw.vs_accounts post.vs_accounts` mp_tac >>
        simp[NoAsms, accounts_agree_except_def, Abbr `D`,
             storage_agree_except_empty, FUN_EQ_THM] >>
        strip_tac >> qx_gen_tac `addr` >>
        qpat_assum `!a. raw.vs_accounts a with storage := _ = _ /\ _`
          (qspec_then `addr` mp_tac) >>
        simp[NoAsms, vfmStateTheory.account_state_component_equality, FUN_EQ_THM]) >>
     `raw.vs_transient = post.vs_transient` by
       (qpat_assum `transient_agree_except _ raw.vs_transient post.vs_transient` mp_tac >>
        simp[NoAsms, transient_agree_except_def, Abbr `D`, storage_agree_except_empty, FUN_EQ_THM]) >>
     `post.vs_returndata = raw.vs_returndata` by
       (simp_tac bool_ss [LIST_EQ_REWRITE] >>
        conj_tac >- FIRST_ASSUM (ACCEPT_TAC o SYM) >>
        gen_tac >> strip_tac >>
        qpat_assum `!i. i < LENGTH raw.vs_returndata /\ _ ==> _`
          (qspec_then `x` (mp_tac o SIMP_RULE (srw_ss()) [Abbr `D`])) >>
        impl_tac >-
          (qpat_assum `LENGTH raw.vs_returndata = LENGTH post.vs_returndata`
             SUBST1_TAC >> simp[Abbr `D`]) >>
        disch_then (ACCEPT_TAC o SYM)) >>
     `vs.vs_requests = []` by
       simp[Abbr `vs`, opt_entry_state_own_def, entry_venom_state_frame_fields] >>
     `post.vs_requests = []` by
       (qpat_assum `raw.vs_requests = vs.vs_requests` (fn req =>
          qpat_assum `vs.vs_requests = []` (fn empty =>
            qpat_assum `LIST_REL _ raw.vs_requests post.vs_requests`
              (ACCEPT_TAC o SIMP_RULE (srw_ss()) [TRANS req empty])))) >>
     fs[]) >>
  `vs.vs_accounts = accounts_after_transfer tx am.accounts /\
    vs.vs_transient = am.tStorage /\ vs.vs_pending_deletions = am.pending_deletions /\
    vs.vs_logs = am.logs` by
    simp[Abbr `vs`, opt_entry_state_own_def, entry_venom_state_frame_fields,
         entry_venom_state_fresh] >>
  `!A a. update_account a (lookup_account a A with
    code := (lookup_account a A).code) A = A` by
    rw[FUN_EQ_THM, vfmStateTheory.update_account_def,
       vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM,
       vfmStateTheory.account_state_component_equality] >>
  `!A a. update_account a (lookup_account a A) A = A` by
    rw[FUN_EQ_THM, vfmStateTheory.update_account_def,
       vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM] >>
  rewrite_tac[gas_readings_rel_def] >>
  qexistsl_tac [`[]`, `gas_readings es`] >> simp[] >>
  qx_gen_tac `gs` >> strip_tac >>
  disj2_tac >> qexists_tac `opt_fuel` >> asm_rewrite_tac[] >>
  qpat_assum `!orc gs. load_contract_trace orc gs am tx mods exps = _`
    (qspecl_then [`SOME os`,`gs`] assume_tac) >>
  simp[Abbr `deploy_post`, load_contract_def, deploy_storage_trace_mods_def,
       transient_agree_def] >>
  Cases_on `MEM tx.target am.pending_deletions`
  >- simp[process_deletions_update_mem, accounts_agree_def] >>
  simp[vfmProgTheory.lookup_account_process_deletions_other, accounts_agree_def]
QED

Resume e2e_deploy_correctness_mods[linked_deploy_ctor_raw_prefix]:
  gen_tac >> strip_tac >>
  qabbrev_tac `start = vi with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>` >>
  `vi = vs with <|vs_fmp := fmp; vs_initial_fmp := fmp;
                 vs_gas_readings := vi.vs_gas_readings|>` by
    (qpat_assum `raw_variant fmp vi vs`
       (mp_tac o PURE_REWRITE_RULE [raw_variant_def, gas_variant_def]) >>
     simp[NoAsms, venom_state_component_equality] >> strip_tac >>
     qpat_assum `fmp = vi.vs_initial_fmp` (fn h =>
       qpat_assum `fmp = vi.vs_fmp` (ACCEPT_TAC o TRANS (SYM h)))) >>
  `fresh_vars_wrt (initial_compile_state "__deploy") start /\
   ~start.vs_halted /\ start.vs_current_bb = (initial_compile_state "__deploy").cs_current_bb /\
   start.vs_inst_idx = LENGTH (initial_compile_state "__deploy").cs_current_insts /\
   vars_pc_only vi start` by
    (conj_tac
     >- (qunabbrev_tac `start` >>
         qpat_assum `vi = _` SUBST1_TAC >>
         simp[NoAsms, Abbr `vs`, fresh_vars_wrt_def, initial_compile_state_def, lookup_var_def,
              opt_entry_state_own_def, entry_venom_state_fresh]) >>
     simp[NoAsms, Abbr `start`, initial_compile_state_def, vars_pc_only_def] >>
     qpat_assum `vi = _` SUBST1_TAC >>
     simp[NoAsms, Abbr `vs`, opt_entry_state_own_def, entry_venom_state_fresh]) >>
  SUBGOAL_THEN ``mut = Payable \/ start.vs_call_ctx.cc_callvalue = 0w`` ASSUME_TAC
  >- (qpat_assum `mut = Payable \/ tx.value = 0` mp_tac >>
      `start.vs_call_ctx.cc_callvalue = n2w tx.value` by
        (drule raw_variant_call_ctx >> simp[Abbr `start`]) >>
      qpat_assum `start.vs_call_ctx.cc_callvalue = _` (fn callvalue =>
        simp[NoAsms, callvalue]) >>
      disch_then (DISJ_CASES_THEN (fn h => simp[NoAsms, h]))) >>
  qspecl_then [`mut = Payable`,`imm_len_mods mods`,`initial_compile_state "__deploy"`,
    `st_pay`,`st1`,`imm`,`deploy_unit.cu_context`,`fn`,`start`]
    mp_tac deploy_ctor_pre_register_gas_path >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `t` (map_every assume_tac o CONJUNCTS)) >>
  `vars_pc_only vi t` by
    (irule vars_pc_only_trans >> qexists_tac `start` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `t` >> qunabbrev_tac `start` >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise e2e_deploy_correctness_mods

Theorem deploy_entry_rel_state_mods:
  check_contract T am.layouts tx.target mods = SOME art /\
  deploy_entry_rel_mods mods exps deploy_bc am tx es ==>
  deploy_state_rel_mods mods exps deploy_bc am tx es /\
  (lookup_account tx.target am.accounts).storage = empty_storage /\
  am.tStorage tx.target = empty_storage
Proof
  strip_tac >>
  drule check_contract_main_module_present >> strip_tac >>
  qpat_x_assum `deploy_entry_rel_mods _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE
      [deploy_entry_rel_mods_def, e2eDeployEntryTheory.deploy_target_fresh_rel_def,
       evm_state_ok_def, frame_fresh_def, frame_tx_rel_def, world_rel_def]) >>
  `ctxt.msgParams.parsed = parse_code 0 FEMPTY (deploy_bc ++ args_bytes)` by
    (qpat_assum `wf_state es` (mp_tac o cj 3 o REWRITE_RULE [wf_state_def]) >>
     qpat_assum `es.contexts = [(ctxt,rb)]` (fn contexts =>
       qpat_assum `ctxt.msgParams.code = deploy_bc ++ args_bytes` (fn code =>
         simp[NoAsms, wf_context_def, contexts, code]))) >>
  simp[NoAsms, deploy_state_rel_mods_def] >>
  conj_tac
  >- (qexistsl_tac [`ctxt`, `rb`, `args_bytes`] >> asm_rewrite_tac[] >>
      fs[optionTheory.IS_SOME_EXISTS]) >>
  asm_rewrite_tac[]
QED

Theorem deploy_storage_ok_from_within_mods:
  horizon_ok H /\
  (lookup_account tx.target am.accounts).storage = empty_storage /\
  am.tStorage tx.target = empty_storage /\
  deploy_within_mods H mods exps am tx es ==>
  !gs. deploy_storage_ok_mods mods exps am tx (MAP SND (call_trace es)) gs
Proof
  simp[e2eCorrectnessTheory.horizon_ok_def] >> strip_tac >> qx_gen_tac `gs` >>
  rw[deploy_storage_ok_mods_def] >>
  simp[deploy_within_mods_def, storage_trace_horizon_def, LET_THM] >>
  conj_tac
  >- (qpat_x_assum `deploy_within_mods _ _ _ _ _ _` mp_tac >>
      simp[deploy_within_mods_def, storage_observations_ok_def, storage_trace_horizon_def,
           storage_trace_regions_def, storage_trace_locks_def, listTheory.EVERY_MEM] >>
      metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `deploy_within_mods _ _ _ _ _ _` mp_tac >>
      simp[deploy_within_mods_def, storage_observations_ok_def, storage_trace_horizon_def,
           storage_trace_regions_def, storage_trace_locks_def, listTheory.EVERY_MEM] >>
      metis_tac[regions_consistent_def]) >>
  conj_tac
  >- (qpat_x_assum `deploy_within_mods _ _ _ _ _ _` mp_tac >>
      simp[deploy_within_mods_def, storage_observations_ok_def, storage_trace_horizon_def,
           storage_trace_regions_def, storage_trace_locks_def, listTheory.EVERY_MEM] >>
      metis_tac[storage_locks_separated_def]) >>
  conj_tac
  >- (irule empty_storage_well_formed_on >>
      Cases >> gvs[get_storage_def, deploy_evaluation_context_mods_def,
                   initial_evaluation_context_def,
                   vyperInterpreterTheory.initial_state_def, lookup_account_def]) >>
  qpat_x_assum `deploy_within_mods _ _ _ _ _ _` mp_tac >>
  simp[deploy_within_mods_def, storage_observations_ok_def,
       storage_trace_backends_well_formed_def, storage_well_formed_on_def,
       storage_trace_regions_def, listTheory.EVERY_MEM,
       storage_trace_horizon_def, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  strip_tac >> gen_tac >> strip_tac >>
  Cases_on `observation` >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!gs. _` (qspecl_then [`gs`] mp_tac) >> strip_tac >>
  Cases_on `observation` >> gvs[]
  >- (rename1 `StorageRoot b n t` >>
      rename1 `StorageBackend f f0` >>
      qpat_x_assum `!region. _` (qspecl_then [`(b,n2w n,t)`] mp_tac) >>
      impl_tac >- (qexists_tac `[(b,n2w n,t)]` >> conj_tac
                   >- (qexists_tac `StorageRoot b n t` >> simp[])
                   >> simp[]) >>
      simp[] >>
      qpat_x_assum `!observation. _`
        (qspecl_then [`StorageBackend f f0`] mp_tac) >>
      simp[] >> strip_tac >>
      qpat_x_assum `!b slot tv. _`
        (qspecl_then [`b`,`n2w n`,`t`] mp_tac) >> simp[])
  >> metis_tac[]
QED

Theorem e2e_deploy_gas_sufficient_mods:
  !fin policy mods exps deploy_bc runtime_bc am tx es H.
    fin IN accepted_finalizers /\
    compile_vyper_mods fin policy mods exps = SOME (deploy_bc, runtime_bc) /\
    deploy_typing_ok_mods mods exps am tx /\
    deploy_entry_rel_mods mods exps deploy_bc am tx es /\
    e2eCorrectness$horizon_ok H
    ==>
    ?g. !g'.
      g <= g' ==>
      ?r es'.
        run_call (add_frame_gas g' es) = SOME (r, es') /\
        (deploy_within_mods H mods exps am tx (add_frame_gas g' es) /\
         (!obs. ~deploy_gas_source_exempt_mods mods
            (load_contract (SOME (MAP SND (call_trace (add_frame_gas g' es))))
               obs am tx mods exps)) /\
         LENGTH (call_trace (add_frame_gas g' es)) < 2 ** 64 /\
         r = INR (SOME OutOfGas) ==>
         max_code_size < LENGTH runtime_bc + imm_len_mods mods)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `compile_vyper_mods _ _ _ _ = _`
    (strip_assume_tac o MATCH_MP compile_vyper_with_mods_success_phases o
     REWRITE_RULE [compile_vyper_mods_def]) >>
  qpat_assum `deploy_typing_ok_mods _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [deploy_typing_ok_mods_def]) >>
  qpat_assum `check_contract T am.layouts tx.target mods = SOME _`
    (strip_assume_tac o MATCH_MP
      vyperTypeContractModesTheory.check_contract_deploy_implies_runtime) >>
  drule_all deploy_entry_rel_state_mods >> strip_tac >>
  qpat_x_assum `deploy_entry_rel_mods _ _ _ _ _ _` kall_tac >>
  drule_all checked_lower_vyper_deploy_unit_source_shape_mods >> strip_tac >>
  drule lower_vyper_deploy_unit_raw_shape_mods >> strip_tac >>
  drule lower_vyper_deploy_unit_global_reserved_mods >> strip_tac >>
  `o1PipelineCorrect$o1_pipeline rpolicy deploy_unit = SOME deploy_out` by
    fs[o1PipelineCorrectTheory.o1_pipeline_def] >>
  drule_all o1PipelineCorrectTheory.run_venom_pipeline_output_shape >> strip_tac >>
  qpat_assum `finalize_codegen _ _ _.po_unit = SOME deploy_bc`
    (strip_assume_tac o MATCH_MP finalize_codegen_success_plan) >>
  `deploy_unit.cu_data_segment =
      [<|ds_label := "runtime_begin"; ds_items := [DataBytes runtime_bc]|>]` by
    (drule_then ACCEPT_TAC lower_vyper_deploy_unit_runtime_data_mods) >>
  `?pre. deploy_out.po_unit.cu_data_segment =
      pre ++ [<|ds_label := "runtime_begin"; ds_items := [DataBytes runtime_bc]|>]` by
    (qpat_assum `o1PipelineCorrect$o1_pipeline _ deploy_unit = _`
       (mp_tac o REWRITE_RULE [o1PipelineCorrectTheory.o1_pipeline_def]) >>
     strip_tac >> drule deploy_pipeline_runtime_suffix >>
     disch_then (qspec_then `runtime_bc` mp_tac) >> simp[]) >>
  `!fn inst. MEM fn deploy_unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
     source_inst_ok ({"code_end"},T) inst` by
    (rpt strip_tac >>
     mp_tac (Q.INST [`unit` |-> `deploy_unit`, `rpolicy` |-> `rpolicy`,
                    `mods` |-> `mods`, `exps` |-> `exps`, `bytes` |-> `runtime_bc`,
                    `fn` |-> `fn`, `inst` |-> `inst`,
                    `checks` |-> `({"code_end"},T)`]
       lower_vyper_deploy_unit_label_checks_mods) >>
     simp[]) >>
  drule_all source_own_flow >> strip_tac >>
  drule_all gasFocusOptLabelFlowTheory.focus_opt_label_flow_own >> strip_tac >>
  `sym_unit_static_ok deploy_out.po_unit` by
    (qspecl_then [`rpolicy`, `deploy_unit`, `deploy_out`]
       mp_tac o1_pipeline_sym_unit_static_ok >> simp[]) >>
  `codegen_ready deploy_out.po_unit.cu_context` by
    (qpat_assum `o1PipelineCorrect$o1_pipeline _ deploy_unit = _`
       (mp_tac o MATCH_MP run_venom_pipeline_success_boundary o
        REWRITE_RULE [o1PipelineCorrectTheory.o1_pipeline_def]) >> simp[]) >>
  `asm_static_wf prog` by
    (drule_all codegen_asm_static_wf >> simp[]) >>
  `FLOOKUP (lo_reloc prog prog') "code_end" = SOME (LENGTH (assemble prog')) /\
   LENGTH (assemble prog') < 65536` by
    (drule_all finalized_codegen_code_end >> simp[]) >>
  `?pre. prog = pre ++ [AsmDataHeader "runtime_begin"; AsmDataItem runtime_bc;
                       AsmDataHeader "code_end"]` by
    (fs[data_segment_asm_def, data_section_asm_def, MAP_APPEND, FLAT_APPEND] >>
     metis_tac[APPEND_ASSOC]) >>
  `?off. FLOOKUP (lo_reloc prog prog') "runtime_begin" = SOME off /\
        DROP off (assemble prog') = runtime_bc /\
        off <= LENGTH (assemble prog') /\ off < dimword(:256)` by
    (mp_tac (Q.INST [`unit` |-> `deploy_out.po_unit`, `bytes` |-> `runtime_bc`]
       finalized_deploy_runtime_slice) >>
     impl_tac >- (asm_rewrite_tac[] >> qexists_tac `pre'` >> REFL_TAC) >>
     disch_then ACCEPT_TAC) >>
  `cplan.cp_initial_fmp < 2 ** 254` by
    (fs[generate_context_plan_def] >>
     drule generate_context_plan_with_headroom >> simp[]) >>
  `assemble prog' <> []` by
    (Cases_on `fin = K SOME`
     >- (drule codegen_assembly_nonempty >> gvs[]) >>
     `fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
     qpat_x_assum `fin = asm_opt_finalizer` SUBST_ALL_TAC >>
     irule codegen_assembly_finalizer_nonempty >>
     qexistsl [`prog`,`rpolicy`,`deploy_out.po_unit`] >> simp[]) >>
  `?fmp:bytes32.
    w2n (opt_entry_state_own prog prog' cplan es).vs_initial_fmp <= w2n fmp /\
    w2n fmp < 2 ** 254 /\
    imm_len_mods mods + unit_alloca_budget deploy_unit.cu_context +
      32 * ctx_dload_count deploy_unit.cu_context <= w2n fmp` by
    (irule deploy_raw_fmp_exists_mods >> asm_rewrite_tac[] >>
     qexistsl [`exps`, `rpolicy`, `runtime_bc`] >> asm_rewrite_tac[]) >>
  `imm_len_mods mods < dimword (:256)` by
    (qpat_assum `imm_len_mods mods + _ + _ <= _` mp_tac >>
     qpat_assum `w2n fmp < 2 ** 254` mp_tac >>
     simp[NoAsms, wordsTheory.dimword_def, venomLayoutTheory.dimindex_256] >>
     decide_tac) >>
  `fixed_region_reserved (imm_len_mods mods) deploy_unit.cu_context /\
   reserved_intervals_wf deploy_unit.cu_context.ctx_global_reserved` by
    (Cases_on `imm_len_mods mods = 0` >>
     fs[fixed_region_reserved_def, reserved_intervals_wf_def, reserved_interval_wf_def]) >>
  `~(?t. runtime_bc = 0xEFw :: t)` by metis_tac[finalize_codegen_not_ef] >>
  drule_then (qx_choose_then `fuel` assume_tac)
    lower_vyper_deploy_unit_uniform_fuel_mods >>
  qspecl_then [`imm_len_mods mods`, `rpolicy`, `deploy_unit`, `deploy_out`,
               `cplan`, `fuel`]
    mp_tac o1PipelineCorrectTheory.run_venom_pipeline_run_bounded_raw >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`fuel'`, `M`] assume_tac) >>
  `deploy_state_rel_mods mods exps (assemble prog') am tx es` by fs[] >>
  `?c0 rb0. es.contexts = [(c0, rb0)] /\ wf_state es` by
    fs[deploy_state_rel_mods_def] >>
  `!g. deploy_state_rel_mods mods exps (assemble prog') am tx (add_frame_gas g es)` by
    simp[deploy_state_rel_add_frame_gas_mods] >>
  `!g. shadow_root (add_frame_gas g es) = add_frame_gas g (shadow_root es)` by
    simp[shadow_root_add_frame_gas] >>
  `!g. wf_state (shadow_root (add_frame_gas g es)) /\
       g <= frame_gas_left (shadow_root (add_frame_gas g es))` by
    simp[add_frame_gas_wf_state, shadow_root_wf_state, wf_state_frame_gas_left] >>
  qspecl_then [`fin`, `rpolicy`, `deploy_out.po_unit`, `cplan`,
    `prog`, `prog'`, `fuel'`, `M`, `code_deposit_cost * max_code_size`]
    mp_tac codegen_gas_surplus_finalized_own >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choose_then `g` assume_tac) >>
  qexists_tac `g` >> gen_tac >> strip_tac >>
  qabbrev_tac `eg = add_frame_gas g' es` >>
  qspec_then `eg` (qx_choosel_then [`r`, `es'`] assume_tac) run_call_total >>
  qexistsl [`r`, `es'`] >> asm_rewrite_tac[] >>
  strip_tac >>
  `!gs. deploy_storage_ok_mods mods exps am tx (MAP SND (call_trace eg)) gs` by
    (irule deploy_storage_ok_from_within_mods >> asm_rewrite_tac[] >>
     qexists_tac `H` >> simp[Abbr `eg`]) >>
  qpat_x_assum `e2eCorrectness$horizon_ok H` kall_tac >>
  qpat_x_assum `deploy_within_mods H mods exps am tx _` kall_tac >>
  qpat_x_assum `(lookup_account tx.target am.accounts).storage = empty_storage` kall_tac >>
  qpat_x_assum `am.tStorage tx.target = empty_storage` kall_tac >>
  `deploy_state_rel_mods mods exps (assemble prog') am tx eg` by
    simp[Abbr `eg`, deploy_state_rel_add_frame_gas_mods] >>
  qabbrev_tac `vs = opt_entry_state_own prog prog' cplan eg with
                     vs_alloca_next := imm_len_mods mods` >>
  qspecl_then [`mods`, `exps`, `prog`, `prog'`, `am`, `tx`, `eg`, `cplan`, `vs`]
    mp_tac opt_deploy_asm_rels_own_mods >>
  impl_tac >- (qpat_assum `Abbrev (vs = _)` (fn abbrev =>
    asm_rewrite_tac[REWRITE_RULE [markerTheory.Abbrev_def] abbrev])) >>
  strip_tac >>
  `?ctxt rb. eg.contexts = [(ctxt, rb)] /\
             ctxt.msgParams.outputTo = Code tx.target /\
             ~ctxt.msgParams.static /\ wf_state eg` by
    fs[deploy_state_rel_mods_def] >>
  `shadow_root eg = add_frame_gas g' (shadow_root es)` by
    simp[Abbr `eg`, shadow_root_add_frame_gas] >>
  `wf_state (shadow_root eg) /\ g' <= frame_gas_left (shadow_root eg)` by
    simp[Abbr `eg`] >>
  `tx with code := vs.vs_code = tx` by
    (qspecl_then [`mods`, `exps`, `assemble prog'`, `am`, `tx`, `prog`,
         `prog'`, `cplan`, `eg`] mp_tac deploy_own_txp_identity_mods >>
     impl_tac >- FIRST_ASSUM ACCEPT_TAC >>
     simp[NoAsms, Abbr `vs`]) >>
  `o1_initial_state_ok vs /\ ~vs.vs_call_ctx.cc_static /\
   vs.vs_initial_fmp = n2w cplan.cp_initial_fmp /\
   vs.vs_fmp = vs.vs_initial_fmp /\ vs.vs_alloca_next = imm_len_mods mods /\
   w2n vs.vs_initial_fmp <= w2n fmp /\
   vs.vs_outcomes = MAP SND (call_trace eg) /\ vs.vs_gas_readings = gas_readings eg` by
    (qpat_assum `w2n (opt_entry_state_own _ _ _ es).vs_initial_fmp <= w2n fmp`
       mp_tac >>
     qpat_assum `eg.contexts = _` (fn hctx =>
       qpat_assum `~ctxt.msgParams.static` (fn hstatic =>
         simp[NoAsms, Abbr `vs`, opt_entry_state_own_def, entry_venom_state_def,
              init_venom_state_def, o1_initial_state_ok_def, hctx, hstatic]))) >>
  `!eom. max_live_eom deploy_out.po_unit.cu_context = SOME eom ==>
          eom <= w2n vs.vs_initial_fmp` by
    (qspecl_then [`deploy_out.po_unit.cu_context`, `cplan`, `vs`]
      mp_tac o1PipelineCorrectTheory.generate_context_plan_eom_room >> simp[]) >>
  `o1_lowered_inv deploy_out.po_unit.cu_context vs /\
    code_end_offset_ok (raw_reachable vs) deploy_out.po_unit.cu_context /\
    venom_run_bounded fuel' M deploy_out.po_unit.cu_context vs /\
    mem_inv (\ctx fn inst s. inst_create_size_ok inst s)
      deploy_out.po_unit.cu_context vs /\
    (?ret ghost. run_call (shadow_root eg) = SOME (INR ret, ghost) /\
      (!c rb. ret = NONE /\ ghost.contexts = [(c, rb)] ==>
         LENGTH c.returnData <= LENGTH runtime_bc + imm_len_mods mods))` suffices_by
    (strip_tac >>
     drule_all o1_pipeline_memory_obligations_raw >> strip_tac >>
     drule_all o1_pipeline_codegen_obligations >> strip_tac >>
     `!s op res s'. frame_inst_at (shadow_root eg) s op /\
        step_inst op s = (res, s') /\ LENGTH s'.contexts = LENGTH s.contexts ==>
        res <> INR (SOME OutOfGas) /\
        code_deposit_cost * max_code_size <= frame_gas_left s'` by
       (rpt gen_tac >> strip_tac >>
        qpat_assum `!g' Inv vs es s op res s'. _`
          (qspecl_then [`g'`, `raw_reachable vs`, `vs`, `shadow_root es`,
                        `s`, `op`, `res`, `s'`] mp_tac) >>
        qpat_assum `shadow_root eg = _` (PURE_REWRITE_TAC o single o GSYM) >>
        simp[]) >>
     drule_all deploy_frame_gas_tail_bounded_output >> strip_tac >> gvs[]) >>
  qabbrev_tac `D = <|d_stor := K (K UNIV); d_trans := K (K UNIV);
                       d_imm := K UNIV; d_ret := K UNIV|>` >>
  `dead_wf D` by simp[Abbr `D`, dead_wf_def] >>
  `sfields_tenv_consistent (make_struct_fields_map_mods mods) (type_env_all_modules mods) /\
    mem_inv (\ctx fn inst s. inst_create_size_ok inst s)
      deploy_out.po_unit.cu_context vs /\
    (!vi. raw_variant fmp vi vs ==>
      raw_unit_memory_ok deploy_unit.cu_context vi /\
      ptr_discipline (imm_len_mods mods) deploy_unit.cu_context vi /\
      mem_inv dload_offset_ok deploy_unit.cu_context vi /\
      mem_inv dload_headroom_ok deploy_unit.cu_context vi /\
      mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                               s.vs_code = vi.vs_code /\
                               s.vs_data_section = vi.vs_data_section)
        deploy_unit.cu_context vi /\
      terminates (run_context fuel deploy_unit.cu_context vi)) /\
    (?ret ghost. run_call (shadow_root eg) = SOME (INR ret, ghost) /\
      (!c rb. ret = NONE /\ ghost.contexts = [(c, rb)] ==>
         LENGTH c.returnData <= LENGTH runtime_bc + imm_len_mods mods))` suffices_by
    (strip_tac >>
     `!bs. constructor_args_encode_mods mods tx bs ==> LENGTH bs < 2 ** 128` by
       (gen_tac >> strip_tac >>
        mp_tac (Q.INST [`mods` |-> `mods`, `exps` |-> `exps`, `rpolicy` |-> `rpolicy`,
                         `runtime_bc` |-> `runtime_bc`, `unit` |-> `deploy_unit`,
                         `tx` |-> `tx`, `bs` |-> `bs`] constructor_args_size_bounded_mods) >>
        asm_rewrite_tac[]) >>
     `code_layout_valid vs` by
       (mp_tac (Q.INST [`es` |-> `eg`, `cplan` |-> `cplan`]
          deploy_entry_code_layout_mods) >>
        impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
        simp[NoAsms, Abbr `vs`, code_layout_valid_def]) >>
     `o1_run_state_ok vs` by simp[o1_run_state_ok_def] >>
     `LENGTH vs.vs_data_section < dimword (:256) DIV 2` by
       (mp_tac (Q.INST [`vs` |-> `vs`, `prefix` |-> `assemble prog'`]
          e2eCorrectnessTheory.data_section_length_bound) >> asm_rewrite_tac[]) >>
     `!vi. taint_within D deploy_unit.cu_context vi` by
       simp[Abbr `D`, taint_within_def] >>
     `venom_run_bounded fuel' M deploy_out.po_unit.cu_context vs` by
       (qpat_assum `!D vs fmp. _ ==> venom_run_bounded _ _ _ _`
          (qspecl_then [`D`, `vs`, `fmp`] mp_tac) >>
        impl_tac
        >- (rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE
              (gen_tac >> strip_tac >>
               qpat_assum `!vi. raw_variant _ vi vs ==> _` (drule_then strip_assume_tac) >>
               simp[]))) >>
        strip_tac) >>
     `code_end_offset_ok (raw_reachable vs) deploy_out.po_unit.cu_context` by
       (qspecl_then [`D`, `imm_len_mods mods`, `rpolicy`, `deploy_unit`,
                     `deploy_out`, `vs`, `fmp`]
          mp_tac o1StaticPipelineCorrectTheory.o1_pipeline_code_end_offset_ok_static_abort >>
        impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
        disch_then (qx_choose_then `vcode` strip_assume_tac) >>
        qpat_assum `!vi. raw_variant _ vi vs ==> _` (drule_then strip_assume_tac) >>
        qpat_x_assum `_ ==> code_end_offset_ok _ _ /\ _` mp_tac >>
        impl_tac >- (rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE simp[])) >>
        disch_then (CONJUNCTS_THEN2 assume_tac (K ALL_TAC)) >>
        qpat_x_assum `code_end_offset_ok (\_ _ _ _. _) _` mp_tac >>
        simp_tac bool_ss [code_end_offset_ok_def, in_static_abort_prefix_def] >>
        metis_tac[replay_exit_raw_call_ctx]) >>
     `o1_lowered_inv deploy_out.po_unit.cu_context vs` by
       (qspecl_then [`D`, `imm_len_mods mods`, `rpolicy`, `deploy_unit`,
                     `deploy_out`, `vs`, `fmp`]
          mp_tac o1PipelineCorrectTheory.run_venom_pipeline_correct >>
        impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
        disch_then (qx_choose_then `vrun` strip_assume_tac) >>
        qpat_assum `!vi. raw_variant _ vi vs ==> _` (drule_then strip_assume_tac) >>
        qpat_x_assum `_ ==> ctx_sim D _ _ vrun vs /\ _` mp_tac >>
        impl_tac >- (rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE simp[])) >>
        simp[]) >>
     metis_tac[]) >>
  suspend "linked_deploy_gas_bound"
QED

Resume e2e_deploy_gas_sufficient_mods[linked_deploy_gas_bound]:
  Cases_on `classify_functions_unit mods exps` >> PairCases_on `r'` >>
  rename1 `classify_functions_unit mods exps = (exts,ints,fb,ctor,imp_ctors)` >>
  Cases_on `ctor`
  >- suspend "linked_empty_deploy_gas" >>
  linked_deploy_constructor_source_tac >>
  linked_deploy_constructor_package_tac >>
  linked_deploy_constructor_package_flags_tac >>
  linked_deploy_constructor_code_tac >>
  suspend "linked_present_deploy_gas"
QED

Resume e2e_deploy_gas_sufficient_mods[linked_present_deploy_gas]:
  Q.ASM_CASES_TAC `mut <> Payable /\ tx.value <> 0`
  >- suspend "linked_present_deploy_gas_rejected_value" >>
  suspend "linked_present_deploy_gas_accepted_value"
QED

(* Project the raw certificate at the uniform fuel, and use the optimized
   Revert for CREATE-size safety. Only the shadow-run conjunct remains. *)
val linked_rejected_gas_memory_tac =
  strip_tac >>
  `!vi. raw_variant fmp vi vs ==>
    raw_unit_memory_ok deploy_unit.cu_context vi /\
    ptr_discipline (imm_len_mods mods) deploy_unit.cu_context vi /\
    mem_inv dload_offset_ok deploy_unit.cu_context vi /\
    mem_inv dload_headroom_ok deploy_unit.cu_context vi /\
    mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                             s.vs_code = vi.vs_code /\ s.vs_data_section = vi.vs_data_section)
      deploy_unit.cu_context vi /\
    terminates (run_context fuel deploy_unit.cu_context vi)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!vi. raw_variant fmp vi vs ==> _ /\ _ /\ taint_within _ _ vi /\ _`
       (qspec_then `vi` (drule_then strip_assume_tac)) >>
     qpat_assum `!n s. terminates (run_context n _ s) ==> _`
       (qspecl_then [`1`,`vi`] mp_tac) >> simp[terminates_def]) >>
  `EVERY wf_function deploy_out.po_unit.cu_context.ctx_functions` by
    (qpat_assum `o1PipelineCorrect$o1_pipeline rpolicy deploy_unit = SOME deploy_out`
       (mp_tac o MATCH_MP run_venom_pipeline_success_unit_wf o
        BETA_RULE o REWRITE_RULE [o1PipelineCorrectTheory.o1_pipeline_def]) >>
     simp[venomCompilerWfTheory.unit_wf_def, venomWfTheory.venom_wf_def, EVERY_MEM]) >>
  `mem_inv (\ctx fn inst s. inst_create_size_ok inst s) deploy_out.po_unit.cu_context vs` by
    (irule revert_run_create_size_ok >> asm_rewrite_tac[] >>
     qexistsl [`opt_fuel`, `post`] >> FIRST_ASSUM ACCEPT_TAC) >>
  asm_rewrite_tac[];

(* The shadow frame retains the deployed program and its argument bytes.
   For the identity finalizer, recover the unrelocated entry relation. *)
val linked_rejected_gas_frame_tac =
  `prog' = prog` by
    (qpat_assum `fin rpolicy prog = SOME prog'` mp_tac >>
     qpat_assum `fin = K SOME` (fn th => simp[NoAsms, th])) >>
  qpat_x_assum `prog' = prog` SUBST_ALL_TAC >>
  qpat_assum `deploy_state_rel_mods mods exps (assemble prog) am tx eg`
    (qx_choosel_then [`frame`,`saved`,`args_bytes`] strip_assume_tac o
     PURE_REWRITE_RULE [deploy_state_rel_mods_def]) >>
  `frame = ctxt /\ saved = rb` by
    (qpat_assum `eg.contexts = [(frame,saved)]` (fn right =>
       qpat_assum `eg.contexts = [(ctxt,rb)]` (mp_tac o TRANS (SYM right))) >>
     simp[NoAsms]) >>
  qpat_x_assum `frame = ctxt` SUBST_ALL_TAC >>
  qpat_x_assum `saved = rb` SUBST_ALL_TAC >>
  `vs = entry_venom_state prog cplan eg with vs_alloca_next := imm_len_mods mods` by
    simp[Abbr `vs`, opt_entry_state_own_identity] >>
  `eg.txParams.blockNumber < dimword (:256)` by
    (qpat_assum `tx_block_fields_rel tx eg.txParams` mp_tac >>
     simp[NoAsms, tx_block_fields_rel_def, tx_env_ok_def] >> strip_tac >>
     irule lt_dimword_256 >> qexists_tac `255` >> simp[]) >>
  `frame_obs (shadow_root eg) = frame_obs eg` by
    (irule shadow_root_frame_obs >>
     qpat_assum `eg.contexts = [(ctxt,rb)]` (fn th => simp[NoAsms, th])) >>
  `call_trace (shadow_root eg) = call_trace eg /\
   gas_readings (shadow_root eg) = gas_readings eg` by
    (qpat_assum `frame_obs (shadow_root eg) = frame_obs eg` (fn th =>
       simp[NoAsms, call_trace_def, gas_readings_def, th])) >>
  qabbrev_tac `c = ctxt with msgParams updated_by
                (\mp. mp with outputTo := Memory <|offset := 0; size := 0|>)` >>
  `(shadow_root eg).contexts = [(c,rb)]` by
    (qpat_assum `eg.contexts = [(ctxt,rb)]` (fn contexts =>
       simp[NoAsms, contexts, Abbr `c`, shadow_root_def, shadow_root_contexts_def]));

val linked_rejected_gas_state_tac =
  `?opt_entry opt_fns. deploy_out.po_unit.cu_context.ctx_functions = opt_entry::opt_fns /\
             get_params (HD opt_entry.fn_blocks).bb_instructions = []` by
    (qpat_assum `unit_shape_ok _`
       (mp_tac o PURE_REWRITE_RULE [unit_shape_ok_def, entry_fn_first_def]) >>
     disch_then (CONJUNCTS_THEN2
       (qx_choosel_then [`entry_name`,`entry_fn`,`other_fns`] strip_assume_tac)
       strip_assume_tac) >>
     qexistsl [`entry_fn`,`other_fns`] >> conj_tac
     >- FIRST_ASSUM ACCEPT_TAC >>
     qpat_assum `get_params (HD (HD _).fn_blocks).bb_instructions = []` mp_tac >>
     qpat_assum `deploy_out.po_unit.cu_context.ctx_functions = entry_fn::other_fns`
       SUBST1_TAC >> simp[NoAsms]) >>
  `msg_ctx_rel vs.vs_call_ctx c.msgParams /\
   tx_ctx_rel vs.vs_tx_ctx (shadow_root eg).txParams /\
   block_ctx_rel vs.vs_block_ctx (shadow_root eg).txParams /\
   blockhash_rel vs (shadow_root eg).txParams` by
    (qpat_assum `vs = _ with vs_alloca_next := _` SUBST1_TAC >>
     qspecl_then [`eg`,`ctxt`,`rb`,`[]`,`prog`,`cplan`] mp_tac
       entry_venom_state_evm_environment >>
     impl_tac >- (conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     simp[NoAsms, Abbr `c`, shadow_root_def, msg_ctx_rel_def, blockhash_rel_def]) >>
  `vs.vs_params = []` by
    (qpat_assum `vs = _ with vs_alloca_next := _` SUBST1_TAC >>
     simp[NoAsms, entry_venom_state_def, init_venom_state_def]) >>
  `initial_state_rel cplan prog 0 opt_entry vs (shadow_root eg)` by
    (qpat_x_assum `shadow_root eg = _` kall_tac >>
     qpat_x_assum `Abbrev (eg = _)` kall_tac >>
     PURE_REWRITE_TAC [initial_state_rel_def] >>
     qpat_assum `(shadow_root eg).contexts = [(c,rb)]` (fn th =>
       simp_tac (srw_ss()) [th, stack_params_rel_def]) >>
     asm_rewrite_tac[] >>
     qpat_assum `vs = _ with vs_alloca_next := _` SUBST1_TAC >>
     simp[entry_venom_state_fresh, entry_venom_state_frame_fields,
          entry_venom_state_created_in_tx, asm_pc_to_offset_zero,
          context_memory_rel_def, Abbr `c`, shadow_root_def,
          rich_listTheory.DROP_LENGTH_APPEND]);

val linked_rejected_gas_context_tac =
  PURE_REWRITE_TAC [initial_ctx_rel_def] >>
  qexistsl [`opt_entry`,`opt_fns`,`c`,`rb`,`[]`] >>
  `(shadow_root eg).msdomain = eg.msdomain` by simp[NoAsms, shadow_root_def] >>
  `vs.vs_data_section = args_bytes` by
    (qpat_assum `vs = _ with vs_alloca_next := _` SUBST1_TAC >>
     simp[entry_venom_state_frame_fields, rich_listTheory.DROP_LENGTH_APPEND]) >>
  `c.msgParams.code = assemble prog ++ vs.vs_data_section` by simp[Abbr `c`] >>
  `vs.vs_call_ctx.cc_created_in_tx` by
    (qpat_assum `vs = _ with vs_alloca_next := _` SUBST1_TAC >>
     simp[entry_venom_state_created_in_tx]) >>
  `c.msgParams.parsed = parse_code 0 FEMPTY c.msgParams.code /\ c.logs = []` by
    (simp[NoAsms, Abbr `c`] >> conj_tac
     >- (qpat_assum `ctxt.msgParams.code = assemble prog ++ args_bytes`
           (PURE_REWRITE_TAC o single) >> FIRST_ASSUM ACCEPT_TAC) >>
     FIRST_ASSUM ACCEPT_TAC) >>
  simp[] >>
  qpat_assum `vs = _ with vs_alloca_next := _` SUBST1_TAC >>
  simp[entry_venom_state_fresh, entry_venom_state_frame_fields] >>
  simp[initial_codegen_state_rel_def, entry_venom_state_def, init_venom_state_def];

val linked_rejected_gas_codegen_obligations_tac =
  qspecl_then [`deploy_out`,`cplan`,`vs`] mp_tac o1_pipeline_memory_obligations_raw >>
  impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  strip_tac >>
  qspecl_then [`rpolicy`,`deploy_unit`,`deploy_out`,`cplan`,`raw_reachable vs`]
    mp_tac o1_pipeline_codegen_obligations >>
  impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >> strip_tac;

val linked_rejected_gas_codegen_tac =
  `?sr ghost. run_call (shadow_root eg) = SOME (sr,ghost) /\
    (frame_resource_starved (shadow_root eg) sr ghost \/
     venom_frame_rel (shadow_root eg) sr ghost (Abort Revert_abort post))` by
    (Cases_on `fin = K SOME`
     >- (`initial_ctx_rel cplan prog deploy_out.po_unit.cu_context vs (shadow_root eg)` by
           (linked_rejected_gas_frame_tac >> linked_rejected_gas_state_tac >>
            linked_rejected_gas_context_tac) >>
         qspecl_then [`opt_fuel`,`rpolicy`,`deploy_out.po_unit`,`cplan`,`prog`,
                      `raw_reachable vs`,`vs`,`shadow_root eg`] mp_tac codegen_correct >>
         impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
         asm_rewrite_tac[]) >>
     `fin = asm_opt_finalizer` by
       (qpat_assum `fin IN accepted_finalizers` mp_tac >>
        qpat_assum `fin <> K SOME` (fn th => simp[NoAsms, accepted_finalizers_def, th])) >>
     qpat_x_assum `fin = asm_opt_finalizer` SUBST_ALL_TAC >>
     qspecl_then [`opt_fuel`,`rpolicy`,`deploy_out.po_unit`,`cplan`,`prog`,`prog'`,
                  `raw_reachable vs`,`vs`,`shadow_root eg`]
       mp_tac codegen_correct_asm_opt_own >>
     impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >> asm_rewrite_tac[]);

(* Both codegen outcomes provide a nonempty exception in the singleton
   shadow root. The cap on successful output therefore holds vacuously. *)
val linked_rejected_gas_shadow_tac =
  `?c rb'. (shadow_root eg).contexts = [(c,rb')]` by
    (qpat_assum `eg.contexts = [(ctxt,rb)]` (fn contexts =>
       simp[NoAsms, shadow_root_def, shadow_root_contexts_def, contexts])) >>
  `sr = INR (SOME exc)` by
    (qpat_assum `(shadow_root eg).contexts = [(_,_)]` (fn context =>
       qpat_assum `frame_outcome (shadow_root eg) sr ghost _ _ _`
         (mp_tac o SIMP_RULE (srw_ss()) [frame_outcome_def, context])) >>
     simp[NoAsms]) >>
  qexistsl [`SOME exc`,`ghost`] >>
  qpat_assum `shadow_root eg = _` (PURE_REWRITE_TAC o single o SYM) >>
  simp[];

val linked_rejected_gas_starved_tac =
  qpat_assum `frame_resource_starved (shadow_root eg) sr ghost`
    (qx_choosel_then [`exc`,`out`,`lgs`]
      (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 assume_tac (K ALL_TAC))) o
     REWRITE_RULE [frame_resource_starved_def]) >>
  linked_rejected_gas_shadow_tac;

val linked_rejected_gas_revert_tac =
  qpat_assum `venom_frame_rel (shadow_root eg) sr ghost (Abort Revert_abort post)`
    (qx_choosel_then [`exc`,`out`,`lgs`] assume_tac o MATCH_MP venom_frame_rel_abort_failure) >>
  linked_rejected_gas_shadow_tac;

val linked_rejected_gas_certificate : term quotation =
  `sfields_tenv_consistent (make_struct_fields_map_mods mods) (type_env_all_modules mods) /\
   (!vi. raw_variant fmp vi vs ==>
     raw_unit_memory_ok deploy_unit.cu_context vi /\
     ptr_discipline (imm_len_mods mods) deploy_unit.cu_context vi /\
     taint_within D deploy_unit.cu_context vi /\
     mem_inv dload_offset_ok deploy_unit.cu_context vi /\
     mem_inv dload_headroom_ok deploy_unit.cu_context vi /\
     mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                              s.vs_code = vi.vs_code /\ s.vs_data_section = vi.vs_data_section)
       deploy_unit.cu_context vi /\
     ?raw. run_context 1 deploy_unit.cu_context vi = Abort Revert_abort raw) /\
   o1_lowered_inv deploy_out.po_unit.cu_context vs /\
   code_end_offset_ok (raw_reachable vs) deploy_out.po_unit.cu_context /\
   (?opt_fuel post. run_context opt_fuel deploy_out.po_unit.cu_context vs = Abort Revert_abort post)`;

Resume e2e_deploy_gas_sufficient_mods[linked_present_deploy_gas_rejected_value]:
  linked_rejected_gas_certificate suffices_by
    (linked_rejected_gas_memory_tac >>
     linked_rejected_gas_codegen_obligations_tac >>
     linked_rejected_gas_codegen_tac
     >- linked_rejected_gas_starved_tac >>
     linked_rejected_gas_revert_tac) >>
  linked_deploy_reject_entry_tac >>
  linked_deploy_reject_state_tac `eg` >>
  linked_deploy_reject_raw_tac >>
  linked_deploy_reject_code_end_tac >>
  linked_deploy_reject_sim_tac >>
  rename1 `run_context opt_fuel deploy_out.po_unit.cu_context vs = Abort Revert_abort post` >>
  rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE
    (qexistsl [`opt_fuel`, `post`] >> FIRST_ASSUM ACCEPT_TAC))
QED

Resume e2e_deploy_gas_sufficient_mods[linked_present_deploy_gas_accepted_value]:
  `cpkg3 = F /\ cpkg4 = global_nonreentrant_slot /\ cpkg5 = T` by
    (qpat_assum `constructor = (mut,F,F,"__init__",src_args,[],NoneT,_)`
       (fn ctor => qpat_assum `set_constructor_package_target _ _ = _`
         (mp_tac o SUBS [ctor])) >>
     simp[package_constructor_unit_def, set_constructor_package_target_def]) >>
  qpat_x_assum `cpkg3 = F` SUBST_ALL_TAC >>
  qpat_x_assum `cpkg4 = global_nonreentrant_slot` SUBST_ALL_TAC >>
  qpat_x_assum `cpkg5 = T` SUBST_ALL_TAC >>
  qpat_x_assum `cpkg2 = (mut = Payable)` SUBST_ALL_TAC >>
  `st3 = st2` by fs[comp_return_def] >>
  qpat_x_assum `st3 = st2` SUBST_ALL_TAC >>
  qabbrev_tac `ctor_ce = ce1 with ce_ctor_exit_label := SOME exit_lbl` >>
  mp_tac (Q.INST [`ce0` |-> `cpkg0`, `key` |-> `global_nonreentrant_slot`,
      `ut` |-> `T`, `rp` |-> `rpolicy`, `cap` |-> `imm_len_mods mods`,
      `args` |-> `cpkg1`, `ifns` |-> `internals`, `stmts` |-> `cpkg6`,
      `pay` |-> `mut = Payable`, `unit` |-> `deploy_unit`, `ce` |-> `ctor_ce`]
    linked_constructor_body_shadow_code) >>
  impl_tac >- simp[Abbr `ctor_ce`] >>
  disch_then (qx_choosel_then [`shadow_unit`,`shadow_fn`,`shadow_sb`]
    strip_assume_tac) >>
  linked_deploy_ctor_ptr_environment_tac `eg` >>
  `shadow_body_inv_mods mods exps deploy_unit.cu_context shadow_unit.cu_context` by
    (qpat_assum `Abbrev (internals = _)`
       (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     drule_all_then ACCEPT_TAC deploy_shadow_body_inv_mods) >>
  linked_deploy_ctor_accepted_inputs_tac >>
  linked_deploy_ctor_source_trace_tac >>
  linked_deploy_ctor_registration_metadata_tac >>
  linked_deploy_ctor_prefix_fields_tac `eg` `ctxt'.msgParams.code` >>
  linked_deploy_ctor_prefix_code_tac >>
  linked_deploy_ctor_before_registration_tac >>
  suspend "linked_present_deploy_gas_accepted_value_body"
QED

(* Read the result tag and return data at the singleton shadow frame. *)
val linked_accepted_gas_frame_bound_tac =
  let
    fun outcome ret =
      qpat_assum `(shadow_root eg).contexts = [(_,_)]` (fn contexts =>
        qpat_assum `frame_outcome (shadow_root eg) sr ghost _ _ _`
          (strip_assume_tac o SIMP_RULE (srw_ss()) [frame_outcome_def, contexts])) >>
      qexistsl_tac [ret, `ghost`] >> conj_tac
      >- (qpat_assum `sr = INR _` (SUBST1_TAC o SYM) >> FIRST_ASSUM ACCEPT_TAC)
    val failure = outcome `SOME exc` >> simp[NoAsms]
    val relation = qpat_assum `venom_frame_rel (shadow_root eg) sr ghost _`
  in
    `?c rb'. (shadow_root eg).contexts = [(c,rb')]` by
      (qpat_assum `eg.contexts = [(_,_)]` (fn contexts =>
        simp[NoAsms, shadow_root_def, shadow_root_contexts_def, contexts])) >>
    pop_assum (fn contexts => POP_ASSUM_LIST (K ALL_TAC) >> assume_tac contexts) >>
    qx_gen_tac `u` >>
    disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (qx_choosel_then [`sr`,`ghost`] (CONJUNCTS_THEN2 assume_tac DISJ_CASES_TAC))))
    >- (qpat_assum `frame_resource_starved (shadow_root eg) sr ghost`
          (qx_choosel_then [`exc`,`out`,`lgs`]
            (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 assume_tac (K ALL_TAC))) o
            REWRITE_RULE [frame_resource_starved_def]) >> failure) >>
    Cases_on `u`
    >- relation (strip_assume_tac o SIMP_RULE (srw_ss()) [venom_frame_rel_def])
    >- (rename1 `venom_frame_rel _ _ _ (Halt post)` >>
        relation (CONJUNCTS_THEN2 assume_tac (K ALL_TAC) o
                  SIMP_RULE (srw_ss()) [venom_frame_rel_def]) >>
        outcome `NONE` >>
        qpat_assum `!p. Halt post = Halt p ==> _`
          (qspec_then `post` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
        qpat_assum `ghost.contexts = _` (fn contexts =>
          qpat_assum `_.returnData = post.vs_returndata` (fn output =>
            qpat_assum `LENGTH post.vs_returndata <= _` (fn bound =>
              simp[NoAsms, contexts] >> rpt strip_tac >>
              gvs[NoAsms, output, bound]))))
    >- (relation (qx_choosel_then [`exc`,`out`,`lgs`] assume_tac o
                  MATCH_MP venom_frame_rel_abort_failure) >> failure)
    >- relation (strip_assume_tac o SIMP_RULE (srw_ss()) [venom_frame_rel_def]) >>
    qpat_assum `terminates (Error _)`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [terminates_def])
  end;

(* Apply finalized codegen at the supplied optimized execution, then
   project the bounded return data from that same shadow call. *)
val linked_accepted_gas_codegen_run_tac =
  Cases_on `fin = K SOME`
  >- (`initial_ctx_rel cplan prog deploy_out.po_unit.cu_context vs (shadow_root eg)` by
        (linked_rejected_gas_frame_tac >> linked_rejected_gas_state_tac >>
         linked_rejected_gas_context_tac) >>
      qspecl_then [`cg_fuel`,`rpolicy`,`deploy_out.po_unit`,`cplan`,`prog`,
                   `raw_reachable vs`,`vs`,`shadow_root eg`] mp_tac codegen_correct >>
      impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
      asm_rewrite_tac[]) >>
  `fin = asm_opt_finalizer` by
    (qpat_assum `fin IN accepted_finalizers` mp_tac >>
     qpat_assum `fin <> K SOME` (fn th => simp[NoAsms, accepted_finalizers_def, th])) >>
  qpat_x_assum `fin = asm_opt_finalizer` SUBST_ALL_TAC >>
  qspecl_then [`cg_fuel`,`rpolicy`,`deploy_out.po_unit`,`cplan`,`prog`,`prog'`,
               `raw_reachable vs`,`vs`,`shadow_root eg`]
    mp_tac codegen_correct_asm_opt_own >>
  impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >> asm_rewrite_tac[];

val linked_accepted_gas_codegen_context_tac =
  let
    fun keep [] facts = POP_ASSUM_LIST (K ALL_TAC) >> map_every assume_tac facts
      | keep (p::ps) facts = qpat_assum p (fn th => keep ps (th::facts))
  in
    keep [`fin IN accepted_finalizers`, `fin rpolicy prog = SOME prog'`,
          `generate_context_plan deploy_out.po_unit.cu_context = SOME cplan`,
          `codegen_assembly rpolicy deploy_out.po_unit = SOME prog`,
          `o1PipelineCorrect$o1_pipeline rpolicy deploy_unit = SOME deploy_out`,
          `unit_shape_ok deploy_out.po_unit`,
          `label_flow_own_ok deploy_out.po_unit.cu_context`,
          `sym_unit_static_ok deploy_out.po_unit`,
          `vs.vs_initial_fmp = n2w cplan.cp_initial_fmp`,
          `vs.vs_code = assemble prog' ++ vs.vs_data_section`,
          `codegen_asm_entry_rel_reloc (lo_reloc prog prog') cplan prog vs
             (entry_asm_state vs (shadow_root eg))`,
          `asm_frame_rel prog' vs.vs_data_section (shadow_root eg)
             (entry_asm_state vs (shadow_root eg)) (shadow_root eg)`,
          `Abbrev (vs = opt_entry_state_own prog prog' cplan eg with
             vs_alloca_next := imm_len_mods mods)`,
          `Abbrev (eg = add_frame_gas g' es)`, `shadow_root eg = _`,
          `deploy_state_rel_mods mods exps (assemble prog') am tx eg`,
          `eg.contexts = [(ctxt,rb)]`, `wf_state (shadow_root eg)`,
          `!u. terminates u /\ _ ==> _`] []
  end;

(* The optimizer consumers also work without an optimized CREATE-size fact. *)
val linked_accepted_gas_shadow_goal =
  sg `(!vi. raw_variant fmp vi vs ==>
      raw_unit_memory_ok deploy_unit.cu_context vi /\
      ptr_discipline (imm_len_mods mods) deploy_unit.cu_context vi /\
      mem_inv dload_offset_ok deploy_unit.cu_context vi /\
      mem_inv dload_headroom_ok deploy_unit.cu_context vi /\
      mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                              s.vs_code = vi.vs_code /\ s.vs_data_section = vi.vs_data_section)
        deploy_unit.cu_context vi /\
      terminates (run_context fuel deploy_unit.cu_context vi) /\
      (!p. run_context fuel deploy_unit.cu_context vi = Halt p ==>
           LENGTH p.vs_returndata <= LENGTH runtime_bc + imm_len_mods mods)) ==>
    sfields_tenv_consistent (make_struct_fields_map_mods mods) (type_env_all_modules mods) /\
    (?ret ghost. run_call (shadow_root eg) = SOME (INR ret,ghost) /\
       (!c rb. ret = NONE /\ ghost.contexts = [(c,rb)] ==>
           LENGTH c.returnData <= LENGTH runtime_bc + imm_len_mods mods))`;

val linked_accepted_gas_shadow_layout_tac =
  `!bs. constructor_args_encode_mods mods tx bs ==> LENGTH bs < 2 ** 128` by
    (gen_tac >> strip_tac >>
     mp_tac (Q.INST [`mods` |-> `mods`, `exps` |-> `exps`, `rpolicy` |-> `rpolicy`,
                      `runtime_bc` |-> `runtime_bc`, `unit` |-> `deploy_unit`,
                      `tx` |-> `tx`, `bs` |-> `bs`] constructor_args_size_bounded_mods) >>
     asm_rewrite_tac[]) >>
  `code_layout_valid vs` by
    (mp_tac (Q.INST [`es` |-> `eg`, `cplan` |-> `cplan`]
       deploy_entry_code_layout_mods) >>
     impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     simp[NoAsms, Abbr `vs`, code_layout_valid_def]) >>
  `o1_run_state_ok vs` by
    (simp[NoAsms, o1_run_state_ok_def] >> rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  `LENGTH vs.vs_data_section < dimword (:256) DIV 2` by
    (mp_tac (Q.INST [`vs` |-> `vs`, `prefix` |-> `assemble prog'`]
       e2eCorrectnessTheory.data_section_length_bound) >> asm_rewrite_tac[]);

fun linked_accepted_gas_shadow_variant_tac v =
  qpat_assum `!vi. raw_variant fmp vi vs ==> _ /\ _ /\ mem_inv dload_offset_ok _ vi /\ _`
    (qspec_then v (drule_then (map_every assume_tac o CONJUNCTS))) >>
  (`!vi. taint_within D deploy_unit.cu_context vi` by
    (qpat_assum `Abbrev (D = _)` (fn d =>
       simp[NoAsms, REWRITE_RULE [markerTheory.Abbrev_def] d, taint_within_def]))) >>
  pop_assum (qspec_then v assume_tac);

val linked_accepted_gas_shadow_code_end_goal =
  sg `code_end_offset_ok (raw_reachable vs) deploy_out.po_unit.cu_context`;

val linked_accepted_gas_shadow_code_end_select_tac =
  qspecl_then [`D`, `imm_len_mods mods`, `rpolicy`, `deploy_unit`,
               `deploy_out`, `vs`, `fmp`]
    mp_tac o1StaticPipelineCorrectTheory.o1_pipeline_code_end_offset_ok_static_abort >>
  impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  disch_then (qx_choose_then `vcode` (map_every assume_tac o CONJUNCTS));

val linked_accepted_gas_shadow_code_end_nonstatic_tac =
  qpat_x_assum `_ ==> code_end_offset_ok _ _ /\ _` mp_tac >>
  impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  disch_then (mp_tac o CONJUNCT1) >>
  qpat_assum `~vs.vs_call_ctx.cc_static` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp_tac bool_ss [code_end_offset_ok_def, in_static_abort_prefix_def] >>
  metis_tac[replay_exit_raw_call_ctx];

val linked_accepted_gas_shadow_sim_tac =
  qspecl_then [`D`, `imm_len_mods mods`, `rpolicy`, `deploy_unit`,
                `deploy_out`, `vs`, `fmp`]
    mp_tac o1PipelineCorrectTheory.run_venom_pipeline_correct >>
  impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  disch_then (qx_choose_then `vrun` (map_every assume_tac o CONJUNCTS)) >>
  linked_accepted_gas_shadow_variant_tac `vrun` >>
  qpat_x_assum `_ ==> ctx_sim D _ _ vrun vs /\ _` mp_tac >>
  impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `ctx_sim D _ _ vrun vs` (mp_tac o PURE_REWRITE_RULE [ctx_sim_def]) >>
  disch_then (qspec_then `fuel` mp_tac) >>
  impl_tac >- FIRST_ASSUM ACCEPT_TAC >>
  disch_then (qx_choose_then `opt_fuel` assume_tac);

val linked_accepted_gas_shadow_result_tac =
  `!u v. dead_result_rel D u v /\
      (!p. u = Halt p ==> LENGTH p.vs_returndata <= LENGTH runtime_bc + imm_len_mods mods) ==>
      terminates v /\
      (!p. v = Halt p ==> LENGTH p.vs_returndata <= LENGTH runtime_bc + imm_len_mods mods)` by
    (POP_ASSUM_LIST (K ALL_TAC) >> Cases >> Cases >>
     simp[dead_result_rel_def, terminates_def] >> decide_tac) >>
  qpat_x_assum `!u v. dead_result_rel D u v /\ _ ==> _`
    (qspecl_then [`run_context fuel deploy_unit.cu_context vrun`,
                  `run_context opt_fuel deploy_out.po_unit.cu_context vs`] mp_tac) >>
  impl_tac >- (conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!cg_fuel u. o1_lowered_inv _ _ /\ _ ==> _`
    (qspecl_then [`opt_fuel`, `run_context opt_fuel deploy_out.po_unit.cu_context vs`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> (REFL_TAC ORELSE FIRST_ASSUM ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC;

(* Select the terminal run at the raw variant's observations. *)
val linked_accepted_gas_raw_exit_goal =
  sg `!vi. raw_variant fmp vi vs ==>
    ?body_fuel terminal root.
      root = vi with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|> /\
      run_from body_fuel deploy_unit.cu_context fn root = terminal /\
      exit_result terminal /\
      mem_safe_run body_fuel deploy_unit.cu_context fn root /\
      ptr_safe_run D (imm_len_mods mods) body_fuel deploy_unit.cu_context fn [] FEMPTY entry_taint root /\
      (!p. terminal = Halt p ==> LENGTH p.vs_returndata <= LENGTH runtime_bc + imm_len_mods mods) /\
      (?obs. create_size_exit_ok deploy_unit.cu_context
        (load_contract (SOME vi.vs_outcomes) obs am tx mods exps) terminal)`;

val linked_accepted_gas_select_tac =
  qx_gen_tac `vi` >> disch_tac >>
  asm "linked_ctor_registered_terminal" (qspec_then `vi` mp_tac) >>
  (impl_tac >- (conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
  disch_then (qx_choose_then `marks` DISJ_CASES_TAC)
  >- (pop_assum (DISJ_CASES_TAC o CONJUNCT2)
      >- (pop_assum (qspec_then `[]` mp_tac) >>
          qpat_assum `!gs. deploy_storage_ok_mods mods exps am tx _ gs`
            (qspec_then `gas_explicit marks vi.vs_gas_readings` (fn th => simp[NoAsms, th]))) >>
      pop_assum (qspec_then `[]` mp_tac) >>
      qpat_assum `!obs. ~deploy_gas_source_exempt_mods mods _`
        (qspec_then `gas_explicit marks vi.vs_gas_readings` mp_tac) >>
      simp[NoAsms, deploy_gas_source_exempt_mods_def]) >>
  pop_assum (qx_choosel_then [`res`,`ee`,`terminal`,`G'`,`tn'`]
    (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!H. valid_horizon cx (initial_state am []) H ee.storage_trace ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- (qpat_assum `storage_trace_domain cx _ ee.storage_trace`
    (ACCEPT_TAC o PURE_REWRITE_RULE [storage_trace_domain_def]))) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (mk_asm "gas_terminal_shape")) >>
  qabbrev_tac `root = vi with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>`;

val linked_accepted_gas_raw_exec_tac =
  qpat_assum `gas_origin_ptr_path _ (root,FEMPTY,entry_taint) _ (terminal,_,_)`
    (mp_tac o MATCH_MP fragGasOriginPtrDeadTheory.gas_origin_ptr_path_dead_mono) >>
  disch_then (qspec_then `D` mp_tac) >>
  (impl_tac >- simp[NoAsms, Abbr `D`]) >>
  disch_then (mp_tac o MATCH_MP fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec) >>
  (disch_then (DISJ_CASES_THEN2
    (qx_choose_then `t` (assume_tac o CONJUNCT1))
    (mp_tac o CONJUNCT2)))
  >- (qpat_assum `exit_result terminal` mp_tac >>
      qpat_assum `terminal = OK t` (fn th => simp[NoAsms, th, exit_result_def])) >>
  disch_then (qx_choose_then `body_fuel` (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`body_fuel`,`terminal`,`root`] >>
  conj_tac >- simp[NoAsms, Abbr `root`] >>
  ntac 4 (conj_tac >- FIRST_ASSUM ACCEPT_TAC);

val linked_accepted_gas_raw_length_tac =
  asm_x "gas_terminal_shape" DISJ_CASES_TAC
  >- (qpat_assum `Abbrev (installed = _)`
        (fn def => pop_assum (qx_choosel_then [`before`,`final`,`codepos`]
          (map_every assume_tac o CONJUNCTS) o BETA_RULE o
          REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] def] o CONJUNCT2)) >>
      qpat_assum `terminal = Halt final` (fn term =>
        qpat_assum `final.vs_returndata = _` (fn bytes =>
          simp[NoAsms, term, bytes, LENGTH_TAKE_EQ]))) >>
  pop_assum DISJ_CASES_TAC
  >- (pop_assum (qx_choose_then `final` (fn th => simp[NoAsms, th]) o CONJUNCT2)) >>
  pop_assum (qx_choosel_then [`err`,`final`,`abort`] (fn th => simp[NoAsms, th]));

val linked_accepted_gas_raw_fields : term quotation =
  `raw_unit_memory_ok deploy_unit.cu_context vi /\
    ptr_discipline (imm_len_mods mods) deploy_unit.cu_context vi /\
    mem_inv dload_offset_ok deploy_unit.cu_context vi /\
    mem_inv dload_headroom_ok deploy_unit.cu_context vi /\
    mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                              s.vs_code = vi.vs_code /\ s.vs_data_section = vi.vs_data_section)
      deploy_unit.cu_context vi /\
    terminates (run_context fuel deploy_unit.cu_context vi) /\
    (!p. run_context fuel deploy_unit.cu_context vi = Halt p ==>
         LENGTH p.vs_returndata <= LENGTH runtime_bc + imm_len_mods mods)`;

(* The constructor finish step preserves the oversized CREATE error. *)
val linked_accepted_gas_raw_size_tac =
  qexists_tac `gas_explicit marks vi.vs_gas_readings` >>
  qpat_assum `raw_variant fmp vi vs`
    (fn variant =>
      qpat_assum `vs.vs_outcomes = MAP SND (call_trace eg)`
        (fn outcomes => PURE_REWRITE_TAC [MATCH_MP raw_variant_outcomes variant, outcomes])) >>
  qpat_assum `!tail. load_contract_trace _ _ am tx mods exps = _`
    (qspec_then `[]` (fn trace => PURE_REWRITE_TAC
       [load_contract_def, PURE_REWRITE_RULE [APPEND_NIL] trace, pairTheory.FST])) >>
  qpat_assum `create_size_exit_ok deploy_unit.cu_context res terminal` mp_tac >>
  PURE_REWRITE_TAC [create_size_exit_ok_def] >>
  disch_tac >> strip_tac >>
  `res = INR (Error (RuntimeError "create initcode too large"))` by
    (qpat_assum `_ ==> res = INR (Error (RuntimeError "create initcode too large"))`
       (drule_all_then ACCEPT_TAC)) >>
  qpat_assum `res = INR (Error (RuntimeError "create initcode too large"))`
    (fn err => simp[NoAsms, err, Abbr `source_finish`]);

val linked_accepted_gas_raw_package =
  `!vi. raw_variant fmp vi vs ==> ` @ linked_accepted_gas_raw_fields;

val linked_accepted_gas_raw_sized_package =
  `!vi. raw_variant fmp vi vs ==> (` @ linked_accepted_gas_raw_fields @ `) /\
    (?obs fr. exit_result (run_context fr deploy_unit.cu_context vi) /\
       create_size_exit_ok deploy_unit.cu_context
         (load_contract (SOME vi.vs_outcomes) obs am tx mods exps)
         (run_context fr deploy_unit.cu_context vi))`;

val linked_accepted_gas_raw_entry_tac =
  qx_gen_tac `vi` >> disch_tac >>
  qpat_assum `!vi. raw_variant fmp vi vs ==> ?body_fuel terminal root. _`
    (drule_then (qx_choosel_then [`body_fuel`,`terminal`,`root`]
      (map_every assume_tac o CONJUNCTS))) >>
  `root.vs_current_bb = "__deploy" /\ root.vs_inst_idx = 0 /\
   root with vs_inst_idx := 0 = root` by
    (qpat_assum `root = _` (fn th => simp[NoAsms, th])) >>
  (Q.SUBGOAL_THEN `?bb. lookup_block "__deploy" fn.fn_blocks = SOME bb`
     (qx_choose_then `bb` assume_tac) >-
    (qpat_assum `fn_entry_label fn = SOME "__deploy"` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `fn.fn_blocks` >>
     simp[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def,
          venomInstTheory.lookup_block_def, listTheory.FIND_thm])) >>
  `lookup_block root.vs_current_bb fn.fn_blocks = SOME bb` by
    (qpat_assum `root.vs_current_bb = _` SUBST1_TAC >> FIRST_ASSUM ACCEPT_TAC) >>
  `phi_prefix_length bb.bb_instructions = 0` by
    (drule_all_then ACCEPT_TAC acceptedContextPhiTheory.lowering_context_ok_block_phi);

val linked_accepted_gas_block_safety_tac =
  `!e. run_from body_fuel deploy_unit.cu_context fn root <> Error e` by
    (qpat_assum `run_from _ _ _ _ = terminal` SUBST1_TAC >>
     drule_then ACCEPT_TAC exit_result_not_error) >>
  `!n. mem_safe_blocks n deploy_unit.cu_context fn root` by
    (`!n. mem_safe_run n deploy_unit.cu_context fn root` by
       (qspecl_then [`body_fuel`,`deploy_unit.cu_context`,`fn`,`root`] mp_tac
         mem_safe_run_all_fuel >> impl_tac >- (conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
        disch_then ACCEPT_TAC) >>
     `eval_phis root bb.bb_instructions = OK root` by
       (irule eval_phis_no_phi >> FIRST_ASSUM ACCEPT_TAC) >>
     mp_tac (Q.INST [`s` |-> `root`,`ctx` |-> `deploy_unit.cu_context`,`fn` |-> `fn`,`bb` |-> `bb`]
       entryDispatchMemTheory.mem_safe_blocks_no_phi) >>
     (impl_tac >- (rpt conj_tac >>
       (FIRST_ASSUM ACCEPT_TAC ORELSE
        (qpat_assum `root with vs_inst_idx := 0 = root` SUBST1_TAC >> FIRST_ASSUM ACCEPT_TAC)))) >>
     disch_then ACCEPT_TAC);

val linked_accepted_gas_ptr_run_tac =
  Q.SUBGOAL_THEN
    `!n. ptr_safe_run D (imm_len_mods mods) n deploy_unit.cu_context fn [] FEMPTY entry_taint root`
    assume_tac >-
    (gen_tac >> irule fragExecPtrTheory.ptr_safe_run_all_fuel >>
     qexists_tac `body_fuel` >> conj_tac >> FIRST_ASSUM ACCEPT_TAC);

val linked_accepted_gas_ptr_blocks_tac =
  Q.SUBGOAL_THEN
    `!n. ptr_safe_blocks D (imm_len_mods mods) n deploy_unit.cu_context fn [] FEMPTY entry_taint root`
    assume_tac >-
    (mp_tac (Q.INST [`s` |-> `root`,`ctx` |-> `deploy_unit.cu_context`,
                     `fn` |-> `fn`,`bb` |-> `bb`,`D` |-> `D`,
                     `lo` |-> `imm_len_mods mods`,`PG` |-> `[]`,
                     `G` |-> `FEMPTY`,`tn` |-> `entry_taint`]
       entryDispatchPtrTheory.ptr_safe_blocks_from_phi_free_run) >>
     (impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >> disch_then ACCEPT_TAC);

val linked_accepted_gas_context_run_tac =
  `run_context (SUC body_fuel) deploy_unit.cu_context vi = terminal` by
    (qspecl_then [`SUC body_fuel`,`deploy_unit.cu_context`,`vi`,`"__deploy"`,`fn`,`"__deploy"`]
       mp_tac run_context_run_blocks >>
     impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     qpat_assum `root = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
     disch_then SUBST1_TAC >>
     qspecl_then [`body_fuel`,`deploy_unit.cu_context`,`fn`,`root`,`bb`] mp_tac
       run_blocks_run_from_no_phi >>
     impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     disch_then SUBST1_TAC >>
     qpat_assum `root with vs_inst_idx := 0 = root` SUBST1_TAC >>
     FIRST_ASSUM ACCEPT_TAC) >>
  `terminates (run_context (SUC body_fuel) deploy_unit.cu_context vi)` by
    (qpat_assum `run_context (SUC body_fuel) _ _ = terminal` SUBST1_TAC >>
     qpat_assum `exit_result terminal` mp_tac >> Cases_on `terminal` >>
     simp[NoAsms, exit_result_def, terminates_def]) >>
  `terminates (run_context fuel deploy_unit.cu_context vi)` by
    (qpat_assum `!n s. terminates (run_context n deploy_unit.cu_context s) ==>
                         terminates (run_context fuel deploy_unit.cu_context s)`
       (qspecl_then [`SUC body_fuel`,`vi`] (drule_then ACCEPT_TAC))) >>
  `run_context fuel deploy_unit.cu_context vi = terminal` by
    (Cases_on `fuel <= SUC body_fuel`
     >- (qpat_assum `run_context (SUC body_fuel) _ _ = terminal` (SUBST1_TAC o SYM) >>
         sym_tac >> irule run_context_terminates_mono >> conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     `SUC body_fuel <= fuel` by decide_tac >>
     qpat_assum `run_context (SUC body_fuel) _ _ = terminal` (SUBST1_TAC o SYM) >>
     irule run_context_terminates_mono >> conj_tac >> FIRST_ASSUM ACCEPT_TAC);

val linked_accepted_gas_layout_tac =
  `!bs. constructor_args_encode_mods mods tx bs ==> LENGTH bs < 2 ** 128` by
    (gen_tac >> strip_tac >>
     mp_tac (Q.INST [`mods` |-> `mods`, `exps` |-> `exps`, `rpolicy` |-> `rpolicy`,
                      `runtime_bc` |-> `runtime_bc`, `unit` |-> `deploy_unit`,
                      `tx` |-> `tx`, `bs` |-> `bs`] constructor_args_size_bounded_mods) >>
     asm_rewrite_tac[]) >>
  `code_layout_valid vs` by
    (mp_tac (Q.INST [`es` |-> `eg`, `cplan` |-> `cplan`]
       deploy_entry_code_layout_mods) >>
     (impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
     simp[NoAsms, Abbr `vs`, code_layout_valid_def]);

val linked_accepted_gas_variant_mem_tac =
  `vi = vs with <|vs_fmp := fmp; vs_initial_fmp := fmp;
                      vs_gas_readings := vi.vs_gas_readings|>` by
    (qpat_assum `raw_variant fmp vi vs`
       (mp_tac o PURE_REWRITE_RULE [raw_variant_def, gas_variant_def]) >>
     simp[NoAsms, venom_state_component_equality] >> strip_tac >>
     qpat_assum `fmp = vi.vs_initial_fmp` (fn h =>
       qpat_assum `fmp = vi.vs_fmp` (ACCEPT_TAC o TRANS (SYM h)))) >>
  `code_layout_valid vi /\ vi.vs_alloca_next = imm_len_mods mods /\
   w2n vi.vs_initial_fmp = w2n fmp /\ w2n vi.vs_initial_fmp <= w2n vi.vs_fmp` by
    (qpat_x_assum `vi = _` SUBST1_TAC >>
     qpat_assum `code_layout_valid vs` mp_tac >>
     qpat_assum `vs.vs_alloca_next = _` mp_tac >> simp[NoAsms, code_layout_valid_def]) >>
  `imm_len_mods mods + unit_alloca_budget deploy_unit.cu_context +
     32 * ctx_dload_count deploy_unit.cu_context <= w2n vi.vs_initial_fmp` by
    (qpat_assum `w2n vi.vs_initial_fmp = w2n fmp` SUBST1_TAC >> FIRST_ASSUM ACCEPT_TAC);

val linked_accepted_gas_dload_reachable_tac =
  Q.SUBGOAL_THEN
    `!f inst s. raw_reachable vi deploy_unit.cu_context f inst s ==> inst_dload_in_section inst s`
    assume_tac >-
    (qspecl_then [`deploy_unit.cu_context`,`"__deploy"`,`fn`,`"__deploy"`,`vi`]
       mp_tac lowered_unit_dload_in_section >>
     (impl_tac >- (rpt conj_tac >>
       (FIRST_ASSUM ACCEPT_TAC ORELSE
        (qpat_assum `root = _` (SUBST1_TAC o SYM) >> FIRST_ASSUM ACCEPT_TAC)))) >>
     disch_then ACCEPT_TAC);

val linked_accepted_gas_dload_mem_tac =
  Q.SUBGOAL_THEN
    `mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                   s.vs_code = vi.vs_code /\ s.vs_data_section = vi.vs_data_section)
        deploy_unit.cu_context vi` assume_tac >-
    (simp[NoAsms, mem_inv_raw_reachable] >> conj_tac
     >- (qexistsl_tac [`"__deploy"`,`fn`,`"__deploy"`] >>
         rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     rpt gen_tac >> disch_tac >> conj_tac
     >- first_x_assum (drule_then ACCEPT_TAC) >>
     drule_then ACCEPT_TAC o1SafeUptoTheory.raw_reachable_code_data);

val linked_accepted_gas_selected_mem_tac =
  let
    fun selected th =
      mp_tac (Q.INST [`dunit` |-> `deploy_unit`, `vs` |-> `vi`, `D` |-> `D`,
                      `func` |-> `fn`, `mods` |-> `mods`, `exps` |-> `exps`,
                      `rpolicy` |-> `rpolicy`, `runtime_bc` |-> `runtime_bc`] (SPEC_ALL th)) >>
      (impl_tac >- (rpt conj_tac >>
        (FIRST_ASSUM ACCEPT_TAC ORELSE
         (qpat_assum `root = _` (SUBST1_TAC o SYM) >> FIRST_ASSUM ACCEPT_TAC)))) >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      conj_tac
      >- (ntac 6 (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >>
          qpat_assum `run_context fuel deploy_unit.cu_context vi = terminal` SUBST1_TAC >>
          FIRST_ASSUM ACCEPT_TAC) >>
      qpat_assum `?obs. create_size_exit_ok deploy_unit.cu_context _ terminal`
        (qx_choose_then `obs` assume_tac) >>
      qexistsl_tac [`obs`,`SUC body_fuel`] >>
      qpat_assum `run_context (SUC body_fuel) deploy_unit.cu_context vi = terminal` SUBST1_TAC >>
      conj_tac >> FIRST_ASSUM ACCEPT_TAC
  in
    Cases_on `ctx_has_dalloca deploy_unit.cu_context`
    >- selected deploy_selected_memory_from_checked_mods >>
    selected deploy_selected_memory_mods
  end;

Resume e2e_deploy_gas_sufficient_mods[linked_present_deploy_gas_accepted_value_body]:
  (linked_positive_epilogue_goal >-
    (linked_positive_epilogue_alloc_producers_tac >> linked_positive_epilogue_copy_producers_tac >>
     linked_positive_epilogue_run_producers_tac >>
     linked_positive_epilogue_setup_tac >> linked_positive_epilogue_entry_tac >>
     (linked_positive_epilogue_imm_ghost_goal >- linked_positive_epilogue_imm_ghost_tac) >>
     linked_positive_epilogue_fresh_tac >> linked_positive_epilogue_alloc_tac >>
     linked_positive_epilogue_open_alloc_tac >> linked_positive_epilogue_alloc_ghost_tac >>
     (linked_positive_epilogue_after_alloc_goal >- linked_positive_epilogue_after_alloc_proof) >>
     linked_positive_epilogue_after_alloc_tac >> linked_positive_epilogue_add_tac >>
     linked_positive_epilogue_after_add_tac >> linked_positive_epilogue_mcopy_tac >>
     linked_positive_epilogue_after_mcopy_tac >> linked_positive_epilogue_codecopy_join_tac >>
     linked_positive_epilogue_after_codecopy_tac >> linked_positive_epilogue_run_halt_tac >> linked_positive_epilogue_identify_halt_tac >>
     linked_positive_epilogue_return_check_tac >> linked_positive_epilogue_scalar_checks_tac >>
     linked_positive_epilogue_begin_block_tac >>
     linked_positive_epilogue_next (`G`,`tn`,`s`,`i0`,`u0`) `Abbrev (s1 = _)`
       [`step_prov [] G i0 u0 = G1`,`step_taint i0 s u0 tn = tn1`] >>
     linked_positive_epilogue_next (`G1`,`tn1`,`s1`,`i1`,`u1`) `Abbrev (s2 = _)`
       [`step_prov [] G1 i1 u1 = G2`,`step_taint i1 s1 u1 tn1 = tn2`] >>
     linked_positive_epilogue_next (`G2`,`tn2`,`s2`,`i2`,`u2`) `Abbrev (s3 = _)`
       [`step_prov [] G2 i2 u2 = G2`,`step_taint i2 s2 u2 tn2 = tn3`] >>
     linked_positive_epilogue_next (`G2`,`tn3`,`s3`,`i3`,`u3`) `Abbrev (s4 = _)`
       [`step_prov [] G2 i3 u3 = G2`,`step_taint i3 s3 u3 tn3 = tn4`] >>
     linked_positive_epilogue_finish_block_tac)) >>
  linked_epilogue_ptr_next_tac >>
  linked_epilogue_ptr_halt_tac >>
  linked_ctor_active_contract_tac >>
  linked_ctor_checker_calls_tac >>
  linked_ctor_struct_args_tac >>
  linked_ctor_rewritten_supported_stmts_tac >>
  linked_ctor_decode_expr_reflect_tac >>
  linked_ctor_decode_occurrence_tac >>
  linked_ctor_subst_idempotent_tac >>
  linked_ctor_registration_fields_tac >>
  linked_ctor_package_fields_tac >>
  linked_ctor_transport_contract_tac >>
  linked_ctor_stmts_env_code_tac >>
  linked_ctor_conditional_body_tac >>
  (linked_ctor_return_fields_goal_tac >- linked_ctor_return_fields_tac) >>
  linked_ctor_return_fragment_tac
  >- (linked_ctor_return_open_fragment_tac >>
      (linked_ctor_return_jump_entry_tac >- linked_ctor_return_jmp_code_tac) >>
      (linked_ctor_return_landing_tac >- linked_ctor_return_alloca_tac) >>
      (linked_ctor_return_inv_goal_tac >- linked_ctor_return_inv_tac) >>
      linked_ctor_return_epilogue_tac >> linked_ctor_return_outcome_tac >>
      (conj_tac >- ((linked_ctor_return_prepend_tac >- linked_ctor_return_jmp_path_tac) >>
                    linked_ctor_return_append_tac)) >>
      linked_ctor_return_post_tac) >>
  linked_ctor_constant_guards_tac >>
  linked_ctor_constant_cells_tac >>
  linked_ctor_constant_folds_tac >>
  linked_ctor_error_annotation_tac >>
  linked_ctor_error_resolution_tac >>
  linked_ctor_custom_errors_tac >>
  (linked_ctor_zero_epilogue_ptr_goal >-
   (linked_ctor_zero_epilogue_setup_tac >> linked_ctor_zero_epilogue_alloc_tac >>
    linked_ctor_zero_epilogue_alloc_step_tac >> linked_ctor_zero_epilogue_alloc_exec_tac >>
    linked_ctor_zero_epilogue_alloc_fmp_tac >>
    linked_ctor_zero_epilogue_alloc_frame_tac >>
    linked_ctor_zero_epilogue_copy_tac >> linked_ctor_zero_epilogue_return_tac)) >>
  linked_ctor_uniform_marked_tail_tac >>
  linked_ctor_epilogue_run_tac >>
  pop_assum (mk_asm "linked_epilogue_raw") >>
  linked_ctor_replacement_no_risky_tac >>
  linked_ctor_replacement_access_tac >>
  linked_ctor_constant_replacement_tac >>
  linked_ctor_constant_roots_tac >>
  linked_ctor_constant_entry_tac >>
  linked_ctor_checked_entry_env_tac >>
  linked_ctor_immutable_guards_tac >>
  linked_ctor_source_well_typed_tac >>
  linked_ctor_source_scope_tac >>
  linked_ctor_source_accounts_tac >>
  linked_ctor_send_value_tac >>
  linked_ctor_paid_accounts_tac >>
  linked_ctor_env_consistency_tac >>
  linked_ctor_bare_globals_layout_tac
  >- (linked_ctor_bare_globals_layout_setup_tac >>
      linked_ctor_bare_globals_regions_tac >>
      linked_ctor_bare_globals_layout_head_tac >>
      (conj_tac >- (linked_ctor_bare_globals_disjoint_tac >>
                    linked_ctor_bare_globals_disjoint_finish_tac)) >>
      linked_ctor_bare_globals_modules_tac) >>
  linked_ctor_alloc_env_tac >>
  linked_ctor_typed_allocation_tac >>
  linked_ctor_register_domain_tac >>
  linked_ctor_formal_domain_tac >>
  linked_ctor_post_registration_domain_tac >>
  linked_ctor_registration_map_tac >>
  linked_ctor_registered_pointers_tac >>
  linked_ctor_formal_pointers_tac >>
  linked_ctor_formal_types_tac >>
  linked_ctor_expr_metadata_tac >>
  linked_ctor_struct_fields_tac >>
  linked_ctor_flags_tac >>
  linked_ctor_flag_fold_tac >>
  linked_ctor_flag_index_helpers_tac >>
  linked_ctor_flag_namespace_tac >>
  linked_ctor_flag_member_tac >>
  (linked_ctor_const_name_free_tac >- (linked_ctor_const_name_free_body_tac >>
    (linked_ctor_const_key_tac >- linked_ctor_const_key_member_tac) >>
    linked_ctor_access_free_root_tac >> linked_ctor_subst_expr_roots_tac >>
    linked_ctor_subst_stmt_roots_tac)) >>
  linked_ctor_stmts_exprs_ok_tac >>
  linked_ctor_source_observation_tac ``eg:execution_state`` >>
  linked_ctor_observed_env_tac ``eg:execution_state`` >>
  linked_ctor_return_decl_tac >>
  (linked_ctor_return_miss_goal >- linked_ctor_return_miss_tac) >>
  linked_ctor_return_key_member_tac >>
  (linked_ctor_return_hit_goal >- linked_ctor_return_hit_tac) >>
  linked_ctor_return_checked_keys_tac >>
  linked_ctor_return_mod_key_tac >>
  (linked_ctor_return_mods_goal >- linked_ctor_return_mods_tac) >>
  linked_ctor_return_types_tac >>
  (linked_ctor_bare_endpoint_tac >- linked_ctor_bare_endpoint_proof_tac) >>
  linked_ctor_bare_slot_source_tac >>
  linked_ctor_bare_slot_frame_tac >>
  (linked_ctor_bare_classify_tac >-
   (linked_ctor_bare_classify_prefix_tac >> linked_ctor_bare_classify_checker_tac)) >>
  linked_ctor_bare_slot_cleanup_tac >>
  linked_ctor_bare_placement_tac >>
  (linked_ctor_immutable_region_type_goal_tac >-
   (linked_ctor_immutable_region_type_tac >>
    (linked_ctor_immutable_region_open_tac >- linked_ctor_immutable_region_lookup_tac) >>
    linked_ctor_immutable_region_size_tac)) >>
  linked_ctor_checked_storage_tables_tac >>
  linked_ctor_checked_map_projections_tac >>
  linked_ctor_checked_place_tables_tac >>
  linked_ctor_checked_bare_hash_tac >>
  linked_deploy_registration_inputs_tac >>
  (linked_deploy_registration_replay_entry_tac >-
    (qx_gen_tac `vi` >> disch_tac >>
     linked_deploy_registration_prefix_tac >>
     linked_deploy_registration_decode_tac >>
     linked_deploy_registration_path_tac >>
     linked_deploy_registration_replay_bytes_tac >>
     linked_deploy_registration_replay_finish_tac)) >>
  `!u. terminates u /\
       (!p. u = Halt p ==> LENGTH p.vs_returndata <= LENGTH runtime_bc + imm_len_mods mods) /\
       (?sr ghost. run_call (shadow_root eg) = SOME (sr,ghost) /\
         (frame_resource_starved (shadow_root eg) sr ghost \/
          venom_frame_rel (shadow_root eg) sr ghost u)) ==>
       ?ret ghost. run_call (shadow_root eg) = SOME (INR ret,ghost) /\
         (!c rb. ret = NONE /\ ghost.contexts = [(c,rb)] ==>
            LENGTH c.returnData <= LENGTH runtime_bc + imm_len_mods mods)` by
    linked_accepted_gas_frame_bound_tac >>
  `!cg_fuel u. o1_lowered_inv deploy_out.po_unit.cu_context vs /\
       code_end_offset_ok (raw_reachable vs) deploy_out.po_unit.cu_context /\
       run_context cg_fuel deploy_out.po_unit.cu_context vs = u /\
       terminates u /\
       (!p. u = Halt p ==> LENGTH p.vs_returndata <= LENGTH runtime_bc + imm_len_mods mods) ==>
       ?ret ghost. run_call (shadow_root eg) = SOME (INR ret,ghost) /\
         (!c rb. ret = NONE /\ ghost.contexts = [(c,rb)] ==>
            LENGTH c.returnData <= LENGTH runtime_bc + imm_len_mods mods)` by
    (linked_accepted_gas_codegen_context_tac >>
     map_every qx_gen_tac [`cg_fuel`,`u`] >> strip_tac >>
     linked_rejected_gas_codegen_obligations_tac >>
     `?sr ghost. run_call (shadow_root eg) = SOME (sr,ghost) /\
       (frame_resource_starved (shadow_root eg) sr ghost \/
        venom_frame_rel (shadow_root eg) sr ghost u)` suffices_by
       (disch_tac >>
        qpat_assum `!u. terminates u /\ _ ==> _` (qspec_then `u` mp_tac) >>
        impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
        disch_then ACCEPT_TAC) >>
     linked_accepted_gas_codegen_run_tac) >>
  (linked_accepted_gas_shadow_goal >-
    (disch_tac >> conj_tac
     >- (irule make_struct_fields_map_mods_consistent >> qexists_tac `F` >>
         qpat_assum `check_contract F am.layouts tx.target mods = SOME _`
           (ACCEPT_TAC o MATCH_MP check_contract_runtime_namespaces)) >>
     linked_accepted_gas_shadow_layout_tac >>
     (linked_accepted_gas_shadow_code_end_goal >-
       (linked_accepted_gas_shadow_code_end_select_tac >>
        linked_accepted_gas_shadow_variant_tac `vcode` >>
        linked_accepted_gas_shadow_code_end_nonstatic_tac)) >>
     linked_accepted_gas_shadow_sim_tac >> linked_accepted_gas_shadow_result_tac)) >>
  pop_assum (mk_asm "linked_accepted_gas_shadow") >>
  linked_ctor_builder_src_other_tac >>
  linked_ctor_builder_src_absent_tac >>
  linked_ctor_builder_src_decl_tac >>
  linked_ctor_builder_mods_absent_tac >>
  linked_ctor_builder_mods_var_tac >>
  linked_ctor_builder_mods_hash_tac >>
  linked_ctor_builder_decl_tac >>
  linked_ctor_decode_unconditional_tac >>
  linked_ctor_support_unconditional_tac >>
  linked_ctor_install_epilogue_exit_tac >>
  linked_ctor_install_epilogue_placement_tac >>
  linked_ctor_install_epilogue_reserved_tac >>
  linked_ctor_install_epilogue_fresh_tac >>
  linked_ctor_registered_imm_transport_tac >>
  linked_ctor_registered_return_buf_tac >>
  (linked_ctor_registered_control_goal >- linked_ctor_registered_control_tac) >>
  linked_ctor_dalloca_windows_tac >>
  linked_ctor_raw_headroom_tac >>
  linked_ctor_variant_headroom_tac ``eg:execution_state`` >>
  (linked_ctor_registered_headroom_goal >-
   (linked_ctor_registered_headroom_setup_tac >> linked_ctor_registered_headroom_transfer_tac)) >>
  linked_ctor_frame_headroom_tac ``eg:execution_state`` >>
  (linked_ctor_registered_ghost_goal >-
   (linked_ctor_registered_ghost_open_tac
    >- (linked_ctor_registered_ghost_frame_tac >> rpt conj_tac
        >- linked_ctor_registered_ghost_low_tac
        >- linked_ctor_registered_ghost_imm_tac >> FIRST_ASSUM ACCEPT_TAC) >>
    linked_ctor_registered_ghost_lookup_tac >> linked_ctor_registered_ghost_support_tac >>
    linked_ctor_registered_ghost_scope_tac >> linked_ctor_registered_ghost_bytes_tac)) >>
  linked_ctor_install_epilogue_static_tac >>
  (linked_ctor_install_epilogue_open_tac >-
   (linked_ctor_install_epilogue_entry_tac >> linked_ctor_install_epilogue_horizon_tac >>
    (linked_ctor_install_epilogue_run_tac >-
     (rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE asm "epilogue_entry_state_rel" ACCEPT_TAC))) >>
    linked_ctor_install_epilogue_run_result_tac >>
    (linked_ctor_install_epilogue_ptr_goal >-
      (linked_ctor_install_epilogue_ptr_setup_tac >> Cases_on `imm_len_mods mods = 0`
       >- (linked_ctor_install_epilogue_zero_code_tac >> linked_ctor_install_epilogue_zero_tac) >>
       linked_ctor_install_epilogue_ptr_fresh_tac >> linked_ctor_install_epilogue_positive_tac >>
       conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
       conj_tac >- simp[NoAsms, Abbr `linked_ret_DF`] >>
       qexistsl_tac [`H`,`body_ce`,`tail_codepos`,`ctor_ce`,`cx`,`src`,`st_epilogue`,
                    `tail_final`,`imm`,`LENGTH runtime_bc`,`st_final`] >>
       rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE simp[NoAsms, Abbr `linked_ret_DF`]))) >>
    linked_ctor_install_epilogue_endpoint_tac)) >>
  disch_tac >>
  linked_ctor_expr_roots_join_tac >>
  linked_ctor_expr_table_join_tac >>
  linked_ctor_expr_layout_join_tac >>
  (linked_ctor_observed_expr_inv_tac ``eg:execution_state`` >-
   (linked_ctor_observed_expr_project_tac ``eg:execution_state`` >>
    linked_ctor_observed_expr_finish_tac)) >>
  linked_ctor_body_except_frame_tac ``eg:execution_state`` >>
  linked_ctor_body_at_return_frame_tac >>
  linked_ctor_subst_control_tac >>
  linked_ctor_source_admissible_tac ``eg:execution_state`` >>
  linked_ctor_paired_env_tac >>
  linked_ctor_body_dead_low_tac >>
  linked_entry_machine_slots_tac >>
  (linked_entry_machine_parts_goal_tac ``eg:execution_state`` >-
   (map_every qx_gen_tac [`vi`,`actual`,`gs`,`H`] >>
    disch_then (map_every assume_tac o CONJUNCTS) >>
    qabbrev_tac `entry_src = es0 with <|gas_obs := gs;
      outcomes := SOME (MAP SND (call_trace eg))|>` >>
    linked_entry_machine_variant_tac >>
    linked_entry_machine_frame_tac ``eg:execution_state`` >>
    linked_entry_machine_world_tac ``eg:execution_state`` >>
    `call_ctx_rel cx.txn actual.vs_call_ctx actual.vs_tx_ctx actual.vs_block_ctx` by
      linked_entry_machine_call_tac ``eg:execution_state`` >>
    `actual.vs_call_ctx.cc_address = cx.txn.target` by linked_entry_machine_address_tac >>
    rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE linked_entry_machine_conjuncts_tac))) >>
  linked_entry_immutable_tac ``eg:execution_state`` >>
  (linked_checked_ctor_entry_goal >-
   (linked_checked_ctor_root_tac >> linked_checked_ctor_root_empty_tac >>
    linked_checked_ctor_root_bound_tac >>
    (linked_checked_ctor_prepare_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
    linked_checked_ctor_open_prepared_tac >> linked_checked_ctor_prepared_tac >>
    linked_checked_ctor_suffix_inputs_tac >>
    (linked_checked_ctor_suffix_tac >- linked_checked_ctor_suffix_premises_tac) >>
    linked_checked_ctor_suffix_open_tac >>
    (linked_checked_ctor_join_origin_goal >- linked_checked_ctor_join_origin_tac) >>
    linked_checked_ctor_join_mem_tac >>
    linked_checked_ctor_cursor_tac >> linked_checked_ctor_end_fmp_tac >>
    linked_checked_ctor_low_tac >> linked_checked_ctor_bytes_tac >>
    (linked_checked_ctor_formal_regions_goal >- linked_checked_ctor_formal_regions_tac) >>
    linked_checked_ctor_region_tac >> linked_checked_ctor_imm_tac >>
    linked_checked_ctor_finish_tac)) >>
  linked_ctor_paid_fields_tac >>
  linked_ctor_paid_backends_tac ``eg:execution_state`` >>
  linked_ctor_entry_storage_tac ``eg:execution_state`` >>
  linked_registered_state_frame_tac ``eg:execution_state`` >>
  linked_ctor_replay_source_tac ``eg:execution_state`` >>
  (linked_ctor_replay_prefix_tac ``eg:execution_state`` >-
    (reverse (linked_ctor_replay_prefix_open_tac ``eg:execution_state`` >-
       linked_ctor_replay_bad_tac ``eg:execution_state``) >-
       (linked_ctor_replay_exempt_open_tac >> linked_ctor_replay_exempt_eval_tac >>
        linked_ctor_replay_exempt_finish_tac >> linked_ctor_replay_exempt_error_tac) >>
     linked_ctor_replay_started_tac >>
     (conj_tac >- linked_ctor_replay_trace_tac) >>
     linked_ctor_replay_path_tac)) >>
  linked_ctor_terminal_install_tac >>
  (linked_ctor_terminal_exit_goal_tac >-
   (linked_ctor_terminal_exit_open_tac
    >~ [`expr_exit post_res _`] >- linked_ctor_terminal_exit_expr_tac >>
    simp[])) >>
  (linked_ctor_fallthrough_goal_tac >-
   (linked_ctor_fallthrough_open_tac >>
    (linked_ctor_fallthrough_fmp_goal_tac >- linked_ctor_fallthrough_fmp_tac) >>
    (linked_ctor_fallthrough_inv_goal_tac >-
      (linked_ctor_fallthrough_inv_tac >>
       (conj_tac >- linked_ctor_fallthrough_state_tac) >>
       (conj_tac >- linked_ctor_fallthrough_imm_tac) >>
       linked_ctor_fallthrough_ghost_tac)) >>
    linked_ctor_fallthrough_epilogue_tac >>
    (conj_tac >-
     ((linked_ctor_fallthrough_jmp_goal_tac >- linked_ctor_fallthrough_jmp_tac) >>
      linked_ctor_fallthrough_append_tac)) >>
    linked_ctor_fallthrough_install_tac >>
    (conj_tac >- linked_ctor_fallthrough_install_state_tac) >>
    (conj_tac >- linked_ctor_fallthrough_install_imm_tac) >>
    rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
  (linked_ctor_terminal_replay_goal_tac >-
   (reverse linked_ctor_terminal_replay_open_tac >-
      (linked_ctor_terminal_replay_exit_tac >> linked_ctor_terminal_replay_exit_close_tac) >>
    linked_ctor_terminal_replay_landed_tac >>
    linked_ctor_terminal_replay_land_fields_tac >>
    linked_ctor_terminal_replay_land_epilogue_tac >>
    linked_ctor_terminal_replay_land_close_tac)) >>
  linked_ctor_native_source_tac >> linked_ctor_native_posts_tac >> linked_ctor_native_land_tac >>
  (linked_ctor_native_replay_goal_tac ``eg:execution_state`` >-
   (linked_ctor_native_replay_open_tac >- (disj1_tac >> FIRST_ASSUM ACCEPT_TAC) >>
    (linked_ctor_native_replay_terminal_tac >-
     (linked_ctor_native_replay_premises_tac >>
      (conj_tac >- linked_ctor_native_replay_q_tac) >>
      linked_ctor_native_replay_r_tac)) >>
    linked_ctor_native_replay_close_tac)) >>
  (linked_registered_body_source_replay_goal >-
   (linked_registered_body_source_replay_tac >> linked_registered_body_source_witness_tac)) >>
  (linked_registered_body_goal_tac ``eg:execution_state`` >-
   (linked_registered_body_open_tac >>
    (linked_registered_body_local_ptr_goal >- linked_registered_body_local_ptr_tac) >>
    linked_registered_body_static_tac >>
    (linked_registered_body_state_tac >- linked_registered_body_state_premises_tac) >>
    linked_registered_body_state_close_tac >>
    linked_registered_body_control_tac >> linked_registered_body_headroom_tac >>
    (linked_registered_body_ghost_goal >-
     (linked_registered_body_ghost_open_tac >- linked_registered_body_ghost_frame_tac >>
      linked_registered_body_formals_tac >> linked_ctor_registered_ghost_bytes_tac)) >>
    (linked_registered_body_apply_tac >- linked_registered_body_apply_premises_tac) >>
    linked_registered_body_apply_close_tac)) >>
  (linked_registered_terminal_goal_tac ``eg:execution_state`` >-
   ((linked_registered_terminal_tac >- linked_registered_terminal_premises_tac) >>
    disch_then ACCEPT_TAC)) >>
  (linked_accepted_gas_raw_exit_goal >-
    (linked_accepted_gas_select_tac >> linked_accepted_gas_raw_exec_tac >>
     conj_tac >- linked_accepted_gas_raw_length_tac >>
     linked_accepted_gas_raw_size_tac)) >>
  linked_accepted_gas_layout_tac >>
  (sg linked_accepted_gas_raw_sized_package >-
    (linked_accepted_gas_raw_entry_tac >> linked_accepted_gas_block_safety_tac >>
     linked_accepted_gas_ptr_run_tac >> linked_accepted_gas_ptr_blocks_tac >>
     linked_accepted_gas_context_run_tac >> linked_accepted_gas_variant_mem_tac >>
     linked_accepted_gas_dload_reachable_tac >> linked_accepted_gas_dload_mem_tac >>
     linked_accepted_gas_selected_mem_tac)) >>
  pop_assum (mk_asm "linked_accepted_gas_raw_sized") >>
  (sg linked_accepted_gas_raw_package >-
    (gen_tac >> disch_tac >>
     asm "linked_accepted_gas_raw_sized" (drule_then (ACCEPT_TAC o CONJUNCT1)))) >>
  pop_assum (mk_asm "linked_accepted_gas_raw") >>
  `mem_inv (\ctx fn inst s. inst_create_size_ok inst s)
     deploy_out.po_unit.cu_context vs` suffices_by
    (disch_then (mk_asm "linked_accepted_gas_create_size") >>
     asm "linked_accepted_gas_shadow" mp_tac >>
     (impl_tac >- asm "linked_accepted_gas_raw" ACCEPT_TAC) >>
     disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
     (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >>
     (reverse conj_tac >-
       ((conj_tac >-
         (qx_gen_tac `vi` >> disch_tac >>
          asm "linked_accepted_gas_raw"
            (qspec_then `vi` (drule_then (map_every assume_tac o CONJUNCTS))) >>
          rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)) >>
        FIRST_ASSUM ACCEPT_TAC)) >>
     asm "linked_accepted_gas_create_size" ACCEPT_TAC) >>
  `fmp_free_ctx deploy_unit.cu_context` by
    (irule source_fmp_free >> conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  `fmp_variant_room (SOME fmp) deploy_out.po_unit.cu_context vs` by
    (PURE_REWRITE_TAC [fmp_variant_room_def] >>
     conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  `!vi. raw_variant fmp vi vs ==>
      o1_pre_walk_inv D deploy_unit.cu_context vi /\
      mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                               s.vs_code = vi.vs_code /\ s.vs_data_section = vi.vs_data_section)
        deploy_unit.cu_context vi` by
    (gen_tac >> disch_tac >>
     asm "linked_accepted_gas_raw"
       (qspec_then `vi` (drule_then (map_every assume_tac o CONJUNCTS))) >>
     `taint_within D deploy_unit.cu_context vi` by
       (qpat_assum `Abbrev (D = _)` (fn d =>
          simp[NoAsms, REWRITE_RULE [markerTheory.Abbrev_def] d, taint_within_def])) >>
     `mem_inv raw_mem_ok deploy_unit.cu_context vi` by
       (qpat_assum `raw_unit_memory_ok deploy_unit.cu_context vi` mp_tac >>
        simp[NoAsms, unitTransformDefsTheory.raw_unit_memory_ok_def, mem_inv_def, raw_mem_ok_def]) >>
     conj_tac
     >- (irule o1_source_pre_walk_inv >>
         rpt (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >>
         PURE_REWRITE_TAC [o1_src_inv_def] >>
         rpt conj_tac >> TRY (FIRST_ASSUM ACCEPT_TAC) >>
         qexists_tac `imm_len_mods mods` >> conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     FIRST_ASSUM ACCEPT_TAC) >>
  mp_tac (Q.INST [`mods` |-> `mods`, `exps` |-> `exps`, `am` |-> `am`,
    `tx` |-> `tx`, `rpolicy` |-> `rpolicy`, `unit` |-> `deploy_unit`,
    `out` |-> `deploy_out`, `vs` |-> `vs`, `D` |-> `D`, `fmp` |-> `fmp`]
    (SPEC_ALL deploy_entry_reachable_create_size_ok_mods)) >>
  impl_tac >-
    (rpt (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >>
     gen_tac >> disch_tac >>
     qpat_assum `!vi. raw_variant fmp vi vs ==> o1_pre_walk_inv _ _ vi /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     asm "linked_accepted_gas_raw_sized" (drule_then (assume_tac o CONJUNCT2)) >>
     qpat_assum `raw_variant fmp vi vs` (fn variant =>
       assume_tac (MATCH_MP raw_variant_call_ctx variant) >>
       assume_tac (MATCH_MP raw_variant_outcomes variant)) >>
     `~vi.vs_call_ctx.cc_static` by
       (qpat_assum `vi.vs_call_ctx = vs.vs_call_ctx` SUBST1_TAC >>
        FIRST_ASSUM ACCEPT_TAC) >>
     rpt (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >>
     qpat_assum `vi.vs_outcomes = vs.vs_outcomes` SUBST1_TAC >>
     qpat_assum `vs.vs_outcomes = MAP SND (call_trace eg)` SUBST1_TAC >>
     FIRST_ASSUM ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

Resume e2e_deploy_gas_sufficient_mods[linked_empty_deploy_gas]:
  qpat_assum `deploy_state_rel_mods mods exps (assemble prog') am tx eg`
    (strip_assume_tac o PURE_REWRITE_RULE [deploy_state_rel_mods_def]) >>
  drule_all linked_empty_deploy_source >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `installed` strip_assume_tac))) >>
  `vs.vs_data_section = [] /\ vs.vs_allocas = FEMPTY /\ ~vs.vs_halted` by
    simp[Abbr `vs`, opt_entry_state_own_def, entry_venom_state_frame_fields,
         entry_venom_state_fresh, rich_listTheory.DROP_LENGTH_APPEND] >>
  `FLOOKUP vs.vs_labels "runtime_begin" = SOME (n2w off)` by
    (qpat_assum `FLOOKUP (lo_reloc prog prog') "runtime_begin" = SOME off`
       (fn lab => simp[NoAsms, Abbr `vs`, opt_entry_state_own_def,
                     finite_mapTheory.FLOOKUP_o_f, lab])) >>
  `DROP off vs.vs_code = runtime_bc` by
    (qpat_assum `vs.vs_code = _` SUBST1_TAC >> asm_rewrite_tac[APPEND_NIL]) >>
  `LENGTH runtime_bc <= LENGTH (assemble prog')` by
    (qpat_assum `DROP off (assemble prog') = runtime_bc` (SUBST1_TAC o SYM) >>
     simp[listTheory.LENGTH_DROP]) >>
  `LENGTH runtime_bc + imm_len_mods mods < dimword (:256)` by
    (qpat_assum `imm_len_mods mods + _ + _ <= _` mp_tac >>
     qpat_assum `w2n fmp < 2 ** 254` mp_tac >>
     simp[NoAsms, wordsTheory.dimword_def, venomLayoutTheory.dimindex_256] >>
     decide_tac) >>
  `sfields_tenv_consistent (make_struct_fields_map_mods mods) (type_env_all_modules mods)` by
    (irule make_struct_fields_map_mods_consistent >>
     qexists_tac `F` >>
     qpat_assum `check_contract F am.layouts tx.target mods = SOME _`
       (ACCEPT_TAC o MATCH_MP check_contract_runtime_namespaces)) >>
  `mem_inv (\ctx fn inst s. inst_create_size_ok inst s)
     deploy_out.po_unit.cu_context vs` by
    (match_mp_tac o1OpcodeAbsenceTheory.mem_inv_create_size_ok_no_create >>
     conj_tac
     >- (qpat_assum `o1PipelineCorrect$o1_pipeline rpolicy deploy_unit = SOME deploy_out`
           (assume_tac o MATCH_MP run_venom_pipeline_success_unit_wf o
            BETA_RULE o REWRITE_RULE [o1PipelineCorrectTheory.o1_pipeline_def]) >>
         fs[venomCompilerWfTheory.unit_wf_def]) >>
     drule_all lower_vyper_deploy_unit_no_ctor_shape_mods >>
     disch_then assume_tac >>
     `!fn inst. MEM fn deploy_unit.cu_context.ctx_functions /\
        MEM inst (fn_insts fn) ==> inst.inst_opcode <> CREATE /\ inst.inst_opcode <> CREATE2` by
       (simp[install_immutable_reservation_def, mk_venom_context_def,
             mk_raw_function_def, fn_insts_def, fn_insts_blocks_def, mk_inst_def] >>
        rpt gen_tac >> strip_tac >>
        FIRST [qpat_assum `_ = inst` (SUBST1_TAC o SYM),
               qpat_assum `inst = _` SUBST1_TAC] >>
        simp_tac (srw_ss()) [mk_inst_def]) >>
     rpt gen_tac >> strip_tac >> conj_tac
     >- (qspecl_then [`rpolicy`,`deploy_unit`,`deploy_out`,`CREATE`]
           mp_tac o1OpcodeAbsenceTheory.o1_pipeline_opcode_absence >>
         impl_tac >- (asm_rewrite_tac[] >> rpt strip_tac >> metis_tac[]) >>
         disch_then drule_all >> simp[]) >>
     qspecl_then [`rpolicy`,`deploy_unit`,`deploy_out`,`CREATE2`]
       mp_tac o1OpcodeAbsenceTheory.o1_pipeline_opcode_absence >>
     impl_tac >- (asm_rewrite_tac[] >> rpt strip_tac >> metis_tac[]) >>
     disch_then drule_all >> simp[]) >>
  `FLOOKUP vs.vs_labels "code_end" = SOME (n2w (LENGTH (assemble prog')))` by
    (qpat_assum `FLOOKUP (lo_reloc prog prog') "code_end" = SOME (LENGTH (assemble prog'))`
       (fn lab => simp[NoAsms, Abbr `vs`, opt_entry_state_own_def,
                     finite_mapTheory.FLOOKUP_o_f, lab])) >>
  `code_layout_valid vs` by
    (PURE_REWRITE_TAC [code_layout_valid_def] >>
     conj_tac >- (qexists_tac `assemble prog'` >> FIRST_ASSUM ACCEPT_TAC) >>
     simp[] >>
     qpat_assum `LENGTH (assemble prog') < 65536` mp_tac >>
     simp[NoAsms, wordsTheory.dimword_def, venomLayoutTheory.dimindex_256] >>
     decide_tac) >>
  `o1_run_state_ok vs` by simp[o1_run_state_ok_def] >>
  `LENGTH vs.vs_data_section < dimword (:256) DIV 2` by
    simp[wordsTheory.dimword_def, venomLayoutTheory.dimindex_256] >>
  `!vi. raw_variant fmp vi vs ==>
    raw_unit_memory_ok deploy_unit.cu_context vi /\
    ptr_discipline (imm_len_mods mods) deploy_unit.cu_context vi /\
    taint_within D deploy_unit.cu_context vi /\
    mem_inv dload_offset_ok deploy_unit.cu_context vi /\
    mem_inv dload_headroom_ok deploy_unit.cu_context vi /\
    mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                             s.vs_code = vi.vs_code /\ s.vs_data_section = vi.vs_data_section)
      deploy_unit.cu_context vi /\
    ?post. run_context 1 deploy_unit.cu_context vi = Halt post /\
      post.vs_returndata = runtime_bc ++ REPLICATE (imm_len_mods mods) 0w /\
      post.vs_accounts = vs.vs_accounts /\ post.vs_transient = vs.vs_transient /\
      post.vs_logs = vs.vs_logs /\ post.vs_pending_deletions = vs.vs_pending_deletions /\
      post.vs_requests = vs.vs_requests` by
    (gen_tac >> strip_tac >>
     mp_tac (Q.INST [`unit` |-> `deploy_unit`, `rp` |-> `rpolicy`,
         `vs` |-> `vs`, `vi` |-> `vi`, `off` |-> `off`, `D` |-> `D`]
       (SPEC_ALL linked_empty_deploy_raw_variant)) >>
     impl_tac >- asm_rewrite_tac[] >> disch_then ACCEPT_TAC) >>
  `!vi. raw_variant fmp vi vs ==>
    raw_unit_memory_ok deploy_unit.cu_context vi /\
    ptr_discipline (imm_len_mods mods) deploy_unit.cu_context vi /\
    mem_inv dload_offset_ok deploy_unit.cu_context vi /\
    mem_inv dload_headroom_ok deploy_unit.cu_context vi /\
    mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                             s.vs_code = vi.vs_code /\ s.vs_data_section = vi.vs_data_section)
      deploy_unit.cu_context vi /\
    terminates (run_context fuel deploy_unit.cu_context vi)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!vi. raw_variant fmp vi vs ==> _ /\ _ /\ taint_within _ _ vi /\ _`
       (qspec_then `vi` (drule_then strip_assume_tac)) >>
     qpat_assum `!n s. terminates (run_context n _ s) ==> _`
       (qspecl_then [`1`,`vi`] mp_tac) >> simp[terminates_def]) >>
  asm_rewrite_tac[] >> suspend "linked_empty_deploy_gas_shadow"
QED

Resume e2e_deploy_gas_sufficient_mods[linked_empty_deploy_gas_shadow]:
  `code_end_offset_ok (raw_reachable vs) deploy_out.po_unit.cu_context` by
    (qspecl_then [`D`, `imm_len_mods mods`, `rpolicy`, `deploy_unit`,
                  `deploy_out`, `vs`, `fmp`]
       mp_tac o1StaticPipelineCorrectTheory.o1_pipeline_code_end_offset_ok_static_abort >>
     impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     disch_then (qx_choose_then `vcode` strip_assume_tac) >>
     qpat_assum `!vi. raw_variant _ vi vs ==> _ /\ _ /\ taint_within _ _ vi /\ _` (drule_then strip_assume_tac) >>
     qpat_x_assum `_ ==> code_end_offset_ok _ _ /\ _` mp_tac >>
     impl_tac >- asm_rewrite_tac[] >>
     disch_then (CONJUNCTS_THEN2 assume_tac (K ALL_TAC)) >>
     qpat_x_assum `code_end_offset_ok (\_ _ _ _. _) _` mp_tac >>
     simp_tac bool_ss [code_end_offset_ok_def, in_static_abort_prefix_def] >>
     metis_tac[replay_exit_raw_call_ctx]) >>
  qspecl_then [`D`, `imm_len_mods mods`, `rpolicy`, `deploy_unit`,
                `deploy_out`, `vs`, `fmp`]
    mp_tac o1PipelineCorrectTheory.run_venom_pipeline_correct >>
  impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  disch_then (qx_choose_then `vrun` strip_assume_tac) >>
  qpat_assum `!vi. raw_variant _ vi vs ==> _ /\ _ /\ taint_within _ _ vi /\ _` (drule_then strip_assume_tac) >>
  qpat_x_assum `_ ==> ctx_sim D _ _ vrun vs /\ _` mp_tac >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then strip_assume_tac >>
  qpat_x_assum `ctx_sim D _ _ vrun vs` (mp_tac o REWRITE_RULE [ctx_sim_def]) >>
  disch_then (qspec_then `1` mp_tac) >>
  simp[terminates_def] >>
  disch_then (qx_choose_then `opt_fuel` assume_tac) >>
  `?post. run_context opt_fuel deploy_out.po_unit.cu_context vs = Halt post /\
          LENGTH post.vs_returndata = LENGTH runtime_bc + imm_len_mods mods` by
    (Cases_on `run_context opt_fuel deploy_out.po_unit.cu_context vs` >>
     qpat_x_assum `dead_result_rel D (Halt raw) _`
       (mp_tac o SIMP_RULE (srw_ss()) [dead_result_rel_def]) >>
     simp_tac (srw_ss()) [] >> strip_tac >>
     qpat_assum `LENGTH post.vs_returndata = LENGTH v.vs_returndata` (SUBST1_TAC o SYM) >>
     qpat_assum `post.vs_returndata = runtime_bc ++ _` SUBST1_TAC >>
     simp_tac (srw_ss()) []) >>
  drule_all o1_pipeline_memory_obligations_raw >> strip_tac >>
  drule_all o1_pipeline_codegen_obligations >> strip_tac >>
  `fin = K SOME ==> initial_ctx_rel cplan prog deploy_out.po_unit.cu_context vs
        (shadow_root eg)` by
    (strip_tac >>
     `prog' = prog` by fs[] >>
     qpat_x_assum `prog' = prog` SUBST_ALL_TAC >>
     `vs = entry_venom_state prog cplan eg with vs_alloca_next := imm_len_mods mods` by
       simp[Abbr `vs`, opt_entry_state_own_identity] >>
     `eg.txParams.blockNumber < dimword (:256)` by
       (fs[tx_block_fields_rel_def, tx_env_ok_def] >>
        irule lt_dimword_256 >> qexists_tac `255` >> simp[]) >>
     `call_trace (shadow_root eg) = call_trace eg` by
       simp[call_trace_def, shadow_root_frame_obs] >>
     `gas_readings (shadow_root eg) = gas_readings eg` by
       (qpat_x_assum `shadow_root eg = _` kall_tac >>
        qpat_x_assum `Abbrev (eg = _)` kall_tac >>
        simp[gas_readings_def, shadow_root_frame_obs]) >>
     `?fn fns. deploy_out.po_unit.cu_context.ctx_functions = fn::fns /\
               get_params (HD fn.fn_blocks).bb_instructions = []` by
       (qpat_assum `unit_shape_ok _`
          (mp_tac o PURE_REWRITE_RULE [unit_shape_ok_def, entry_fn_first_def]) >>
        disch_then (CONJUNCTS_THEN2
          (qx_choosel_then [`entry_name`, `entry_fn`, `other_fns`] strip_assume_tac)
          strip_assume_tac) >>
        qexistsl [`entry_fn`, `other_fns`] >> conj_tac
        >- FIRST_ASSUM ACCEPT_TAC >>
        qpat_assum `get_params (HD (HD _).fn_blocks).bb_instructions = []` mp_tac >>
        qpat_assum `deploy_out.po_unit.cu_context.ctx_functions = entry_fn::other_fns` SUBST1_TAC >>
        simp[NoAsms]) >>
     qabbrev_tac `c = ctxt with msgParams updated_by
                          (\mp. mp with outputTo := Memory <|offset := 0; size := 0|>)` >>
     `(shadow_root eg).contexts = [(c,rb)]` by
       (qpat_assum `eg.contexts = [(ctxt,rb)]` (fn contexts =>
          simp_tac (srw_ss()) [contexts, Abbr `c`, shadow_root_def,
            shadow_root_contexts_def])) >>
     `msg_ctx_rel vs.vs_call_ctx c.msgParams /\
      tx_ctx_rel vs.vs_tx_ctx (shadow_root eg).txParams /\
      block_ctx_rel vs.vs_block_ctx (shadow_root eg).txParams /\
      blockhash_rel vs (shadow_root eg).txParams` by
       (qpat_assum `vs = _ with vs_alloca_next := _` SUBST1_TAC >>
        qspecl_then [`eg`,`ctxt`,`rb`,`[]`,`prog`,`cplan`] mp_tac
          entry_venom_state_evm_environment >>
        impl_tac >- (conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
        simp[NoAsms, Abbr `c`, shadow_root_def, msg_ctx_rel_def, blockhash_rel_def]) >>
     `vs.vs_params = []` by
       (qpat_assum `vs = _ with vs_alloca_next := _` SUBST1_TAC >>
        simp[NoAsms, entry_venom_state_def, init_venom_state_def]) >>
     `ctxt' = ctxt /\ rb' = rb` by
       (qpat_assum `eg.contexts = [(ctxt',rb')]` (fn right =>
          qpat_assum `eg.contexts = [(ctxt,rb)]` (mp_tac o TRANS (SYM right))) >>
        simp_tac (srw_ss()) []) >>
     qpat_x_assum `ctxt' = ctxt` SUBST_ALL_TAC >>
     qpat_x_assum `rb' = rb` SUBST_ALL_TAC >>
     `initial_state_rel cplan prog 0 fn vs (shadow_root eg)` by
       (qpat_x_assum `shadow_root eg = _` kall_tac >>
        qpat_x_assum `Abbrev (eg = _)` kall_tac >>
        PURE_REWRITE_TAC [initial_state_rel_def] >>
        qpat_assum `(shadow_root eg).contexts = [(c,rb)]` (fn th =>
          simp_tac (srw_ss()) [th, stack_params_rel_def]) >>
        asm_rewrite_tac[] >>
        qpat_assum `vs = _ with vs_alloca_next := _` SUBST1_TAC >>
        simp[entry_venom_state_fresh, entry_venom_state_frame_fields,
             entry_venom_state_created_in_tx, asm_pc_to_offset_zero,
             context_memory_rel_def, Abbr `c`, shadow_root_def,
             rich_listTheory.DROP_LENGTH_APPEND]) >>
     PURE_REWRITE_TAC [initial_ctx_rel_def] >>
     qexistsl [`fn`, `fns`, `c`, `rb`, `[]`] >>
     `(shadow_root eg).msdomain = eg.msdomain` by simp[NoAsms, shadow_root_def] >>
     `c.msgParams.code = assemble prog ++ vs.vs_data_section` by
       (qpat_assum `vs = _ with vs_alloca_next := _` SUBST1_TAC >>
        simp[Abbr `c`, entry_venom_state_frame_fields, rich_listTheory.DROP_LENGTH_APPEND]) >>
     `vs.vs_call_ctx.cc_created_in_tx` by
       (qpat_assum `vs = _ with vs_alloca_next := _` SUBST1_TAC >>
        simp[entry_venom_state_created_in_tx]) >>
     `c.msgParams.parsed = parse_code 0 FEMPTY c.msgParams.code /\ c.logs = []` by
       (simp[NoAsms, Abbr `c`] >> conj_tac
        >- (qpat_assum `ctxt.msgParams.code = assemble prog ++ args_bytes`
              (fn th => REWRITE_TAC [th]) >> FIRST_ASSUM ACCEPT_TAC) >>
        FIRST_ASSUM ACCEPT_TAC) >>
     simp[shadow_root_wf_state] >>
     qpat_assum `vs = _ with vs_alloca_next := _` SUBST1_TAC >>
     simp[entry_venom_state_fresh, entry_venom_state_frame_fields] >>
     simp[initial_codegen_state_rel_def, entry_venom_state_def, init_venom_state_def]) >>
  `?sr ghost. run_call (shadow_root eg) = SOME (sr,ghost) /\
    (frame_resource_starved (shadow_root eg) sr ghost \/
     venom_frame_rel (shadow_root eg) sr ghost (Halt post'))` by
    (Cases_on `fin = K SOME`
     >- (qspecl_then [`opt_fuel`,`rpolicy`,`deploy_out.po_unit`,`cplan`,`prog`,
                       `raw_reachable vs`,`vs`,`shadow_root eg`]
          mp_tac codegen_correct >>
         impl_tac >- (rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE fs[])) >>
         simp[]) >>
     `fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
     qpat_x_assum `fin = asm_opt_finalizer` SUBST_ALL_TAC >>
     qspecl_then [`opt_fuel`,`rpolicy`,`deploy_out.po_unit`,`cplan`,`prog`,`prog'`,
                   `raw_reachable vs`,`vs`,`shadow_root eg`]
       mp_tac codegen_correct_asm_opt_own >>
     impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >> simp[]) >>
  `?c rb'. (shadow_root eg).contexts = [(c,rb')]` by
    (qpat_assum `eg.contexts = [(ctxt,rb)]` (fn contexts =>
       simp[NoAsms, shadow_root_def, shadow_root_contexts_def, contexts])) >>
  FIRST [
    qpat_x_assum `frame_resource_starved (shadow_root eg) sr ghost`
        (qx_choosel_then [`exc`,`out`,`lgs`] (map_every assume_tac o CONJUNCTS) o
         REWRITE_RULE [frame_resource_starved_def]) >>
    qexistsl_tac [`SOME exc`,`ghost`],
    qpat_x_assum `venom_frame_rel (shadow_root eg) sr ghost (Halt post')`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [venom_frame_rel_def]) >>
    qexistsl_tac [`NONE`,`ghost`]] >>
  qpat_assum `(shadow_root eg).contexts = [(_,_)]` (fn context =>
    qpat_x_assum `frame_outcome (shadow_root eg) sr ghost _ _ _`
      (strip_assume_tac o SIMP_RULE (srw_ss()) [frame_outcome_def, context])) >>
  qpat_assum `shadow_root eg = _` (PURE_REWRITE_TAC o single o SYM) >>
  simp[] >> rpt strip_tac >> gvs[]
QED

Resume e2e_deploy_gas_sufficient_mods[linked_deploy_ctor_raw_prefix]:
  gen_tac >> strip_tac >>
  qabbrev_tac `start = vi with <|vs_prev_bb := NONE; vs_current_bb := "__deploy"; vs_inst_idx := 0|>` >>
  `vi = vs with <|vs_fmp := fmp; vs_initial_fmp := fmp;
                 vs_gas_readings := vi.vs_gas_readings|>` by
    (qpat_assum `raw_variant fmp vi vs`
       (mp_tac o PURE_REWRITE_RULE [raw_variant_def, gas_variant_def]) >>
     simp[NoAsms, venom_state_component_equality] >> strip_tac >>
     qpat_assum `fmp = vi.vs_initial_fmp` (fn h =>
       qpat_assum `fmp = vi.vs_fmp` (ACCEPT_TAC o TRANS (SYM h)))) >>
  `fresh_vars_wrt (initial_compile_state "__deploy") start /\
   ~start.vs_halted /\ start.vs_current_bb = (initial_compile_state "__deploy").cs_current_bb /\
   start.vs_inst_idx = LENGTH (initial_compile_state "__deploy").cs_current_insts /\
   vars_pc_only vi start` by
    (conj_tac
     >- (qunabbrev_tac `start` >>
         qpat_assum `vi = _` SUBST1_TAC >>
         simp[NoAsms, Abbr `vs`, fresh_vars_wrt_def, initial_compile_state_def, lookup_var_def,
              opt_entry_state_own_def, entry_venom_state_fresh]) >>
     simp[NoAsms, Abbr `start`, initial_compile_state_def, vars_pc_only_def] >>
     qpat_assum `vi = _` SUBST1_TAC >>
     simp[NoAsms, Abbr `vs`, opt_entry_state_own_def, entry_venom_state_fresh]) >>
  SUBGOAL_THEN ``mut = Payable \/ start.vs_call_ctx.cc_callvalue = 0w`` ASSUME_TAC
  >- (qpat_assum `mut = Payable \/ tx.value = 0` mp_tac >>
      `start.vs_call_ctx.cc_callvalue = n2w tx.value` by
        (drule raw_variant_call_ctx >> simp[Abbr `start`]) >>
      qpat_assum `start.vs_call_ctx.cc_callvalue = _` (fn callvalue =>
        simp[NoAsms, callvalue]) >>
      disch_then (DISJ_CASES_THEN (fn h => simp[NoAsms, h]))) >>
  qspecl_then [`mut = Payable`,`imm_len_mods mods`,`initial_compile_state "__deploy"`,
    `st_pay`,`st1`,`imm`,`deploy_unit.cu_context`,`fn`,`start`]
    mp_tac deploy_ctor_pre_register_gas_path >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `t` (map_every assume_tac o CONJUNCTS)) >>
  `vars_pc_only vi t` by
    (irule vars_pc_only_trans >> qexists_tac `start` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `t` >> qunabbrev_tac `start` >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise e2e_deploy_gas_sufficient_mods

Theorem vyper_call_gas_sufficient_mods:
  !fin policy mods exps deploy_bc runtime_bc am tx es.
    fin IN accepted_finalizers /\
    compile_vyper_mods fin policy mods exps = SOME (deploy_bc, runtime_bc) /\
    source_typing_ok_mods mods exps am tx /\
    call_state_rel_mods mods exps runtime_bc am tx es
    ==>
    ?g. !g'.
      g <= g' ==>
      ?r es'.
        run_call (add_frame_gas g' es) = SOME (r, es') /\
        ((!f vals.
            calldata_dispatch_mods mods exps tx.calldata = SOME (f, vals) ==>
              (!gs. call_storage_ok am
                 (tx with <| function_name := f; args := vals |>)
                 (MAP SND (call_trace (add_frame_gas g' es))) gs) /\
              (!obs. ~gas_source_exempt_mods mods
                 (tx with <| function_name := f; args := vals |>)
                 (call_external (SOME (MAP SND (call_trace (add_frame_gas g' es))))
                    obs am (tx with <| function_name := f; args := vals |>))) /\
              LENGTH (call_trace (add_frame_gas g' es)) < 2 ** 64) ==>
         ~frame_raises (add_frame_gas g' es) OutOfGas)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `compile_vyper_mods _ _ _ _ = _`
    (strip_assume_tac o MATCH_MP compile_vyper_with_mods_success_phases o
     REWRITE_RULE [compile_vyper_mods_def]) >>
  qpat_assum `call_state_rel_mods _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [call_state_rel_mods_def]) >>
  drule_all source_typing_ok_runtime_ready_mods >> strip_tac >>
  drule_all lower_vyper_runtime_unit_source_unit_ok_mods >> strip_tac >>
  drule lower_vyper_runtime_unit_raw_shape_mods >> strip_tac >>
  drule lower_vyper_runtime_unit_data_empty_mods >> strip_tac >>
  drule lower_vyper_runtime_unit_global_reserved_mods >> strip_tac >>
  `fixed_region_reserved 0 runtime_unit.cu_context /\
   reserved_intervals_wf runtime_unit.cu_context.ctx_global_reserved` by
    simp[fixed_region_reserved_def, reserved_intervals_wf_def] >>
  `o1PipelineCorrect$o1_pipeline rpolicy runtime_unit = SOME runtime_out` by
    fs[o1PipelineCorrectTheory.o1_pipeline_def] >>
  drule_all o1PipelineCorrectTheory.run_venom_pipeline_output_shape >> strip_tac >>
  `codegen_ready runtime_out.po_unit.cu_context` by
    (qpat_assum `o1PipelineCorrect$o1_pipeline _ runtime_unit = _`
       (mp_tac o MATCH_MP run_venom_pipeline_success_boundary o
        REWRITE_RULE [o1PipelineCorrectTheory.o1_pipeline_def]) >> simp[]) >>
  `!fn inst. MEM fn runtime_unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
     source_inst_ok ({"code_end"},T) inst` by
    metis_tac[lower_vyper_runtime_unit_label_checks_mods] >>
  drule_all source_own_flow >> strip_tac >>
  `!fn inst. MEM fn runtime_unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
     ~MEM (Label "runtime_begin") inst.inst_operands` by
    (rpt strip_tac >>
     drule_all (Q.INST [`source_checks` |-> `({"runtime_begin"},F)`]
       lower_vyper_runtime_unit_label_checks_mods) >>
     simp[source_inst_ok_def, EVERY_MEM, rb_operand_ok_for_def] >>
     qexists_tac `Label "runtime_begin"` >> simp[]) >>
  `sym_unit_static_ok runtime_out.po_unit` by
    (qspecl_then [`rpolicy`, `runtime_unit`, `runtime_out`]
       mp_tac o1_pipeline_sym_unit_static_ok >> simp[] >> metis_tac[]) >>
  drule_all gasFocusOptLabelFlowTheory.focus_opt_label_flow_own >> strip_tac >>
  qpat_assum `finalize_codegen _ _ _.po_unit = SOME runtime_bc`
    (strip_assume_tac o MATCH_MP finalize_codegen_success_plan) >>
  `cplan.cp_initial_fmp < 2 ** 254` by
    (fs[generate_context_plan_def] >>
     drule generate_context_plan_with_headroom >> simp[]) >>
  `?fmp:bytes32.
    w2n (opt_entry_state_own prog prog' cplan es).vs_initial_fmp <= w2n fmp /\
    w2n fmp < 2 ** 254 /\
    unit_alloca_budget runtime_unit.cu_context +
      32 * ctx_dload_count runtime_unit.cu_context <= w2n fmp` by
    (irule call_raw_fmp_exists_mods >> asm_rewrite_tac[]) >>
  `o1_initial_state_ok (opt_entry_state_own prog prog' cplan es) /\
   (opt_entry_state_own prog prog' cplan es).vs_fmp =
     (opt_entry_state_own prog prog' cplan es).vs_initial_fmp /\
   (opt_entry_state_own prog prog' cplan es).vs_initial_fmp = n2w cplan.cp_initial_fmp` by
    simp[opt_entry_state_own_def, entry_venom_state_def, o1_initial_state_ok_def,
         init_venom_state_def] >>
  `!eom. max_live_eom runtime_out.po_unit.cu_context = SOME eom ==>
          eom <= w2n (opt_entry_state_own prog prog' cplan es).vs_initial_fmp` by
    (qspecl_then [`runtime_out.po_unit.cu_context`, `cplan`,
        `opt_entry_state_own prog prog' cplan es`]
       mp_tac o1PipelineCorrectTheory.generate_context_plan_eom_room >> simp[]) >>
  `call_state_rel_mods mods exps (assemble prog') am tx es` by fs[] >>
  `code_layout_valid (opt_entry_state_own prog prog' cplan es)` by
    (qspecl_then [`fin`, `mods`, `exps`, `rpolicy`, `prog`, `prog'`,
         `am`, `tx`, `es`, `cplan`, `runtime_out.po_unit`]
       mp_tac opt_entry_code_layout_valid_own_mods >>
     asm_rewrite_tac[]) >>
  drule_then (qx_choose_then `fuel` assume_tac)
    lower_vyper_runtime_unit_uniform_fuel_mods >>
  qspecl_then [`0`, `rpolicy`, `runtime_unit`, `runtime_out`, `cplan`, `fuel`]
    mp_tac o1StaticPipelineCorrectTheory.run_venom_pipeline_run_bounded_static_abort >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`fuel'`, `M`] assume_tac) >>
  `assemble prog' <> []` by
    (Cases_on `fin = K SOME`
     >- (drule codegen_assembly_nonempty >> gvs[]) >>
     `fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
     qpat_x_assum `fin = asm_opt_finalizer` SUBST_ALL_TAC >>
     irule codegen_assembly_finalizer_nonempty >>
     qexistsl [`prog`,`rpolicy`,`runtime_out.po_unit`] >> simp[]) >>
  qspecl_then [`mods`, `exps`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`]
    mp_tac opt_entry_asm_rels_own_mods >>
  impl_tac >- asm_rewrite_tac[] >> strip_tac >>
  `wf_state es` by fs[evm_state_ok_def] >>
  `!g. opt_entry_state_own prog prog' cplan (add_frame_gas g es) =
      opt_entry_state_own prog prog' cplan es with
        <|vs_outcomes := MAP SND (call_trace (add_frame_gas g es));
          vs_gas_readings := gas_readings (add_frame_gas g es)|>` by
    simp[NoAsms, opt_entry_state_own_def, entry_venom_state_add_frame_gas,
         venom_state_component_equality] >>
  `!g. code_layout_valid (opt_entry_state_own prog prog' cplan (add_frame_gas g es)) /\
       (opt_entry_state_own prog prog' cplan (add_frame_gas g es)).vs_code =
       assemble prog' ++
         (opt_entry_state_own prog prog' cplan (add_frame_gas g es)).vs_data_section` by
    (gen_tac >>
     qpat_assum `!g. opt_entry_state_own _ _ _ (add_frame_gas g es) = _`
       (qspec_then `g` SUBST1_TAC) >>
     qpat_assum `code_layout_valid (opt_entry_state_own _ _ _ es)` mp_tac >>
     qpat_assum `(opt_entry_state_own _ _ _ es).vs_code = _` mp_tac >>
     simp[NoAsms, code_layout_valid_def]) >>
  `!g.
     codegen_asm_entry_rel_reloc (lo_reloc prog prog') cplan prog
       (opt_entry_state_own prog prog' cplan (add_frame_gas g es))
       (entry_asm_state (opt_entry_state_own prog prog' cplan (add_frame_gas g es))
          (add_frame_gas g es)) /\
     asm_frame_rel prog'
       (opt_entry_state_own prog prog' cplan (add_frame_gas g es)).vs_data_section
       (add_frame_gas g es)
       (entry_asm_state (opt_entry_state_own prog prog' cplan (add_frame_gas g es))
          (add_frame_gas g es)) (add_frame_gas g es)` by
    (gen_tac >>
     qpat_assum `!g. opt_entry_state_own _ _ _ (add_frame_gas g es) = _`
       (qspec_then `g` SUBST1_TAC) >>
     drule add_frame_gas_contexts >> disch_then (qspec_then `g` assume_tac) >>
     `(add_frame_gas g es).originalAccounts = es.originalAccounts` by
       simp[add_frame_gas_def] >>
     `wf_state (add_frame_gas g es)` by simp[add_frame_gas_wf_state] >>
     conj_tac
     >- (qpat_assum `codegen_asm_entry_rel_reloc _ _ _ _ _` mp_tac >>
         qpat_assum `es.contexts = _` (fn before_gas =>
           qpat_assum `(add_frame_gas g es).contexts = _` (fn after_gas =>
             simp[NoAsms, before_gas, after_gas, codegen_asm_entry_rel_reloc_def,
                  entry_asm_state_def, shared_state_rel_def,
                  venom_asm_terminal_rel_def]))) >>
     qpat_assum `asm_frame_rel _ _ _ _ _` mp_tac >>
     qpat_assum `es.contexts = _` (fn before_gas =>
       qpat_assum `(add_frame_gas g es).contexts = _` (fn after_gas =>
         simp[NoAsms, before_gas, after_gas, asm_frame_rel_def, asm_evm_rel_def,
              entry_asm_state_def, opt_entry_state_own_def,
              entry_venom_state_frame_fields, entry_venom_state_fresh,
              add_frame_gas_fields, relationTheory.RTC_REFL])) >>
     asm_rewrite_tac[]) >>
  qspecl_then [`fin`, `rpolicy`, `runtime_out.po_unit`, `cplan`,
    `prog`, `prog'`, `fuel'`, `M`, `0`] mp_tac codegen_gas_surplus_finalized_own >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choose_then `g` assume_tac) >>
  qexists_tac `g` >> gen_tac >> strip_tac >>
  qabbrev_tac `eg = add_frame_gas g' es` >>
  qspec_then `eg` (qx_choosel_then [`r`, `es'`] assume_tac) run_call_total >>
  qexistsl [`r`, `es'`] >> asm_rewrite_tac[] >>
  strip_tac >> strip_tac >>
  `?op. frame_inst_raises eg OutOfGas op` by
    (qpat_assum `call_state_rel_mods _ _ runtime_bc _ _ es`
       (mp_tac o MATCH_MP call_state_rel_add_frame_gas_raises_mods) >>
     disch_then (qspec_then `g'` mp_tac) >> simp[Abbr `eg`]) >>
  qpat_x_assum `frame_inst_raises eg OutOfGas _`
    (strip_assume_tac o PURE_REWRITE_RULE [frame_inst_raises_def]) >>
  qabbrev_tac `vs = opt_entry_state_own prog prog' cplan eg` >>
  `g' <= frame_gas_left eg /\ wf_state eg` by
    simp[Abbr `eg`, wf_state_frame_gas_left, add_frame_gas_wf_state] >>
  `LENGTH s'.contexts = LENGTH s.contexts` by fs[frame_inst_at_step] >>
  `initial_venom_state_rel_mods mods am tx vs` by
    (`initial_venom_state_rel_mods mods am tx
        (opt_entry_state_own prog prog' cplan es)` by
       (qspecl_then [`mods`, `exps`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`]
          mp_tac opt_entry_initial_venom_state_rel_mods >> asm_rewrite_tac[]) >>
     qunabbrev_tac `vs` >> qunabbrev_tac `eg` >>
     qpat_assum `!g. opt_entry_state_own _ _ _ (add_frame_gas g es) = _`
       (qspec_then `g'` SUBST1_TAC) >>
     qpat_x_assum `initial_venom_state_rel_mods _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE
          [initial_venom_state_rel_mods_def, venom_env_rel_def]) >>
     simp[NoAsms, initial_venom_state_rel_mods_def, venom_env_rel_def] >>
     rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  `o1_initial_state_ok vs /\ vs.vs_initial_fmp = n2w cplan.cp_initial_fmp /\
   vs.vs_fmp = vs.vs_initial_fmp /\ w2n vs.vs_initial_fmp <= w2n fmp /\
   vs.vs_outcomes = MAP SND (call_trace eg) /\ vs.vs_gas_readings = gas_readings eg` by
    (conj_tac
     >- (qpat_assum `initial_venom_state_rel_mods mods am tx vs`
           (strip_assume_tac o PURE_REWRITE_RULE [initial_venom_state_rel_mods_def]) >>
         simp[o1_initial_state_ok_def]) >>
     `vs.vs_initial_fmp = n2w cplan.cp_initial_fmp /\ vs.vs_fmp = vs.vs_initial_fmp` by
       simp[NoAsms, Abbr `vs`, opt_entry_state_own_def, entry_venom_state_def] >>
     asm_rewrite_tac[] >>
     conj_tac
     >- (qpat_assum `w2n (opt_entry_state_own _ _ _ es).vs_initial_fmp <= w2n fmp` mp_tac >>
         simp[NoAsms, opt_entry_state_own_def, entry_venom_state_def]) >>
     simp[NoAsms, Abbr `vs`, opt_entry_state_own_def, entry_venom_state_frame_fields]) >>
  `code_layout_valid vs /\ vs.vs_code = assemble prog' ++ vs.vs_data_section` by
    (qpat_assum `!g. code_layout_valid (opt_entry_state_own _ _ _ _) /\ _`
       (qspec_then `g'` mp_tac) >> simp[Abbr `vs`, Abbr `eg`]) >>
  `LENGTH vs.vs_data_section < dimword (:256) DIV 2` by
    (mp_tac (Q.INST [`vs` |-> `vs`, `prefix` |-> `assemble prog'`]
       e2eCorrectnessTheory.data_section_length_bound) >> asm_rewrite_tac[]) >>
  `!eom. max_live_eom runtime_out.po_unit.cu_context = SOME eom ==>
          eom <= w2n vs.vs_initial_fmp` by
    (qspecl_then [`runtime_out.po_unit.cu_context`, `cplan`, `vs`]
      mp_tac o1PipelineCorrectTheory.generate_context_plan_eom_room >> simp[]) >>
  `o1_lowered_inv runtime_out.po_unit.cu_context vs /\
    code_end_offset_ok (raw_reachable vs) runtime_out.po_unit.cu_context /\
    venom_run_bounded fuel' M runtime_out.po_unit.cu_context vs /\
    mem_inv (\ctx fn inst s. inst_create_size_ok inst s)
      runtime_out.po_unit.cu_context vs` suffices_by
    (strip_tac >>
     drule_all o1_pipeline_memory_obligations_raw >> strip_tac >>
     drule_all o1_pipeline_codegen_obligations >> strip_tac >>
     qpat_x_assum `!g' Inv vs es s op res s'. _`
       (qspecl_then [`g'`, `raw_reachable vs`, `vs`, `es`,
                     `s`, `op`, `INR (SOME OutOfGas)`, `s'`] mp_tac) >>
     fs[Abbr `vs`, Abbr `eg`]) >>
  `vs.vs_call_ctx.cc_static = tx.is_static` by
    (qpat_assum `initial_venom_state_rel_mods _ _ _ vs`
       (strip_assume_tac o PURE_REWRITE_RULE
          [initial_venom_state_rel_mods_def, venom_env_rel_def, call_ctx_rel_def]) >>
     FIRST_ASSUM ACCEPT_TAC) >>
  qabbrev_tac `D = <|d_stor := K (K UNIV); d_trans := K (K UNIV);
                       d_imm := K UNIV; d_ret := K UNIV|>` >>
  `dead_wf D` by simp[Abbr `D`, dead_wf_def] >>
  `!vi. raw_variant fmp vi vs ==>
       initial_venom_state_rel_mods mods am tx vi /\ code_layout_valid vi /\
       vi.vs_fmp = fmp /\ vi.vs_initial_fmp = fmp /\ vi.vs_outcomes = vs.vs_outcomes` by
    (gen_tac >> strip_tac >>
     `vi = vs with <|vs_fmp := fmp; vs_initial_fmp := fmp;
                     vs_gas_readings := vi.vs_gas_readings|>` by
       (qpat_assum `raw_variant fmp vi vs`
          (mp_tac o PURE_REWRITE_RULE [raw_variant_def, gas_variant_def]) >>
        simp[NoAsms, venom_state_component_equality] >> strip_tac >>
        qpat_assum `fmp = vi.vs_initial_fmp` (fn h =>
          qpat_assum `fmp = vi.vs_fmp` (ACCEPT_TAC o TRANS (SYM h)))) >>
     qpat_assum `vi = _` SUBST1_TAC >>
     conj_tac
     >- (qpat_assum `initial_venom_state_rel_mods _ _ _ vs` mp_tac >>
         simp[NoAsms, initial_venom_state_rel_mods_def, venom_env_rel_def]) >>
     qpat_assum `code_layout_valid vs` mp_tac >>
     simp[NoAsms, code_layout_valid_def]) >>
  `!vi. raw_variant fmp vi vs ==>
       mem_inv dload_headroom_ok runtime_unit.cu_context vi /\
       taint_within D runtime_unit.cu_context vi` by
    (gen_tac >> strip_tac >>
     qpat_assum `!vi. raw_variant fmp vi vs ==> _` (drule_then strip_assume_tac) >>
     conj_tac
     >- (qspecl_then [`mods`, `exps`, `rpolicy`, `runtime_unit`, `am`, `tx`, `vi`]
            mp_tac lower_vyper_runtime_unit_dload_headroom_ok_mods >>
         asm_rewrite_tac[]) >>
     simp[Abbr `D`, taint_within_def]) >>
  `mem_inv (\ctx fn inst s. inst_create_size_ok inst s)
      runtime_out.po_unit.cu_context vs /\
    (!vi. raw_variant fmp vi vs ==>
      raw_unit_memory_ok runtime_unit.cu_context vi /\
      ptr_discipline 0 runtime_unit.cu_context vi /\
      mem_inv dload_offset_ok runtime_unit.cu_context vi /\
      mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                               s.vs_code = vi.vs_code /\
                               s.vs_data_section = vi.vs_data_section)
        runtime_unit.cu_context vi /\
      terminates (run_context fuel runtime_unit.cu_context vi) /\
      (tx.is_static ==>
       ~(!n. terminates (run_context n runtime_unit.cu_context vi) ==>
             ?u. run_context n runtime_unit.cu_context vi = Abort ExHalt_abort u)))`
    suffices_by
    (strip_tac >>
     `venom_run_bounded fuel' M runtime_out.po_unit.cu_context vs` by
       (qpat_assum `!D vs fmp. _ ==> venom_run_bounded _ _ _ _`
          (qspecl_then [`D`, `vs`, `fmp`] mp_tac) >>
        impl_tac
        >- (rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE
              (gen_tac >> strip_tac >>
               qpat_assum `!vi. raw_variant _ vi vs ==> raw_unit_memory_ok _ _ /\ _`
          (drule_then strip_assume_tac) >>
        qpat_assum `!vi. raw_variant _ vi vs ==> mem_inv dload_headroom_ok _ _ /\ _`
          (drule_then strip_assume_tac) >>
               qpat_assum `!vi. raw_variant _ vi vs ==> mem_inv dload_headroom_ok _ _ /\ _`
                 (drule_then strip_assume_tac) >>
               asm_rewrite_tac[]))) >>
        strip_tac) >>
     `code_end_offset_ok (raw_reachable vs) runtime_out.po_unit.cu_context` by
       (qspecl_then [`D`, `0`, `rpolicy`, `runtime_unit`, `runtime_out`, `vs`, `fmp`]
          mp_tac o1StaticPipelineCorrectTheory.o1_pipeline_code_end_offset_ok_static_abort >>
        impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
        disch_then (qx_choose_then `vcode` strip_assume_tac) >>
        qpat_assum `!vi. raw_variant _ vi vs ==> raw_unit_memory_ok _ _ /\ _`
          (drule_then strip_assume_tac) >>
        qpat_assum `!vi. raw_variant _ vi vs ==> mem_inv dload_headroom_ok _ _ /\ _`
          (drule_then strip_assume_tac) >>
        qpat_x_assum `_ ==> code_end_offset_ok _ _ /\ _` mp_tac >>
        impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
        disch_then (CONJUNCTS_THEN2 assume_tac (DISJ_CASES_THEN assume_tac))
        >- FIRST_ASSUM ACCEPT_TAC >>
        Cases_on `tx.is_static`
        >- (qpat_assum `tx.is_static ==> ~(!n. terminates
                   (run_context n runtime_unit.cu_context vcode) ==> _)` (fn h =>
              qpat_assum `tx.is_static` (fn hstatic =>
                qpat_assum `!n. terminates (run_context n runtime_unit.cu_context vcode) ==> _`
                  (CONTR_TAC o MP (NOT_ELIM (MP h hstatic)))))) >>
        qpat_x_assum `code_end_offset_ok (\_ _ _ _. _) _` mp_tac >>
        simp_tac bool_ss [code_end_offset_ok_def, in_static_abort_prefix_def] >>
        metis_tac[replay_exit_raw_call_ctx]) >>
     `o1_lowered_inv runtime_out.po_unit.cu_context vs` by
       (Cases_on `tx.is_static`
        >- (qspecl_then [`D`, `0`, `rpolicy`, `runtime_unit`, `runtime_out`, `vs`, `fmp`]
              mp_tac o1StaticPipelineCorrectTheory.run_venom_pipeline_correct_static_abort >>
            impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
            disch_then (qx_choose_then `vstatic` strip_assume_tac) >>
            qpat_assum `!vi. raw_variant _ vi vs ==> raw_unit_memory_ok _ _ /\ _`
          (drule_then strip_assume_tac) >>
        qpat_assum `!vi. raw_variant _ vi vs ==> mem_inv dload_headroom_ok _ _ /\ _`
          (drule_then strip_assume_tac) >>
            qpat_x_assum `_ ==> ctx_sim D _ _ vstatic vs /\ ctx_abort_rq D _ _ vstatic vs /\ _`
              mp_tac >>
            impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
            disch_then (CONJUNCTS_THEN2 (K ALL_TAC)
              (CONJUNCTS_THEN2 (K ALL_TAC) (DISJ_CASES_THEN assume_tac)))
            >- FIRST_ASSUM ACCEPT_TAC >>
            qpat_x_assum `(?eom. _) /\ !n. terminates
                (run_context n runtime_unit.cu_context vstatic) ==> _`
              (CONJUNCTS_THEN2 (K ALL_TAC) assume_tac) >>
            qpat_assum `tx.is_static ==> ~(!n. terminates
                 (run_context n runtime_unit.cu_context vstatic) ==> _)` (fn h =>
              qpat_assum `tx.is_static` (fn hstatic =>
                qpat_assum `!n. terminates (run_context n runtime_unit.cu_context vstatic) ==> _`
                  (CONTR_TAC o MP (NOT_ELIM (MP h hstatic)))))) >>
        `o1_run_state_ok vs` by simp[o1_run_state_ok_def] >>
        qspecl_then [`D`, `0`, `rpolicy`, `runtime_unit`, `runtime_out`, `vs`, `fmp`]
          mp_tac o1PipelineCorrectTheory.run_venom_pipeline_correct >>
        impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
        disch_then (qx_choose_then `vrun` strip_assume_tac) >>
        qpat_assum `!vi. raw_variant _ vi vs ==> raw_unit_memory_ok _ _ /\ _`
          (drule_then strip_assume_tac) >>
        qpat_assum `!vi. raw_variant _ vi vs ==> mem_inv dload_headroom_ok _ _ /\ _`
          (drule_then strip_assume_tac) >>
        qpat_x_assum `_ ==> ctx_sim D _ _ vrun vs /\ _` mp_tac >>
        impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >> simp[]) >>
     asm_rewrite_tac[]) >>
  suspend "linked_runtime_gas_bound"
QED

val linked_runtime_gas_raw_fields : term quotation =
  `raw_unit_memory_ok runtime_unit.cu_context vi /\
      ptr_discipline 0 runtime_unit.cu_context vi /\
      mem_inv dload_offset_ok runtime_unit.cu_context vi /\
      mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                               s.vs_code = vi.vs_code /\
                               s.vs_data_section = vi.vs_data_section)
        runtime_unit.cu_context vi /\
      terminates (run_context fuel runtime_unit.cu_context vi) /\
      (tx.is_static ==>
       ~(!n. terminates (run_context n runtime_unit.cu_context vi) ==>
             ?u. run_context n runtime_unit.cu_context vi = Abort ExHalt_abort u))`;

val linked_runtime_gas_raw_sized =
  `!vi. raw_variant fmp vi vs ==> (` @ linked_runtime_gas_raw_fields @ `) /\
    ((!fn inst s. raw_reachable vi runtime_unit.cu_context fn inst s ==>
        inst_create_size_ok inst s) \/
     ?f vals obs fr.
       calldata_dispatch_mods mods exps tx.calldata = SOME (f,vals) /\
       ~gas_source_exempt_mods mods
         (tx with <|function_name := f; args := vals|>)
         (call_external (SOME vi.vs_outcomes) obs am
           (tx with <|function_name := f; args := vals|>)) /\
       exit_result (run_context fr runtime_unit.cu_context vi) /\
       create_size_exit_ok runtime_unit.cu_context
         (FST (call_external (SOME vi.vs_outcomes) obs am
            (tx with <|function_name := f; args := vals|>)))
         (run_context fr runtime_unit.cu_context vi))`;

Resume vyper_call_gas_sufficient_mods[linked_runtime_gas_bound]:
  (sg linked_runtime_gas_raw_sized >- suspend "linked_runtime_gas_raw_variants") >>
  pop_assum (mk_asm "linked_runtime_gas_sized") >>
  conj_tac
  >- (`fmp_free_ctx runtime_unit.cu_context` by
        (irule source_fmp_free >> conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
      `fmp_variant_room (SOME fmp) runtime_out.po_unit.cu_context vs` by
        (PURE_REWRITE_TAC [fmp_variant_room_def] >>
         conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
      mp_tac (Q.INST [`mods` |-> `mods`, `exps` |-> `exps`, `am` |-> `am`,
        `tx` |-> `tx`, `rpolicy` |-> `rpolicy`, `unit` |-> `runtime_unit`,
        `out` |-> `runtime_out`, `vs` |-> `vs`, `D` |-> `D`, `fmp` |-> `fmp`]
        (SPEC_ALL call_entry_reachable_create_size_ok_mods)) >>
      impl_tac >-
        (rpt (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >>
         gen_tac >> disch_tac >>
         asm "linked_runtime_gas_sized" (drule_then (CONJUNCTS_THEN2
           (map_every assume_tac o CONJUNCTS) (mk_asm "linked_raw_size"))) >>
         qpat_assum `!vi. raw_variant fmp vi vs ==> mem_inv dload_headroom_ok _ _ /\ _`
           (drule_then (map_every assume_tac o CONJUNCTS)) >>
         `mem_inv raw_mem_ok runtime_unit.cu_context vi` by
           (qpat_assum `raw_unit_memory_ok runtime_unit.cu_context vi` mp_tac >>
            simp[NoAsms, unitTransformDefsTheory.raw_unit_memory_ok_def,
                 mem_inv_def, raw_mem_ok_def]) >>
         conj_tac
         >- (irule o1_source_pre_walk_inv >>
             rpt (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >>
             PURE_REWRITE_TAC [o1_src_inv_def] >>
             rpt conj_tac >> TRY (FIRST_ASSUM ACCEPT_TAC) >>
             qexists_tac `0` >> conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
         conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
         asm "linked_raw_size" DISJ_CASES_TAC
         >- (disj1_tac >> FIRST_ASSUM ACCEPT_TAC) >>
         disj2_tac >>
         pop_assum (qx_choosel_then [`fname`,`vals`,`obs`,`fr`]
           (map_every assume_tac o CONJUNCTS)) >>
         qexistsl_tac [`fname`,`vals`,`obs`,`fr`] >>
         rpt (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >>
         qpat_assum `raw_variant fmp vi vs`
           (SUBST1_TAC o MATCH_MP raw_variant_call_ctx) >>
         qpat_assum `vs.vs_call_ctx.cc_static = tx.is_static` SUBST1_TAC >>
         FIRST_ASSUM ACCEPT_TAC) >>
      disch_then ACCEPT_TAC) >>
  gen_tac >> disch_tac >>
  asm "linked_runtime_gas_sized" (drule_then (ACCEPT_TAC o CONJUNCT1))
QED

Resume vyper_call_gas_sufficient_mods[linked_runtime_gas_raw_variants]:
  Cases_on `calldata_dispatch_mods mods exps tx.calldata`
  >- suspend "linked_runtime_gas_rejection" >>
  suspend "linked_runtime_gas_selected"
QED

(* Shared raw state and dispatch-miss Revert certificate. *)
val linked_runtime_gas_rejection_entry_tac =
  qpat_assum `!vi. raw_variant fmp vi vs ==> initial_venom_state_rel_mods _ _ _ vi /\ _`
    (drule_then strip_assume_tac) >>
  `vi.vs_call_ctx.cc_calldata = tx.calldata` by
    (qpat_assum `initial_venom_state_rel_mods mods am tx vi`
       (strip_assume_tac o PURE_REWRITE_RULE
          [initial_venom_state_rel_mods_def, venom_env_rel_def, call_ctx_rel_def]) >>
     FIRST_ASSUM ACCEPT_TAC) >>
  `ctx_has_dalloca runtime_unit.cu_context ==>
    unit_alloca_budget runtime_unit.cu_context <= w2n vi.vs_initial_fmp /\
    w2n vi.vs_initial_fmp < 2 ** 254` by
    (strip_tac >> qpat_assum `vi.vs_initial_fmp = fmp`
       (SUBST1_TAC o AP_TERM ``w2n : bytes32 -> num``) >>
     conj_tac
     >- (qpat_assum `unit_alloca_budget runtime_unit.cu_context + _ <= _` mp_tac >>
         decide_tac) >>
     FIRST_ASSUM ACCEPT_TAC) >>
  `LENGTH tx.calldata < 2 ** 64` by
    (qpat_assum `es.contexts = (ctxt,rb)::rest` (fn contexts =>
       qpat_assum `evm_state_ok es`
         (mp_tac o SIMP_RULE (srw_ss()) [contexts, evm_state_ok_def,
           vfmCalldataBoundTheory.calldata_bounded_def])) >>
     qpat_assum `frame_tx_rel tx es ctxt` (mp_tac o REWRITE_RULE [frame_tx_rel_def]) >>
     rpt strip_tac >>
     qpat_assum `buffer_to_list ctxt.msgParams.data = tx.calldata`
       (fn calldata => PURE_REWRITE_TAC [GSYM calldata, vfmBufferTheory.LENGTH_buffer_to_list]) >>
     simp[]) >>
  `ctx_has_dalloca runtime_unit.cu_context ==>
    !fn inst s. raw_reachable (vi with vs_outcomes := []) runtime_unit.cu_context
      fn inst s ==> dalloca_fmp_headroom inst s` by
    (strip_tac >>
     `account_code_lengths_ok vi.vs_accounts /\ ~vi.vs_halted /\
      vi.vs_fmp = vi.vs_initial_fmp` by
       (qpat_assum `initial_venom_state_rel_mods mods am _ vi`
          (strip_assume_tac o PURE_REWRITE_RULE [initial_venom_state_rel_mods_def]) >>
        conj_tac
        >- (qpat_assum `vi.vs_accounts = _` SUBST1_TAC >>
            qpat_assum `machine_well_typed am`
              (ACCEPT_TAC o MATCH_MP
                (Q.INST [`tx` |-> `tx`] initial_account_codes_after_transfer))) >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     `!fn i s. MEM fn runtime_unit.cu_context.ctx_functions /\
       active_inst fn i s /\ i.inst_opcode = DALLOCA ==>
         raw_call_dalloca_window fn i s \/ create_copy_dalloca_window fn i s \/
         create_blueprint_dalloca_window fn i s` by
       (rpt gen_tac >> strip_tac >>
        rename1 `active_inst fn i active` >>
        mp_tac (Q.INST [`fn` |-> `fn`, `i` |-> `i`, `s` |-> `active`]
          active_inst_dalloca_windows_with_blueprint) >>
        impl_tac
        >- (conj_tac
            >- (qpat_assum `lowering_context_ok runtime_unit.cu_context`
                  (mp_tac o SIMP_RULE (srw_ss()) [lowering_context_ok_def, EVERY_MEM]) >>
                simp[]) >>
            conj_tac >- qpat_assum `active_inst fn i active` ACCEPT_TAC >>
            conj_tac >- qpat_assum `i.inst_opcode = DALLOCA` ACCEPT_TAC >>
            gen_tac >> strip_tac >>
            mp_tac (Q.INST [`unit` |-> `runtime_unit`, `rp` |-> `rpolicy`,
              `window` |-> `\chunk k. raw_call_dalloca_chunk chunk k \/
                create_copy_dalloca_chunk chunk k \/ create_blueprint_dalloca_chunk chunk k`]
              lower_vyper_runtime_unit_dalloca_windows_mods) >>
            impl_tac >- simp[] >>
            disch_then (qspecl_then [`fn`, `bb`] mp_tac) >> simp[]) >>
        disch_then ACCEPT_TAC) >>
     mp_tac (Q.INST [`ctx` |-> `runtime_unit.cu_context`,
                   `vi` |-> `vi with vs_outcomes := []`]
       raw_headroom_from_dalloca_windows) >>
     simp[NoAsms, outcomes_accounts_typed_def] >>
     disch_then match_mp_tac >>
     conj_tac >- qpat_assum `lowering_context_ok runtime_unit.cu_context` ACCEPT_TAC >>
     conj_tac >- qpat_assum `account_code_lengths_ok vi.vs_accounts` ACCEPT_TAC >>
     conj_tac >- qpat_assum `~vi.vs_halted` ACCEPT_TAC >>
     conj_tac >- qpat_assum `vi.vs_fmp = vi.vs_initial_fmp` ACCEPT_TAC >>
     conj_tac
     >- (qpat_assum `vi.vs_initial_fmp = fmp` SUBST1_TAC >>
         qpat_assum `w2n fmp < 2 ** 254` (ACCEPT_TAC o REWRITE_RULE [EVAL ``2 ** 254:num``])) >>
     conj_tac
     >- (qpat_assum `vi.vs_call_ctx.cc_calldata = tx.calldata` SUBST1_TAC >>
         qpat_assum `LENGTH tx.calldata < 2 ** 64` (ACCEPT_TAC o REWRITE_RULE [EVAL ``2 ** 64:num``])) >>
     first_assum ACCEPT_TAC) >>
  `?fn stopped marks.
     runtime_unit.cu_context.ctx_entry = SOME "__entry" /\
     lookup_function "__entry" runtime_unit.cu_context.ctx_functions = SOME fn /\
     fn_entry_label fn = SOME "__entry" /\
     (?stop_fuel. run_context stop_fuel runtime_unit.cu_context vi = Abort Revert_abort stopped) /\
     gas_path_mem runtime_unit.cu_context fn
       (vi with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>)
       marks (Abort Revert_abort stopped) /\
     (!n. ptr_safe_blocks D 0 n runtime_unit.cu_context fn [] FEMPTY entry_taint
       (vi with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>))` by
    (linked_runtime_rejection_tac `tx`);

Resume vyper_call_gas_sufficient_mods[linked_runtime_gas_rejection]:
  qx_gen_tac `vi` >> strip_tac >>
  linked_runtime_gas_rejection_entry_tac >>
  `!n. mem_safe_blocks n runtime_unit.cu_context fn
     (vi with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>)` by
    (qspecl_then [`mods`, `exps`, `rpolicy`, `runtime_unit`, `fn`,
        `vi with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>`,
        `marks`, `Abort Revert_abort stopped`]
      mp_tac lower_vyper_runtime_unit_exit_mem_safe_blocks_mods >>
     simp[exit_result_def]) >>
  `ptr_discipline 0 runtime_unit.cu_context vi` by
    (qspecl_then [`mods`, `exps`, `rpolicy`, `runtime_unit`, `vi`, `fn`, `"__entry"`, `D`]
      mp_tac lower_vyper_runtime_unit_ptr_taint_mods >> simp[]) >>
  `raw_unit_memory_ok runtime_unit.cu_context vi` by
    (Cases_on `ctx_has_dalloca runtime_unit.cu_context`
     >- (`!f inst w. raw_reachable vi runtime_unit.cu_context f inst w ==>
             dalloca_no_wrap inst w /\ w2n w.vs_initial_fmp <= w2n w.vs_fmp` by
           (qspecl_then [`0`,`runtime_unit.cu_context`,`"__entry"`,`fn`,`"__entry"`,`vi`]
              mp_tac lowered_unit_checked_dalloca_facts >> asm_rewrite_tac[]) >>
         qspecl_then [`mods`,`exps`,`rpolicy`,`runtime_unit`,`am`,`tx`,
                      `vi`,`fn`,`"__entry"`,`D`]
           mp_tac lower_vyper_runtime_unit_memory_ok_from_no_wrap_mods >>
         impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >> simp[]) >>
     qspecl_then [`mods`,`exps`,`rpolicy`,`runtime_unit`,`am`,`tx`,
                  `vi`,`fn`,`"__entry"`,`D`]
       mp_tac lower_vyper_runtime_unit_memory_ok_mods >> simp[]) >>
  `mem_inv dload_offset_ok runtime_unit.cu_context vi` by
    (qspecl_then [`mods`, `exps`, `rpolicy`, `runtime_unit`, `vi`, `fn`, `"__entry"`]
      mp_tac lower_vyper_runtime_unit_dload_offset_ok_mods >> simp[]) >>
  `mem_inv (\ctx fn inst w. inst_dload_in_section inst w /\
                  w.vs_code = vi.vs_code /\ w.vs_data_section = vi.vs_data_section)
     runtime_unit.cu_context vi` by
    (qspecl_then [`mods`, `exps`, `rpolicy`, `runtime_unit`, `vi`, `fn`, `"__entry"`]
      mp_tac lower_vyper_runtime_unit_dload_in_section_mods >> simp[]) >>
  `terminates (run_context stop_fuel runtime_unit.cu_context vi)` by
    simp[terminates_def] >>
  `terminates (run_context fuel runtime_unit.cu_context vi)` by
    (qpat_assum `!n s. terminates (run_context n runtime_unit.cu_context s) ==>
                 terminates (run_context fuel runtime_unit.cu_context s)`
       (qspecl_then [`stop_fuel`,`vi`] (fn preserves =>
         qpat_assum `terminates (run_context stop_fuel runtime_unit.cu_context vi)`
           (ACCEPT_TAC o MATCH_MP preserves)))) >>
  conj_tac
  >- (asm_rewrite_tac[] >> strip_tac >> strip_tac >>
      qpat_assum `!n. terminates (run_context n runtime_unit.cu_context vi) ==>
                      ?u. run_context n runtime_unit.cu_context vi = Abort ExHalt_abort u`
        (qspec_then `stop_fuel` mp_tac) >> simp[]) >>
  disj1_tac >> rpt gen_tac >> disch_tac >> CCONTR_TAC >>
  `EVERY wf_function runtime_unit.cu_context.ctx_functions` by
    (drule_then (ACCEPT_TAC o CONJUNCT1) entryCreateExitTheory.create_size_raw_unit_wf) >>
  `!err. run_context stop_fuel runtime_unit.cu_context vi <> Error err` by
    (qpat_assum `run_context stop_fuel _ _ = Abort Revert_abort _`
       (fn stopped => simp[NoAsms, stopped])) >>
  rename1 `raw_reachable vi runtime_unit.cu_context reached_fn reached_inst reached_state` >>
  mp_tac (Q.INST [`ctx` |-> `runtime_unit.cu_context`, `vi` |-> `vi`,
                  `fuel` |-> `stop_fuel`, `fn` |-> `reached_fn`,
                  `i` |-> `reached_inst`, `s` |-> `reached_state`]
    entryCreateRejectTheory.raw_reached_oversized_create_terminal) >>
  asm_rewrite_tac[] >> simp[]
QED

val linked_runtime_gas_frame_tac =
  qpat_assum `!vi. raw_variant fmp vi vs ==> initial_venom_state_rel_mods _ _ _ vi /\ _`
    (drule_then strip_assume_tac) >>
  `vi.vs_call_ctx.cc_calldata = tx.calldata` by
    (qpat_assum `initial_venom_state_rel_mods mods am tx vi`
       (strip_assume_tac o PURE_REWRITE_RULE
          [initial_venom_state_rel_mods_def, venom_env_rel_def, call_ctx_rel_def]) >>
     FIRST_ASSUM ACCEPT_TAC) >>
  `LENGTH tx.calldata < 2 ** 64` by
    (qpat_assum `es.contexts = (ctxt,rb)::rest` (fn contexts =>
       qpat_assum `evm_state_ok es`
         (mp_tac o SIMP_RULE (srw_ss()) [contexts, evm_state_ok_def,
           vfmCalldataBoundTheory.calldata_bounded_def])) >>
     qpat_assum `frame_tx_rel tx es ctxt` (mp_tac o REWRITE_RULE [frame_tx_rel_def]) >>
     rpt strip_tac >>
     qpat_assum `buffer_to_list ctxt.msgParams.data = tx.calldata`
       (fn calldata => PURE_REWRITE_TAC [GSYM calldata, vfmBufferTheory.LENGTH_buffer_to_list]) >>
     simp[]);

val linked_runtime_gas_dispatch_tac =
  rename1 `calldata_dispatch_mods mods exps tx.calldata = SOME picked` >>
  PairCases_on `picked` >>
  rename1 `calldata_dispatch_mods mods exps tx.calldata = SOME (fname,vals)` >>
  qabbrev_tac `td = tx with <|function_name := fname; args := vals|>` >>
  qpat_assum `!f actual. SOME (fname,vals) = SOME (f,actual) ==> _`
    (qspecl_then [`fname`,`vals`] mp_tac) >> simp[NoAsms] >>
  disch_then (fn facts => qpat_assum `Abbrev (td = _)` (fn selected =>
    map_every assume_tac (CONJUNCTS (PURE_REWRITE_RULE
      [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] selected)] facts))));

val linked_runtime_gas_dalloca_headroom_tac =
  strip_tac >>
  `account_code_lengths_ok vi.vs_accounts` by
    (qpat_assum `initial_venom_state_rel_mods mods am td vi`
       (strip_assume_tac o PURE_REWRITE_RULE [initial_venom_state_rel_mods_def]) >>
     qpat_assum `vi.vs_accounts = _` SUBST1_TAC >>
     qpat_assum `machine_well_typed am`
       (ACCEPT_TAC o MATCH_MP
         (Q.INST [`tx` |-> `td`] initial_account_codes_after_transfer))) >>
  `!fn i s. MEM fn runtime_unit.cu_context.ctx_functions /\
    active_inst fn i s /\ i.inst_opcode = DALLOCA ==>
      raw_call_dalloca_window fn i s \/ create_copy_dalloca_window fn i s \/
      create_blueprint_dalloca_window fn i s` by
    (rpt gen_tac >> strip_tac >>
     rename1 `active_inst fn i active` >>
     mp_tac (Q.INST [`fn` |-> `fn`, `i` |-> `i`, `s` |-> `active`]
       active_inst_dalloca_windows_with_blueprint) >>
     impl_tac
     >- (conj_tac
         >- (qpat_assum `lowering_context_ok runtime_unit.cu_context`
               (mp_tac o SIMP_RULE (srw_ss()) [lowering_context_ok_def, EVERY_MEM]) >>
             simp[]) >>
         conj_tac >- qpat_assum `active_inst fn i active` ACCEPT_TAC >>
         conj_tac >- qpat_assum `i.inst_opcode = DALLOCA` ACCEPT_TAC >>
         gen_tac >> strip_tac >>
         mp_tac (Q.INST [`unit` |-> `runtime_unit`, `rp` |-> `rpolicy`,
           `window` |-> `\chunk k. raw_call_dalloca_chunk chunk k \/
             create_copy_dalloca_chunk chunk k \/ create_blueprint_dalloca_chunk chunk k`]
           lower_vyper_runtime_unit_dalloca_windows_mods) >>
         impl_tac >- simp[] >>
         disch_then (qspecl_then [`fn`, `bb`] mp_tac) >> simp[]) >>
     disch_then ACCEPT_TAC) >>
  mp_tac (Q.INST [`ctx` |-> `runtime_unit.cu_context`, `vi` |-> `vi`]
    raw_headroom_from_dalloca_windows) >>
  disch_then match_mp_tac >>
  qpat_assum `initial_venom_state_rel_mods mods am td vi`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [initial_venom_state_rel_mods_def]) >>
  conj_tac >- qpat_assum `lowering_context_ok runtime_unit.cu_context` ACCEPT_TAC >>
  conj_tac >- qpat_assum `account_code_lengths_ok vi.vs_accounts` ACCEPT_TAC >>
  conj_tac >- qpat_assum `~vi.vs_halted` ACCEPT_TAC >>
  conj_tac >- qpat_assum `vi.vs_fmp = vi.vs_initial_fmp` ACCEPT_TAC >>
  conj_tac
  >- (qpat_assum `vi.vs_initial_fmp = fmp` SUBST1_TAC >>
      qpat_assum `w2n fmp < 2 ** 254` ACCEPT_TAC) >>
  conj_tac >- qpat_assum `LENGTH vi.vs_outcomes < 2 ** 64` ACCEPT_TAC >>
  conj_tac >- qpat_assum `outcomes_accounts_typed (SOME vi.vs_outcomes)` ACCEPT_TAC >>
  conj_tac
  >- (qpat_assum `vi.vs_call_ctx.cc_calldata = tx.calldata` SUBST1_TAC >>
      qpat_assum `LENGTH tx.calldata < 2 ** 64` ACCEPT_TAC) >>
  first_assum ACCEPT_TAC;

val linked_runtime_gas_selected_state_tac =
  `vi.vs_outcomes = MAP SND (call_trace eg)` by
    (qpat_assum `vi.vs_outcomes = vs.vs_outcomes` SUBST1_TAC >>
     FIRST_ASSUM ACCEPT_TAC) >>
  `source_typing_ok_mods mods exps am td` by
    simp[Abbr `td`, call_premises_dispatch_invariant_mods] >>
  `td.target = tx.target /\ td.is_static = tx.is_static` by simp[Abbr `td`] >>
  `source_deployment_rel_mods mods exps am td` by
    (qpat_assum `source_deployment_rel_mods mods exps am tx` mp_tac >>
     qpat_assum `td.target = tx.target` (fn target =>
       PURE_REWRITE_TAC [source_deployment_rel_mods_def, layouts_agree_mods_def, target]) >>
     disch_then ACCEPT_TAC) >>
  `initial_venom_state_rel_mods mods am td vi <=>
    initial_venom_state_rel_mods mods am tx vi` by
    simp[NoAsms, Abbr `td`, initial_venom_state_rel_mods_def, venom_env_rel_def,
         call_ctx_rel_def, tx_env_ok_def, value_transfer_ok_def, accounts_after_transfer_def] >>
  `initial_venom_state_rel_mods mods am td vi` by
    (qpat_assum `initial_venom_state_rel_mods _ _ td _ <=> _`
       (fn equivalence => PURE_REWRITE_TAC [equivalence]) >>
     first_assum ACCEPT_TAC) >>
  `LENGTH vi.vs_outcomes < 2 ** 64` by
    (qpat_assum `vi.vs_outcomes = MAP SND (call_trace eg)` SUBST1_TAC >>
     PURE_REWRITE_TAC [listTheory.LENGTH_MAP] >>
     qpat_assum `LENGTH (call_trace eg) < _` mp_tac >> simp[NoAsms]) >>
  `outcomes_accounts_typed (SOME vi.vs_outcomes)` by
    (qpat_assum `vi.vs_outcomes = vs.vs_outcomes` SUBST1_TAC >>
     qpat_assum `vs.vs_outcomes = _` SUBST1_TAC >>
     `wf_state eg /\ balance_bounded (2 ** 256 - 1) eg /\ returndata_bounded eg` by
       fs[Abbr `eg`, evm_state_ok_def, add_frame_gas_wf_state, add_frame_gas_bounded] >>
     drule_all call_trace_outcomes_bounded >>
     simp[outcomes_accounts_typed_def, EVERY_MEM]) >>
  `ctx_has_dalloca runtime_unit.cu_context ==>
    unit_alloca_budget runtime_unit.cu_context <= w2n vi.vs_initial_fmp /\
    w2n vi.vs_initial_fmp < 2 ** 254` by
    (strip_tac >> qpat_assum `vi.vs_initial_fmp = fmp` SUBST1_TAC >>
     conj_tac
     >- (qpat_assum `unit_alloca_budget runtime_unit.cu_context + _ <= _` mp_tac >>
         decide_tac) >>
     FIRST_ASSUM ACCEPT_TAC) >>
  `ctx_has_dalloca runtime_unit.cu_context ==>
     !f inst w. raw_reachable vi runtime_unit.cu_context f inst w ==>
       dalloca_fmp_headroom inst w` by
    linked_runtime_gas_dalloca_headroom_tac;

Resume vyper_call_gas_sufficient_mods[linked_runtime_gas_selected]:
  qx_gen_tac `vi` >> strip_tac >>
  linked_runtime_gas_frame_tac >>
  linked_runtime_gas_dispatch_tac >>
  linked_runtime_gas_selected_state_tac >>
  `?shadow_ctx marks.
      source_unit_execution_correct_with_mods shadow_ctx marks mods exps
        (external_return_type_mods mods exps td.function_name) am td runtime_unit vi /\
      ((?tail. call_storage_ok am td vi.vs_outcomes
        (gas_explicit marks vi.vs_gas_readings ++ tail)) ==>
       !tail. FST (call_external (SOME vi.vs_outcomes)
         (gas_explicit marks vi.vs_gas_readings ++ tail) am td) <>
         INR (Error (RuntimeError "msg.gas: no gas reading")))` by
    (mp_tac (Q.INST [`unit` |-> `runtime_unit`, `tx` |-> `td`]
       linked_runtime_dispatched_readings_certificate) >>
     impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     disch_then (qx_choose_then `shadow_ctx` (qspec_then `vi` mp_tac)) >>
     impl_tac
     >- (simp[Abbr `td`] >> fs[] >> rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     disch_then (qx_choose_then `marks` (fn cert =>
       qexistsl_tac [`shadow_ctx`, `marks`] >> ACCEPT_TAC cert))) >>
  `call_storage_ok am td vi.vs_outcomes (gas_explicit marks vi.vs_gas_readings)` by
    (qpat_assum `vi.vs_outcomes = MAP SND (call_trace eg)` SUBST1_TAC >>
     qpat_assum `!gs. call_storage_ok am td (MAP SND (call_trace eg)) gs`
       (qspec_then `gas_explicit marks vi.vs_gas_readings` ACCEPT_TAC)) >>
  `FST (call_external (SOME vi.vs_outcomes)
      (gas_explicit marks vi.vs_gas_readings) am td) <>
    INR (Error (RuntimeError "msg.gas: no gas reading"))` by
     (qpat_assum `(?tail. call_storage_ok am td vi.vs_outcomes _) ==> !tail. _` mp_tac >>
      impl_tac >- (qexists_tac `[]` >> asm_rewrite_tac[APPEND_NIL]) >>
      disch_then (qspec_then `[]` (ACCEPT_TAC o PURE_REWRITE_RULE [APPEND_NIL]))) >>
  qabbrev_tac `gs = gas_explicit marks vi.vs_gas_readings` >>
  `~gas_source_exempt_mods mods td (call_external (SOME vi.vs_outcomes) gs am td)` by
    (qpat_assum `vi.vs_outcomes = MAP SND (call_trace eg)` SUBST1_TAC >>
     qpat_assum `!obs. ~gas_source_exempt_mods mods td
        (call_external (SOME (MAP SND (call_trace eg))) obs am td)`
       (qspec_then `gs` ACCEPT_TAC)) >>
  `~source_exempt_mods mods (call_external (SOME vi.vs_outcomes) gs am td)` by
    fs[gas_source_exempt_mods_def] >>
  `?fr. exit_result (run_context fr runtime_unit.cu_context vi) /\
     create_size_exit_ok runtime_unit.cu_context
       (FST (call_external (SOME vi.vs_outcomes) gs am td))
       (run_context fr runtime_unit.cu_context vi)` by
    (mp_tac (Q.INST [`shadow_ctx` |-> `shadow_ctx`, `marks` |-> `marks`,
       `mods` |-> `mods`, `exps` |-> `exps`, `am` |-> `am`, `tx` |-> `td`,
       `unit` |-> `runtime_unit`, `vs` |-> `vi`,
       `ret` |-> `external_return_type_mods mods exps td.function_name`]
       (SPEC_ALL source_unit_create_size_run_mods)) >>
     qpat_assum `Abbrev (gs = _)` (fn fill =>
       PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] fill)]) >>
     impl_tac >-
       (rpt (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >>
        rpt gen_tac >> strip_tac >>
        drule_all_then ACCEPT_TAC acceptedContextPhiTheory.lowering_context_ok_block_phi) >>
     disch_then ACCEPT_TAC) >>
  mp_tac (Q.INST [`unit` |-> `runtime_unit`, `tx` |-> `td`,
      `vs` |-> `vi`, `tail` |-> `[]`, `marks` |-> `marks`,
      `ret` |-> `external_return_type_mods mods exps td.function_name`]
    linked_runtime_certificate_exit) >>
  qpat_assum `Abbrev (gs = _)` (fn filling =>
    PURE_REWRITE_TAC [APPEND_NIL, GSYM (REWRITE_RULE [markerTheory.Abbrev_def] filling)]) >>
  impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`fn`,`stop_fuel`] (map_every assume_tac o CONJUNCTS)) >>
  qabbrev_tac `obs = source_storage_trace am td vi.vs_outcomes gs` >>
  qabbrev_tac `Hsel = storage_trace_horizon obs` >>
  `valid_horizon (initial_evaluation_context am.sources am.layouts td NONE)
    (initial_state am []) Hsel obs` by
    fs[Abbr `Hsel`, Abbr `obs`, storage_trace_domain_def] >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `Hsel` mp_tac) >>
  simp[Abbr `obs`] >> strip_tac >>
  qabbrev_tac `Ksel = cx_dead Hsel (initial_evaluation_context am.sources am.layouts td NONE)` >>
  `ptr_discipline 0 runtime_unit.cu_context vi` by
    (qspecl_then [`mods`,`exps`,`rpolicy`,`runtime_unit`,`vi`,`fn`,`"__entry"`,`Ksel`]
      mp_tac lower_vyper_runtime_unit_ptr_taint_mods >> simp[Abbr `Ksel`]) >>
  `raw_unit_memory_ok runtime_unit.cu_context vi` by
    (Cases_on `ctx_has_dalloca runtime_unit.cu_context`
     >- (`!f inst w. raw_reachable vi runtime_unit.cu_context f inst w ==>
             dalloca_no_wrap inst w /\ w2n w.vs_initial_fmp <= w2n w.vs_fmp` by
           (qspecl_then [`0`,`runtime_unit.cu_context`,`"__entry"`,`fn`,`"__entry"`,`vi`]
              mp_tac lowered_unit_checked_dalloca_facts >> asm_rewrite_tac[]) >>
         qspecl_then [`mods`,`exps`,`rpolicy`,`runtime_unit`,`am`,`td`,
                      `vi`,`fn`,`"__entry"`,`Ksel`]
           mp_tac lower_vyper_runtime_unit_memory_ok_from_no_wrap_mods >>
         impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
         disch_then (ACCEPT_TAC o CONJUNCT1)) >>
     qspecl_then [`mods`,`exps`,`rpolicy`,`runtime_unit`,`am`,`td`,
                  `vi`,`fn`,`"__entry"`,`Ksel`]
       mp_tac lower_vyper_runtime_unit_memory_ok_mods >>
     impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  `mem_inv dload_offset_ok runtime_unit.cu_context vi` by
    (qspecl_then [`mods`, `exps`, `rpolicy`, `runtime_unit`, `vi`, `fn`, `"__entry"`]
      mp_tac lower_vyper_runtime_unit_dload_offset_ok_mods >> simp[]) >>
  `mem_inv (\ctx fn inst w. inst_dload_in_section inst w /\
                  w.vs_code = vi.vs_code /\ w.vs_data_section = vi.vs_data_section)
     runtime_unit.cu_context vi` by
    (qspecl_then [`mods`, `exps`, `rpolicy`, `runtime_unit`, `vi`, `fn`, `"__entry"`]
      mp_tac lower_vyper_runtime_unit_dload_in_section_mods >> simp[]) >>
  `terminates (run_context fuel runtime_unit.cu_context vi)` by
    (qpat_assum `!n s. terminates (run_context n runtime_unit.cu_context s) ==>
                 terminates (run_context fuel runtime_unit.cu_context s)`
       (qspecl_then [`stop_fuel`,`vi`] (fn preserves =>
         qpat_assum `terminates (run_context stop_fuel runtime_unit.cu_context vi)`
           (ACCEPT_TAC o MATCH_MP preserves)))) >>
  reverse conj_tac
  >- (disj2_tac >>
      qpat_assum `?fr. exit_result (run_context fr runtime_unit.cu_context vi) /\ _`
        (qx_choose_then `exit_fuel` (map_every assume_tac o CONJUNCTS)) >>
      qexistsl_tac [`fname`,`vals`,`gs`,`exit_fuel`] >>
      qpat_assum `Abbrev (td = _)` (fn td =>
        PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] td)]) >>
      rpt conj_tac >> (REFL_TAC ORELSE FIRST_ASSUM ACCEPT_TAC)) >>
  asm_rewrite_tac[] >> strip_tac >>
  qexists_tac `stop_fuel` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >>
  `td.is_static` by
    (qpat_assum `td.is_static <=> tx.is_static` (fn static => PURE_REWRITE_TAC [static]) >>
     first_assum ACCEPT_TAC) >>
  qpat_assum `run_context stop_fuel runtime_unit.cu_context vi = Abort ExHalt_abort _`
    (fn halted =>
      qpat_assum `external_call_result_rel_mods _ _ _ _ _ _ (run_context stop_fuel _ _)`
        (mp_tac o PURE_REWRITE_RULE [halted])) >>
  qpat_assum `~gas_source_exempt_mods mods td _` mp_tac >>
  qpat_assum `FST (call_external (SOME vi.vs_outcomes) gs am td) <> _` mp_tac >>
  `call_external (SOME (MAP SND (call_trace eg))) gs am td =
   call_external (SOME vi.vs_outcomes) gs am td` by
    (qpat_assum `vi.vs_outcomes = MAP SND (call_trace eg)`
       (fn outcomes => PURE_REWRITE_TAC [outcomes]) >> REFL_TAC) >>
  pop_assum (fn outcomes => PURE_REWRITE_TAC [outcomes]) >>
  qpat_assum `td.is_static` (fn static =>
    POP_ASSUM_LIST (K ALL_TAC) >>
    PURE_REWRITE_TAC [gas_source_exempt_mods_def, static]) >>
  Cases_on `call_external (SOME vi.vs_outcomes) gs am td` >>
  rename1 `(source_result,source_rest)` >>
  PairCases_on `source_rest` >> Cases_on `source_result` >>
  simp[NoAsms, external_call_result_rel_mods_def, LET_THM] >>
  rename1 `INR exc` >> Cases_on `exc` >> simp[NoAsms] >>
  rename1 `Error err` >> Cases_on `err` >> simp[NoAsms] >>
  metis_tac[]
QED

Finalise vyper_call_gas_sufficient_mods

val singleton_equivalence =
  let
    fun specialize ([], [], body) = body
      | specialize (variable :: variables, value :: values, body) =
          specialize (variables, values, subst [variable |-> value] body)
      | specialize _ = raise Fail "unexpected linked top binder list"
  in
    fn lifted => fn original =>
      let
        val (lifted_vars, lifted_body) = strip_forall (concl lifted)
        val (original_vars, _) = strip_forall (concl original)
      in
        case original_vars of
          fin :: policy :: tops :: rest =>
            let
              val mods = ``[(NONE : num option, ^tops)]``
              val exps = ``[] : (string # num) list``
              val instance = specialize
                (lifted_vars, fin :: policy :: mods :: exps :: rest, lifted_body)
            in
              mk_eq (list_mk_forall (original_vars, instance), concl original)
            end
        | _ => raise Fail "unexpected singleton top binder list"
      end
  end;

Theorem vyper_call_correct_mods_singleton:
  ^(singleton_equivalence vyper_call_correct_mods
      e2eCorrectnessTheory.vyper_call_correct)
Proof
  simp[compile_vyper_mods_singleton,
       source_typing_ok_mods_singleton, call_state_rel_mods_singleton,
       call_within_mods_singleton, calldata_result_rel_mods_singleton]
QED

Theorem e2e_deploy_correctness_mods_singleton:
  ^(singleton_equivalence e2e_deploy_correctness_mods
      e2eDeployCorrectnessTheory.e2e_deploy_correctness)
Proof
  simp[compile_vyper_mods_singleton,
       deploy_typing_ok_mods_singleton, deploy_state_rel_mods_singleton,
       deploy_call_result_rel_mods_singleton]
QED

Theorem e2e_deploy_gas_sufficient_mods_singleton:
  ^(singleton_equivalence e2e_deploy_gas_sufficient_mods
      e2eGasSufficientTopTheory.e2e_deploy_gas_sufficient)
Proof
  simp[compile_vyper_mods_singleton,
       deploy_typing_ok_mods_singleton, deploy_entry_rel_mods_singleton,
       deploy_within_mods_singleton, deploy_gas_source_exempt_mods_singleton,
       imm_len_mods_singleton]
QED

Theorem vyper_call_gas_sufficient_mods_singleton:
  ^(singleton_equivalence vyper_call_gas_sufficient_mods
      e2eGasSufficientTopTheory.vyper_call_gas_sufficient)
Proof
  simp[compile_vyper_mods_singleton,
       source_typing_ok_mods_singleton, call_state_rel_mods_singleton,
       calldata_dispatch_mods_singleton, gas_source_exempt_mods_singleton]
QED
