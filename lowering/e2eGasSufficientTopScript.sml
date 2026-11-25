(* The sufficient-gas companions over the accepted finalizers: each joins
 * its identity case from e2eGasSufficient with its assembly-optimizer case,
 * as vyper_call_correct_guarded and e2e_deploy_correctness do.
 *
 * TOP-LEVEL:
 *   vyper_call_gas_sufficient -- the companion of vyper_call_correct_guarded
 *   e2e_deploy_gas_sufficient -- the companion of e2e_deploy_correctness
 *)
Theory e2eGasSufficientTop
Ancestors
  stackPlanGen[qualified,ignore_grammar] ctorCallFreeExpr
  ownSymSrcUnit codegenLabelDisciplined fnPlanPlaceRevertPostamble
  codegenSymOwnRel gasFocusOptLabelFlow[qualified,ignore_grammar]
  e2eGasSufficient e2eComposition asmOptimizer
  e2eCorrectness e2eDefs e2eEntry e2eOptEntry e2eProducers
  callRawVariant callDynamicMemory[qualified,ignore_grammar] sourceUnitExitSafe exprSimHypsDefs
  vyperLoweringCorrect loweringRuntimeCorrect loweringMemCorrect
  loweringShapeSource runtimeLabelReadiness fragFuelUnit
  e2eDeployRawFmp e2eDeployAtMarks e2eDeployDefs
  ctorDeployDefs ctorDeployDefsReach ctorDeployRawEntryFacts whitelistCheckerGate
  ctorDeployFrame ctorDeployShape ctorDeployDead ctorDeployRunBounded
  ctorDeployInitcodeAsm ctorDeployMemoryFrontier ctorDeployLoweringSource
  deployUnitProducers deployUnitExecution deployUnitExitSafe
  deployFrameReplay compileVyper compilePhasesProps
  codegen codegenGasAsmOpt codegenAsmProgOk codegenAsmOpt
  codegenEntrySim codegenEntryRel asmFrameRel codegenRel frameRel
  asmOptNonemptyFinalizer immutableCodeLayout
  frameGas frameStep unitTransformDefs lowerDloadDefs ptrDiscipline
  o1PassContract o1PipelineCorrect o1CodeEndOffset o1StaticPipelineCorrect
  o1OpcodeAbsence o1LabelFlowCompose o1SafeUpto unitMemInv
  contextRawReachable dftGasInvOracleFrame staticAbortDefs venomExecProofs codegenSymRel
  deployDynamicMemory vyperInterpreter vfmExecution vfmContext list

val _ = Parse.hide "tops";

(* ===== The assembly optimizer's cases ===== *)

(* Gas top-ups keep the entry layout and read the new execution's streams. *)
Triviality opt_entry_state_own_add_frame_gas:
  opt_entry_state_own prog prog' cplan (add_frame_gas g es) =
  opt_entry_state_own prog prog' cplan es with
    <|vs_outcomes := MAP SND (call_trace (add_frame_gas g es));
      vs_gas_readings := gas_readings (add_frame_gas g es)|>
Proof
  simp[opt_entry_state_own_def, entry_venom_state_add_frame_gas,
       venomStateTheory.venom_state_component_equality]
QED

Triviality opt_entry_asm_rel_own_add_frame_gas:
  wf_state es /\
  codegen_asm_entry_rel_reloc (lo_reloc prog prog') cplan prog
    (opt_entry_state_own prog prog' cplan es)
    (entry_asm_state (opt_entry_state_own prog prog' cplan es) es) /\
  asm_frame_rel prog' (opt_entry_state_own prog prog' cplan es).vs_data_section es
    (entry_asm_state (opt_entry_state_own prog prog' cplan es) es) es ==>
  !g.
    codegen_asm_entry_rel_reloc (lo_reloc prog prog') cplan prog
      (opt_entry_state_own prog prog' cplan (add_frame_gas g es))
      (entry_asm_state (opt_entry_state_own prog prog' cplan (add_frame_gas g es))
         (add_frame_gas g es)) /\
    asm_frame_rel prog'
      (opt_entry_state_own prog prog' cplan (add_frame_gas g es)).vs_data_section
      (add_frame_gas g es)
      (entry_asm_state (opt_entry_state_own prog prog' cplan (add_frame_gas g es))
         (add_frame_gas g es))
      (add_frame_gas g es)
Proof
  simp[opt_entry_state_own_add_frame_gas] >> strip_tac >> gen_tac >>
  Cases_on `es.contexts` >- fs[asm_frame_rel_def] >>
  PairCases_on `h` >>
  drule add_frame_gas_contexts >> disch_then (qspec_then `g` assume_tac) >>
  `(add_frame_gas g es).originalAccounts = es.originalAccounts` by
    simp[add_frame_gas_def] >>
  `wf_state (add_frame_gas g es)` by simp[add_frame_gas_wf_state] >>
  conj_tac
  >- fs[codegen_asm_entry_rel_reloc_def, entry_asm_state_def, shared_state_rel_def,
        venom_asm_terminal_rel_def] >>
  fs[asm_frame_rel_def, asm_evm_rel_def, entry_asm_state_def,
     opt_entry_state_own_def, entry_venom_state_frame_fields, entry_venom_state_fresh,
     add_frame_gas_fields, relationTheory.RTC_REFL]
QED

(* Gas sufficiency for calls compiled with the final assembly optimizer. *)
Theorem vyper_call_gas_sufficient_asm_opt:
  !policy tops deploy_bc runtime_bc am tx es.
    compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es
    ==>
    ?g. !g'.
      g <= g' /\
      (!f vals.
         calldata_dispatch tops tx.calldata = SOME (f, vals) ==>
           (!gs. call_storage_ok am
              (tx with <| function_name := f; args := vals |>)
              (MAP SND (call_trace (add_frame_gas g' es))) gs) /\
           (!obs. ~gas_source_exempt tops
              (tx with <| function_name := f; args := vals |>)
              (call_external (SOME (MAP SND (call_trace (add_frame_gas g' es))))
                 obs am (tx with <| function_name := f; args := vals |>))) /\
           LENGTH (call_trace (add_frame_gas g' es)) < 2 ** 64)
      ==>
      ?r es'.
        run_call (add_frame_gas g' es) = SOME (r, es') /\
        (frame_raises (add_frame_gas g' es) OutOfGas ==>
         ?s. frame_inst_at (add_frame_gas g' es) s ReturnDataCopy)
Proof
  rpt strip_tac >>
  drule compile_vyper_runtime_phases_asm_opt >> strip_tac >>
  qpat_x_assum `runtime_bc = assemble _` SUBST_ALL_TAC >>
  qpat_x_assum `prog = _` kall_tac >>
  `?art. check_contract F am.layouts tx.target [(NONE, tops)] = SOME art` by
    metis_tac[source_typing_ok_def] >>
  drule_all lower_vyper_runtime_unit_checked_source_shape >> strip_tac >>
  drule_all lower_vyper_runtime_unit_defs_reach_uses >> strip_tac >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  `assemble prog' <> []` by
    (irule codegen_assembly_finalizer_nonempty >> metis_tac[]) >>
  `source_deployment_rel tops am tx` by
    fs[call_state_rel_def, frame_fresh_def, frame_tx_rel_def, world_rel_def] >>
  `EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
   fixed_region_reserved 0 unit.cu_context` by
    (drule lower_vyper_runtime_unit_raw_defaults >>
     simp[fixed_region_reserved_def]) >>
  `reserved_intervals_wf unit.cu_context.ctx_global_reserved` by
    (drule lower_vyper_runtime_unit_global_reserved >>
     simp[staticLayoutDefsTheory.reserved_intervals_wf_def]) >>
  drule_all lower_vyper_runtime_unit_sym_src_ok_own >> strip_tac >>
  drule_all gasFocusOptLabelFlowTheory.focus_opt_label_flow_own >> strip_tac >>
  drule_all o1_pipeline_sym_unit_static_ok >> strip_tac >>
  `!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
     ~MEM (Label "runtime_begin") inst.inst_operands` by
    metis_tac[lower_vyper_runtime_unit_no_runtime_begin] >>
  drule_all call_gas_uniform_fuel >>
  disch_then (qx_choose_then `fuel` assume_tac) >>
  qspecl_then [`0`, `rpolicy`, `unit`, `out`, `cplan`, `fuel`] mp_tac
    run_venom_pipeline_run_bounded_static_abort >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`fuel'`, `M`] assume_tac) >>
  qspecl_then [`rpolicy`, `out.po_unit`, `cplan`, `prog`, `prog'`, `fuel'`, `M`]
    mp_tac codegen_gas_sufficient_asm_opt_own >>
  impl_tac >- simp[] >> disch_then (qx_choose_then `g` assume_tac) >>
  qexists_tac `g` >> rpt strip_tac >>
  drule call_state_rel_add_frame_gas_raises >>
  disch_then (qspec_then `g'` (fn th => PURE_REWRITE_TAC [th])) >>
  qabbrev_tac `eg = add_frame_gas g' es` >>
  `wf_state es` by fs[call_state_rel_def, evm_state_ok_def] >>
  `outcomes_accounts_typed (SOME (MAP SND (call_trace eg)))` by
    (`wf_state eg /\ balance_bounded (2 ** 256 - 1) eg /\ returndata_bounded eg`
       by fs[Abbr`eg`, call_state_rel_def, evm_state_ok_def, add_frame_gas_wf_state,
             add_frame_gas_bounded] >>
     drule_all call_trace_outcomes_bounded >>
     simp[outcomes_accounts_typed_def, listTheory.EVERY_MEM]) >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`]
    mp_tac opt_entry_asm_rels_own >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all opt_entry_asm_rel_own_add_frame_gas >>
  disch_then (qspec_then `g'` strip_assume_tac) >>
  qspecl_then [`asm_opt_finalizer`, `tops`, `rpolicy`, `prog`, `prog'`,
               `am`, `tx`, `es`, `cplan`, `out.po_unit`]
    mp_tac opt_entry_code_layout_valid_own >>
  impl_tac >- simp[accepted_finalizers_def] >> strip_tac >>
  qabbrev_tac `vs = opt_entry_state_own prog prog' cplan eg` >>
  `o1_initial_state_ok (opt_entry_state_own prog prog' cplan es) /\
   (opt_entry_state_own prog prog' cplan es).vs_fmp = n2w cplan.cp_initial_fmp /\
   (opt_entry_state_own prog prog' cplan es).vs_initial_fmp = n2w cplan.cp_initial_fmp /\
   (opt_entry_state_own prog prog' cplan es).vs_call_ctx.cc_static = tx.is_static` by
    (simp[opt_entry_state_own_def, entry_venom_state_def,
          o1_initial_state_ok_def, venomStateTheory.init_venom_state_def] >>
     fs[call_state_rel_def, frame_tx_rel_def]) >>
  `code_layout_valid vs` by
    (qpat_assum `code_layout_valid (opt_entry_state_own _ _ _ _)` mp_tac >>
     simp_tac (srw_ss ())
       [Abbr `vs`, Abbr `eg`, opt_entry_state_own_add_frame_gas,
        code_layout_valid_def]) >>
  `o1_initial_state_ok vs /\
   vs.vs_initial_fmp = n2w cplan.cp_initial_fmp /\ vs.vs_fmp = vs.vs_initial_fmp /\
   vs.vs_call_ctx.cc_static = tx.is_static /\
   vs.vs_outcomes = MAP SND (call_trace eg) /\
   vs.vs_code = assemble prog' ++ vs.vs_data_section` by
    (qpat_assum `o1_initial_state_ok (opt_entry_state_own _ _ _ _)` mp_tac >>
     simp_tac (srw_ss ())
       [Abbr `vs`, Abbr `eg`, opt_entry_state_own_add_frame_gas,
        o1_initial_state_ok_def] >>
     asm_rewrite_tac[]) >>
  `mem_inv (\ctx fn inst s. inst_create_size_ok inst s)
      out.po_unit.cu_context vs` by
    (Cases_on `EXISTS (top_body_has expr_create_root) tops`
     >- (qspecl_then [`T`, `asm_opt_finalizer`, `tops`, `rpolicy`, `unit`, `out`,
                      `prog`, `prog'`, `cplan`, `am`, `tx`, `eg`, `vs`]
           mp_tac call_entry_reachable_create_size_ok >>
         impl_tac >- (simp[accepted_finalizers_def, Abbr `vs`, Abbr `eg`] >> metis_tac[]) >>
         simp[]) >>
     metis_tac[o1_runtime_unit_create_size_ok]) >>
  `initial_venom_state_rel tops am tx vs` by
    (`initial_venom_state_rel tops am tx (opt_entry_state_own prog prog' cplan es)` by
       metis_tac[opt_entry_initial_venom_state_rel_own, opt_entry_own_txp_identity] >>
     fs[Abbr `vs`, Abbr `eg`, opt_entry_state_own_add_frame_gas,
        initial_venom_state_rel_def, vyperLoweringCorrectTheory.venom_env_rel_def]) >>
  `outcomes_accounts_typed (SOME vs.vs_outcomes)` by simp[] >>
  `!f vals. calldata_dispatch tops tx.calldata = SOME (f, vals) ==>
      (!obs. call_storage_ok am
         (tx with <| function_name := f; args := vals |>) vs.vs_outcomes obs) /\
      (!obs. ~gas_source_exempt tops
         (tx with <| function_name := f; args := vals |>)
         (call_external (SOME vs.vs_outcomes) obs am
            (tx with <| function_name := f; args := vals |>)))` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!f vals. calldata_dispatch tops tx.calldata = _ ==> _`
       (qspecl_then [`f`, `vals`] mp_tac) >> simp[]) >>
  qabbrev_tac `D = <| d_stor := K (K UNIV); d_trans := K (K UNIV);
                      d_imm := K UNIV; d_ret := K UNIV |>` >>
  `dead_wf D` by simp[Abbr`D`, dead_wf_def] >>
  `!f vals. calldata_dispatch tops tx.calldata = SOME (f, vals) ==>
     LENGTH vs.vs_outcomes < 2 ** 64 /\ LENGTH tx.calldata < 2 ** 64` by
    (rpt gen_tac >> strip_tac >> conj_tac
     >- (qpat_assum `!f vals. calldata_dispatch tops tx.calldata = SOME (f,vals) ==>
          _ /\ _ /\ LENGTH (call_trace eg) < _`
           (qspecl_then [`f`,`vals`] (fn branch =>
              qpat_assum `calldata_dispatch tops tx.calldata = SOME (f,vals)`
                (assume_tac o cj 3 o MATCH_MP branch))) >>
         fs[Abbr `eg`]) >>
     drule callDynamicMemoryTheory.call_state_rel_calldata_bound >> simp[]) >>
  `cplan.cp_initial_fmp < 2 ** 254` by
    (fs[stackPlanGenTheory.generate_context_plan_def] >>
     drule stackPlanGenTheory.generate_context_plan_with_headroom >> simp[]) >>
  `w2n vs.vs_initial_fmp < 2 ** 254` by
    (fs[wordsTheory.w2n_n2w, wordsTheory.dimword_def, venomLayoutTheory.dimindex_256] >>
     decide_tac) >>
  drule callDynamicMemoryTheory.call_source_raw_fmp >>
  disch_then (qspec_then `vs.vs_initial_fmp` strip_assume_tac) >>
  `!vi. raw_variant fmp vi vs ==>
      raw_unit_memory_ok unit.cu_context vi /\
      ptr_discipline 0 unit.cu_context vi /\
      taint_within D unit.cu_context vi /\
      mem_inv dload_offset_ok unit.cu_context vi /\
      mem_inv dload_headroom_ok unit.cu_context vi /\
      mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                               s.vs_code = vi.vs_code /\
                               s.vs_data_section = vi.vs_data_section)
        unit.cu_context vi /\
      terminates (run_context fuel unit.cu_context vi) /\
      (tx.is_static ==>
       ~(!n. terminates (run_context n unit.cu_context vi) ==>
             ?u. run_context n unit.cu_context vi = Abort ExHalt_abort u))` by
    (gen_tac >> strip_tac >>
     qspecl_then [`tops`, `rpolicy`, `unit`, `am`, `tx`, `vs`, `vi`, `fuel`, `fmp`]
       mp_tac call_gas_raw_variant_facts >>
     impl_tac >- (simp[] >> rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     simp[Abbr`D`, taint_within_def]) >>
  `venom_run_bounded fuel' M out.po_unit.cu_context vs` by
    (qpat_x_assum `!D vs fmp. _ ==> venom_run_bounded _ _ _ _`
       (qspecl_then [`D`, `vs`, `fmp`] mp_tac) >>
     impl_tac >- (simp[] >> metis_tac[]) >> simp[]) >>
  `LENGTH vs.vs_data_section < dimword (:256) DIV 2` by
    (irule data_section_length_bound >> conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
     qexists_tac `assemble prog'` >> simp[]) >>
  `!eom. max_live_eom out.po_unit.cu_context = SOME eom ==>
         eom <= w2n vs.vs_initial_fmp` by
    metis_tac[generate_context_plan_eom_room] >>
  `code_end_offset_ok (raw_reachable vs) out.po_unit.cu_context` by
    (qspecl_then [`D`, `0`, `rpolicy`, `unit`, `out`, `vs`, `fmp`]
       mp_tac o1_pipeline_code_end_offset_ok_static_abort >>
     impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then (qx_choose_then `vcode` strip_assume_tac) >>
     qpat_assum `!vi. raw_variant _ vi vs ==> _` (qspec_then `vcode` mp_tac) >>
     impl_tac >- FIRST_ASSUM ACCEPT_TAC >> strip_tac >>
     qpat_x_assum `_ ==> code_end_offset_ok _ _ /\ _` mp_tac >>
     impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     disch_then (CONJUNCTS_THEN2 assume_tac (DISJ_CASES_THEN assume_tac))
     >- first_assum ACCEPT_TAC >>
     Cases_on `tx.is_static` >- metis_tac[] >>
     qpat_x_assum `code_end_offset_ok (\_ _ _ _. _) _` mp_tac >>
     simp_tac bool_ss [code_end_offset_ok_def, in_static_abort_prefix_def] >>
     metis_tac[gasFocusReplayExitTheory.replay_exit_raw_call_ctx]) >>
  `o1_lowered_inv out.po_unit.cu_context vs` by
    (Cases_on `tx.is_static`
     >- (qspecl_then [`D`, `0`, `rpolicy`, `unit`, `out`, `vs`, `fmp`]
           mp_tac run_venom_pipeline_correct_static_abort >>
         impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
         disch_then (qx_choose_then `vstatic` strip_assume_tac) >>
         qpat_assum `!vi. raw_variant _ vi vs ==> _` (qspec_then `vstatic` mp_tac) >>
         impl_tac >- FIRST_ASSUM ACCEPT_TAC >> strip_tac >>
         qpat_x_assum `_ ==> ctx_sim D _ _ vstatic vs /\ ctx_abort_rq D _ _ vstatic vs /\ _`
           mp_tac >>
         impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >> metis_tac[]) >>
     `o1_run_state_ok vs` by fs[o1_run_state_ok_def] >>
     qspecl_then [`D`, `0`, `rpolicy`, `unit`, `out`, `vs`, `fmp`]
       mp_tac run_venom_pipeline_correct >>
     impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then (qx_choose_then `vrun` strip_assume_tac) >>
     qpat_assum `!vi. raw_variant _ vi vs ==> _` (qspec_then `vrun` mp_tac) >>
     impl_tac >- FIRST_ASSUM ACCEPT_TAC >> strip_tac >>
     qpat_x_assum `_ ==> ctx_sim D _ _ vrun vs /\ _` mp_tac >>
     impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >> simp[]) >>
  drule_all o1_pipeline_memory_obligations_raw >> strip_tac >>
  drule_all o1_pipeline_codegen_obligations >> strip_tac >>
  qpat_x_assum `!g' Inv vs es. _`
    (qspecl_then [`g'`, `raw_reachable vs`, `vs`, `es`] mp_tac) >>
  fs[Abbr`eg`]
QED

Theorem e2e_deploy_gas_sufficient_asm_opt:
  !policy tops deploy_bc runtime_bc am tx es.
    compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\ supported_program_deploy tops /\
    deploy_typing_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    ~(?t. runtime_bc = 0xEFw :: t)
    ==>
    ?g. !g'.
      g <= g' /\
      LENGTH (call_trace (add_frame_gas g' es)) < 2 ** 64 /\
      (!gs. deploy_storage_ok tops am tx
              (MAP SND (call_trace (add_frame_gas g' es))) gs) /\
      (!obs. ~deploy_gas_source_exempt tops
         (load_contract (SOME (MAP SND (call_trace (add_frame_gas g' es))))
            obs am tx [(NONE, tops)] []))
      ==>
      ?r es'.
        run_call (add_frame_gas g' es) = SOME (r, es') /\
        (r = INR (SOME OutOfGas) ==>
         max_code_size < LENGTH runtime_bc + imm_len tops \/
         ?s. frame_inst_at (add_frame_gas g' es) s ReturnDataCopy)
Proof
  rpt strip_tac >>
  drule compile_vyper_deploy_phases_asm_opt >> strip_tac >>
  qpat_x_assum `deploy_bc = assemble prog'` SUBST_ALL_TAC >>
  `asm_opt_finalizer IN accepted_finalizers` by simp[accepted_finalizers_def] >>
  `deploy_source_ok tops am tx` by simp[deploy_source_ok_def] >>
  drule_all deploy_unit_o1_shape_ok >> strip_tac >>
  drule_all deploy_unit_defs_reach_uses >> strip_tac >>
  `o1PipelineCorrect$o1_pipeline rpolicy dunit = SOME dout /\
   codegen_assembly rpolicy dout.po_unit = SOME prog /\
   generate_context_plan dout.po_unit.cu_context = SOME cplan /\
   lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit` by
    fs[deploy_phases_def] >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  `assemble prog <> []` by metis_tac[codegen_assembly_nonempty] >>
  `assemble prog' <> []` by
    (irule codegen_assembly_finalizer_nonempty >> metis_tac[]) >>
  drule_all lower_vyper_deploy_unit_sym_src_ok_own >> strip_tac >>
  drule_all gasFocusOptLabelFlowTheory.focus_opt_label_flow_own >> strip_tac >>
  drule_all o1_pipeline_sym_unit_static_ok >> strip_tac >>
  `lowering_context_ok dunit.cu_context` by metis_tac[deploy_unit_context_ok] >>
  qspecl_then [`tops`, `rpolicy`, `runtime_bc`, `dunit`, `am`, `tx`]
    mp_tac deploy_unit_fns_fuel_stable >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all run_context_uniform_fuel >>
  disch_then (qx_choose_then `fuel` assume_tac) >>
  qspecl_then [`imm_len tops`, `rpolicy`, `dunit`, `dout`, `cplan`, `fuel`]
    mp_tac run_venom_pipeline_run_bounded_raw >>
  impl_tac >- simp[] >> disch_then (qx_choosel_then [`fuel'`, `M`] assume_tac) >>
  qspecl_then [`rpolicy`, `dout.po_unit`, `cplan`, `prog`, `prog'`, `fuel'`, `M`,
               `code_deposit_cost * max_code_size`] mp_tac
    codegen_gas_surplus_asm_opt_own >>
  impl_tac >- simp[] >> disch_then (qx_choose_then `g` assume_tac) >>
  qexists_tac `g` >> rpt strip_tac >>
  `?c0 rb0. es.contexts = [(c0, rb0)] /\ wf_state es` by
    fs[deploy_state_rel_def] >>
  qabbrev_tac `eg = add_frame_gas g' es` >>
  Cases_on `?s. frame_inst_at eg s ReturnDataCopy`
  >- (qspec_then `eg` strip_assume_tac run_call_total >> metis_tac[]) >>
  `deploy_state_rel tops (assemble prog') am tx eg` by
    (simp[Abbr`eg`] >> irule deploy_state_rel_add_frame_gas >> simp[]) >>
  qpat_x_assum `deploy_state_rel _ _ _ _ es` kall_tac >>
  `?ctxt rb. eg.contexts = [(ctxt, rb)] /\
             ctxt.msgParams.outputTo = Code tx.target /\ wf_state eg` by
    fs[deploy_state_rel_def] >>
  `!t. ~frame_inst_at (shadow_root eg) t ReturnDataCopy` by
    (rpt strip_tac >> `eg.contexts <> []` by simp[] >>
     drule_all shadow_root_frame_inst_at >> metis_tac[]) >>
  `shadow_root eg = add_frame_gas g' (shadow_root es)` by
    (simp[Abbr`eg`] >> irule shadow_root_add_frame_gas >> fs[]) >>
  `wf_state (shadow_root eg)` by simp[shadow_root_wf_state] >>
  `g' <= frame_gas_left (shadow_root eg)` by
    (qpat_x_assum `shadow_root eg = _` SUBST1_TAC >>
     irule wf_state_frame_gas_left >> simp[shadow_root_wf_state]) >>
  qabbrev_tac `vs = opt_deploy_entry_state_own prog prog' cplan tops eg` >>
  qabbrev_tac `txp = tx with code := vs.vs_code` >>
  `txp = tx` by
    (simp[Abbr `txp`, Abbr `vs`] >> metis_tac[deploy_own_txp_identity]) >>
  `deploy_source_ok tops am txp` by simp[] >>
  `code_layout_valid vs` by
    (mp_tac (Q.INST [`fin` |-> `asm_opt_finalizer`, `es` |-> `eg`]
               deploy_raw_entry_code_layout) >>
     impl_tac >- simp[] >>
     simp[code_layout_valid_def, Abbr `vs`]) >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `eg`, `cplan`]
    mp_tac opt_deploy_asm_rels_own >>
  impl_tac >- simp[] >> strip_tac >>
  `vs.vs_code = assemble prog' ++ vs.vs_data_section` by fs[Abbr `vs`] >>
  `vs.vs_initial_fmp = n2w cplan.cp_initial_fmp /\
   vs.vs_alloca_next = imm_len tops /\ vs.vs_fmp = vs.vs_initial_fmp /\
   vs.vs_outcomes = MAP SND (call_trace eg)` by
    simp[Abbr `vs`, opt_deploy_entry_state_own_def, opt_entry_state_own_def,
         entry_venom_state_def] >>
  `o1_run_state_ok vs` by
    (simp[Abbr`vs`, o1_run_state_ok_def, o1_initial_state_ok_def,
          opt_deploy_entry_state_own_def, opt_entry_state_own_def, entry_venom_state_def,
          venomStateTheory.init_venom_state_def] >>
     gvs[deploy_state_rel_def]) >>
  `txp.function_name = "__init__" /\ txp.target = tx.target` by
    fs[Abbr`txp`, deploy_state_rel_def] >>
  `!gs. deploy_storage_ok tops am txp vs.vs_outcomes gs` by
    simp[] >>
  `!obs. load_contract (SOME vs.vs_outcomes) obs am txp [(NONE,tops)] [] =
         load_contract (SOME vs.vs_outcomes) obs am tx [(NONE,tops)] []` by
    simp[] >>
  `!obs. ~deploy_gas_source_exempt tops
          (load_contract (SOME vs.vs_outcomes) obs am txp [(NONE,tops)] [])` by fs[] >>
  `mem_inv (\ctx fn inst s. inst_create_size_ok inst s)
      dout.po_unit.cu_context vs` by
    (Cases_on `deploy_dalloca_form_occurs expr_create_root tops`
     >- (qspecl_then [`asm_opt_finalizer`, `policy`, `tops`, `runtime_bc`, `rpolicy`,
                      `dunit`, `dout`, `prog`, `prog'`, `cplan`, `am`, `tx`,
                      `eg`, `vs`]
           mp_tac deploy_entry_reachable_create_size_ok >> simp[Abbr `vs`, Abbr `txp`]) >>
     drule_all deploy_entry_create_size_ok >> simp[]) >>
  qspecl_then [`policy`, `tops`, `runtime_bc`, `rpolicy`, `dunit`, `dout`,
               `prog`, `prog'`, `cplan`, `eg`] mp_tac deploy_raw_fmp_exists >>
  impl_tac >- simp[] >> disch_then (qx_choose_then `fmp` strip_assume_tac) >>
  `w2n vs.vs_initial_fmp <= w2n fmp` by simp[Abbr `vs`] >>
  qabbrev_tac `Du = <| d_stor := K (K UNIV); d_trans := K (K UNIV);
                       d_imm := K UNIV; d_ret := K UNIV |>` >>
  `dead_wf Du` by simp[Abbr `Du`, dead_wf_def] >>
  `!vi. raw_variant fmp vi vs ==>
      ?(H : (bool # bytes32 # type_value) list # num list) obs efuel.
        raw_unit_memory_ok dunit.cu_context vi /\
        ptr_discipline (imm_len tops) dunit.cu_context vi /\
        taint_within (deploy_dead H tops runtime_bc am txp) dunit.cu_context vi /\
        mem_inv dload_offset_ok dunit.cu_context vi /\
        mem_inv dload_headroom_ok dunit.cu_context vi /\
        mem_inv (\c f inst s. inst_dload_in_section inst s /\
                             s.vs_code = vi.vs_code /\
                             s.vs_data_section = vi.vs_data_section)
          dunit.cu_context vi /\
        deploy_venom_result_rel H tops runtime_bc txp
          (load_contract (SOME vs.vs_outcomes) obs am txp [(NONE,tops)] [])
          (run_context efuel dunit.cu_context vi)` by
    (gen_tac >> strip_tac >>
     qspecl_then [`asm_opt_finalizer`, `policy`, `tops`, `runtime_bc`, `rpolicy`,
                  `dunit`, `dout`, `prog`, `prog'`, `cplan`, `am`, `tx`,
                  `eg`, `vs`, `vi`, `fmp`] mp_tac deploy_gas_raw_variant_facts >>
     impl_tac >- fs[Abbr `vs`, deploy_gas_source_exempt_def] >> fs[]) >>
  `venom_run_bounded fuel' M dout.po_unit.cu_context vs` by
    (qpat_x_assum `!D vs fmp. _ ==> venom_run_bounded _ _ _ _`
       (qspecl_then [`Du`, `vs`, `fmp`] mp_tac) >>
     impl_tac >- (simp[] >> gen_tac >> strip_tac >>
       qpat_assum `!vi. raw_variant _ vi vs ==> _` drule >> strip_tac >>
       `terminates (run_context fuel dunit.cu_context vs_in)` by
         (qpat_x_assum `!s f. terminates _ ==> _` irule >>
          metis_tac[deploy_venom_result_rel_terminates]) >>
       simp[Abbr`Du`, taint_within_def]) >> simp[]) >>
  `LENGTH vs.vs_data_section < dimword (:256) DIV 2` by
    (irule data_section_length_bound >> conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
     qexists_tac `assemble prog'` >> simp[]) >>
  `!eom. max_live_eom dout.po_unit.cu_context = SOME eom ==>
         eom <= w2n vs.vs_initial_fmp` by
    metis_tac[generate_context_plan_eom_room] >>
  qspecl_then [`imm_len tops`, `rpolicy`, `dunit`, `dout`, `vs`,
               `fmp`] mp_tac run_venom_pipeline_correct_all_dead >>
  impl_tac >- simp[] >> strip_tac >>
  qpat_assum `!vi. raw_variant _ vi vs ==> _` drule >> strip_tac >>
  qabbrev_tac `D = deploy_dead H tops runtime_bc am txp` >>
  `dead_wf D` by simp[Abbr`D`, deploy_dead_wf] >>
  `ctx_sim D dunit.cu_context dout.po_unit.cu_context vs_in vs /\
   o1_lowered_inv dout.po_unit.cu_context vs` by
    (qpat_x_assum `!D. _ ==> _` (qspec_then `D` mp_tac) >>
     impl_tac >- fs[Abbr`D`] >> simp[]) >>
  `~vs.vs_call_ctx.cc_static` by fs[o1_run_state_ok_def] >>
  `code_end_offset_ok (raw_reachable vs) dout.po_unit.cu_context` by
    (qspecl_then [`Du`, `imm_len tops`, `rpolicy`, `dunit`, `dout`, `vs`, `fmp`]
       mp_tac o1_pipeline_code_end_offset_ok_static_abort >>
     impl_tac >- (fs[o1_run_state_ok_def] >> rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     disch_then (qx_choose_then `vcode` strip_assume_tac) >>
     qpat_assum `!vi. raw_variant _ vi vs ==> _` (qspec_then `vcode` mp_tac) >>
     impl_tac >- FIRST_ASSUM ACCEPT_TAC >> strip_tac >>
     qpat_x_assum `_ ==> code_end_offset_ok _ _ /\ _` mp_tac >>
     impl_tac >- simp[Abbr `Du`, taint_within_def] >>
     disch_then (mp_tac o CONJUNCT1) >>
     simp_tac bool_ss [code_end_offset_ok_def, in_static_abort_prefix_def] >>
     metis_tac[gasFocusReplayExitTheory.replay_exit_raw_call_ctx]) >>
  drule_all o1_pipeline_memory_obligations_raw >> strip_tac >>
  drule_all o1_pipeline_codegen_obligations >> strip_tac >>
  `terminates (run_context efuel dunit.cu_context vs_in)` by
    metis_tac[deploy_venom_result_rel_terminates] >>
  `?vfuel. dead_result_rel D (run_context efuel dunit.cu_context vs_in)
             (run_context vfuel dout.po_unit.cu_context vs)` by
    metis_tac[ctx_sim_def] >>
  `~deploy_source_exempt tops
      (load_contract (SOME vs.vs_outcomes) obs am txp [(NONE,tops)] [])` by
    fs[deploy_gas_source_exempt_def] >>
  qspecl_then [`H`, `tops`, `runtime_bc`, `am`, `txp`,
               `SOME vs.vs_outcomes`, `obs`,
               `load_contract (SOME vs.vs_outcomes) obs am txp [(NONE,tops)] []`,
               `run_context efuel dunit.cu_context vs_in`,
               `run_context vfuel dout.po_unit.cu_context vs`] mp_tac
    deploy_venom_result_rel_dead >>
  impl_tac >- fs[Abbr`D`, deploy_state_rel_def] >> strip_tac >>
  qabbrev_tac `sh = shadow_root eg` >>
  `!s op r s'. frame_inst_at sh s op /\ step_inst op s = (r, s') /\
               LENGTH s'.contexts = LENGTH s.contexts ==>
               r <> INR (SOME OutOfGas) /\
               code_deposit_cost * max_code_size <= frame_gas_left s'` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!g' Inv vs es s op r s'. _`
       (qspecl_then [`g'`, `raw_reachable vs`, `vs`, `shadow_root es`,
                     `s`, `op`, `r`, `s'`] mp_tac) >>
     qpat_assum `sh = add_frame_gas _ _`
       (fn th => PURE_REWRITE_TAC [GSYM th]) >>
     impl_tac >- fs[Abbr`sh`, Abbr`vs`] >> simp[]) >>
  qspecl_then [`vfuel`, `rpolicy`, `dout.po_unit`, `cplan`, `prog`, `prog'`,
               `raw_reachable vs`, `vs`, `sh`] mp_tac codegen_correct_asm_opt_own >>
  impl_tac >- fs[Abbr`vs`, Abbr`sh`] >>
  disch_then (qx_choosel_then [`r`, `es'`]
     (fn th => map_every assume_tac (CONJUNCTS th))) >>
  qspecl_then [`H`, `eg`, `ctxt`, `rb`, `txp`, `tops`, `runtime_bc`,
               `load_contract (SOME vs.vs_outcomes) obs am txp [(NONE,tops)] []`,
               `run_context vfuel dout.po_unit.cu_context vs`,
               `r`, `es'`] mp_tac deploy_frame_gas_tail >>
  impl_tac
  >- (qpat_assum `Abbrev (sh = shadow_root eg)`
        (fn th => PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
      rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE simp[])) >>
  simp[]
QED

(* ===== The companions ===== *)

(* TOP-LEVEL: one theorem over the accepted finalizers, with
   vyper_call_correct_guarded's finalizer premises. *)
Theorem vyper_call_gas_sufficient:
  !fin policy tops deploy_bc runtime_bc am tx es.
    fin IN accepted_finalizers /\
    compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
    source_typing_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es
    ==>
    ?g. !g'.
      g <= g' ==>
      ?r es'.
        run_call (add_frame_gas g' es) = SOME (r, es') /\
        ((!f vals.
            calldata_dispatch tops tx.calldata = SOME (f, vals) ==>
              (!gs. call_storage_ok am
                 (tx with <| function_name := f; args := vals |>)
                 (MAP SND (call_trace (add_frame_gas g' es))) gs) /\
              (!obs. ~gas_source_exempt tops
                 (tx with <| function_name := f; args := vals |>)
                 (call_external (SOME (MAP SND (call_trace (add_frame_gas g' es))))
                    obs am (tx with <| function_name := f; args := vals |>))) /\
              LENGTH (call_trace (add_frame_gas g' es)) < 2 ** 64) /\
         frame_raises (add_frame_gas g' es) OutOfGas ==>
         ?s. frame_inst_at (add_frame_gas g' es) s ReturnDataCopy)
Proof
  rpt gen_tac >> strip_tac >>
  `supported_program tops` by (
    irule source_typing_ok_supported_program >>
    fs[e2eDefsTheory.call_state_rel_def] >> metis_tac[]) >>
  `?g. !g'.
     g <= g' /\
     (!f vals.
        calldata_dispatch tops tx.calldata = SOME (f, vals) ==>
          (!gs. call_storage_ok am
             (tx with <| function_name := f; args := vals |>)
             (MAP SND (call_trace (add_frame_gas g' es))) gs) /\
          (!obs. ~gas_source_exempt tops
             (tx with <| function_name := f; args := vals |>)
             (call_external (SOME (MAP SND (call_trace (add_frame_gas g' es))))
                obs am (tx with <| function_name := f; args := vals |>))) /\
          LENGTH (call_trace (add_frame_gas g' es)) < 2 ** 64)
     ==>
     ?r es'.
       run_call (add_frame_gas g' es) = SOME (r, es') /\
       (frame_raises (add_frame_gas g' es) OutOfGas ==>
        ?s. frame_inst_at (add_frame_gas g' es) s ReturnDataCopy)` by
    (`fin = K SOME \/ fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
     pop_assum strip_assume_tac >> pop_assum SUBST_ALL_TAC
     >- (drule_all vyper_call_gas_sufficient_identity >> simp[])
     >>
     drule_all vyper_call_gas_sufficient_asm_opt >> simp[]) >>
  (* run_call is total, so the run exists whatever the conditions *)
  qexists_tac `g` >> rpt strip_tac >>
  qspec_then `add_frame_gas g' es` strip_assume_tac run_call_total >>
  qexistsl_tac [`r`, `es'`] >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!g'. g <= g' /\ _ ==> _` (qspec_then `g'` mp_tac) >>
  impl_tac >- fs[] >>
  strip_tac >> metis_tac[]
QED

(* TOP-LEVEL: one theorem over the accepted finalizers, with
   e2e_deploy_correctness's finalizer premises.  The RETURNDATACOPY escape is
   for constructors that call out; with today's call-free constructors only
   the code-size escape is taken. *)
Theorem e2e_deploy_gas_sufficient:
  !fin policy tops deploy_bc runtime_bc am tx es.
    fin IN accepted_finalizers /\
    compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
    deploy_typing_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es
    ==>
    ?g. !g'.
      g <= g' ==>
      ?r es'.
        run_call (add_frame_gas g' es) = SOME (r, es') /\
        ((!gs. deploy_storage_ok tops am tx
                 (MAP SND (call_trace (add_frame_gas g' es))) gs) /\
         (!obs. ~deploy_gas_source_exempt tops
            (load_contract (SOME (MAP SND (call_trace (add_frame_gas g' es))))
               obs am tx [(NONE, tops)] [])) /\
         LENGTH (call_trace (add_frame_gas g' es)) < 2 ** 64 /\
         r = INR (SOME OutOfGas) ==>
         max_code_size < LENGTH runtime_bc + imm_len tops \/
         ?s. frame_inst_at (add_frame_gas g' es) s ReturnDataCopy)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_vyper_runtime_not_ef >> strip_tac >>
  `supported_program tops /\ supported_program_deploy tops` by (
    irule deploy_typing_ok_supported_programs >>
    fs[deploy_state_rel_def] >> metis_tac[]) >>
  `?g. !g'.
     g <= g' /\
     LENGTH (call_trace (add_frame_gas g' es)) < 2 ** 64 /\
     (!gs. deploy_storage_ok tops am tx
             (MAP SND (call_trace (add_frame_gas g' es))) gs) /\
     (!obs. ~deploy_gas_source_exempt tops
        (load_contract (SOME (MAP SND (call_trace (add_frame_gas g' es))))
           obs am tx [(NONE, tops)] []))
     ==>
     ?r es'.
       run_call (add_frame_gas g' es) = SOME (r, es') /\
       (r = INR (SOME OutOfGas) ==>
        max_code_size < LENGTH runtime_bc + imm_len tops \/
        ?s. frame_inst_at (add_frame_gas g' es) s ReturnDataCopy)` by
    (`fin = K SOME \/ fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
     pop_assum strip_assume_tac >> pop_assum SUBST_ALL_TAC
     >- (drule_all e2e_deploy_gas_sufficient_identity >> simp[])
     >>
     drule_all e2e_deploy_gas_sufficient_asm_opt >> simp[]) >>
  (* run_call is total, so the run exists whatever the conditions *)
  qexists_tac `g` >> rpt strip_tac >>
  qspec_then `add_frame_gas g' es` strip_assume_tac run_call_total >>
  qexistsl_tac [`r`, `es'`] >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!g'. g <= g' /\ _ ==> _` (qspec_then `g'` mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >> gvs[] >>
  DISJ2_TAC >> qexists_tac `s` >> first_assum ACCEPT_TAC
QED
