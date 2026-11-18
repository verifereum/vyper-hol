(* The sufficient-gas companions over the accepted finalizers: each joins
 * its identity case from e2eGasSufficient with its assembly-optimizer case,
 * as vyper_call_correct and e2e_deploy_correctness do.
 *
 * TOP-LEVEL:
 *   vyper_call_gas_sufficient -- the companion of vyper_call_correct
 *   e2e_deploy_gas_sufficient -- the companion of e2e_deploy_correctness
 *)
Theory e2eGasSufficientTop
Ancestors
  e2eGasSufficient e2eComposition asmOptimizer
  e2eCorrectness e2eDefs e2eEntry e2eOptEntry e2eProducers
  callCodeTrace callRawVariant sourceUnitExitSafe exprSimHypsDefs
  vyperLoweringCorrect loweringRuntimeCorrect loweringMemCorrect
  loweringShapeSource runtimeLabelReadiness runtimeSymSrcUnit fragFuelUnit
  e2eDeployRawFmp e2eDeployAtMarks e2eDeployDefs deploySymSrcUnit
  ctorDeployDefs ctorDeployDefsReach ctorDeployRawEntryFacts
  ctorDeployFrame ctorDeployShape ctorDeployDead ctorDeployRunBounded
  ctorDeployInitcodeAsm ctorDeployMemoryFrontier ctorDeployLoweringSource
  ctorDeployCallFree deployUnitProducers deployUnitExecution deployUnitExitSafe
  deployFrameReplay compileVyper compilePhasesProps
  codegen codegenGasAsmOpt codegenAsmProgOk codegenAsmOpt
  codegenEntrySim codegenEntryRel asmFrameRel codegenRel frameRel
  asmOptNonemptyFinalizer immutableCodeLayout
  frameGas frameStep unitTransformDefs lowerDloadDefs ptrDiscipline
  o1PassContract o1PipelineCorrect o1CodeEndOffset o1StaticPipelineCorrect
  o1OpcodeAbsence o1LabelFlowCompose o1SafeUpto unitMemInv
  vyperInterpreter vfmExecution vfmContext list

val _ = Parse.hide "tops";

(* ===== The assembly optimizer's cases ===== *)

(* Gas top-ups keep the entry layout and read the new execution's streams. *)
Triviality opt_entry_state_add_frame_gas:
  opt_entry_state prog prog' cplan (add_frame_gas g es) =
  opt_entry_state prog prog' cplan es with
    <|vs_outcomes := MAP SND (call_trace (add_frame_gas g es));
      vs_gas_readings := gas_readings (add_frame_gas g es)|>
Proof
  `(FST (HD (add_frame_gas g es).contexts)).msgParams.code =
   (FST (HD es.contexts)).msgParams.code` by
    (Cases_on `es.contexts` >- simp[add_frame_gas_def] >>
     PairCases_on `h` >> simp[add_frame_gas_def]) >>
  simp[opt_entry_state_def, entry_venom_state_add_frame_gas,
       venomStateTheory.venom_state_component_equality]
QED

Triviality opt_entry_asm_rel_add_frame_gas:
  wf_state es /\
  codegen_asm_entry_rel cplan prog (opt_entry_state prog prog' cplan es)
    (entry_asm_state (opt_entry_state prog prog' cplan es) es) /\
  asm_frame_rel prog' (opt_entry_state prog prog' cplan es).vs_data_section es
    (entry_asm_state (opt_entry_state prog prog' cplan es) es with
       as_code := assemble prog' ++
                    (opt_entry_state prog prog' cplan es).vs_data_section) es ==>
  !g.
    codegen_asm_entry_rel cplan prog
      (opt_entry_state prog prog' cplan (add_frame_gas g es))
      (entry_asm_state (opt_entry_state prog prog' cplan (add_frame_gas g es))
         (add_frame_gas g es)) /\
    asm_frame_rel prog'
      (opt_entry_state prog prog' cplan (add_frame_gas g es)).vs_data_section
      (add_frame_gas g es)
      (entry_asm_state (opt_entry_state prog prog' cplan (add_frame_gas g es))
         (add_frame_gas g es) with
       as_code := assemble prog' ++
         (opt_entry_state prog prog' cplan (add_frame_gas g es)).vs_data_section)
      (add_frame_gas g es)
Proof
  simp[opt_entry_state_add_frame_gas] >> strip_tac >> gen_tac >>
  Cases_on `es.contexts` >- fs[asm_frame_rel_def] >>
  PairCases_on `h` >>
  drule add_frame_gas_contexts >> disch_then (qspec_then `g` assume_tac) >>
  `(add_frame_gas g es).originalAccounts = es.originalAccounts` by
    simp[add_frame_gas_def] >>
  `wf_state (add_frame_gas g es)` by simp[add_frame_gas_wf_state] >>
  conj_tac
  >- fs[codegen_asm_entry_rel_def, entry_asm_state_def, shared_state_rel_def,
        venom_asm_terminal_rel_def] >>
  fs[asm_frame_rel_def, asm_evm_rel_def, entry_asm_state_def,
     opt_entry_state_def, entry_venom_state_frame_fields, entry_venom_state_fresh,
     add_frame_gas_fields, relationTheory.RTC_REFL]
QED

Triviality entry_data_section_bound:
  code_layout_valid vs /\ vs.vs_code = code ++ vs.vs_data_section /\ code <> [] ==>
  LENGTH vs.vs_data_section < dimword (:256) DIV 2
Proof
  strip_tac >>
  `0 < LENGTH code` by (Cases_on `code` >> fs[]) >>
  fs[code_layout_valid_def] >> decide_tac
QED

(* At the finalized call's entry, the raw unit sees the unoptimized code.
   The storage and source exemption guards transfer because the program
   cannot observe its own code. *)
Theorem vyper_call_gas_sufficient_asm_opt:
  !policy tops deploy_bc runtime_bc am tx es.
    compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) /\
    ~program_reads_self_code tops /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es
    ==>
    ?g. !g'.
      g <= g' /\
      (case calldata_dispatch tops tx.calldata of
         NONE => T
       | SOME (f, vals) =>
           (!gs. call_storage_ok am
              (tx with <| function_name := f; args := vals |>)
              (MAP SND (call_trace (add_frame_gas g' es))) gs) /\
           (!obs. ~gas_source_exempt tops
              (tx with <| function_name := f; args := vals |>)
              (call_external (SOME (MAP SND (call_trace (add_frame_gas g' es))))
                 obs am (tx with <| function_name := f; args := vals |>)))) /\
      LENGTH (call_trace (add_frame_gas g' es)) < 2 ** 64
      ==>
      ?r es'.
        run_call (add_frame_gas g' es) = SOME (r, es') /\
        (frame_raises (add_frame_gas g' es) OutOfGas ==>
         ?s. frame_inst_at (add_frame_gas g' es) s ReturnDataCopy)
Proof
  PURE_REWRITE_TAC [frame_raises_inst_raises] >>
  rpt strip_tac >>
  drule compile_vyper_runtime_phases_asm_opt >> strip_tac >>
  qpat_x_assum `runtime_bc = assemble _` SUBST_ALL_TAC >>
  qpat_x_assum `prog = _` kall_tac >>
  drule supported_program_raw_shape_free_program >> strip_tac >>
  `?art. check_contract F am.layouts tx.target [(NONE, tops)] = SOME art` by
    metis_tac[source_typing_ok_def] >>
  drule_all lower_vyper_runtime_unit_source_unit_ok >> strip_tac >>
  drule_all lower_vyper_runtime_unit_o1_shape_extras >> strip_tac >>
  drule_all lower_vyper_runtime_unit_defs_reach_uses >> strip_tac >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  `~ctx_has_dalloca unit.cu_context` by
    (irule every_no_dalloca >>
     drule_all lower_vyper_runtime_unit_no_dalloca_checked >> simp[]) >>
  `assemble prog <> []` by
    metis_tac[codegenAsmProgOkTheory.codegen_assembly_nonempty] >>
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
  drule_all lower_vyper_runtime_unit_sym_src_ok >> strip_tac >>
  drule_all o1_pipeline_label_flow_preserved >> strip_tac >>
  drule_all o1_pipeline_sym_unit_static_ok >> strip_tac >>
  `!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
     ~MEM (Label "runtime_begin") inst.inst_operands` by
    metis_tac[lower_vyper_runtime_unit_no_runtime_begin] >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  qspecl_then [`tops`, `rpolicy`, `unit`] mp_tac
    lower_vyper_runtime_unit_fns_stable >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all run_context_terminates_uniform >>
  disch_then (qx_choose_then `fuel` assume_tac) >>
  qspecl_then [`0`, `rpolicy`, `unit`, `out`, `cplan`, `fuel`] mp_tac
    run_venom_pipeline_run_bounded_static_abort >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`fuel'`, `M`] assume_tac) >>
  qspecl_then [`rpolicy`, `out.po_unit`, `cplan`, `prog`, `prog'`, `fuel'`, `M`]
    mp_tac codegen_gas_sufficient_asm_opt >>
  impl_tac >- simp[] >> disch_then (qx_choose_then `g` assume_tac) >>
  `!vs. mem_inv (\ctx fn inst s. inst_create_size_ok inst s)
          out.po_unit.cu_context vs` by
    metis_tac[o1_runtime_unit_create_size_ok] >>
  qexists_tac `g` >> rpt strip_tac >>
  qabbrev_tac `eg = add_frame_gas g' es` >>
  `wf_state es` by fs[call_state_rel_def, evm_state_ok_def] >>
  `outcomes_accounts_typed (SOME (MAP SND (call_trace eg)))` by
    (`wf_state eg /\ balance_bounded (2 ** 256 - 1) eg /\ returndata_bounded eg`
       by fs[Abbr`eg`, call_state_rel_def, evm_state_ok_def, add_frame_gas_wf_state,
             add_frame_gas_bounded] >>
     drule_all call_trace_outcomes_bounded >>
     simp[outcomes_accounts_typed_def, listTheory.EVERY_MEM]) >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`, `out.po_unit`]
    mp_tac opt_entry_codegen_asm_entry_rel >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`, `out.po_unit`]
    mp_tac opt_entry_asm_frame_rel >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all opt_entry_asm_rel_add_frame_gas >>
  disch_then (qspec_then `g'` strip_assume_tac) >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`,
               `rpolicy`, `out.po_unit`] mp_tac opt_entry_code_layout_valid >>
  impl_tac >- simp[] >> strip_tac >>
  qabbrev_tac `vs = opt_entry_state prog prog' cplan eg` >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`,
               `opt_entry_state prog prog' cplan es`] mp_tac opt_entry_fields >>
  impl_tac >- simp[] >> strip_tac >>
  `code_layout_valid vs /\ o1_initial_state_ok vs /\
   vs.vs_initial_fmp = n2w cplan.cp_initial_fmp /\ vs.vs_fmp = vs.vs_initial_fmp /\
   vs.vs_call_ctx.cc_static = tx.is_static /\
   vs.vs_outcomes = MAP SND (call_trace eg) /\
   vs.vs_code = assemble prog ++ vs.vs_data_section /\
   valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret` by
    fs[Abbr`vs`, Abbr`eg`, opt_entry_state_add_frame_gas,
       o1_initial_state_ok_def, code_layout_valid_def] >>
  qabbrev_tac `txp = tx with code := vs.vs_code` >>
  `initial_venom_state_rel tops am txp vs` by
    (qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`]
       mp_tac opt_entry_initial_venom_state_rel >>
     simp[Abbr`txp`, Abbr`vs`, Abbr`eg`, opt_entry_state_add_frame_gas,
          initial_venom_state_rel_def, vyperLoweringCorrectTheory.venom_env_rel_def]) >>
  `source_typing_ok tops am txp` by
    (simp[Abbr`txp`] >> irule source_typing_ok_code_update >>
     fs[code_layout_valid_def, wordsTheory.dimword_def,
        fcpLib.INDEX_CONV ``dimindex(:256)``] >> decide_tac) >>
  `source_deployment_rel tops am txp` by
    fs[Abbr`txp`, source_deployment_rel_def, layouts_agree_def] >>
  `ALOOKUP am.sources tx.target = SOME [(NONE, tops)]` by
    fs[source_deployment_rel_def, layouts_agree_def] >>
  `!gs. call_storage_ok am txp vs.vs_outcomes gs` by
    (fs[Abbr`txp`] >> metis_tac[call_storage_ok_code_update]) >>
  `!obs. call_external (SOME vs.vs_outcomes) obs am txp =
         call_external (SOME vs.vs_outcomes) obs am tx` by
    (gen_tac >> simp[Abbr`txp`, vyperInterpreterTheory.call_external_def] >>
     `call_external_trace (SOME vs.vs_outcomes) obs am (tx with code := vs.vs_code) =
      call_external_trace (SOME vs.vs_outcomes) obs am tx` suffices_by simp[] >>
     irule call_external_trace_no_self_code_update >>
     qexists_tac `tops` >> simp[]) >>
  `!obs. ~gas_source_exempt tops txp
           (call_external (SOME vs.vs_outcomes) obs am txp)` by
    fs[gas_source_exempt_def, Abbr`txp`] >>
  qspecl_then [`tops`, `rpolicy`, `unit`, `am`, `txp`, `ret`] mp_tac
    lower_vyper_runtime_unit_run_bounded >>
  impl_tac >- simp[] >> disch_then (qx_choose_then `fuelp` assume_tac) >>
  qabbrev_tac `D = <| d_stor := K (K UNIV); d_trans := K (K UNIV);
                      d_imm := K UNIV; d_ret := K UNIV |>` >>
  `dead_wf D` by simp[Abbr`D`, dead_wf_def] >>
  `!vi. raw_variant vs.vs_initial_fmp vi vs ==>
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
      (txp.is_static ==>
       ~(!n. terminates (run_context n unit.cu_context vi) ==>
             ?u. run_context n unit.cu_context vi = Abort ExHalt_abort u))` by
    (gen_tac >> strip_tac >>
     `gas_variant vi vs` by metis_tac[raw_variant_gas_variant] >>
     `initial_venom_state_rel tops am txp vi` by
       metis_tac[gas_variant_initial_venom_state_rel] >>
     `vi.vs_outcomes = vs.vs_outcomes /\ vi.vs_call_ctx = vs.vs_call_ctx`
       by metis_tac[gas_variant_outcomes, gas_variant_call_ctx] >>
     `code_layout_valid vi` by
       (irule gas_variant_code_layout_valid >> qexists_tac `vs` >> simp[]) >>
     `valid_vyper_call tops txp vi.vs_call_ctx.cc_calldata ret` by
       gvs[Abbr`txp`, valid_vyper_call_def] >>
     `outcomes_accounts_typed (SOME vi.vs_outcomes) /\
      (!marks. call_storage_ok am txp vi.vs_outcomes
                (gas_explicit marks vi.vs_gas_readings)) /\
      !marks. ~source_exempt tops
        (call_external (SOME vi.vs_outcomes)
           (gas_explicit marks vi.vs_gas_readings) am txp)` by
       (qpat_assum `vi.vs_outcomes = vs.vs_outcomes`
          (fn th => PURE_REWRITE_TAC [th]) >>
        rpt conj_tac
        >- fs[]
        >- (gen_tac >>
            qpat_assum `!gs. call_storage_ok am txp _ gs`
              (qspec_then `gas_explicit marks vi.vs_gas_readings` ACCEPT_TAC)) >>
        gen_tac >>
        qpat_assum `!obs. ~gas_source_exempt tops txp _`
          (qspec_then `gas_explicit marks vi.vs_gas_readings`
             (ACCEPT_TAC o CONJUNCT1 o
              SIMP_RULE (srw_ss()) [gas_source_exempt_def]))) >>
     drule_all lower_vyper_runtime_unit_correct_readings_available >>
     strip_tac >>
     qspecl_then [`marks`, `tops`, `ret`, `am`, `txp`, `unit`, `vi`, `rpolicy`]
       mp_tac source_unit_exit_safe_runs >>
     impl_tac >- fs[] >> strip_tac >>
     `terminates (run_context fuel unit.cu_context vi)` by
       (qpat_x_assum `!f s. terminates _ ==> _`
          (qspecl_then [`fuelp`, `vi`] mp_tac) >>
        impl_tac
        >- (qpat_x_assum `!vs. _ ==> terminates (run_context fuelp _ _)`
              irule >> simp[]) >>
        simp[]) >>
     `vi.vs_fmp = vi.vs_initial_fmp` by
       fs[raw_variant_def, gas_variant_def,
          venomStateTheory.venom_state_component_equality] >>
     `w2n vi.vs_initial_fmp <= w2n vi.vs_fmp` by simp[] >>
     drule_all lower_vyper_runtime_unit_memory_ok >> strip_tac >>
     `mem_inv dload_offset_ok unit.cu_context vi` by
       (irule lower_vyper_runtime_unit_dload_offset_ok >> metis_tac[]) >>
     `mem_inv dload_headroom_ok unit.cu_context vi` by
       (irule lower_vyper_runtime_unit_dload_headroom_ok >> metis_tac[]) >>
     `mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                              s.vs_code = vi.vs_code /\
                              s.vs_data_section = vi.vs_data_section)
        unit.cu_context vi` by
       (irule lower_vyper_runtime_unit_dload_in_section >> metis_tac[]) >>
     simp[Abbr`D`, taint_within_def] >> strip_tac >>
     `call_storage_ok am txp vi.vs_outcomes
        (gas_explicit marks vi.vs_gas_readings)` by
       (qpat_assum `!marks. call_storage_ok am txp vi.vs_outcomes _`
          (qspec_then `marks` ACCEPT_TAC)) >>
     `FST (call_external (SOME vi.vs_outcomes)
            (gas_explicit marks vi.vs_gas_readings) am txp) <>
        INR (Error (RuntimeError "msg.gas: no gas reading"))` by
       (qpat_x_assum `(?tail. _) ==> _` mp_tac >>
        impl_tac
        >- (qexists_tac `[]` >> PURE_REWRITE_TAC [APPEND_NIL] >>
            FIRST_ASSUM ACCEPT_TAC) >>
        disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
     `~gas_source_exempt tops txp
        (call_external (SOME vi.vs_outcomes)
           (gas_explicit marks vi.vs_gas_readings) am txp)` by
       (qpat_assum `vi.vs_outcomes = vs.vs_outcomes`
          (fn th => PURE_REWRITE_TAC [th]) >>
        qpat_assum `!obs. ~gas_source_exempt tops txp _`
          (qspec_then `gas_explicit marks vi.vs_gas_readings` ACCEPT_TAC)) >>
     qspecl_then [`tops`, `ret`, `am`, `txp`, `unit`, `vi`, `marks`] mp_tac
       call_gas_static_no_abort >>
     impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >> simp[]) >>
  `venom_run_bounded fuel' M out.po_unit.cu_context vs` by
    (qpat_x_assum `!D vs fmp. _ ==> venom_run_bounded _ _ _ _`
       (qspecl_then [`D`, `vs`, `vs.vs_initial_fmp`] mp_tac) >>
     impl_tac >- (simp[] >> metis_tac[]) >> simp[]) >>
  `LENGTH vs.vs_data_section < dimword (:256) DIV 2` by
    (irule entry_data_section_bound >> conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
     qexists_tac `assemble prog` >> simp[]) >>
  `!eom. max_live_eom out.po_unit.cu_context = SOME eom ==>
         eom <= w2n vs.vs_initial_fmp` by
    metis_tac[generate_context_plan_eom_room] >>
  `o1_lowered_inv out.po_unit.cu_context vs /\
   code_end_offset_ok (raw_reachable vs) out.po_unit.cu_context` by
    (Cases_on `txp.is_static`
     >- (`code_end_offset_ok (raw_reachable vs) out.po_unit.cu_context` by
           (qspecl_then [`D`, `0`, `rpolicy`, `unit`, `out`, `vs`,
                        `vs.vs_initial_fmp`]
              mp_tac o1_pipeline_code_end_offset_ok_static_abort >>
            impl_tac >- (rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE simp[])) >>
            disch_then (qx_choose_then `vcode` strip_assume_tac) >>
            qpat_assum `!vi. raw_variant _ vi vs ==> _`
              (qspec_then `vcode` mp_tac) >>
            impl_tac >- FIRST_ASSUM ACCEPT_TAC >> strip_tac >>
            qpat_x_assum `_ ==> code_end_offset_ok _ _ /\ _` mp_tac >>
            impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
            disch_then (assume_tac o CONJUNCT2) >> metis_tac[]) >>
         qspecl_then [`D`, `0`, `rpolicy`, `unit`, `out`, `vs`, `vs.vs_initial_fmp`]
           mp_tac run_venom_pipeline_correct_static_abort >>
         impl_tac >- (rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE simp[])) >>
         disch_then (qx_choose_then `vstatic` strip_assume_tac) >>
         qpat_assum `!vi. raw_variant _ vi vs ==> _`
           (qspec_then `vstatic` mp_tac) >>
         impl_tac >- FIRST_ASSUM ACCEPT_TAC >> strip_tac >>
         qpat_x_assum `_ ==> ctx_sim D _ _ vstatic vs /\ ctx_abort_rq D _ _ vstatic vs /\ _`
           mp_tac >>
         impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
         disch_then (assume_tac o CONJUNCT2 o CONJUNCT2) >> metis_tac[]) >>
     `o1_run_state_ok vs` by fs[o1_run_state_ok_def, Abbr`txp`] >>
     qspecl_then [`D`, `0`, `rpolicy`, `unit`, `out`, `vs`, `vs.vs_initial_fmp`]
       mp_tac o1_pipeline_code_end_offset_ok >>
     impl_tac >- (rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE simp[])) >>
     disch_then (qx_choose_then `vi` strip_assume_tac) >>
     qpat_assum `!vi. raw_variant _ vi vs ==> _` (qspec_then `vi` mp_tac) >>
     impl_tac >- FIRST_ASSUM ACCEPT_TAC >> strip_tac >>
     qpat_x_assum `_ ==> ctx_sim D _ _ vi vs /\ _` mp_tac >>
     impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >> simp[]) >>
  drule_all o1_pipeline_memory_obligations_raw >> strip_tac >>
  drule_all o1_pipeline_codegen_obligations >> strip_tac >>
  qpat_x_assum `!g' Inv vs es. _`
    (qspecl_then [`g'`, `raw_reachable vs`, `vs`, `es`] mp_tac) >>
  fs[Abbr`eg`]
QED

Triviality compile_vyper_deploy_phases_asm_opt:
  compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) ==>
  ?rpolicy dunit dout prog prog' cplan.
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    asm_opt_finalizer rpolicy prog = SOME prog' /\
    deploy_bc = assemble prog'
Proof
  simp[compile_vyper_def, deploy_phases_def] >> strip_tac >>
  drule compile_vyper_with_success_phases >> strip_tac >>
  gvs[finalize_codegen_def, o1PipelineCorrectTheory.o1_pipeline_def,
      AllCaseEqs()] >>
  qpat_x_assum `codegen_assembly rpolicy deploy_out.po_unit = SOME _`
    (strip_assume_tac o MATCH_MP codegen_assembly_success_shape) >>
  goal_assum $ drule_at Any >> gvs[]
QED

(* The constructor's finalized creation frame reserves enough gas at each
   step to pay the largest permitted code deposit. *)
Theorem e2e_deploy_gas_sufficient_asm_opt:
  !policy tops deploy_bc runtime_bc am tx es.
    compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) /\
    ~program_reads_self_code tops /\
    supported_program tops /\ supported_program_deploy tops /\
    constructor_call_free tops /\
    deploy_typing_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    ~(?t. runtime_bc = 0xEFw :: t)
    ==>
    ?g. !g'.
      g <= g' /\
      (!gs. deploy_storage_ok tops am tx
              (MAP SND (call_trace (add_frame_gas g' es))) gs) /\
      (!obs. ~deploy_gas_source_exempt tops
         (load_contract NONE obs am tx [(NONE, tops)] []))
      ==>
      ?r es'.
        run_call (add_frame_gas g' es) = SOME (r, es') /\
        (r = INR (SOME OutOfGas) ==>
         max_code_size < LENGTH runtime_bc + imm_len tops)
Proof
  rpt strip_tac >>
  drule compile_vyper_deploy_phases_asm_opt >> strip_tac >>
  qpat_x_assum `deploy_bc = assemble prog'` SUBST_ALL_TAC >>
  `asm_opt_finalizer IN accepted_finalizers` by simp[accepted_finalizers_def] >>
  `deploy_source_ok tops am tx` by simp[deploy_source_ok_def] >>
  drule_all deploy_unit_shape_ok >> strip_tac >>
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
  drule_all lower_vyper_deploy_unit_sym_src_ok >> strip_tac >>
  drule_all o1_pipeline_label_flow_preserved >> strip_tac >>
  drule_all o1_pipeline_sym_unit_static_ok >> strip_tac >>
  drule_all lower_vyper_deploy_unit_call_free_entry >> strip_tac >>
  `!fn inst. MEM fn dout.po_unit.cu_context.ctx_functions /\
             MEM inst (fn_insts fn) ==> inst.inst_opcode <> RETURNDATACOPY` by
    (rpt gen_tac >> strip_tac >>
     qspecl_then [`rpolicy`, `dunit`, `dout`, `efn`, `RETURNDATACOPY`] mp_tac
       o1_pipeline_leaf_entry_opcode_absence >>
     impl_tac >- fs[] >> disch_then drule_all >> simp[]) >>
  drule_all codegen_assembly_no_returndatacopy >> strip_tac >>
  `lowering_context_ok dunit.cu_context` by metis_tac[deploy_unit_context_ok] >>
  qspecl_then [`tops`, `rpolicy`, `runtime_bc`, `dunit`, `am`, `tx`]
    mp_tac deploy_unit_fns_fuel_stable >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all run_context_uniform_fuel >>
  disch_then (qx_choose_then `fuel` assume_tac) >>
  qspecl_then [`imm_len tops`, `rpolicy`, `dunit`, `dout`, `cplan`, `fuel`]
    mp_tac run_venom_pipeline_run_bounded >>
  impl_tac >- simp[] >> disch_then (qx_choosel_then [`fuel'`, `M`] assume_tac) >>
  qspecl_then [`rpolicy`, `dout.po_unit`, `cplan`, `prog`, `prog'`, `fuel'`, `M`,
               `code_deposit_cost * max_code_size`] mp_tac
    codegen_gas_surplus_asm_opt >>
  impl_tac >- simp[] >> disch_then (qx_choose_then `g` assume_tac) >>
  qexists_tac `g` >> rpt strip_tac >>
  `!vs. mem_inv (\ctx fn inst s. inst_create_size_ok inst s)
          dout.po_unit.cu_context vs` by
    (drule_all o1_deploy_unit_create_size_ok >> simp[]) >>
  `?c0 rb0. es.contexts = [(c0, rb0)] /\ wf_state es` by
    fs[deploy_state_rel_def] >>
  qabbrev_tac `eg = add_frame_gas g' es` >>
  `deploy_state_rel tops (assemble prog') am tx eg` by
    (simp[Abbr`eg`] >> irule deploy_state_rel_add_frame_gas >> simp[]) >>
  qpat_x_assum `deploy_state_rel _ _ _ _ es` kall_tac >>
  `?ctxt rb. eg.contexts = [(ctxt, rb)] /\
             ctxt.msgParams.outputTo = Code tx.target /\ wf_state eg` by
    fs[deploy_state_rel_def] >>
  `shadow_root eg = add_frame_gas g' (shadow_root es)` by
    (simp[Abbr`eg`] >> irule shadow_root_add_frame_gas >> fs[]) >>
  `wf_state (shadow_root eg)` by simp[shadow_root_wf_state] >>
  `g' <= frame_gas_left (shadow_root eg)` by
    (qpat_x_assum `shadow_root eg = _` SUBST1_TAC >>
     irule wf_state_frame_gas_left >> simp[shadow_root_wf_state]) >>
  qabbrev_tac `vs = opt_deploy_entry_state prog prog' cplan tops eg` >>
  qabbrev_tac `txp = tx with code := vs.vs_code` >>
  `deploy_source_ok tops am txp` by
    (simp[Abbr`txp`, Abbr`vs`] >>
     drule_all deploy_source_ok_opt_code >> simp[]) >>
  `code_layout_valid vs` by
    (mp_tac (Q.INST [`es` |-> `eg`] deploy_raw_entry_code_layout) >>
     impl_tac >- fs[Abbr`txp`, Abbr`vs`] >>
     simp[code_layout_valid_def, Abbr`vs`]) >>
  `vs.vs_initial_fmp = n2w cplan.cp_initial_fmp /\
   vs.vs_code = assemble prog ++ vs.vs_data_section /\
   vs.vs_alloca_next = imm_len tops /\ vs.vs_fmp = vs.vs_initial_fmp /\
   vs.vs_outcomes = MAP SND (call_trace eg)` by
    simp[Abbr`vs`, opt_deploy_entry_state_def, opt_entry_state_def,
         entry_venom_state_def] >>
  `o1_run_state_ok vs` by
    (simp[Abbr`vs`, o1_run_state_ok_def, o1_initial_state_ok_def,
          opt_deploy_entry_state_def, opt_entry_state_def, entry_venom_state_def,
          venomStateTheory.init_venom_state_def] >>
     gvs[deploy_state_rel_def]) >>
  `txp.function_name = "__init__" /\ txp.target = tx.target` by
    fs[Abbr`txp`, deploy_state_rel_def] >>
  `!gs. deploy_storage_ok tops am txp vs.vs_outcomes gs` by
    simp[Abbr`txp`, deploy_storage_ok_code_update] >>
  `!obs. load_contract NONE obs am txp [(NONE,tops)] [] =
         load_contract NONE obs am tx [(NONE,tops)] []` by
    simp[Abbr`txp`, load_contract_def, load_contract_trace_code_update] >>
  `!obs. ~deploy_gas_source_exempt tops
          (load_contract NONE obs am txp [(NONE,tops)] [])` by fs[] >>
  qspecl_then [`asm_opt_finalizer`, `policy`, `tops`, `runtime_bc`, `rpolicy`,
               `dunit`, `dout`, `prog`, `prog'`, `cplan`, `am`, `tx`,
               `eg`, `vs.vs_initial_fmp`] mp_tac
    deploy_unit_execution_correct_raw_fmp >>
  impl_tac >- simp[] >>
  strip_tac >>
  qabbrev_tac `Du = <| d_stor := K (K UNIV); d_trans := K (K UNIV);
                       d_imm := K UNIV; d_ret := K UNIV |>` >>
  `dead_wf Du` by simp[Abbr`Du`, dead_wf_def] >>
  `!vi. raw_variant vs.vs_initial_fmp vi vs ==>
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
          (load_contract NONE obs am txp [(NONE,tops)] [])
          (run_context efuel dunit.cu_context vi)` by
    (gen_tac >> strip_tac >>
     `gas_variant vi vs` by metis_tac[raw_variant_gas_variant, o1_run_state_ok_def] >>
     `vi.vs_outcomes = vs.vs_outcomes` by metis_tac[gas_variant_outcomes] >>
     `code_layout_valid vi` by
       (irule gas_variant_code_layout_valid >> qexists_tac `vs` >> simp[]) >>
     `vi.vs_alloca_next = imm_len tops /\ vi.vs_initial_fmp = vi.vs_fmp` by
       fs[raw_variant_def, gas_variant_def,
          venomStateTheory.venom_state_component_equality] >>
     `?marks. deploy_unit_execution_correct_at marks tops runtime_bc am txp dunit vi`
       by
       (simp[deploy_unit_execution_correct_at_with] >>
        qpat_x_assum `!vs. raw_variant _ vs _ ==> _` (qspec_then `vi` mp_tac) >>
        impl_tac >- fs[Abbr`vs`] >> fs[Abbr`txp`, Abbr`vs`] >>
        metis_tac[]) >>
     qspecl_then [`marks`, `tops`, `runtime_bc`, `am`, `txp`, `dunit`, `vi`, `[]`]
       mp_tac deploy_unit_exit_safe_runs >>
     REWRITE_TAC [APPEND_NIL] >>
     qabbrev_tac `obs = gas_explicit marks vi.vs_gas_readings` >>
     `load_contract (SOME vi.vs_outcomes) obs am txp [(NONE,tops)] [] =
      load_contract NONE obs am txp [(NONE,tops)] []` by
       metis_tac[load_contract_call_free] >>
     `deploy_storage_ok tops am txp vi.vs_outcomes obs` by
       (qpat_assum `vi.vs_outcomes = vs.vs_outcomes`
          (fn th => PURE_REWRITE_TAC [th]) >>
        qpat_assum `!gs. deploy_storage_ok tops am txp _ gs`
          (qspec_then `obs` ACCEPT_TAC)) >>
     `~deploy_source_exempt tops
         (load_contract (SOME vi.vs_outcomes) obs am txp [(NONE,tops)] [])` by
       (qpat_assum `load_contract (SOME vi.vs_outcomes) obs am txp _ _ = _`
          (fn th => PURE_REWRITE_TAC [th]) >>
        qpat_assum `!obs. ~deploy_gas_source_exempt tops _`
          (qspec_then `obs` (ACCEPT_TAC o CONJUNCT1 o
            SIMP_RULE (srw_ss()) [deploy_gas_source_exempt_def]))) >>
     impl_tac >- (rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
     strip_tac >>
     rename1 `deploy_venom_result_rel _ _ _ _ _ (run_context vf _ vi)` >>
     qabbrev_tac `H = storage_trace_horizon
                      (deploy_storage_trace (SOME vi.vs_outcomes) obs am txp tops)` >>
     `w2n vi.vs_initial_fmp <= w2n vi.vs_fmp` by simp[] >>
     drule_all deploy_selected_memory >> strip_tac >>
     `dunit.cu_context.ctx_entry = SOME "__deploy"` by
       (drule lower_vyper_deploy_unit_entry >> simp[]) >>
     `mem_inv (\c f inst s. inst_dload_in_section inst s /\
                           s.vs_code = vi.vs_code /\
                           s.vs_data_section = vi.vs_data_section)
        dunit.cu_context vi` by
       (simp[mem_inv_raw_reachable] >> rpt strip_tac >>
        drule raw_reachable_code_data >> strip_tac >>
        simp[] >> irule lowered_unit_dload_in_section >>
        metis_tac[]) >>
     qpat_assum `load_contract (SOME vi.vs_outcomes) obs am txp _ _ = _`
       (fn th => qpat_x_assum `deploy_venom_result_rel H _ _ _ _ _`
          (assume_tac o REWRITE_RULE [th])) >>
     qexistsl_tac [`H`, `obs`, `vf`] >> rpt conj_tac >>
     FIRST_ASSUM ACCEPT_TAC) >>
  `venom_run_bounded fuel' M dout.po_unit.cu_context vs` by
    (qpat_x_assum `!D vs. _ ==> venom_run_bounded _ _ _ _`
       (qspecl_then [`Du`, `vs`] mp_tac) >>
     impl_tac >- (simp[] >> gen_tac >> strip_tac >>
       `raw_variant vs.vs_initial_fmp vs_in vs` by
         metis_tac[raw_variant_gas_variant, o1_run_state_ok_def] >>
       qpat_assum `!vi. raw_variant _ vi vs ==> _` drule >> strip_tac >>
       `terminates (run_context fuel dunit.cu_context vs_in)` by
         (qpat_x_assum `!s f. terminates _ ==> _` irule >>
          metis_tac[deploy_venom_result_rel_terminates]) >>
       simp[Abbr`Du`, taint_within_def]) >> simp[]) >>
  `LENGTH vs.vs_data_section < dimword (:256) DIV 2` by
    (irule entry_data_section_bound >> conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
     qexists_tac `assemble prog` >> simp[]) >>
  `!eom. max_live_eom dout.po_unit.cu_context = SOME eom ==>
         eom <= w2n vs.vs_initial_fmp` by
    metis_tac[generate_context_plan_eom_room] >>
  qspecl_then [`imm_len tops`, `rpolicy`, `dunit`, `dout`, `vs`,
               `vs.vs_initial_fmp`] mp_tac run_venom_pipeline_correct_all_dead >>
  impl_tac >- simp[] >> strip_tac >>
  qpat_assum `!vi. raw_variant _ vi vs ==> _` drule >> strip_tac >>
  qabbrev_tac `D = deploy_dead H tops runtime_bc am txp` >>
  `dead_wf D` by simp[Abbr`D`, deploy_dead_wf] >>
  `ctx_sim D dunit.cu_context dout.po_unit.cu_context vs_in vs /\
   o1_lowered_inv dout.po_unit.cu_context vs` by
    (qpat_x_assum `!D. _ ==> _` (qspec_then `D` mp_tac) >>
     impl_tac >- fs[Abbr`D`] >> simp[]) >>
  `code_end_offset_ok (raw_reachable vs) dout.po_unit.cu_context` by
    (qspecl_then [`Du`, `imm_len tops`, `rpolicy`, `dunit`, `dout`, `vs`,
                 `vs.vs_initial_fmp`] mp_tac o1_pipeline_code_end_offset_ok >>
     impl_tac >- (rpt conj_tac >> (FIRST_ASSUM ACCEPT_TAC ORELSE simp[])) >>
     disch_then (qx_choose_then `vcode` strip_assume_tac) >>
     qpat_assum `!vi. raw_variant _ vi vs ==> _` (qspec_then `vcode` mp_tac) >>
     impl_tac >- FIRST_ASSUM ACCEPT_TAC >> strip_tac >>
     qpat_x_assum `_ ==> ctx_sim Du _ _ _ _ /\ _` mp_tac >>
     impl_tac >- simp[Abbr`Du`, taint_within_def] >> simp[]) >>
  drule_all o1_pipeline_memory_obligations_raw >> strip_tac >>
  drule_all o1_pipeline_codegen_obligations >> strip_tac >>
  `terminates (run_context efuel dunit.cu_context vs_in)` by
    metis_tac[deploy_venom_result_rel_terminates] >>
  `?vfuel. dead_result_rel D (run_context efuel dunit.cu_context vs_in)
             (run_context vfuel dout.po_unit.cu_context vs)` by
    metis_tac[ctx_sim_def] >>
  `~deploy_source_exempt tops
      (load_contract NONE obs am txp [(NONE,tops)] [])` by
    fs[deploy_gas_source_exempt_def] >>
  qspecl_then [`H`, `tops`, `runtime_bc`, `am`, `txp`, `obs`,
               `load_contract NONE obs am txp [(NONE,tops)] []`,
               `run_context efuel dunit.cu_context vs_in`,
               `run_context vfuel dout.po_unit.cu_context vs`] mp_tac
    deploy_venom_result_rel_dead >>
  impl_tac >- fs[Abbr`D`] >> strip_tac >>
  drule_all opt_deploy_codegen_asm_entry_rel >>
  disch_then (qspecl_then [`prog`, `cplan`] assume_tac) >>
  drule_all opt_deploy_asm_frame_rel >>
  disch_then (qspecl_then [`prog`, `cplan`] assume_tac) >>
  qabbrev_tac `sh = shadow_root eg` >>
  `!t. ~frame_inst_at sh t ReturnDataCopy` by
    (gen_tac >>
     qspecl_then [`rpolicy`, `dout.po_unit`, `cplan`, `prog`, `prog'`, `fuel'`,
                  `M`, `raw_reachable vs`, `vs`, `sh`, `t`] mp_tac
       codegen_no_returndatacopy_asm_opt >>
     impl_tac >- fs[Abbr`vs`, Abbr`sh`] >> simp[]) >>
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
               `raw_reachable vs`, `vs`, `sh`] mp_tac codegen_correct_asm_opt >>
  impl_tac >- fs[Abbr`vs`, Abbr`sh`] >>
  disch_then (qx_choosel_then [`r`, `es'`]
     (fn th => map_every assume_tac (CONJUNCTS th))) >>
  qspecl_then [`H`, `eg`, `ctxt`, `rb`, `txp`, `tops`, `runtime_bc`,
               `load_contract NONE obs am txp [(NONE,tops)] []`,
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
   vyper_call_correct's finalizer premises. *)
Theorem vyper_call_gas_sufficient:
  !fin policy tops deploy_bc runtime_bc am tx es.
    fin IN accepted_finalizers /\
    (fin = asm_opt_finalizer ==> ~program_reads_self_code tops) /\
    compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es
    ==>
    ?g. !g'.
      g <= g' ==>
      ?r es'.
        run_call (add_frame_gas g' es) = SOME (r, es') /\
        ((case calldata_dispatch tops tx.calldata of
            NONE => T
          | SOME (f, vals) =>
              (!gs. call_storage_ok am
                 (tx with <| function_name := f; args := vals |>)
                 (MAP SND (call_trace (add_frame_gas g' es))) gs) /\
              (!obs. ~gas_source_exempt tops
                 (tx with <| function_name := f; args := vals |>)
                 (call_external (SOME (MAP SND (call_trace (add_frame_gas g' es))))
                    obs am (tx with <| function_name := f; args := vals |>)))) /\
         LENGTH (call_trace (add_frame_gas g' es)) < 2 ** 64 /\
         frame_raises (add_frame_gas g' es) OutOfGas ==>
         ?s. frame_inst_at (add_frame_gas g' es) s ReturnDataCopy)
Proof
  rpt gen_tac >> strip_tac >>
  `?g. !g'.
     g <= g' /\
     (!gs. call_storage_ok am tx
        (MAP SND (call_trace (add_frame_gas g' es))) gs) /\
     (!obs. ~gas_source_exempt tops tx
        (call_external (SOME (MAP SND (call_trace (add_frame_gas g' es))))
           obs am tx)) /\
     LENGTH (call_trace (add_frame_gas g' es)) < 2 ** 64
     ==>
     ?r es'.
       run_call (add_frame_gas g' es) = SOME (r, es') /\
       (frame_raises (add_frame_gas g' es) OutOfGas ==>
        ?s. frame_inst_at (add_frame_gas g' es) s ReturnDataCopy)` by
    (`fin = K SOME \/ fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
     pop_assum strip_assume_tac >> pop_assum SUBST_ALL_TAC
     >- (drule_all vyper_call_gas_sufficient_identity >> simp[])
     >> `~program_reads_self_code tops` by fs[] >>
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
    (fin = asm_opt_finalizer ==> ~program_reads_self_code tops) /\
    compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\ supported_program_deploy tops /\
    constructor_call_free tops /\
    deploy_typing_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    ~(?t. runtime_bc = 0xEFw :: t)
    ==>
    ?g. !g'.
      g <= g' ==>
      ?r es'.
        run_call (add_frame_gas g' es) = SOME (r, es') /\
        ((!gs. deploy_storage_ok tops am tx
                 (MAP SND (call_trace (add_frame_gas g' es))) gs) /\
         (!obs. ~deploy_gas_source_exempt tops
            (load_contract NONE obs am tx [(NONE, tops)] [])) /\
         r = INR (SOME OutOfGas) ==>
         max_code_size < LENGTH runtime_bc + imm_len tops \/
         ?s. frame_inst_at (add_frame_gas g' es) s ReturnDataCopy)
Proof
  rpt gen_tac >> strip_tac >>
  `?g. !g'.
     g <= g' /\
     (!gs. deploy_storage_ok tops am tx
             (MAP SND (call_trace (add_frame_gas g' es))) gs) /\
     (!obs. ~deploy_gas_source_exempt tops
        (load_contract NONE obs am tx [(NONE, tops)] []))
     ==>
     ?r es'.
       run_call (add_frame_gas g' es) = SOME (r, es') /\
       (r = INR (SOME OutOfGas) ==>
        max_code_size < LENGTH runtime_bc + imm_len tops)` by
    (`fin = K SOME \/ fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
     pop_assum strip_assume_tac >> pop_assum SUBST_ALL_TAC
     >- (drule_all e2e_deploy_gas_sufficient_identity >> simp[])
     >> `~program_reads_self_code tops` by fs[] >>
     drule_all e2e_deploy_gas_sufficient_asm_opt >> simp[]) >>
  (* run_call is total, so the run exists whatever the conditions *)
  qexists_tac `g` >> rpt strip_tac >>
  qspec_then `add_frame_gas g' es` strip_assume_tac run_call_total >>
  qexistsl_tac [`r`, `es'`] >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!g'. g <= g' /\ _ ==> _` (qspec_then `g'` mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >> gvs[]
QED
