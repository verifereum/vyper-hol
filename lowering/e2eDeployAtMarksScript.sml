(*
 * e2e_deploy_correct_from_gas_link: the deploy theorem from a link between the
 * frame's gas readings and selected raw entry states; the deployment twin of
 * e2eCallAtMarks.
 *
 * For every guarded filling of the frame's gas readings, the caller supplies
 * a raw deployment unit's entry state vs (a gas variant of the compiled
 * run's entry state) whose marked readings the filling extends, the S4
 * simulation facts on vs for every well-formed dead mask, and the
 * selected-run certificate at its marks.  At each such filling, the exit
 * arm gives the entry's memory- and pointer-safe runs at the run's own
 * storage horizon H (deployUnitExitSafe); the ctorDeployMemoryFrontier
 * bridges turn them into the S4 memory facts, which give ctx_sim at
 * deploy_dead H; codegen and the creation frame finish.
 *
 * TOP-LEVEL:
 *   e2e_deploy_correct_from_gas_link -- the deploy result relation at every
 *     filling, from the facts above
 *)
Theory e2eDeployAtMarks
Ancestors
  codegenLabelDisciplined fnPlanPlaceRevertPostamble finite_map
  ownSymSrcUnit gasFocusOptLabelFlow[qualified,ignore_grammar] codegenSymOwnRel ctorDeployRawEntryFacts
  e2eDeployDefs e2eDefs ctorDeployDefs deployUnitExecution deployUnitExitSafe
  totalBalanceOverflowCore
  ctorDeployMemoryFrontier ctorDeployImmBudget ctorDeployInitcode
  ctorDeployEntry ctorDeployShape ctorDeployDefsReach ctorDeployDead
  ctorDeployLoweringSource
  ctorDeployFrame compileVyper codegen e2eProducers e2eComposition e2eEntry
  o1PipelineCorrect o1PipelineCompose o1PassContract codegenCorrectness passSimulationDefs
  lowerDloadDefs gasSummary vyperStorageFootprint
  deploySymSrcGeneratorFrame[qualified] runtimeSymSrcPackageTransport[qualified] codegenAsmOpt codegenSymRel codegenEntryRel asmFrameRel
  compilePhasesProps asmOptimizer contextCodegenRel contextRawReachable
  contextPlanLayoutProps asmDataSuffixProps frameRel codegenRel
  loweringStateRelDefs vyperArith callTrace memSafeRun frameObsStep
  asmOptNonemptyFinalizer o1SymStaticData o1SymStaticPipeline
  venomPipelineDriverProps venomCompilerWf venomWf o1LabelFlowCompose
  stepWriteFootprint deployUnitProducers ctorDeployInitcodeAsm
  immutableCodeLayout codegenEncodingWf unitMemInv deployFrameReplay
  vyperInterpreter

Theorem compile_vyper_runtime_nonempty_asm_opt[local]:
  compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) ==>
  runtime_bc <> []
Proof
  strip_tac >> drule compile_vyper_runtime_phases_asm_opt >> strip_tac >>
  gvs[] >> irule codegen_assembly_finalizer_nonempty >>
  goal_assum (drule_at Any) >> metis_tac[]
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

Theorem opt_deploy_codegen_asm_entry_rel:
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

Theorem opt_deploy_asm_frame_rel:
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

Theorem opt_deploy_asm_rels_own:
  !tops prog prog' am tx es cplan.
    deploy_state_rel tops (assemble prog') am tx es /\
    assemble prog' <> [] ==>
    (opt_deploy_entry_state_own prog prog' cplan tops es).vs_code =
      assemble prog' ++ (opt_deploy_entry_state_own prog prog' cplan tops es).vs_data_section /\
    codegen_asm_entry_rel_reloc (lo_reloc prog prog') cplan prog
      (opt_deploy_entry_state_own prog prog' cplan tops es)
      (entry_asm_state (opt_deploy_entry_state_own prog prog' cplan tops es)
        (shadow_root es)) /\
    asm_frame_rel prog'
      (opt_deploy_entry_state_own prog prog' cplan tops es).vs_data_section
      (shadow_root es)
      (entry_asm_state (opt_deploy_entry_state_own prog prog' cplan tops es)
        (shadow_root es))
      (shadow_root es)
Proof
  rpt strip_tac >>
  `wf_state (shadow_root es)` by fs[deploy_state_rel_def, shadow_root_wf_state] >>
  fs[deploy_state_rel_def] >>
  drule shadow_root_single >> strip_tac >>
  `es.txParams.blockNumber < dimword (:256)` by
    (fs[e2eDefsTheory.tx_block_fields_rel_def, tx_env_ok_def] >>
     irule lt_dimword_256 >> qexists_tac `255` >> simp[]) >>
  simp[codegen_asm_entry_rel_reloc_def, asm_frame_rel_def, asm_evm_rel_def,
       entry_asm_state_def, shared_state_rel_def, venom_asm_terminal_rel_def,
       opt_deploy_entry_state_own_def, opt_entry_state_own_def,
       data_suffix_assemble, asm_pc_to_offset_zero, entry_venom_state_frame_fields,
       finite_mapTheory.FLOOKUP_o_f] >>
  gvs[entry_venom_state_def, venomStateTheory.init_venom_state_def,
      contextCodegenRelTheory.context_memory_rel_def, wordsTheory.w2n_n2w,
      listTheory.DROP_APPEND, CONJ_ASSOC] >>
  gen_tac >> Cases_on `FLOOKUP (lo_reloc prog prog') l` >> simp[]
QED

Theorem deploy_venom_result_rel_code_update[local]:
  deploy_venom_result_rel H tops runtime_bc (tx with code := c) src vr =
  deploy_venom_result_rel H tops runtime_bc tx src vr
Proof
  Cases_on `src`
  >- (rename1 `INL p` >> PairCases_on `p` >> Cases_on `vr` >>
      simp[deploy_venom_result_rel_def,
           initial_evaluation_context_def]) >>
  rename1 `INR exc` >> Cases_on `exc` >> Cases_on `vr` >>
  simp[deploy_venom_result_rel_def]
QED

Theorem deploy_result_rel_code_update[local]:
  deploy_result_rel H tops runtime_bc (tx with code := c) es r es' src =
  deploy_result_rel H tops runtime_bc tx es r es' src
Proof
  Cases_on `src`
  >- (rename1 `INL p` >> PairCases_on `p` >>
      simp[deploy_result_rel_def, e2eDefsTheory.effects_agree_def,
           initial_evaluation_context_def]) >>
  rename1 `INR exc` >> Cases_on `exc` >> simp[deploy_result_rel_def]
QED

(* The bridges at the deployment entry: the S4 memory facts of vs from its
   memory-safe and pointer-safe runs from "__deploy". *)
Theorem deploy_selected_memory_from_checked:
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  vs.vs_alloca_next = imm_len tops /\
  ctx_has_dalloca dunit.cu_context /\
  (ctx_has_dalloca dunit.cu_context ==>
     imm_len tops + unit_alloca_budget dunit.cu_context +
       32 * ctx_dload_count dunit.cu_context <= w2n vs.vs_initial_fmp) /\
  code_layout_valid vs /\
  lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME func /\
  fn_entry_label func = SOME "__deploy" /\
  (!fuel. mem_safe_blocks fuel dunit.cu_context func
     (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                 vs_inst_idx := 0 |>)) /\
  (!fuel. ptr_safe_blocks D (imm_len tops) fuel dunit.cu_context func [] FEMPTY
     entry_taint
     (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                 vs_inst_idx := 0 |>)) ==>
  raw_unit_memory_ok dunit.cu_context vs /\
  ptr_discipline (imm_len tops) dunit.cu_context vs /\
  taint_within D dunit.cu_context vs /\
  mem_inv dload_offset_ok dunit.cu_context vs /\
  mem_inv dload_headroom_ok dunit.cu_context vs
Proof
  strip_tac >>
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit` by
    fs[deploy_phases_def] >>
  drule lower_vyper_deploy_unit_context_ok >> strip_tac >>
  `dunit.cu_context.ctx_entry = SOME "__deploy"` by
    (drule lower_vyper_deploy_unit_entry >> simp[]) >>
  drule deploy_imm_alloca_budget_ok >> strip_tac >>
  `imm_len tops + unit_alloca_budget dunit.cu_context < dimword (:256)` by
    decide_tac >>
  `ptr_discipline (imm_len tops) dunit.cu_context vs /\
   taint_within D dunit.cu_context vs` by
    (match_mp_tac (Q.SPECL [`D`, `imm_len tops`, `dunit.cu_context`,
        `"__deploy"`, `func`, `"__deploy"`, `vs`] lowered_unit_ptr_taint) >>
     simp[]) >>
  `!f inst s. raw_reachable vs dunit.cu_context f inst s ==>
      dalloca_no_wrap inst s /\ w2n s.vs_initial_fmp <= w2n s.vs_fmp` by
    (match_mp_tac (Q.SPECL [`imm_len tops`, `dunit.cu_context`,
        `"__deploy"`, `func`, `"__deploy"`, `vs`] lowered_unit_checked_dalloca_facts) >>
     simp[]) >>
  simp[] >> rpt conj_tac
  >- (qspecl_then [`imm_len tops`, `dunit.cu_context`, `"__deploy"`, `func`,
                   `"__deploy"`, `vs`] mp_tac lowered_unit_raw_memory_ok_from_no_wrap >>
      impl_tac >- (gvs[] >> first_assum ACCEPT_TAC) >> simp[])
  >- (qspecl_then [`dunit.cu_context`, `"__deploy"`, `func`, `"__deploy"`,
                   `vs`] mp_tac lowered_unit_dload_offset_ok >>
      impl_tac >- (gvs[] >> first_assum ACCEPT_TAC) >> simp[]) >>
  qspecl_then [`imm_len tops`, `dunit.cu_context`, `"__deploy"`, `func`, `vs`]
    mp_tac lowered_unit_dload_headroom_ok_from >>
  impl_tac >- (gvs[] >> first_assum ACCEPT_TAC) >> simp[]
QED

Theorem deploy_selected_memory:
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  deploy_source_ok tops am tx /\
  ~ctx_has_dalloca dunit.cu_context /\
  vs.vs_alloca_next = imm_len tops /\
  w2n vs.vs_initial_fmp <= w2n vs.vs_fmp /\
  code_layout_valid vs /\
  lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME func /\
  fn_entry_label func = SOME "__deploy" /\
  (!fuel. mem_safe_blocks fuel dunit.cu_context func
     (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                 vs_inst_idx := 0 |>)) /\
  (!fuel. ptr_safe_blocks D (imm_len tops) fuel dunit.cu_context func [] FEMPTY
     entry_taint
     (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                 vs_inst_idx := 0 |>)) ==>
  raw_unit_memory_ok dunit.cu_context vs /\
  ptr_discipline (imm_len tops) dunit.cu_context vs /\
  taint_within D dunit.cu_context vs /\
  mem_inv dload_offset_ok dunit.cu_context vs /\
  mem_inv dload_headroom_ok dunit.cu_context vs
Proof
  strip_tac >>
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit` by
    fs[deploy_phases_def] >>
  drule lower_vyper_deploy_unit_context_ok >> strip_tac >>
  drule lower_vyper_deploy_unit_entry >> strip_tac >>
  drule_all deploy_unit_o1_shape_ok >> strip_tac >>
  drule deploy_imm_alloca_budget_ok >> strip_tac >>
  `EVERY pre_fmp_ops dunit.cu_context.ctx_functions` by
    (rw[listTheory.EVERY_MEM] >> irule source_pre_fmp_ops >> metis_tac[]) >>
  `imm_len tops + unit_alloca_budget dunit.cu_context < dimword (:256)` by
    decide_tac >>
  rpt conj_tac
  >- (qspecl_then [`imm_len tops`, `dunit.cu_context`, `"__deploy"`, `func`,
                   `"__deploy"`, `vs`] mp_tac lowered_unit_raw_memory_ok_from >>
      impl_tac >- fs[] >> simp[])
  >- (qspecl_then [`D`, `imm_len tops`, `dunit.cu_context`, `"__deploy"`,
                   `func`, `"__deploy"`, `vs`] mp_tac lowered_unit_ptr_taint >>
      impl_tac >- fs[] >> simp[])
  >- (qspecl_then [`D`, `imm_len tops`, `dunit.cu_context`, `"__deploy"`,
                   `func`, `"__deploy"`, `vs`] mp_tac lowered_unit_ptr_taint >>
      impl_tac >- fs[] >> simp[])
  >- (qspecl_then [`dunit.cu_context`, `"__deploy"`, `func`, `"__deploy"`,
                   `vs`] mp_tac lowered_unit_dload_offset_ok >>
      impl_tac >- fs[] >> simp[]) >>
  qspecl_then [`imm_len tops`, `dunit.cu_context`, `"__deploy"`, `func`, `vs`]
    mp_tac lowered_unit_dload_headroom_ok_from >>
  impl_tac >- fs[] >> simp[]
QED

(* The entry state's own facts: its callee outcomes, its code layout, and the
   compiled entry state's initial context relation. *)
Theorem deploy_entry_facts[local]:
  fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
  deploy_phases policy tops (assemble prog, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  deploy_state_rel tops (assemble prog') am tx es /\
  vs_out = opt_deploy_entry_state_own prog prog' cplan tops es /\
  txp = tx with code := vs_out.vs_code /\
  deploy_source_ok tops am txp /\
  raw_variant fmp vs vs_out ==>
  vs.vs_outcomes = MAP SND (call_trace es) /\ code_layout_valid vs /\
  unit_shape_ok dout.po_unit /\
  vs.vs_alloca_next = imm_len tops /\
  vs.vs_initial_fmp = fmp /\ vs.vs_fmp = fmp
Proof
  strip_tac >>
  drule_all deploy_unit_o1_shape_ok >> strip_tac >>
  drule_all deploy_unit_defs_reach_uses >> strip_tac >>
  `o1PipelineCorrect$o1_pipeline rpolicy dunit = SOME dout /\
   codegen_assembly rpolicy dout.po_unit = SOME prog` by
    fs[deploy_phases_def] >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  `txp = tx` by
    (qpat_assum `vs_out = _` (fn th => asm_rewrite_tac [th]) >>
     drule_all deploy_own_txp_identity >> simp[]) >>
  `code_layout_valid vs_out` by
    (Q.SUBGOAL_THEN
       `code_layout_valid
          (vs_out with <|vs_gas_readings := vs_out.vs_gas_readings;
                         vs_fmp := fmp; vs_initial_fmp := fmp|>)` mp_tac
     >- (gvs[] >> irule deploy_raw_entry_code_layout >> metis_tac[]) >>
     simp[code_layout_valid_def]) >>
  `code_layout_valid vs` by
    (MATCH_MP_TAC (Q.INST
       [`si` |-> `vs`, `so` |-> `vs_out with <|vs_fmp := fmp; vs_initial_fmp := fmp|>`]
       gas_variant_code_layout_valid) >>
     conj_tac >- fs[raw_variant_def] >>
     qpat_x_assum `code_layout_valid vs_out` mp_tac >>
     simp[code_layout_valid_def]) >>
  qpat_x_assum `raw_variant _ _ _` mp_tac >>
  simp[raw_variant_def, gas_variant_def] >>
  disch_then (mp_tac o Q.AP_TERM
    `\s:venom_state. (s.vs_outcomes, s.vs_alloca_next,
       s.vs_initial_fmp, s.vs_fmp)`) >>
  simp[opt_deploy_entry_state_own_def, opt_entry_state_own_def,
       entry_venom_state_frame_fields, entry_venom_state_def] >>
  metis_tac[]
QED

(* At one tail of gas readings past the marked ones, where the constructor
   run's storage guard holds. *)
Theorem deploy_correct_at_tail[local]:
  fin IN accepted_finalizers /\
  fin rpolicy prog = SOME prog' /\
  compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
  deploy_phases policy tops (assemble prog, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  deploy_state_rel tops (assemble prog') am tx es /\
  LENGTH (call_trace es) < 2 ** 64 /\
  vs_out = opt_deploy_entry_state_own prog prog' cplan tops es /\
  txp = tx with code := vs_out.vs_code /\
  deploy_source_ok tops am txp /\
  ~(?t. runtime_bc = 0xEFw :: t) /\
  w2n vs_out.vs_initial_fmp <= w2n fmp /\
  w2n fmp < 2 ** 254 /\
  imm_len tops + unit_alloca_budget dunit.cu_context +
    32 * ctx_dload_count dunit.cu_context <= w2n fmp /\
  raw_variant fmp vs vs_out /\
  (~deploy_source_exempt tops
     (load_contract (SOME vs.vs_outcomes)
       (gas_explicit marks vs.vs_gas_readings ++ tail)
       am txp [(NONE, tops)] []) ==>
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
  deploy_unit_execution_correct_at marks tops runtime_bc am txp dunit vs /\
  run_call es = SOME (r, es') /\
  deploy_storage_ok tops am txp vs.vs_outcomes
    (gas_explicit marks vs.vs_gas_readings ++ tail) ==>
  creation_resource_starved es r es' \/
  deploy_result_rel
    (storage_trace_horizon
       (deploy_storage_trace (SOME vs.vs_outcomes)
          (gas_explicit marks vs.vs_gas_readings ++ tail) am txp tops))
    tops runtime_bc txp es r es'
    (load_contract (SOME vs.vs_outcomes)
       (gas_explicit marks vs.vs_gas_readings ++ tail) am txp [(NONE, tops)] [])
Proof
  strip_tac >>
  `runtime_bc <> []` by
    (Cases_on `fin = K SOME`
     >- metis_tac[compile_vyper_runtime_nonempty] >>
     `fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
     metis_tac[compile_vyper_runtime_nonempty_asm_opt]) >>
  drule_all deploy_entry_facts >> strip_tac >>
  `txp = tx` by metis_tac[deploy_own_txp_identity] >>
  `~deploy_source_exempt tops
       (load_contract (SOME vs.vs_outcomes)
          (gas_explicit marks vs.vs_gas_readings ++ tail) am txp
          [(NONE, tops)] [])` by (
    qpat_assum `deploy_unit_execution_correct_at _ _ _ _ _ _ _`
      (strip_assume_tac o REWRITE_RULE [deploy_unit_execution_correct_at_def])
    >- (qpat_assum `!tail. ~deploy_storage_ok _ _ _ _ _`
          (qspec_then `tail` mp_tac) >> gvs[]) >>
    qpat_assum `!tail. load_contract_trace _ _ _ _ _ _ = _`
      (qspec_then `tail` assume_tac) >>
    `source_result_ok src` by
      metis_tac[deploy_state_rel_no_recipient_overflow_core] >>
    `~deploy_source_exempt tops src` by
      (Cases_on `src`
       >- gvs[deploy_source_exempt_def]
       >- (Cases_on `y` >>
           gvs[deploy_source_exempt_def, unspecified_behaviour_exempt_def,
               vyperBalanceOverflowTheory.source_result_ok_def] >>
           Cases_on `e` >>
           gvs[deploy_source_exempt_def, unspecified_behaviour_exempt_def,
               vyperBalanceOverflowTheory.source_result_ok_def])) >>
    simp[load_contract_def] >> metis_tac[]
  ) >>
  `txp.function_name = "__init__"` by gvs[deploy_state_rel_def] >>
  qpat_x_assum `~deploy_source_exempt _ _ ==> _` drule >> strip_tac >>
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit` by
    fs[deploy_phases_def] >>
  drule lower_vyper_deploy_unit_context_ok >> strip_tac >>
  drule_all deploy_unit_o1_shape_ok >> strip_tac >>
  qspecl_then [`marks`, `tops`, `runtime_bc`, `am`, `txp`, `dunit`, `vs`, `tail`]
    mp_tac deploy_unit_exit_safe_runs >>
  impl_tac >- gvs[] >> strip_tac >>
  qabbrev_tac `H = storage_trace_horizon
    (deploy_storage_trace (SOME vs.vs_outcomes)
       (gas_explicit marks vs.vs_gas_readings ++ tail) am txp tops)` >>
  `w2n vs.vs_initial_fmp <= w2n vs.vs_fmp` by simp[] >>
  `raw_unit_memory_ok dunit.cu_context vs /\
   ptr_discipline (imm_len tops) dunit.cu_context vs /\
   taint_within (deploy_dead H tops runtime_bc am txp) dunit.cu_context vs /\
   mem_inv dload_offset_ok dunit.cu_context vs /\
   mem_inv dload_headroom_ok dunit.cu_context vs` by
    (Cases_on `ctx_has_dalloca dunit.cu_context`
     >- (irule deploy_selected_memory_from_checked >>
         rpt conj_tac >>
         TRY (first_assum ACCEPT_TAC) >>
         TRY (qexistsl_tac [`cplan`, `assemble prog`, `dout`, `policy`,
                             `prog`, `rpolicy`, `runtime_bc`] >> simp[]) >>
         gvs[]) >>
     metis_tac[deploy_selected_memory]) >>
  `ctx_sim (deploy_dead H tops runtime_bc am txp) dunit.cu_context
     dout.po_unit.cu_context vs vs_out /\
   (fin = asm_opt_finalizer ==>
      code_end_offset_ok (raw_reachable vs_out) dout.po_unit.cu_context) /\
   o1_lowered_inv dout.po_unit.cu_context vs_out` by
    (qpat_assum `!D. _ ==> _`
       (qspec_then `deploy_dead H tops runtime_bc am txp` mp_tac) >>
     impl_tac >- gvs[deploy_dead_wf] >> disch_then ACCEPT_TAC) >>
  `terminates (run_context fuel dunit.cu_context vs)` by
    metis_tac[deploy_venom_result_rel_terminates] >>
  `?fuel'. dead_result_rel (deploy_dead H tops runtime_bc am txp)
             (run_context fuel dunit.cu_context vs)
             (run_context fuel' dout.po_unit.cu_context vs_out)` by
    metis_tac[ctx_sim_def] >>
  qspecl_then [`H`, `tops`, `runtime_bc`, `am`, `txp`, `SOME vs.vs_outcomes`,
               `gas_explicit marks vs.vs_gas_readings ++ tail`,
               `load_contract (SOME vs.vs_outcomes)
                  (gas_explicit marks vs.vs_gas_readings ++ tail) am txp
                  [(NONE, tops)] []`,
               `run_context fuel dunit.cu_context vs`,
               `run_context fuel' dout.po_unit.cu_context vs_out`] mp_tac
    deploy_venom_result_rel_dead >>
  impl_tac >- gvs[deploy_state_rel_def] >> strip_tac >>
  `vs_out.vs_initial_fmp = n2w cplan.cp_initial_fmp` by
    fs[opt_deploy_entry_state_own_def, opt_entry_state_own_def, entry_venom_state_def] >>
  `o1PipelineCorrect$o1_pipeline rpolicy dunit = SOME dout /\
   codegen_assembly rpolicy dout.po_unit = SOME prog /\
   generate_context_plan dout.po_unit.cu_context = SOME cplan` by
    fs[deploy_phases_def] >>
  drule_all o1_pipeline_memory_obligations_raw >> strip_tac >>
  drule_all o1_pipeline_codegen_obligations >> strip_tac >>
  `?rr ee. run_call (shadow_root es) = SOME (rr, ee) /\
    (frame_resource_starved (shadow_root es) rr ee \/
     venom_frame_rel (shadow_root es) rr ee
       (run_context fuel' dout.po_unit.cu_context vs_out))` by
    (Cases_on `fin = K SOME`
     >- (`prog' = prog` by fs[] >>
         `vs_out = deploy_entry_state prog cplan tops es /\ txp = tx` by
           metis_tac[opt_deploy_entry_state_own_identity, deploy_own_txp_identity] >>
         qpat_x_assum `prog' = prog` SUBST_ALL_TAC >>
         qpat_x_assum `txp = tx` SUBST_ALL_TAC >>
         drule_all deploy_initcode_half_bounded >> strip_tac >>
         drule_all deploy_entry_state_ok >> strip_tac >>
         qspecl_then [`fuel'`, `rpolicy`, `dout.po_unit`, `cplan`, `prog`,
                      `raw_reachable vs_out`, `vs_out`, `shadow_root es`]
           mp_tac codegen_correct >>
         impl_tac >- gvs[] >> disch_then ACCEPT_TAC) >>
     `fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
     `supported_program tops /\ supported_program_deploy tops` by fs[deploy_source_ok_def] >>
     drule_all lower_vyper_deploy_unit_sym_src_ok_own >> strip_tac >>
     drule_all deploy_unit_defs_reach_uses >> strip_tac >>
     drule_all gasFocusOptLabelFlowTheory.focus_opt_label_flow_own >> strip_tac >>
     drule_all o1_pipeline_sym_unit_static_ok >> strip_tac >>
     `assemble prog' <> []` by
       (irule codegen_assembly_finalizer_nonempty >> metis_tac[]) >>
     qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`]
       mp_tac opt_deploy_asm_rels_own >>
     impl_tac >- simp[] >> disch_then strip_assume_tac >>
     qspecl_then [`fuel'`, `rpolicy`, `dout.po_unit`, `cplan`, `prog`, `prog'`,
                  `raw_reachable vs_out`, `vs_out`, `shadow_root es`]
       mp_tac codegen_correct_asm_opt_own >>
     impl_tac >- gvs[] >>
     disch_then ACCEPT_TAC) >>
  `deploy_venom_result_rel H tops runtime_bc tx
     (load_contract (SOME vs.vs_outcomes)
       (gas_explicit marks vs.vs_gas_readings ++ tail) am txp [(NONE, tops)] [])
     (run_context fuel' dout.po_unit.cu_context vs_out)` by
    metis_tac[deploy_venom_result_rel_code_update] >>
  qspecl_then [`H`, `tops`, `runtime_bc`, `assemble prog'`, `am`, `tx`, `es`,
               `load_contract (SOME vs.vs_outcomes)
                 (gas_explicit marks vs.vs_gas_readings ++ tail)
                 am txp [(NONE, tops)] []`,
               `run_context fuel' dout.po_unit.cu_context vs_out`]
    mp_tac deploy_venom_frame >>
  impl_tac >- metis_tac[] >> strip_tac >>
  gvs[deploy_result_rel_code_update]
QED

(* TOP-LEVEL.  Where the frame is not starved, every filling of its gas
   readings that meets the constructor run's storage guard extends the marked
   readings of some raw entry state vs carrying the S4 facts and the
   selected-run certificate at its marks; then the deploy result relation
   holds at every filling. *)
Theorem e2e_deploy_correct_from_gas_link:
  !fin policy tops deploy_bc runtime_bc rpolicy dunit dout prog prog' cplan
   am tx txp es vs_out fmp r es'.
    fin IN accepted_finalizers /\
    fin rpolicy prog = SOME prog' /\
    compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_state_rel tops (assemble prog') am tx es /\
    LENGTH (call_trace es) < 2 ** 64 /\
    vs_out = opt_deploy_entry_state_own prog prog' cplan tops es /\
    txp = tx with code := vs_out.vs_code /\
    deploy_source_ok tops am txp /\
    ~(?t. runtime_bc = 0xEFw :: t) /\
    w2n vs_out.vs_initial_fmp <= w2n fmp /\
    w2n fmp < 2 ** 254 /\
    imm_len tops + unit_alloca_budget dunit.cu_context +
      32 * ctx_dload_count dunit.cu_context <= w2n fmp /\
    run_call es = SOME (r, es') /\
    (creation_resource_starved es r es' \/
     gas_readings_rel (gas_readings es)
       (\gs. deploy_storage_ok tops am txp (MAP SND (call_trace es)) gs ==>
             ?vs marks tail.
               gs = gas_explicit marks vs.vs_gas_readings ++ tail /\
               raw_variant fmp vs vs_out /\
               (~deploy_source_exempt tops
                  (load_contract (SOME vs.vs_outcomes)
                    (gas_explicit marks vs.vs_gas_readings ++ tail)
                    am txp [(NONE, tops)] []) ==>
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
               deploy_unit_execution_correct_at marks tops runtime_bc am txp dunit vs))
    ==>
    creation_resource_starved es r es' \/
    deploy_call_result_rel tops runtime_bc am txp es r es'
Proof
  rpt strip_tac >>
  Cases_on `creation_resource_starved es r es'` >> fs[] >>
  simp[deploy_call_result_rel_def] >>
  drule gas_readings_rel_mono >> disch_then irule >>
  rpt gen_tac >> BETA_TAC >> rpt strip_tac >>
  qpat_x_assum `deploy_storage_ok _ _ _ _ gs ==> _` mp_tac >>
  impl_tac >- gvs[] >> strip_tac >>
  qpat_x_assum `gs = gas_explicit _ _ ++ _` SUBST_ALL_TAC >>
  drule_all deploy_entry_facts >> strip_tac >>
  qpat_x_assum `vs.vs_outcomes = _` (SUBST_ALL_TAC o SYM) >>
  `~(?t. runtime_bc = 0xEFw :: t)` by fs[] >>
  mp_tac deploy_correct_at_tail >>
  impl_tac >- (gvs[] >> metis_tac[]) >>
  strip_tac >> gvs[]
QED
