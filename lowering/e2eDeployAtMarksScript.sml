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
  e2eDeployDefs e2eDefs ctorDeployDefs deployUnitExecution deployUnitExitSafe
  ctorDeployMemoryFrontier ctorDeployImmBudget ctorDeployInitcode
  ctorDeployEntry ctorDeployShape ctorDeployDefsReach ctorDeployDead
  ctorDeployLoweringSource
  ctorDeployFrame compileVyper codegen e2eProducers e2eComposition e2eEntry
  o1PipelineCorrect o1PipelineCompose o1PassContract codegenCorrectness passSimulationDefs
  lowerDloadDefs gasSummary vyperStorageFootprint
  deploySymSrcUnit codegenAsmOpt codegenSymRel codegenEntryRel asmFrameRel
  compilePhasesProps asmOptimizer contextCodegenRel contextRawReachable
  contextPlanLayoutProps asmDataSuffixProps frameRel codegenRel
  loweringStateRelDefs vyperArith callTrace memSafeRun frameObsStep
  asmOptNonemptyFinalizer o1SymStaticData o1SymStaticPipeline
  venomPipelineDriverProps venomCompilerWf venomWf o1LabelFlowCompose
  stepWriteFootprint deployUnitProducers ctorDeployInitcodeAsm
  immutableCodeLayout codegenEncodingWf unitMemInv deployFrameReplay
  vyperInterpreter

Theorem compile_vyper_runtime_phases_asm_opt[local]:
  compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) ==>
  ?rpolicy unit out prog prog' cplan.
    resolve_o1_policy policy = SOME rpolicy /\
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    out.po_final_assembly = rpolicy.rpol_final_assembly /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    generate_context_plan out.po_unit.cu_context = SOME cplan /\
    assembly_target_safe rpolicy.rpol_target prog /\
    prog = execute_plan cplan.cp_initial_fmp (context_plan_ops cplan) ++
           data_segment_asm out.po_unit.cu_data_segment ++
           [AsmDataHeader "code_end"] /\
    asm_opt_finalizer rpolicy prog = SOME prog' /\
    assembly_target_safe rpolicy.rpol_target prog' /\
    runtime_bc = assemble prog'
Proof
  simp[compile_vyper_def] >> strip_tac >>
  drule compile_vyper_with_success_phases >> strip_tac >>
  gvs[finalize_codegen_def, o1PipelineCorrectTheory.o1_pipeline_def,
      AllCaseEqs()] >>
  rename1 `lower_vyper_runtime_unit tops rpolicy = SOME unit` >>
  rename1 `run_venom_pipeline (K T) (K T) (K T)
             rpolicy o1_pipeline_spec unit = SOME out` >>
  qpat_x_assum `codegen_assembly rpolicy out.po_unit = SOME _`
    (strip_assume_tac o MATCH_MP codegen_assembly_success_shape) >>
  goal_assum $ drule_at Any >> gvs[]
QED

Theorem compile_vyper_runtime_nonempty_asm_opt[local]:
  compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) ==>
  runtime_bc <> []
Proof
  strip_tac >> drule compile_vyper_runtime_phases_asm_opt >> strip_tac >>
  gvs[] >> irule codegen_assembly_finalizer_nonempty >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem o1_pipeline_memory_obligations_raw[local]:
  !out cplan vs.
    generate_context_plan out.po_unit.cu_context = SOME cplan /\
    o1_lowered_inv out.po_unit.cu_context vs /\
    vs.vs_initial_fmp = n2w cplan.cp_initial_fmp
    ==>
    codegen_memory_obligations (raw_reachable vs) out.po_unit.cu_context cplan /\
    codegen_reachability_package (raw_reachable vs) out.po_unit.cu_context vs
Proof
  rpt gen_tac >> strip_tac >>
  drule generate_context_plan_spill_gap >> strip_tac >>
  `?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
         mem_inv (lowered_mem_ok eom (w2n vs.vs_initial_fmp))
           out.po_unit.cu_context vs` by
    (fs[o1_lowered_inv_def, mem_inv_raw_reachable] >>
     rpt strip_tac >> first_x_assum drule >>
     drule ctxLookupAgreeTheory.raw_reachable_initial_fmp >>
     simp[lowered_mem_fact_def, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  gvs[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  metis_tac[mem_inv_codegen_obligations, step_write_footprint_holds]
QED

Theorem o1_pipeline_sym_unit_static_ok[local]:
  !rpolicy unit out.
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                    ds.ds_items) unit.cu_data_segment /\
  ((?fn inst. MEM fn unit.cu_context.ctx_functions /\
              MEM inst (fn_insts fn) /\
              MEM (Label "runtime_begin") inst.inst_operands) ==>
   EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment) ==>
  sym_unit_static_ok out.po_unit
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`rpolicy`, `unit`, `out`] mp_tac
    o1_pipeline_runtime_reference_reflects >>
  impl_tac >- simp[] >> strip_tac >>
  fs[o1PipelineCorrectTheory.o1_pipeline_def] >>
  drule_all run_venom_pipeline_bytes_only >> strip_tac >>
  drule run_venom_pipeline_success_unit_wf >> strip_tac >>
  fs[sym_unit_static_ok_def, unit_wf_def, venom_wf_def] >>
  metis_tac[]
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
      simp[deploy_result_rel_def,
           initial_evaluation_context_def]) >>
  rename1 `INR exc` >> Cases_on `exc` >> simp[deploy_result_rel_def]
QED

Theorem deploy_exempt_result_rel[local]:
  deploy_source_exempt tops src ==>
  deploy_result_rel H tops runtime_bc tx es r es' src
Proof
  Cases_on `src` >> simp[deploy_source_exempt_def] >>
  rename1 `INR exc` >> Cases_on `exc` >>
  simp[deploy_source_exempt_def, deploy_result_rel_def]
QED

(* The bridges at the deployment entry: the S4 memory facts of vs from its
   memory-safe and pointer-safe runs from "__deploy". *)
Theorem deploy_selected_memory[local]:
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  deploy_source_ok tops am tx /\
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
  drule_all deploy_unit_shape_ok >> strip_tac >>
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
  deploy_phases policy tops (assemble prog, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  deploy_state_rel tops (assemble prog') am tx es /\
  vs_out = opt_deploy_entry_state prog prog' cplan tops es /\
  txp = tx with code := vs_out.vs_code /\
  deploy_source_ok tops am txp /\
  raw_variant fmp vs vs_out ==>
  vs.vs_outcomes = MAP SND (call_trace es) /\ code_layout_valid vs /\
  unit_shape_ok dout.po_unit /\
  vs.vs_alloca_next = imm_len tops /\
  vs.vs_initial_fmp = fmp /\ vs.vs_fmp = fmp
Proof
  strip_tac >>
  drule_all deploy_unit_shape_ok >> strip_tac >>
  drule_all deploy_unit_defs_reach_uses >> strip_tac >>
  `o1PipelineCorrect$o1_pipeline rpolicy dunit = SOME dout /\
   codegen_assembly rpolicy dout.po_unit = SOME prog` by
    fs[deploy_phases_def] >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  drule_all deploy_bc_size_bounded >> strip_tac >>
  `?args_bytes.
     (FST (HD es.contexts)).msgParams.code = assemble prog' ++ args_bytes /\
     constructor_args_encode tops txp args_bytes` by
    (fs[deploy_state_rel_def, constructor_args_encode_def] >> metis_tac[]) >>
  `LENGTH args_bytes < 2 ** 128` by
    metis_tac[constructor_args_size_bounded] >>
  drule_all codegen_assembly_asm_encoding_wf >> strip_tac >>
  `FLOOKUP (SND (compute_label_offsets prog)) "code_end" =
     SOME (LENGTH (assemble prog))` by
    (irule immutable_code_end_length >>
     fs[deploy_phases_def] >> metis_tac[listTheory.APPEND_ASSOC]) >>
  `LENGTH args_bytes + LENGTH (assemble prog) <= dimword (:256) DIV 2` by
    (fs[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
     decide_tac) >>
  `code_layout_valid vs_out` by
    simp[code_layout_valid_def, opt_deploy_entry_state_def,
         opt_entry_state_def, entry_venom_state_frame_fields,
         rich_listTheory.DROP_LENGTH_APPEND] >>
  `code_layout_valid vs` by
    (MATCH_MP_TAC (Q.INST
       [`si` |-> `vs`, `so` |-> `vs_out with <|vs_fmp := fmp; vs_initial_fmp := fmp|>`]
       gas_variant_code_layout_valid) >>
     conj_tac >- metis_tac[raw_variant_def] >>
     qpat_x_assum `code_layout_valid vs_out` mp_tac >>
     simp[code_layout_valid_def]) >>
  qpat_x_assum `raw_variant _ _ _` mp_tac >>
  simp[raw_variant_def, gas_variant_def] >>
  disch_then (mp_tac o Q.AP_TERM
    `\s:venom_state. (s.vs_outcomes, s.vs_alloca_next,
       s.vs_initial_fmp, s.vs_fmp)`) >>
  simp[opt_deploy_entry_state_def, opt_entry_state_def,
       entry_venom_state_frame_fields, entry_venom_state_def] >>
  metis_tac[]
QED

(* At one tail of gas readings past the marked ones, where the constructor
   run's storage guard holds. *)
Theorem deploy_correct_at_tail[local]:
  fin IN accepted_finalizers /\
  fin rpolicy prog = SOME prog' /\
  (fin = asm_opt_finalizer ==> ~program_reads_self_code tops) /\
  compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
  deploy_phases policy tops (assemble prog, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  deploy_state_rel tops (assemble prog') am tx es /\
  vs_out = opt_deploy_entry_state prog prog' cplan tops es /\
  txp = tx with code := vs_out.vs_code /\
  deploy_source_ok tops am txp /\
  ~(?t. runtime_bc = 0xEFw :: t) /\
  w2n vs_out.vs_initial_fmp <= w2n fmp /\
  w2n fmp < 2 ** 254 /\
  unit_alloca_budget dunit.cu_context +
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
  `txp.function_name = "__init__"` by gvs[deploy_state_rel_def] >>
  `load_contract (SOME vs.vs_outcomes)
      (gas_explicit marks vs.vs_gas_readings ++ tail) am txp [(NONE, tops)] [] =
   load_contract NONE
      (gas_explicit marks vs.vs_gas_readings ++ tail) am txp [(NONE, tops)] []` by
    metis_tac[load_contract_call_free] >>
  Cases_on `deploy_source_exempt tops
              (load_contract (SOME vs.vs_outcomes)
                 (gas_explicit marks vs.vs_gas_readings ++ tail) am txp
                 [(NONE, tops)] [])`
  >- (disj2_tac >> irule deploy_exempt_result_rel >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `~deploy_source_exempt _ _ ==> _` drule >> strip_tac >>
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit` by
    fs[deploy_phases_def] >>
  drule lower_vyper_deploy_unit_context_ok >> strip_tac >>
  drule_all deploy_unit_shape_ok >> strip_tac >>
  qspecl_then [`marks`, `tops`, `runtime_bc`, `am`, `txp`, `dunit`, `vs`, `tail`]
    mp_tac deploy_unit_exit_safe_runs >>
  impl_tac >- gvs[] >> strip_tac >>
  qabbrev_tac `H = storage_trace_horizon
    (deploy_storage_trace (SOME vs.vs_outcomes)
       (gas_explicit marks vs.vs_gas_readings ++ tail) am txp tops)` >>
  `w2n vs.vs_initial_fmp <= w2n vs.vs_fmp` by simp[] >>
  drule_all deploy_selected_memory >> strip_tac >>
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
  qspecl_then [`H`, `tops`, `runtime_bc`, `am`, `txp`,
               `gas_explicit marks vs.vs_gas_readings ++ tail`,
               `load_contract (SOME vs.vs_outcomes)
                  (gas_explicit marks vs.vs_gas_readings ++ tail) am txp
                  [(NONE, tops)] []`,
               `run_context fuel dunit.cu_context vs`,
               `run_context fuel' dout.po_unit.cu_context vs_out`] mp_tac
    deploy_venom_result_rel_dead >>
  impl_tac >- gvs[] >> strip_tac >>
  `vs_out.vs_initial_fmp = n2w cplan.cp_initial_fmp` by
    fs[opt_deploy_entry_state_def, opt_entry_state_def, entry_venom_state_def] >>
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
           metis_tac[opt_deploy_entry_state_identity, deploy_txp_identity] >>
         qpat_x_assum `prog' = prog` SUBST_ALL_TAC >>
         qpat_x_assum `txp = tx` SUBST_ALL_TAC >>
         drule_all deploy_initcode_half_bounded >> strip_tac >>
         drule_all deploy_entry_state_ok >> strip_tac >>
         qspecl_then [`fuel'`, `rpolicy`, `dout.po_unit`, `cplan`, `prog`,
                      `raw_reachable vs_out`, `vs_out`, `shadow_root es`]
           mp_tac codegen_correct >>
         impl_tac >- gvs[] >> disch_then ACCEPT_TAC) >>
     `fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
     `supported_program tops /\ supported_program_deploy tops /\
      ~program_reads_self_code tops` by fs[deploy_source_ok_def] >>
     drule_all lower_vyper_deploy_unit_sym_src_ok >> strip_tac >>
     drule_all deploy_unit_defs_reach_uses >> strip_tac >>
     drule_all o1_pipeline_label_flow_preserved >> strip_tac >>
     drule_all o1_pipeline_sym_unit_static_ok >> strip_tac >>
     drule_all opt_deploy_codegen_asm_entry_rel >>
     disch_then (qspecl_then [`prog`, `cplan`] assume_tac) >>
     `assemble prog' <> []` by
       (irule codegen_assembly_finalizer_nonempty >> metis_tac[]) >>
     drule_all opt_deploy_asm_frame_rel >>
     disch_then (qspecl_then [`prog`, `cplan`] assume_tac) >>
     qspecl_then [`fuel'`, `rpolicy`, `dout.po_unit`, `cplan`, `prog`, `prog'`,
                  `raw_reachable vs_out`, `vs_out`, `shadow_root es`]
       mp_tac codegen_correct_asm_opt >>
     impl_tac
     >- gvs[opt_deploy_entry_state_def, opt_entry_state_def] >>
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
    (fin = asm_opt_finalizer ==> ~program_reads_self_code tops) /\
    compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_state_rel tops (assemble prog') am tx es /\
    vs_out = opt_deploy_entry_state prog prog' cplan tops es /\
    txp = tx with code := vs_out.vs_code /\
    deploy_source_ok tops am txp /\
    ~(?t. runtime_bc = 0xEFw :: t) /\
    w2n vs_out.vs_initial_fmp <= w2n fmp /\
    w2n fmp < 2 ** 254 /\
    unit_alloca_budget dunit.cu_context +
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
