(* Deployment boundary for the optimizer's shadow transaction. *)
Theory asmOptCodeDeploy
Ancestors
  asmOptCodeCommon e2eDeployAsmOpt e2eSelfCodeFree ctorDeployDefs
  e2eDeployDefs vyperInterpreter
  supportedDecls vyperTypeEntryReadiness vyperTypeContractSoundness
  ctorDeployInitcode ctorDeployInitcodeAsm ctorDeployEntry ctorDeployShape
  ctorDeployDefsReach ctorDeployLowering ctorDeployMemory ctorDeployDload ctorDeployDead
  ctorDeployFrame e2eComposition e2eProducers o1PipelineCorrect o1PassContract
  codegenCorrectness codegenAsmOpt e2eAsmOpt lowerDloadDefs e2eEntry
  gasSummary asmOptimizer deployOutcomesFreeUnit deploySymSrcUnit

Theorem supported_headers_constants_env:
  !ts acc. EVERY (supported_declaration_header tops) ts ==>
  constants_env cx am addr mid ts acc = SOME acc
Proof
  Induct >> simp[vyperInterpreterTheory.constants_env_def] >>
  rpt gen_tac >> Cases_on `h` >>
  simp[vyperInterpreterTheory.constants_env_def] >>
  rename1 `VariableDecl vis mut name ty slot` >> Cases_on `mut` >>
  simp[vyperInterpreterTheory.constants_env_def, supported_constants_rejected]
QED

Theorem supported_evaluate_all_constants:
  supported_program tops ==>
  evaluate_all_constants cx am addr [(NONE,tops)] =
  SOME (merge_constants addr NONE FEMPTY am)
Proof
  strip_tac >>
  `EVERY (supported_declaration_header tops) tops` by
    fs[supportedProgramTheory.supported_program_def,
       supportedDeclsTheory.supported_declaration_headers_def] >>
  simp[vyperInterpreterTheory.evaluate_all_constants_def,
       vyperInterpreterTheory.constants_order_def,
       vyperInterpreterTheory.evaluate_module_constants_def,
       supported_headers_constants_env] >>
  drule supported_headers_constants_env >> strip_tac >> simp[]
QED

Theorem deploy_typing_ok_code_update:
  supported_program tops /\ deploy_typing_ok tops am tx /\ LENGTH c < 2 ** 256 ==>
  deploy_typing_ok tops am (tx with code := c)
Proof
  simp[deploy_typing_ok_def] >> strip_tac >>
  qexistsl_tac [`deploy_art`, `runtime_art`, `imms`] >>
  gvs[call_tx_well_typed_def,
      checked_deployment_constants_ready_def, supported_evaluate_all_constants,
      deploy_evaluation_context_def, initial_evaluation_context_def,
      vyperContextTheory.get_tenv_def, vyperContextTheory.get_module_code_def]
QED

Theorem deploy_evaluation_context_code_update:
  deploy_evaluation_context tops am (tx with code := c) =
  (deploy_evaluation_context tops am tx with
    txn := ((deploy_evaluation_context tops am tx).txn with code := c))
Proof
  simp[deploy_evaluation_context_def, initial_evaluation_context_def]
QED

Theorem deploy_storage_ok_code_update:
  deploy_storage_ok tops am (tx with code := c) = deploy_storage_ok tops am tx
Proof
  simp[deploy_storage_ok_def, deploy_evaluation_context_code_update,
       contract_storage_well_formed_txn_code_update,
       storage_layout_safe_txn_code_update]
QED

Theorem deploy_dead_code_update:
  deploy_dead tops runtime_bc am (tx with code := c) = deploy_dead tops runtime_bc am tx
Proof
  simp[deploy_dead_def, initial_evaluation_context_code_update,
       storage_dead_txn_code_update]
QED

Theorem deploy_venom_result_rel_code_update:
  deploy_venom_result_rel tops runtime_bc (tx with code := c) src vr =
  deploy_venom_result_rel tops runtime_bc tx src vr
Proof
  Cases_on `src` >- (PairCases_on `x` >> Cases_on `vr` >>
    simp[deploy_venom_result_rel_def, initial_evaluation_context_code_update,
         agree_txn_code_update, storage_dead_txn_code_update]) >>
  Cases_on `y` >> Cases_on `vr` >> simp[deploy_venom_result_rel_def]
QED

Theorem deploy_result_rel_code_update:
  deploy_result_rel tops runtime_bc (tx with code := c) es r es' src =
  deploy_result_rel tops runtime_bc tx es r es' src
Proof
  Cases_on `src` >- (PairCases_on `x` >>
    simp[deploy_result_rel_def, initial_evaluation_context_code_update,
         agree_txn_code_update, storage_dead_txn_code_update]) >>
  Cases_on `y` >> simp[deploy_result_rel_def]
QED

Theorem opt_deploy_code_half_bounded:
  deploy_phases policy tops (assemble prog, runtime_bc) arts /\
  deploy_source_ok tops am tx /\
  deploy_state_rel tops (assemble prog') am tx es ==>
  LENGTH (opt_deploy_entry_state prog prog' cplan tops es).vs_code <= dimword(:256) DIV 2
Proof
  strip_tac >> drule_all ctorDeployInitcodeAsmTheory.deploy_bc_size_bounded >> strip_tac >>
  fs[deploy_state_rel_def] >>
  drule_all ctorDeployInitcodeTheory.constructor_args_size_bounded >>
  simp[opt_deploy_entry_state_def, e2eAsmOptTheory.opt_entry_state_def,
       e2eEntryTheory.entry_venom_state_def, rich_listTheory.DROP_LENGTH_APPEND,
       wordsTheory.dimword_def]
QED

(* The shadow frame is only needed by source-stage producers. *)
Theorem opt_deploy_source_entry:
  deploy_phases policy tops (assemble prog, runtime_bc) (rpolicy,dunit,dout,prog,cplan) /\
  asm_opt_finalizer rpolicy prog = SOME prog' /\
  deploy_source_ok tops am tx /\ deploy_state_rel tops (assemble prog') am tx es ==>
  ?es_p.
    deploy_source_ok tops am
      (tx with code := (opt_deploy_entry_state prog prog' cplan tops es).vs_code) /\
    deploy_state_rel tops (assemble prog) am
      (tx with code := (opt_deploy_entry_state prog prog' cplan tops es).vs_code) es_p /\
    gas_variant (opt_deploy_entry_state prog prog' cplan tops es with vs_outcomes := [])
      (deploy_entry_state prog cplan tops es_p) /\
    o1_run_state_ok (opt_deploy_entry_state prog prog' cplan tops es)
Proof
  strip_tac >> drule_all opt_deploy_frame >> strip_tac >>
  qabbrev_tac `vs_out = opt_deploy_entry_state prog prog' cplan tops es` >>
  `LENGTH vs_out.vs_code <= dimword(:256) DIV 2` by
    (simp[Abbr `vs_out`] >> irule opt_deploy_code_half_bounded >> metis_tac[]) >>
  `deploy_source_ok tops am (tx with code := vs_out.vs_code)` by
    (fs[deploy_source_ok_def] >>
     conj_tac >- (irule deploy_typing_ok_code_update >> simp[] >>
       gvs[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``]) >>
     simp[deploy_storage_ok_code_update]) >>
  drule_all deploy_unit_shape_ok >> strip_tac >>
  drule_all deploy_unit_defs_reach_uses >> strip_tac >>
  drule_all deploy_initcode_half_bounded >> strip_tac >>
  `o1PipelineCorrect$o1_pipeline rpolicy dunit = SOME dout` by fs[deploy_phases_def] >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  drule_all deploy_entry_state_ok >> strip_tac >>
  `o1_run_state_ok (vs_out with vs_outcomes := [])` by
    metis_tac[gas_variant_run_state_ok] >>
  qexists_tac `es_p` >> simp[] >>
  fs[o1_run_state_ok_def, unitTransformDefsTheory.o1_initial_state_ok_def,
     code_layout_valid_def]
QED

Theorem opt_deploy_pipeline_ready:
  deploy_phases policy tops (assemble prog, runtime_bc) (rpolicy,dunit,dout,prog,cplan) /\
  asm_opt_finalizer rpolicy prog = SOME prog' /\
  deploy_source_ok tops am tx /\ deploy_state_rel tops (assemble prog') am tx es /\
  ~program_reads_self_code tops ==>
  ?vs_in.
    gas_variant vs_in (opt_deploy_entry_state prog prog' cplan tops es) /\
    (raw_unit_memory_ok dunit.cu_context vs_in /\
     ptr_discipline (imm_len tops) dunit.cu_context vs_in /\
     taint_within (deploy_dead tops runtime_bc am tx) dunit.cu_context vs_in /\
     mem_inv dload_offset_ok dunit.cu_context vs_in /\
     mem_inv dload_headroom_ok dunit.cu_context vs_in /\
     mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
         s.vs_code = vs_in.vs_code /\ s.vs_data_section = vs_in.vs_data_section)
       dunit.cu_context vs_in ==>
     ctx_sim (deploy_dead tops runtime_bc am tx) dunit.cu_context dout.po_unit.cu_context
       vs_in (opt_deploy_entry_state prog prog' cplan tops es) /\
     o1_lowered_inv dout.po_unit.cu_context (opt_deploy_entry_state prog prog' cplan tops es) /\
     code_end_offset_ok (raw_reachable (opt_deploy_entry_state prog prog' cplan tops es))
       dout.po_unit.cu_context)
Proof
  strip_tac >> drule_all opt_deploy_source_entry >> strip_tac >>
  qabbrev_tac `vs_out = opt_deploy_entry_state prog prog' cplan tops es` >>
  drule_all deploy_unit_shape_ok >> strip_tac >>
  drule_all deploy_unit_defs_reach_uses >> strip_tac >>
  `o1PipelineCorrect$o1_pipeline rpolicy dunit = SOME dout /\
   codegen_assembly rpolicy dout.po_unit = SOME prog /\
   generate_context_plan dout.po_unit.cu_context = SOME cplan` by
    fs[deploy_phases_def] >>
  `assemble prog <> []` by
    metis_tac[codegenAsmProgOkTheory.codegen_assembly_nonempty] >>
  `vs_out.vs_initial_fmp = n2w cplan.cp_initial_fmp /\
   vs_out.vs_code = assemble prog ++ vs_out.vs_data_section` by
    simp[Abbr `vs_out`, opt_deploy_entry_state_def, opt_entry_state_def,
         entry_venom_state_def] >>
  `LENGTH vs_out.vs_data_section < dimword (:256) DIV 2` by
    (`LENGTH vs_out.vs_code <= dimword (:256) DIV 2` by
       fs[o1_run_state_ok_def, code_layout_valid_def] >>
     `0 < LENGTH (assemble prog)` by (Cases_on `assemble prog` >> fs[]) >>
     qpat_x_assum `0 < _` mp_tac >>
     qpat_x_assum `LENGTH vs_out.vs_code <= _` mp_tac >>
     qpat_x_assum `vs_out.vs_code = _` (fn th => REWRITE_TAC [th]) >> simp[]) >>
  `supported_program tops /\ supported_program_deploy tops` by fs[deploy_source_ok_def] >>
  drule_all lower_vyper_deploy_unit_sym_src_ok >> strip_tac >>
  qspecl_then [`deploy_dead tops runtime_bc am tx`, `imm_len tops`, `rpolicy`,
               `dunit`, `dout`, `vs_out`] mp_tac o1_pipeline_code_end_offset_ok >>
  impl_tac >-
    (qpat_assum `!fn inst. _ ==> ~MEM (Label "code_end") _`
       (fn th => REWRITE_TAC [th]) >> fs[deploy_dead_wf]) >> strip_tac >>
  goal_assum $ drule_at Any >> simp[]
QED

Theorem asm_opt_deploy_source_run:
  deploy_phases policy tops (assemble prog, runtime_bc) (rpolicy,dunit,dout,prog,cplan) /\
  asm_opt_finalizer rpolicy prog = SOME prog' /\
  deploy_source_ok tops am tx /\ deploy_state_rel tops (assemble prog') am tx es /\
  ~program_reads_self_code tops ==>
  (?gobs. deploy_source_exempt tops (load_contract NONE gobs am tx [(NONE,tops)] [])) \/
  (?gobs fuel. deploy_venom_result_rel tops runtime_bc tx
    (load_contract NONE gobs am tx [(NONE,tops)] [])
    (run_context fuel dout.po_unit.cu_context
      (opt_deploy_entry_state prog prog' cplan tops es)) /\
    o1_lowered_inv dout.po_unit.cu_context (opt_deploy_entry_state prog prog' cplan tops es) /\
    code_end_offset_ok (raw_reachable (opt_deploy_entry_state prog prog' cplan tops es))
      dout.po_unit.cu_context)
Proof
  strip_tac >> drule_all opt_deploy_source_entry >> strip_tac >>
  drule_all opt_deploy_pipeline_ready >> strip_tac >>
  qabbrev_tac `vs_out = opt_deploy_entry_state prog prog' cplan tops es` >>
  `gas_variant (vs_in with vs_outcomes := [])
     (deploy_entry_state prog cplan tops es_p)` by
    (gvs[gas_variant_def, venomStateTheory.venom_state_component_equality]) >>
  `supported_program tops` by fs[deploy_source_ok_def] >>
  `code_layout_valid vs_in` by
    (irule gas_variant_code_layout_valid >> qexists_tac `vs_out` >> fs[o1_run_state_ok_def]) >>
  drule_all deploy_unit_outcomes_free >>
  simp[deploy_venom_result_rel_code_update, deploy_dead_code_update,
       load_contract_self_code_free] >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  Cases_on `?gobs. deploy_source_exempt tops (load_contract NONE gobs am tx [(NONE,tops)] [])`
  >- simp[] >>
  `?marks fuel. deploy_venom_result_rel tops runtime_bc tx
     (load_contract NONE (gas_explicit marks vs_in.vs_gas_readings) am tx [(NONE,tops)] [])
     (run_context fuel dunit.cu_context vs_in)` by metis_tac[] >>
  `raw_unit_memory_ok dunit.cu_context vs_in /\
   ptr_discipline (imm_len tops) dunit.cu_context vs_in /\
   taint_within (deploy_dead tops runtime_bc am tx) dunit.cu_context vs_in /\
   mem_inv dload_offset_ok dunit.cu_context vs_in /\
   mem_inv dload_headroom_ok dunit.cu_context vs_in /\
   mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
       s.vs_code = vs_in.vs_code /\ s.vs_data_section = vs_in.vs_data_section)
     dunit.cu_context vs_in` by metis_tac[] >>
  `ctx_sim (deploy_dead tops runtime_bc am tx) dunit.cu_context
     dout.po_unit.cu_context vs_in vs_out /\
   o1_lowered_inv dout.po_unit.cu_context vs_out /\
   code_end_offset_ok (raw_reachable vs_out) dout.po_unit.cu_context` by metis_tac[] >>
  `terminates (run_context fuel dunit.cu_context vs_in)` by
    metis_tac[deploy_venom_result_rel_terminates] >>
  `?fuel'. dead_result_rel (deploy_dead tops runtime_bc am tx)
    (run_context fuel dunit.cu_context vs_in)
    (run_context fuel' dout.po_unit.cu_context vs_out)` by metis_tac[ctx_sim_def] >>
  `~deploy_source_exempt tops
     (load_contract NONE (gas_explicit marks vs_in.vs_gas_readings) am tx [(NONE,tops)] [])`
    by metis_tac[] >>
  qspecl_then [`tops`, `runtime_bc`, `am`, `tx`,
               `gas_explicit marks vs_in.vs_gas_readings`] mp_tac deploy_venom_result_rel_dead >>
  simp[] >> disch_then drule_all >> strip_tac >>
  metis_tac[]
QED

Theorem asm_opt_deploy_machine_run:
  deploy_phases policy tops (assemble prog, runtime_bc) (rpolicy,dunit,dout,prog,cplan) /\
  asm_opt_finalizer rpolicy prog = SOME prog' /\
  deploy_source_ok tops am tx /\ deploy_state_rel tops (assemble prog') am tx es /\
  assemble prog' <> [] /\ ~program_reads_self_code tops /\
  o1_lowered_inv dout.po_unit.cu_context (opt_deploy_entry_state prog prog' cplan tops es) /\
  code_end_offset_ok (raw_reachable (opt_deploy_entry_state prog prog' cplan tops es))
    dout.po_unit.cu_context ==>
  ?r g. run_call (shadow_root es) = SOME (r,g) /\
    (frame_resource_starved (shadow_root es) r g \/
     venom_frame_rel (shadow_root es) r g
       (run_context fuel dout.po_unit.cu_context
         (opt_deploy_entry_state prog prog' cplan tops es)))
Proof
  strip_tac >> drule_all opt_deploy_source_entry >> strip_tac >>
  qabbrev_tac `vs_out = opt_deploy_entry_state prog prog' cplan tops es` >>
  drule_all deploy_unit_shape_ok >> strip_tac >>
  drule_all deploy_unit_defs_reach_uses >> strip_tac >>
  `o1PipelineCorrect$o1_pipeline rpolicy dunit = SOME dout /\
   codegen_assembly rpolicy dout.po_unit = SOME prog /\
   generate_context_plan dout.po_unit.cu_context = SOME cplan` by fs[deploy_phases_def] >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  `vs_out.vs_initial_fmp = n2w cplan.cp_initial_fmp /\
   vs_out.vs_code = assemble prog ++ vs_out.vs_data_section` by
    simp[Abbr `vs_out`, opt_deploy_entry_state_def, opt_entry_state_def, entry_venom_state_def] >>
  drule_all o1_pipeline_memory_obligations_raw >> strip_tac >>
  drule_all o1_pipeline_codegen_obligations >> strip_tac >>
  `supported_program tops /\ supported_program_deploy tops` by fs[deploy_source_ok_def] >>
  drule_all lower_vyper_deploy_unit_sym_src_ok >> strip_tac >>
  `label_flow_ok dout.po_unit.cu_context` by
    (irule o1_pipeline_label_flow_ok >> metis_tac[]) >>
  `sym_unit_static_ok dout.po_unit` by
    (irule o1_pipeline_sym_unit_static_ok >> metis_tac[]) >>
  `code_layout_valid vs_out` by fs[o1_run_state_ok_def] >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`,
               `dout.po_unit`] mp_tac opt_deploy_codegen_asm_entry_rel >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`,
               `dout.po_unit`] mp_tac opt_deploy_asm_frame_rel >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  qspecl_then [`fuel`, `rpolicy`, `dout.po_unit`, `cplan`, `prog`, `prog'`,
               `raw_reachable vs_out`, `vs_out`, `shadow_root es`] mp_tac codegen_correct_asm_opt >>
  impl_tac >- (fs[Abbr `vs_out`]) >> simp[]
QED

Theorem asm_opt_deploy_result:
  deploy_phases policy tops (assemble prog, runtime_bc) (rpolicy,dunit,dout,prog,cplan) /\
  asm_opt_finalizer rpolicy prog = SOME prog' /\
  deploy_source_ok tops am tx /\ deploy_state_rel tops (assemble prog') am tx es /\
  ~program_reads_self_code tops /\ assemble prog' <> [] /\ runtime_bc <> [] /\
  ~(?t. runtime_bc = 0xEFw :: t) ==>
  ?r es'. run_call es = SOME (r,es') /\
    (frame_resource_starved es r es' \/
     ?gobs. deploy_result_rel tops runtime_bc tx es r es'
       (load_contract NONE gobs am tx [(NONE,tops)] []))
Proof
  strip_tac >> drule_all asm_opt_deploy_source_run >> strip_tac
  >- (qspec_then `es` strip_assume_tac run_call_total >>
      qexistsl_tac [`r`, `es'`] >> simp[] >> disj2_tac >> qexists_tac `gobs` >>
      Cases_on `load_contract NONE gobs am tx [(NONE,tops)] []` >>
      fs[deploy_source_exempt_def] >> rename1 `INR exc` >>
      Cases_on `exc` >> fs[deploy_result_rel_def]) >>
  drule_all asm_opt_deploy_machine_run >>
  disch_then (qspec_then `fuel` strip_assume_tac) >>
  `?r es'. run_call es = SOME (r,es') /\
    (frame_resource_starved es r es' \/ deploy_result_rel tops runtime_bc tx es r es'
      (load_contract NONE gobs am tx [(NONE,tops)] []))` by
    (irule deploy_venom_frame >> metis_tac[]) >>
  metis_tac[]
QED
