Theory asmOptCodeDeploy
Ancestors
  e2eDeployDefs e2eDeployAsmOpt e2eAsmOpt e2eSelfCodeFree ctorDeployDefs
  selfCodeFreeContext
  ctorDeployFrame e2eComposition e2eProducers o1PipelineCorrect o1PassContract
  codegenAsmOpt codegenCorrectness contextCodegenRel lowerDloadDefs
  vyperInterpreter accountsRelProps asmOptCodeCommon codegenEntrySim

Theorem deploy_storage_ok_code_update:
  supported_program tops /\ ~program_reads_self_code tops ==>
  (deploy_storage_ok tops am (tx with code := c) os gobs =
   deploy_storage_ok tops am tx os gobs)
Proof
  rpt strip_tac >>
  `!st (regions : (bool # bytes32 # type_value) list).
     storage_well_formed_on (deploy_evaluation_context tops am (tx with code := c))
       st regions =
     storage_well_formed_on (deploy_evaluation_context tops am tx) st regions` by
    (rpt gen_tac >>
     irule vyperCallFiniteStorageSupportTheory.storage_well_formed_on_target >>
     simp[deploy_evaluation_context_def, initial_evaluation_context_def]) >>
  fs[deploy_storage_ok_def, deploy_storage_trace_self_code_free,
     vyperStorageFootprintTheory.storage_trace_backends_well_formed_def]
QED

Theorem asm_opt_deploy_result:
  deploy_phases policy tops (assemble prog, runtime_bc)
    (rpolicy,dunit,dout,prog,cplan) /\
  asm_opt_finalizer rpolicy prog = SOME prog' /\
  deploy_source_ok tops am tx /\
  deploy_state_rel tops (assemble prog') am tx es /\
  ~program_reads_self_code tops /\ assemble prog' <> [] /\ runtime_bc <> [] /\
  ~(?t. runtime_bc = 0xEFw :: t) /\
  o1_lowered_inv dout.po_unit.cu_context
    (opt_deploy_entry_state prog prog' cplan tops es) /\
  code_end_offset_ok
    (raw_reachable (opt_deploy_entry_state prog prog' cplan tops es))
    dout.po_unit.cu_context /\
  (?fuel. deploy_venom_result_rel H tops runtime_bc tx
    (load_contract (SOME (MAP SND (call_trace es))) gobs am tx [(NONE,tops)] [])
    (run_context fuel dout.po_unit.cu_context
      (opt_deploy_entry_state prog prog' cplan tops es))) ==>
  ?r es'. run_call es = SOME (r,es') /\
    (creation_resource_starved es r es' \/
     deploy_result_rel H tops runtime_bc tx es r es'
       (load_contract (SOME (MAP SND (call_trace es))) gobs am tx [(NONE,tops)] []))
Proof
  rpt strip_tac >>
  drule_all ctorDeployDefsReachTheory.deploy_unit_defs_reach_uses >> strip_tac >>
  fs[deploy_source_ok_def] >>
  drule_all deploySymSrcUnitTheory.lower_vyper_deploy_unit_sym_src_ok >> strip_tac >>
  fs[deploy_phases_def] >>
  drule_all ctorDeployShapeTheory.lower_vyper_deploy_unit_source_unit_ok >> strip_tac >>
  drule_all ctorDeployShapeTheory.lower_vyper_deploy_unit_o1_shape_extras >> strip_tac >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  drule_all o1LabelFlowComposeTheory.o1_pipeline_label_flow_preserved >> strip_tac >>
  drule_all o1_pipeline_sym_unit_static_ok >> strip_tac >>
  `(opt_deploy_entry_state prog prog' cplan tops es).vs_initial_fmp =
      n2w cplan.cp_initial_fmp` by
    simp[opt_deploy_entry_state_def, opt_entry_state_def,
         e2eEntryTheory.entry_venom_state_def] >>
  drule_all o1_pipeline_memory_obligations_raw >> strip_tac >>
  drule_all o1_pipeline_codegen_obligations >> strip_tac >>
  `(opt_deploy_entry_state prog prog' cplan tops es).vs_code =
     assemble prog ++ (opt_deploy_entry_state prog prog' cplan tops es).vs_data_section` by
    simp[opt_deploy_entry_state_def, opt_entry_state_def] >>
  drule_all opt_deploy_codegen_asm_entry_rel >>
  disch_then (qspecl_then [`prog`, `cplan`] assume_tac) >>
  drule_all opt_deploy_asm_frame_rel >>
  disch_then (qspecl_then [`prog`, `cplan`] assume_tac) >>
  drule_all codegen_correct_asm_opt >>
  disch_then (qspec_then `fuel` assume_tac) >>
  metis_tac[deploy_venom_frame]
QED

Theorem deploy_dead_code_update:
  deploy_dead H tops runtime_bc am (tx with code := c) =
  deploy_dead H tops runtime_bc am tx
Proof
  simp[deploy_dead_def]
QED

Theorem deploy_venom_result_rel_code_update:
  deploy_venom_result_rel H tops runtime_bc (tx with code := c) src vr =
  deploy_venom_result_rel H tops runtime_bc tx src vr
Proof
  Cases_on `src`
  >- (rename1 `INL p` >> PairCases_on `p` >> Cases_on `vr` >>
      simp[deploy_venom_result_rel_def,
           initial_evaluation_context_code_update, agree_txn_code_update]) >>
  rename1 `INR exc` >> Cases_on `exc` >> Cases_on `vr` >>
  simp[deploy_venom_result_rel_def]
QED

Theorem deploy_result_rel_code_update:
  deploy_result_rel H tops runtime_bc (tx with code := c) es r es' src =
  deploy_result_rel H tops runtime_bc tx es r es' src
Proof
  Cases_on `src`
  >- (rename1 `INL p` >> PairCases_on `p` >>
      simp[deploy_result_rel_def,
           initial_evaluation_context_code_update, agree_txn_code_update]) >>
  rename1 `INR exc` >> Cases_on `exc` >> simp[deploy_result_rel_def]
QED
