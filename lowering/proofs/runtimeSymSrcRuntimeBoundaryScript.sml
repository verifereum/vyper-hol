Theory runtimeSymSrcRuntimeBoundary
Ancestors
  runtimeSymSrcPackageTransport runtimeSymSrcModuleArgs
  runtimeSymSrcModuleBodies runtimeSymSrcInternalFunction
  runtimeSymSrcFunctionLists runtimeSymSrcModuleDispatch
  runtimeSymSrcGeneratorContracts runtimeSymSrcEmissionProbe vyperCompiler compileVyper
  list loweringShapeDefs compileEnv venomInst
  runtimeSymSrcOrdinaryPackages runtimeSymSrcGroupedPackages loweringShapeProps
  runtimeSymSrcInterfaces

Theorem runtime_sym_initial:
  EVERY P (state_insts (initial_compile_state entry))
Proof
  simp[state_insts_def, all_blocks_def, initial_compile_state_def]
QED

Theorem runtime_sym_run_lowering:
  (!s u s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_generate_runtime sels exts ints fb Linear bc mb db ei s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  run_lowering sels exts ints fb rp bc mb db ei entry = SOME unit ==>
  !fn. MEM fn unit.cu_context.ctx_functions ==>
    EVERY runtime_sym_inst (fn_insts fn)
Proof
  simp[run_lowering_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[AllCaseEqs(), lowering_policy_ok_def] >>
  `EVERY runtime_sym_inst (state_insts st1)` by
    (metis_tac[runtime_sym_initial]) >>
  drule_all runtime_sym_extract >> simp[]
QED

Theorem runtime_sym_run_grouped_lowering:
  (!s u s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_generate_grouped_runtime groups ints fb s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  run_grouped_lowering groups ints fb rp entry = SOME unit ==>
  !fn. MEM fn unit.cu_context.ctx_functions ==>
    EVERY runtime_sym_inst (fn_insts fn)
Proof
  simp[run_grouped_lowering_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[AllCaseEqs()] >>
  `EVERY runtime_sym_inst (state_insts st1)` by
    (metis_tac[runtime_sym_initial]) >>
  drule_all runtime_sym_extract >> simp[]
QED

Theorem runtime_sym_selectors:
  !sources tenv. EVERY (\(sel,lbl,tz). runtime_sym_label lbl)
    (build_selectors tenv sources)
Proof
  Induct >> simp[build_selectors_def] >> gen_tac >> PairCases_on `h` >>
  simp[build_selectors_def, compute_selector_def] >> simp[runtime_sym_label_def]
QED

Theorem runtime_sym_fallback_classified_body:
  supported_program tops /\ ~program_reads_self_code tops /\
  (!bindings ce lc ty ss. runtime_sym_stmts_contract tops bindings compile_stmts ce lc ty ss) /\
  set_fallback_package_target target
    (package_fallback_fn tops trans keys (FST (SND (SND (classify_functions tops))))) =
    SOME (ce,pay,nr,key,tr,view,stmts,ret) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_fallback_body ce pay nr key tr view stmts ret s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  Cases_on `FST (SND (SND (classify_functions tops)))`
  >- simp[package_fallback_fn_def, set_fallback_package_target_def] >>
  PairCases_on `x` >> Cases_on `u` >> strip_tac >>
  drule_at (Pat `set_fallback_package_target _ _ = _`) runtime_sym_fallback_package_body >>
  simp[] >> disch_then irule >> qexists `s` >> simp[]
QED
