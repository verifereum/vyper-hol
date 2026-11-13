Theory runtimeSymSrcRuntimeBoundary
Ancestors
  runtimeSymSrcPackageTransport runtimeSymSrcModuleArgs
  runtimeSymSrcModuleBodies runtimeSymSrcInternalFunction
  runtimeSymSrcFunctionLists runtimeSymSrcModuleDispatch
  runtimeSymSrcGeneratorContracts runtimeSymSrcEmissionProbe vyperCompiler compileVyper
  list loweringShapeDefs compileEnv venomInst

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
