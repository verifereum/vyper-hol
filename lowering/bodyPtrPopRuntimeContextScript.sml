Theory bodyPtrPopRuntimeContext
Ancestors bodyPtrPopRuntimeListsBoundary bodyPtrPopSourceSupport
  bodyPtrPopContextPackaging bodyPtrPopCompilerBoundary bodyPtrPopBoundaryContract
  vyperCompiler compileVyper compileEnv list

Theorem pop_initial_compile_state_boundary:
  pop_comp_boundary (initial_compile_state label)
Proof
  simp[initial_compile_state_def, pop_comp_boundary_def]
QED

Theorem pop_run_lowering_context:
  EVERY (\(lbl,ce,args,mincds,pay,nr,key,tr,view,stmts,ret).
    ?bindings. supported_stmts tops bindings stmts) exts /\
  EVERY (\(lbl,ce,params,buf,nr,key,tr,view,ctor,imm,stmts,ret).
    ?bindings. supported_stmts tops bindings stmts) ints /\
  (case fb of NONE => T | SOME (ce,pay,nr,key,tr,view,stmts,ret) =>
    ?bindings. supported_stmts tops bindings stmts) /\
  run_lowering sels exts ints fb policy buckets meta dense info label = SOME cu ==>
  EVERY (\f. EVERY (\bb. ~occurs5 pop_guarded5 bb.bb_instructions) f.fn_blocks)
    cu.cu_context.ctx_functions
Proof
  simp[run_lowering_def] >> rpt strip_tac >>
  gvs[AllCaseEqs(), lowering_policy_ok_def] >>
  pairarg_tac >> gvs[AllCaseEqs()] >>
  drule_at (Pat `compile_generate_runtime _ _ _ _ _ _ _ _ _ _ = _`)
    pop_generate_runtime_linear_boundary >>
  disch_then (qspec_then `tops` mp_tac) >>
  simp[pop_initial_compile_state_boundary] >> strip_tac >>
  drule_all pop_extract_context_boundary >> simp[]
QED

Theorem pop_lower_runtime_context:
  supported_program tops /\ lower_vyper_runtime_unit tops policy = SOME cu ==>
  EVERY (\f. EVERY (\bb. ~occurs5 pop_guarded5 bb.bb_instructions) f.fn_blocks)
    cu.cu_context.ctx_functions
Proof
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  simp[lower_vyper_runtime_unit_def] >> rpt strip_tac >> gvs[] >>
  drule_at (Pat `run_lowering _ _ _ _ _ _ _ _ _ _ = _`) pop_run_lowering_context >>
  disch_then irule >> qexists_tac `tops` >> rpt conj_tac >> FIRST_PROVE
    [drule_all pop_external_packages_support >> disch_then MATCH_ACCEPT_TAC,
     drule_all pop_internal_packages_support >> disch_then MATCH_ACCEPT_TAC,
     (irule pop_fallback_package_support >> goal_assum drule >> simp[])]
QED
