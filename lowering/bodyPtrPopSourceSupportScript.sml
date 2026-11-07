Theory bodyPtrPopSourceSupport
Ancestors supportedProgram supportedStmts compileVyper loweringShapeProps
  vyperAST list

Theorem pop_source_function_body_support:
  supported_program tops /\
  MEM (FunctionDecl vis mut nr rr name args defaults ret stmts) tops ==>
  ?bindings. supported_stmts tops bindings stmts
Proof
  strip_tac >> drule_all supported_program_function >>
  simp[supported_function_body_def] >> metis_tac[]
QED

Theorem pop_external_packages_support:
  supported_program tops /\ classify_functions tops = (exts,ints,fb,ctor) ==>
  EVERY (\(lbl,ce,args,mincds,pay,nr,key,tr,view,stmts,ret).
    ?bindings. supported_stmts tops bindings stmts)
    (MAP (set_external_package_target target o package_external_fn tops trans keys) exts)
Proof
  rpt strip_tac >> simp[EVERY_MAP, EVERY_MEM] >> rpt gen_tac >> strip_tac >>
  PairCases_on `x` >>
  simp[package_external_fn_def, set_external_package_target_def] >>
  `MEM (FunctionDecl External x0 x1 x2 x3 x4 x5 x6 x7) tops` by
    metis_tac[classify_functions_external_source, pairTheory.FST] >>
  drule_all pop_source_function_body_support >> simp[]
QED

Theorem pop_internal_packages_support:
  supported_program tops /\ classify_functions tops = (exts,ints,fb,ctor) ==>
  EVERY (\(lbl,ce,args,buf,nr,key,tr,view,ctor,imm,stmts,ret).
    ?bindings. supported_stmts tops bindings stmts)
    (MAP (set_internal_package_target target o
      package_internal_fn tops trans keys is_ctor imm_len) ints)
Proof
  rpt strip_tac >> simp[EVERY_MAP, EVERY_MEM] >> rpt gen_tac >> strip_tac >>
  PairCases_on `x` >>
  simp[package_internal_fn_def, set_internal_package_target_def] >>
  `MEM (FunctionDecl Internal x0 x1 x2 x3 x4 x5 x6 x7) tops` by
    metis_tac[MEM_classify_internal, pairTheory.FST, pairTheory.SND] >>
  drule_all pop_source_function_body_support >> simp[]
QED

Theorem pop_fallback_package_support:
  supported_program tops /\ classify_functions tops = (exts,ints,fb,ctor) ==>
  (case set_fallback_package_target target (package_fallback_fn tops trans keys fb) of
    NONE => T | SOME (ce,pay,nr,key,tr,view,stmts,ret) =>
      ?bindings. supported_stmts tops bindings stmts)
Proof
  Cases_on `fb` >> simp[package_fallback_fn_def, set_fallback_package_target_def] >>
  rpt strip_tac >> PairCases_on `x` >>
  simp[package_fallback_fn_def, set_fallback_package_target_def] >>
  `MEM (FunctionDecl External x0 x1 x2 x3 x4 x5 x6 x7) tops` by
    metis_tac[classify_functions_fallback_mem, pairTheory.FST, pairTheory.SND] >>
  drule_all pop_source_function_body_support >> simp[]
QED
