Theory bodyPtrIfExpCallableReturn
Ancestors
  compileVyper vyperInterpreter memoryLocalRhsProps supportedNames
  vyperTypeContractStaticMaps

Theorem ifexp_deploy_return_map:
  !tops name fm nr args dflts ret body.
    lookup_function NONE name Internal tops = NONE /\
    lookup_function NONE name Deploy tops = SOME (fm,nr,args,dflts,ret,body) ==>
    build_func_return_type tops name = ret
Proof
  Induct_on `tops`
  >- simp[lookup_function_def, build_func_return_type_def, AllCaseEqs()] >>
  rpt gen_tac >> Cases_on `h` >>
  simp[lookup_function_def, build_func_return_type_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
  >- (Cases_on `f` >> gvs[] >> metis_tac[]) >>
  Cases_on `v` >> gvs[lookup_function_def] >> metis_tac[]
QED

Theorem ifexp_callable_return_map:
  !tops deploying name fm nr args dflts ret body.
    ALL_DISTINCT (supported_function_names tops) /\
    lookup_callable_function deploying name tops = SOME (fm,nr,args,dflts,ret,body) ==>
    build_func_return_type tops name = ret
Proof
  rpt strip_tac >>
  gvs[lookup_callable_function_def, AllCaseEqs()]
  >- metis_tac[ifexp_deploy_return_map] >>
  drule lookup_function_Internal_SOME_MEM >> strip_tac >>
  irule build_func_return_type_distinct >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED
