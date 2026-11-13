(* Task-only provenance for the selected runtime's internal return table. *)
Theory externalReturnDeclarationProvenance
Ancestors
  externalReturnBufferlessCopyProbe externalReturnIntcallMetadata
  e2eDefs supportedNames supportedProgram vyperContext vyperInterpreter
  compileVyper compileEnv vyperTypeContractContext vyperTypeContractStaticMaps

Theorem return_runtime_module:
  source_deployment_rel tops am tx /\
  get_module_code (initial_evaluation_context am.sources am.layouts tx NONE)
    sid = SOME ts ==> sid = NONE /\ ts = tops
Proof
  simp[source_deployment_rel_def, get_module_code_def,
    initial_evaluation_context_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `sid` >> gvs[]
QED

Theorem return_runtime_not_deploy:
  ~(initial_evaluation_context sources layouts tx NONE).in_deploy
Proof
  simp[initial_evaluation_context_def]
QED

Theorem return_internal_lookup_name[local]:
  !tops name fm nr params dflts ret body.
  lookup_function NONE name Internal tops =
    SOME (fm,nr,params,dflts,ret,body) ==>
  MEM name (supported_function_names tops)
Proof
  Induct_on `tops` >> simp[lookup_function_def] >>
  Cases_on `h` >> simp[lookup_function_def, supported_function_names_def]
  >~ [`VariableDecl vis`] >- (Cases_on `vis` >> simp[lookup_function_def])
  >~ [`HashMapDecl vis`] >- (Cases_on `vis` >> simp[lookup_function_def]) >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem return_internal_table_distinct[local]:
  !tops name fm nr params dflts ret body.
  ALL_DISTINCT (supported_function_names tops) /\
  lookup_function NONE name Internal tops =
    SOME (fm,nr,params,dflts,ret,body) ==>
  build_func_return_type tops name = ret
Proof
  Induct_on `tops` >> simp[lookup_function_def] >>
  Cases_on `h` >>
  simp[supported_function_names_def, lookup_function_def,
    build_func_return_type_def]
  >~ [`VariableDecl vis`] >- (Cases_on `vis` >> simp[lookup_function_def])
  >~ [`HashMapDecl vis`] >- (Cases_on `vis` >> simp[lookup_function_def]) >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  rpt IF_CASES_TAC >> gvs[] >> metis_tac[return_internal_lookup_name]
QED

Theorem return_runtime_callable_table:
  !tops name fm nr params dflts ret body.
  supported_program tops /\
  lookup_callable_function F name tops =
    SOME (fm,nr,params,dflts,ret,body) ==>
  build_func_return_type tops name = ret
Proof
  simp[lookup_callable_function_def, AllCaseEqs()] >> rpt strip_tac >>
  drule supported_program_names >>
  simp[supported_declaration_names_def] >> strip_tac >>
  metis_tac[return_internal_table_distinct]
QED

Theorem return_runtime_physical_widens:
  source_deployment_rel tops am tx /\ supported_program tops /\
  ce.ce_func_return_type = build_func_return_type tops /\
  env_consistent env
    (initial_evaluation_context am.sources am.layouts tx NONE) es /\
  well_typed_expr env (Call ann (IntCall (sid,name)) args drv) ==>
  type_widens_to env.type_defs
    (ce.ce_func_return_type (nsid_to_string (sid,name))) ann
Proof
  strip_tac >> drule_all return_bufferless_typed_intcall_decl >> strip_tac >>
  drule_all return_runtime_module >> strip_tac >> gvs[] >>
  gvs[return_runtime_not_deploy] >>
  drule_all return_runtime_callable_table >>
  simp[nsid_to_string_def] >> metis_tac[]
QED

Theorem return_singleton_type_env[local]:
  type_env_all_modules [(NONE,tops)] = type_env tops
Proof
  simp[type_env_all_modules_def, type_env_def, finite_mapTheory.FUNION_FEMPTY_2]
QED

Theorem return_runtime_physical_evaluate:
  source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\ supported_program tops /\
  ce.ce_func_return_type = build_func_return_type tops /\
  env_consistent env
    (initial_evaluation_context am.sources am.layouts tx NONE) es /\
  well_typed_expr env (Call ann (IntCall (sid,name)) args drv) ==>
  ?ptv. evaluate_type (type_env tops)
    (ce.ce_func_return_type (nsid_to_string (sid,name))) = SOME ptv
Proof
  strip_tac >> drule_all return_bufferless_typed_intcall_decl >> strip_tac >>
  drule_all return_runtime_module >> strip_tac >> gvs[] >>
  gvs[return_runtime_not_deploy] >>
  drule_all return_runtime_callable_table >> strip_tac >>
  drule lookup_callable_function_F_SOME_MEM >> strip_tac >>
  gvs[source_typing_ok_def] >>
  drule check_contract_main_module_allocated >> simp[] >> strip_tac >>
  `check_function_body am.layouts tx.target [(NONE,tops)] art NONE
     Internal fm nr params dflts sig.ret_ty body'` by
    (irule check_contract_runtime_function_body_MEM >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  gvs[vyperTypeContractTheory.check_function_body_def, return_singleton_type_env,
    nsid_to_string_def, optionTheory.IS_SOME_EXISTS]
QED
