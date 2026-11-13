(* Callable return layouts for the if-expression memory leaf. *)
Theory bodyIfExpReturnLayout
Ancestors
  memoryLocalRhsProps supportedProgram supportedNames compileVyper
  vyperTypeContractStaticMaps vyperInterpreter bodySim exprSimHypsDefs
  vyperTypeInvariants

Theorem ifexp_deploy_return_map[local]:
  !tops name fm nr args dflts ret body.
    lookup_function NONE name Internal tops = NONE /\
    lookup_function NONE name Deploy tops = SOME (fm,nr,args,dflts,ret,body) ==>
    build_func_return_type tops name = ret
Proof
  Induct_on `tops` >- simp[lookup_function_def, build_func_return_type_def] >>
  gen_tac >> Cases_on `h` >>
  simp[lookup_function_def, build_func_return_type_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
  >- (Cases_on `f` >> gvs[] >> metis_tac[])
  >- (Cases_on `v` >> gvs[lookup_function_def] >> metis_tac[]) >>
  Cases_on `v` >> gvs[lookup_function_def] >> metis_tac[]
QED

Theorem ifexp_callable_return_map:
  !tops deploy name fm nr args dflts ret body.
    supported_program tops /\
    lookup_callable_function deploy name tops = SOME (fm,nr,args,dflts,ret,body) ==>
    build_func_return_type tops name = ret
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (supported_function_names tops)` by
    fs[supported_program_def, supported_declaration_names_def] >>
  fs[lookup_callable_function_def, AllCaseEqs()]
  >- (drule_all ifexp_deploy_return_map >> simp[]) >>
  drule lookup_function_Internal_SOME_MEM >> strip_tac >>
  irule build_func_return_type_distinct >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem ifexp_body_signature_return:
  !tops ctx cenv cx env es name sig.
    body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
    FLOOKUP env.fn_sigs (NONE,name) = SOME sig ==>
    cenv.ce_func_return_type name = sig.ret_ty
Proof
  rpt strip_tac >>
  `fn_sigs_consistent env.fn_sigs cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  qpat_x_assum `fn_sigs_consistent _ _` mp_tac >>
  simp[fn_sigs_consistent_def] >>
  disch_then drule >> strip_tac >>
  gvs[body_inv_def] >>
  drule_all ifexp_callable_return_map >> simp[]
QED
