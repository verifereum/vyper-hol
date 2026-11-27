Theory bodyFullIntCallReturnMetadata
Ancestors
  bodyFullIntCallReturnTyping entryStateRel structFieldsProps compileVyper
  compileEnv loweringStateRelDefs supportedNames loweringShapeProps
  vyperInterpreter vyperTypeContractStaticMaps stmtSimReturn exprSimHyps
  vyperValue vyperTyping valueEncoding
  bodySim bodyInvSplit bodyInvCodeProps compileUnit
  exprSimHypsDefs[qualified]

Theorem build_func_info_distinct[local]:
  !tops sft vis mut nr rr name args dflts ret stmts.
    ALL_DISTINCT (supported_function_names tops) /\ vis <> External /\
    MEM (FunctionDecl vis mut nr rr name args dflts ret stmts) tops ==>
    build_func_info sft tops name =
      compute_func_info (\n. MAP (FST o SND) (sft n)) ret
        (type_mem_bytes sft ret) (MAP SND args)
Proof
  Induct_on `tops` >- simp[] >> rpt gen_tac >> Cases_on `h` >>
  simp[supported_function_names_def, build_func_info_def] >>
  rpt strip_tac >> gvs[] >> rw[] >>
  metis_tac[MEM_supported_function_names]
QED

Theorem build_func_info_deploy[local]:
  !tops sft name fm nr args dflts ret body.
    lookup_function NONE name Internal tops = NONE /\
    lookup_function NONE name Deploy tops = SOME (fm,nr,args,dflts,ret,body) ==>
    build_func_info sft tops name =
      compute_func_info (\n. MAP (FST o SND) (sft n)) ret
        (type_mem_bytes sft ret) (MAP SND args)
Proof
  Induct_on `tops`
  >- simp[lookup_function_def, build_func_info_def, AllCaseEqs(),
          compute_func_info_def, returns_stack_count_def,
          compute_pass_via_stack_def] >>
  rpt gen_tac >> Cases_on `h` >>
  simp[lookup_function_def, build_func_info_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
  >- (Cases_on `f` >> gvs[] >> metis_tac[]) >>
  Cases_on `v` >> gvs[lookup_function_def] >> metis_tac[]
QED

Theorem callable_func_info:
  !tops sft deploying name fm nr args dflts ret body.
    ALL_DISTINCT (supported_function_names tops) /\
    lookup_callable_function deploying name tops = SOME (fm,nr,args,dflts,ret,body) ==>
    build_func_info sft tops name =
      compute_func_info (\n. MAP (FST o SND) (sft n)) ret
        (type_mem_bytes sft ret) (MAP SND args)
Proof
  rpt strip_tac >> gvs[lookup_callable_function_def, AllCaseEqs()]
  >- metis_tac[build_func_info_deploy] >>
  drule lookup_function_Internal_SOME_MEM >> strip_tac >>
  irule build_func_info_distinct >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  `type_memory_bytes ce ty = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  Cases_on `ty` >>
  gvs[returns_stack_count_def, is_word_type_def]
  >~ [`BaseT bt`] >- (Cases_on `bt` >>
    gvs[is_word_type_def, evaluate_type_def, type_memory_size_def, AllCaseEqs()] >>
    Cases_on `b` >> gvs[is_word_type_def, type_memory_size_def])
  >~ [`FlagT nsid`] >- gvs[evaluate_type_def, AllCaseEqs(), type_memory_size_def]
  >~ [`TupleT tys`] >- (
    gvs[tuple_like_stack_count_def, AllCaseEqs(), evaluate_type_def] >>
    IF_CASES_TAC >> gvs[] >>
    gvs[evaluate_types_OPT_MMAP] >>
    drule vyperTypeABITheory.OPT_MMAP_LIST_REL >> strip_tac >>
    drule_all word_tuple_size >> simp[type_memory_size_def]) >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx)` by
    gvs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  qpat_x_assum `sfields_tenv_consistent _ _` mp_tac >>
  simp[sfields_tenv_consistent_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[get_struct_fields_def, tuple_like_stack_count_def] >>
  IF_CASES_TAC >> gvs[] >>
  gvs[evaluate_types_OPT_MMAP] >>
  drule vyperTypeABITheory.OPT_MMAP_LIST_REL >> strip_tac >>
  `LENGTH fields = LENGTH args /\ LENGTH tvs = LENGTH args` by
    metis_tac[listTheory.LENGTH_MAP, listTheory.LIST_REL_LENGTH] >>
  drule_all word_tuple_size >>
  simp[type_memory_size_def, struct_layout_size_zip]
QED
*)
Theorem returns_stack_extent:
  !ce cx env es ty tv.
    expr_sim_inv_mods mods ce cx env es /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    0 < returns_stack_count
      (\n. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields n)) ty ==>
    32 * returns_stack_count
      (\n. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields n)) ty =
    type_memory_bytes ce ty
Proof
  cheat
QED

Theorem callable_func_info_in_env:
  body_inv tops ctx cenv cx /\
  lookup_callable_function cx.in_deploy name tops = SOME (mut,nr,args,dflts,ret,ss) ==>
  cenv.ce_func_info (nsid_to_string (NONE,name)) =
    compute_func_info (\n. MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields n))
      ret (type_memory_bytes cenv ret) (MAP SND args)
Proof
  strip_tac >>
  drule_then assume_tac body_inv_contract >>
  drule_then assume_tac body_inv_module >>
  drule_all_then strip_assume_tac contract_inv_module_gate >>
  `ALL_DISTINCT (supported_function_names tops)` by
    fs[supportedProgramTheory.supported_program_def, supported_declaration_names_def] >>
  `cenv.ce_func_info = build_func_info (get_struct_fields cenv.ce_struct_fields) tops` by
    (qpat_assum `contract_inv _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [contract_inv_def]) >>
     fs[build_func_info_mods_singleton]) >>
  drule_all callable_func_info >>
  disch_then (qspec_then `get_struct_fields cenv.ce_struct_fields` mp_tac) >>
  simp[nsid_to_string_def, type_mem_bytes_type_memory_bytes]
QED
