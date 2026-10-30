(* Semantic byte sizes at actual struct callers, including forward references.
   Child types are evaluated with the parent removed, then restored to the
   complete environment used by the compiler's field-size construction. *)
Theory abiCallerStructSize
Ancestors
  abiCallerStructFields abiCallerTypeEnv compileVyper compileEnv valueEncoding
  vyperTypeABI vyperContext vyperValue finite_map list pair combin arithmetic

Theorem abi_caller_struct_fields_total:
  !fields tvs.
  LIST_REL (\ty tv. evaluate_type env ty = SOME tv) (MAP SND fields) tvs ==>
  SUM (MAP (SND o SND) (build_struct_fields_one env fields)) =
    type_memory_size_fields (ZIP (MAP FST fields,tvs))
Proof
  Induct_on `fields`
  >- (Cases >> simp[build_struct_fields_one_def, type_memory_size_def]) >>
  qx_gen_tac `field_arg` >> Cases_on `field_arg` >> Cases >>
  simp[build_struct_fields_one_def, type_memory_size_def] >>
  rpt strip_tac >> fs[build_struct_fields_one_def, field_mem_bytes_def] >>
  qpat_x_assum `!tvs. LIST_REL _ _ tvs ==> _` drule >> simp[ADD_COMM]
QED

Theorem abi_caller_struct_memory_size:
  !tops vis mut func_name fargs ret_type (code_stmts:stmt list) use_trans
    in_deploy name tv.
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  evaluate_type (type_env tops) (StructT (NONE,name)) = SOME tv ==>
  type_memory_bytes
    (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans)
    (StructT (NONE,name)) = type_memory_size tv
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `evaluate_type _ _ = SOME _`
    (mp_tac o ONCE_REWRITE_RULE [evaluate_type_def]) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `FLOOKUP (type_env tops) (NONE,name) = SOME (StructArgs fields)` >>
  rename1 `evaluate_types _ _ [] = SOME field_tvs` >>
  `FLOOKUP
     (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans).
       ce_struct_fields name = SOME (build_struct_fields_one (type_env tops) fields)` by
    (irule abi_caller_constructed_struct_fields >> simp[] >>
     qexists_tac `in_deploy` >> first_assum ACCEPT_TAC) >>
  drule evaluate_types_LIST_REL >> strip_tac >>
  simp[type_memory_bytes_def, nsid_to_string_def, get_struct_fields_def,
       type_memory_size_def] >>
  irule abi_caller_struct_fields_total >>
  irule LIST_REL_mono >>
  qexists_tac `\ty tv.
    evaluate_type ((type_env tops) \\ (NONE,name)) ty = SOME tv` >>
  asm_simp_tac bool_ss [] >> rpt strip_tac >>
  drule (cj 1 vyperTypeExprSoundnessTheory.evaluate_type_mono) >> simp[]
QED
