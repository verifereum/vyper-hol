Theory abiCallerStructSize
Ancestors
  compileVyper compileEnv valueEncoding vyperContext vyperValue vyperTypeContract finite_map
  list rich_list combin pair abiCallerTypeEnv vyperTypeABI arithmetic

(* Struct fields and their byte sizes supplied by actual compiler construction.
   Namespace uniqueness comes from the existing checked-contract interface. *)
Theorem abi_caller_struct_field_sizes:
  MEM (name,ty,sz) (build_struct_fields_one env args) /\
  evaluate_type env ty = SOME tv ==>
  MEM (name,ty) args /\ sz = type_memory_size tv
Proof
  simp[build_struct_fields_one_def, field_mem_bytes_def, MEM_MAP, EXISTS_PROD] >>
  rpt strip_tac >> gvs[]
QED

Theorem abi_caller_struct_fields_types:
  MAP (\(name,ty,sz). (name,ty)) (build_struct_fields_one env args) = args
Proof
  Induct_on `args` >- simp[build_struct_fields_one_def] >>
  qx_gen_tac `arg` >> Cases_on `arg` >> fs[build_struct_fields_one_def]
QED

Theorem abi_caller_struct_fields_unchanged:
  !tops env sf name.
  ~MEM ((src:num option),name)
    (FLAT (MAP (type_def_keys_toplevel src) tops)) ==>
  FLOOKUP (build_struct_fields_map env tops sf) name = FLOOKUP sf name
Proof
  Induct_on `tops` >- simp[build_struct_fields_map_def] >>
  qx_gen_tac `top` >> Cases_on `top` >>
  simp[build_struct_fields_map_def, type_def_keys_toplevel_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[FLOOKUP_UPDATE]
QED

Theorem abi_caller_struct_fields_append:
  !pre post env sf.
  build_struct_fields_map env (pre ++ post) sf =
    build_struct_fields_map env post (build_struct_fields_map env pre sf)
Proof
  Induct_on `pre` >- simp[build_struct_fields_map_def] >>
  qx_gen_tac `top` >> Cases_on `top` >> simp[build_struct_fields_map_def]
QED

Theorem abi_caller_struct_fields_member:
  !tops env sf name args.
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  MEM (StructDecl name args) tops ==>
  FLOOKUP (build_struct_fields_map env tops sf) name =
    SOME (build_struct_fields_one env args)
Proof
  rpt strip_tac >>
  qpat_x_assum `MEM (StructDecl name args) tops`
    (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
  rename1 `tops = pre ++ StructDecl name args::post` >>
  gvs[MAP_APPEND, FLAT_APPEND, type_def_keys_toplevel_def, ALL_DISTINCT_APPEND] >>
  simp[abi_caller_struct_fields_append, build_struct_fields_map_def] >>
  asm_simp_tac (srw_ss()) [FLOOKUP_UPDATE,
    Q.INST [`src` |-> `NONE:num option`] abi_caller_struct_fields_unchanged]
QED

Theorem abi_caller_type_env_struct:
  !tops sid name args.
  FLOOKUP (type_env_for_module src tops) (sid,name) = SOME (StructArgs args) ==>
  sid = src /\ MEM (StructDecl name args) tops
Proof
  Induct_on `tops` >- simp[type_env_for_module_def] >>
  qx_gen_tac `top` >> Cases_on `top` >>
  simp[type_env_for_module_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem abi_caller_constructed_struct_fields:
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  FLOOKUP (type_env tops) (NONE,name) = SOME (StructArgs args) ==>
  FLOOKUP
    (build_compile_env tops vis mut func_name fargs ret_type (code_stmts:stmt list) use_trans).
      ce_struct_fields name =
    SOME (build_struct_fields_one (type_env tops) args)
Proof
  strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops))` by
    fs[contract_namespaces_ok_def, contract_keys_def] >>
  qpat_assum `FLOOKUP (type_env tops) _ = _`
    (mp_tac o PURE_REWRITE_RULE [type_env_def]) >> strip_tac >>
  drule_all (Q.INST [`src` |-> `NONE:num option`] abi_caller_type_env_struct) >>
  strip_tac >>
  simp[build_compile_env_ce_struct_fields, make_struct_fields_map_def] >>
  irule abi_caller_struct_fields_member >> simp[]
QED

(* Semantic byte sizes at actual struct callers, including forward references.
   Child types are evaluated with the parent removed, then restored to the
   complete environment used by the compiler's field-size construction. *)
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
