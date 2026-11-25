(* Supported, checked main-module metadata producer. The namespace premise
   is obtained from the real source checker, not a speculative cenv invariant. *)
Theory typedCopyProducer
Ancestors
  typedCopyMetadata typedCopyDomain supportedProgram supportedDecls
  vyperTypeContract vyperTypeContractStaticMaps vyperTypeSystem
  checkedTypeNamespace supportedStmtTraverse
  vyperContext compileVyper alist list pair finite_map

Theorem struct_decl_type_key_member:
  MEM (StructDecl name args) tops ==>
  MEM (src,name) (FLAT (MAP (type_def_keys_toplevel src) tops))
Proof
  strip_tac >> simp[MEM_FLAT] >>
  qexists_tac `type_def_keys_toplevel src (StructDecl name args)` >>
  simp[MEM_MAP, type_def_keys_toplevel_def] >>
  qexists_tac `StructDecl name args` >> simp[type_def_keys_toplevel_def]
QED

Theorem distinct_type_keys_struct_args_unique:
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) ==>
  struct_args_unique tops
Proof
  Induct_on `tops` >- simp[struct_args_unique_def] >>
  Cases_on `h` >> simp[type_def_keys_toplevel_def] >> rpt strip_tac >>
  fs[struct_args_unique_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[struct_decl_type_key_member]
QED

Theorem checked_contract_struct_args_unique:
  check_contract in_deploy layouts addr [(NONE,tops)] = SOME art ==>
  struct_args_unique tops
Proof
  simp[check_contract_def, AllCaseEqs()] >> rpt strip_tac >>
  irule distinct_type_keys_struct_args_unique >>
  fs[contract_namespaces_ok_def, contract_keys_def] >> simp[]
QED

Theorem supported_checked_struct_metadata_acyclic:
  supported_program tops /\
  check_contract in_deploy layouts addr [(NONE,tops)] = SOME art ==>
  acyclic_struct_metadata (make_struct_fields_map tops)
Proof
  strip_tac >> drule_then assume_tac checked_contract_struct_args_unique >>
  `!name fields. MEM (StructDecl name fields) tops ==>
    EVERY (supported_type_namespace o SND) fields` by
    (rpt strip_tac >>
     `check_toplevel_decl [(NONE,tops)] art NONE (StructDecl name fields)` by
       (drule check_contract_toplevel_decl_MEM_checked >> simp[ALOOKUP_def]) >>
     fs[check_toplevel_decl_def, EVERY_MEM, FORALL_PROD, type_env_all_modules_def,
        GSYM type_env_def, FUNION_FEMPTY_2] >>
     metis_tac[singleton_well_formed_type_namespace, assignable_type_well_formed]) >>
  irule make_struct_fields_map_acyclic >> fs[supported_program_def] >>
  first_assum ACCEPT_TAC
QED

Theorem supported_checked_compile_env_struct_metadata_acyclic:
  supported_program tops /\
  check_contract in_deploy layouts addr [(NONE,tops)] = SOME art ==>
  acyclic_struct_metadata
    (build_compile_env tops vis mut name args ret stmts use_transient).ce_struct_fields
Proof
  simp[build_compile_env_ce_struct_fields] >> rpt strip_tac >>
  drule_all supported_checked_struct_metadata_acyclic >> simp[]
QED
