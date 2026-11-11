(* Supported, checked main-module metadata producer. The namespace premise
   is obtained from the real source checker, not a speculative cenv invariant. *)
Theory typedCopyProducer
Ancestors
  typedCopyMetadata typedCopyDomain supportedProgram supportedDecls
  vyperTypeContract compileVyper list pair

Theorem struct_decl_type_key_member:
  MEM (StructDecl name args) tops ==>
  MEM ((NONE:num option),name)
      (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops))
Proof
  Induct_on `tops` >> simp[] >> rpt strip_tac >> gvs[]
  >- simp[type_def_keys_toplevel_def]
  >> Cases_on `h` >> simp[type_def_keys_toplevel_def] >> metis_tac[]
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
  rpt strip_tac >> irule make_struct_fields_map_acyclic >> conj_tac
  >- (drule checked_contract_struct_args_unique >> simp[])
  >> fs[supported_program_def]
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
