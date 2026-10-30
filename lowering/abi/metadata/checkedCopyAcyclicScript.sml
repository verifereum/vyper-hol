(* TOP-LEVEL: successful main-module checking establishes acyclicity of the
   actual compiler metadata, including nested and forward-declared structs. *)
Theory checkedCopyAcyclic
Ancestors
  copyAccessibility copyAcyclicProps structSourceProps typedCopyMetadata typedCopyProducer
  typedCopyDomain compileVyper compileEnv vyperContext vyperTypeContract vyperTypeSystem
  vyperValue vyperAST finite_map relation list pair combin

Theorem check_contract_struct_fields_assignable:
  !in_deploy layouts addr mods art src tops name fields.
    check_contract in_deploy layouts addr mods = SOME art /\ MEM (src,tops) mods /\
    MEM (StructDecl name fields) tops ==>
    EVERY (assignable_type (type_env_all_modules mods) o SND) fields
Proof
  rpt strip_tac >> gvs[check_contract_def] >>
  `check_module in_deploy layouts addr mods
    (build_contract_type_artifact in_deploy mods) (src,tops)` by fs[EVERY_MEM] >>
  `check_toplevel_decl layouts addr mods
    (build_contract_type_artifact in_deploy mods) src (StructDecl name fields)` by
    (qpat_x_assum `check_module _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [check_module_def, EVERY_MEM] >> strip_tac >>
     first_x_assum irule >> simp[]) >>
  gvs[check_toplevel_decl_def, o_DEF] >>
  qpat_x_assum `EVERY _ fields` mp_tac >> simp[EVERY_MEM, FORALL_PROD]
QED

Theorem checked_main_struct_fields_assignable:
  !tops in_deploy layouts addr art name fields.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    MEM (StructDecl name fields) tops ==>
    EVERY (assignable_type (type_env tops) o SND) fields
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`in_deploy`, `layouts`, `addr`, `[(NONE,tops)]`, `art`, `NONE`,
    `tops`, `name`, `fields`] check_contract_struct_fields_assignable) >>
  simp[type_env_all_modules_def, type_env_def]
QED

Theorem checked_copy_source_agrees:
  !tops in_deploy layouts addr art.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art ==>
    copy_source_agrees (make_struct_fields_map tops) (type_env tops)
Proof
  rpt strip_tac >> simp_tac bool_ss [copy_source_agrees_def] >> rpt strip_tac >>
  drule_all checked_struct_metadata_types >> strip_tac >> simp[get_struct_fields_def]
QED

Theorem assignable_list_copy_accessible:
  !sf tenv tys. copy_source_agrees sf tenv /\ EVERY (assignable_type tenv) tys ==>
    EVERY (WFP (type_copy_child sf)) tys
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [EVERY_MEM] >>
  qx_gen_tac `ty` >> DISCH_TAC >> `assignable_type tenv ty` by fs[EVERY_MEM] >>
  mp_tac (Q.SPECL [`tenv`, `ty`] assignable_type_copy_accessible) >> simp[]
QED

Theorem checked_copy_fields_accessible:
  !tops in_deploy layouts addr art name.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art ==>
    EVERY (WFP (type_copy_child (make_struct_fields_map tops)))
      (MAP (FST o SND) (get_struct_fields (make_struct_fields_map tops) name))
Proof
  rpt gen_tac >> DISCH_TAC >>
  `copy_source_agrees (make_struct_fields_map tops) (type_env tops)` by
    (drule_all checked_copy_source_agrees >> simp[]) >>
  Cases_on `FLOOKUP (make_struct_fields_map tops) name`
  >- simp[get_struct_fields_def] >>
  rename1 `FLOOKUP (make_struct_fields_map tops) name = SOME fields` >>
  drule make_struct_fields_origin >> strip_tac >>
  `EVERY (assignable_type (type_env tops) o SND) args` by
    (drule_all checked_main_struct_fields_assignable >> simp[]) >>
  `EVERY (assignable_type (type_env tops)) (MAP SND args)` by fs[EVERY_MAP, o_DEF] >>
  mp_tac (Q.SPECL [`make_struct_fields_map tops`, `type_env tops`, `MAP SND (args:(string # type) list)`]
    assignable_list_copy_accessible) >> simp[get_struct_fields_def]
QED

Theorem checked_struct_metadata_well_founded:
  !tops in_deploy layouts addr art.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art ==>
    WF (type_copy_child (make_struct_fields_map tops))
Proof
  rpt strip_tac >> irule copy_fields_accessible_well_founded >> gen_tac >>
  drule_all checked_copy_fields_accessible >> simp[]
QED

Theorem checked_struct_metadata_acyclic:
  !tops in_deploy layouts addr art.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art ==>
    acyclic_struct_metadata (make_struct_fields_map tops)
Proof
  rpt strip_tac >> irule wf_type_copy_child_acyclic >>
  drule_all checked_struct_metadata_well_founded >> simp[]
QED

Theorem checked_compile_env_struct_metadata_acyclic:
  !tops in_deploy layouts addr art vis mut name args ret stmts transient.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art ==>
    acyclic_struct_metadata
      (build_compile_env tops vis mut name args ret stmts transient).ce_struct_fields
Proof
  simp[build_compile_env_ce_struct_fields] >> rpt strip_tac >>
  drule_all checked_struct_metadata_acyclic >> simp[]
QED
