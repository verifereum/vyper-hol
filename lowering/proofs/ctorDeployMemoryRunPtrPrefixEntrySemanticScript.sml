Theory ctorDeployMemoryRunPtrPrefixEntrySemantic
Ancestors
  ctorDeployMemoryRunMemEntryLanding
  compileEnv
  ctorDeployLoweringFrame ctorDeployLoweringEntryImmutableMemory ctorDeployLoweringNoCtor
  ctorDeployDefs e2eDeployDefs e2eDefs e2eEntry compileVyper
  immutableLocationProps immutableRelation entryStateRel entryLocals
  vyperTypeContract vyperTypeContractStaticMaps supportedProgram supportedDecls
  finite_map list alist vyperContext vyperInterpreter

Theorem deploy_ptr_ctor_environment:
  !tops rp runtime unit body ce nr key ut imm exit sa sb sj se sp sf func.
  deploy_ctor_code tops rp runtime unit
    (body,ce,nr,key,ut,imm,exit,sa,sb,sj,se,sp,sf,func) ==>
  immutable_section_layout ce tops /\ ce.ce_module = NONE /\ ce.ce_is_ctor
Proof
  rpt gen_tac >> strip_tac >>
  drule deploy_ctor_module_locations >> strip_tac >>
  drule deploy_ctor_return_metadata >> strip_tac >> simp[] >>
  qspecl_then [`tops`, `Deploy`, `Pure`, `"__init__"`, `[]`, `NoneT`, `[]`, `F`]
    mp_tac immutable_build_compile_env_layout >>
  simp[immutable_section_layout_def, build_compile_env_module_vars]
QED



Theorem deploy_ptr_source_variable_names_distinct[local]:
  deploy_source_ok tops am tx ==>
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))
Proof
  simp[deploy_source_ok_def, deploy_typing_ok_def] >>
  rpt strip_tac >>
  qpat_x_assum `check_contract T _ _ _ = _` mp_tac >>
  simp[check_contract_def, contract_namespaces_ok_def,
       contract_keys_def, AllCaseEqs()] >>
  strip_tac >> asm_rewrite_tac[]
QED

Theorem deploy_ptr_ctor_storage_vars:
  !tops am tx bc es rp runtime unit body ce nr key ut imm exit sa sb sj se sp sf func.
  deploy_source_ok tops am tx /\ deploy_state_rel tops bc am tx es /\
  deploy_ctor_code tops rp runtime unit
    (body,ce,nr,key,ut,imm,exit,sa,sb,sj,se,sp,sf,func) ==>
  storage_vars_rel ce (deploy_evaluation_context tops am tx) /\
  transient_vars_rel ce (deploy_evaluation_context tops am tx)
Proof
  rpt gen_tac >> strip_tac >>
  drule deploy_ptr_source_variable_names_distinct >> strip_tac >>
  drule deploy_ctor_module_locations >> strip_tac >>
  irule ctorDeployMemoryRunMemEntryLandingTheory.ctor_landing_storage_layout >>
  conj_tac >- simp[] >>
  qexistsl_tac [`am with <|sources := (tx.target,[(NONE,tops)])::am.sources;
                         exports := []|>`, `tops`, `tx`] >>
  simp[deploy_evaluation_context_def, initial_evaluation_context_def,
       source_deployment_rel_def, layouts_agree_def] >>
  fs[deploy_source_ok_def, supported_program_def, deploy_state_rel_def,
     layouts_agree_def]
QED
