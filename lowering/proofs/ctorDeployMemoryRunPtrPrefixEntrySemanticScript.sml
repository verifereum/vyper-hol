Theory ctorDeployMemoryRunPtrPrefixEntrySemantic
Ancestors
  ctorDeployLoweringFrame ctorDeployMemoryRunPtrPrefixEntryImmutable
  ctorDeployDefs e2eDeployDefs e2eDefs e2eEntry compileEnv compileVyper
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

Theorem deploy_ptr_module_lookup_immutable_frame[local]:
  !tops sft off key loc.
    ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
    FLOOKUP (add_module_var_locations tops FEMPTY) key = SOME loc ==>
    FLOOKUP (add_immutable_locations sft tops off
      (add_module_var_locations tops FEMPTY)) key = SOME loc
Proof
  rpt gen_tac >> strip_tac >>
  `!vis name ty slot.
     MEM (VariableDecl vis Immutable name ty slot) tops ==>
     (NONE, name) <> key` by
    (rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
     drule_then (qspecl_then
       [`FEMPTY`, `VariableDecl vis Immutable name ty slot`, `name`] mp_tac)
       add_module_var_locations_mem >>
     simp[toplevel_vtype_keys_toplevel_def] >>
     Cases_on `slot` >> simp[add_module_var_locations_def]) >>
  drule add_immutable_locations_lookup_unchanged >> simp[]
QED

Theorem deploy_ptr_storage_vars_immutable[local]:
  !tops am tx cenv cx.
    supported_declaration_headers tops /\
    ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
    source_deployment_rel tops am tx /\
    cx.sources = am.sources /\ cx.layouts = am.layouts /\
    cx.txn.target = tx.target /\ cenv.ce_module = NONE /\
    cenv.ce_module_vars = add_immutable_locations
      (get_struct_fields (make_struct_fields_map tops)) tops 0
      (add_module_var_locations tops FEMPTY) ==>
    storage_vars_rel cenv cx /\ transient_vars_rel cenv cx
Proof
  rpt gen_tac >> strip_tac >>
  `storage_vars_rel (cenv with ce_module_vars := add_module_var_locations tops FEMPTY) cx /\
   transient_vars_rel (cenv with ce_module_vars := add_module_var_locations tops FEMPTY) cx` by
    (irule entry_storage_vars_rel >> simp[] >>
     qexistsl_tac [`am`, `tops`, `tx`] >> simp[]) >>
  `!key slot.
    (FLOOKUP (add_immutable_locations
      (get_struct_fields (make_struct_fields_map tops)) tops 0
      (add_module_var_locations tops FEMPTY)) key = SOME (StorageLoc slot) <=>
     FLOOKUP (add_module_var_locations tops FEMPTY) key = SOME (StorageLoc slot)) /\
    (FLOOKUP (add_immutable_locations
      (get_struct_fields (make_struct_fields_map tops)) tops 0
      (add_module_var_locations tops FEMPTY)) key = SOME (TransientLoc slot) <=>
     FLOOKUP (add_module_var_locations tops FEMPTY) key = SOME (TransientLoc slot))` by
    (rpt gen_tac >> conj_tac >> eq_tac >> strip_tac
     >- (drule add_immutable_locations_FLOOKUP >> simp[])
     >- (irule deploy_ptr_module_lookup_immutable_frame >> simp[])
     >- (drule add_immutable_locations_FLOOKUP >> simp[])
     >- (irule deploy_ptr_module_lookup_immutable_frame >> simp[])) >>
  `!src ts. get_module_code cx src = SOME ts ==> src = NONE /\ ts = tops` by
    (gvs[source_deployment_rel_def, get_module_code_def] >> Cases >> simp[]) >>
  gvs[storage_vars_rel_def, transient_vars_rel_def] >>
  conj_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  first_assum drule_all >> simp[]
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
  irule deploy_ptr_storage_vars_immutable >>
  conj_tac >- simp[] >>
  qexistsl_tac [`am with <|sources := (tx.target,[(NONE,tops)])::am.sources;
                         exports := []|>`, `tops`, `tx`] >>
  simp[deploy_evaluation_context_def, initial_evaluation_context_def,
       source_deployment_rel_def, layouts_agree_def] >>
  fs[deploy_source_ok_def, supported_program_def, deploy_state_rel_def,
     layouts_agree_def]
QED
