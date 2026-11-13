Theory targetStorageDomain
Ancestors
  targetPlaceSim supportedProgram supportedTargets supportedTypes supportedDecls
  supportedExprForms alist

Theorem supported_target_storage_domain:
  !bt pt nid.
    supported_program tops /\
    supported_target_info tops bindings bt = SOME pt /\
    target_root bt = TopLevelNameTarget nid ==>
    (case pt of ValPT ty => supported_storage_type tops ty
     | MapPT kt vt => supported_hashmap_key_type kt /\ supported_hashmap_value tops vt)
Proof
  `(!e:expr. T) /\ (!bt. !pt nid.
    supported_program tops /\
    supported_target_info tops bindings bt = SOME pt /\
    target_root bt = TopLevelNameTarget nid ==>
    (case pt of ValPT ty => supported_storage_type tops ty
     | MapPT kt vt => supported_hashmap_key_type kt /\ supported_hashmap_value tops vt))`
    suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[target_root_def, supported_target_info_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()]
  >~ [`supported_place_root tops id`] >- (
    gvs[supported_place_root_def, AllCaseEqs(), supported_program_def,
        supported_declaration_headers_def, optionTheory.option_case_compute] >>
    rename1 `supported_variable_decl tops _ = SOME (_,mut,_,_)` >>
    Cases_on `mut` >> gvs[])
  >~ [`supported_hashmap_decl tops p = SOME _`] >- (
    gvs[supported_program_def, supported_declaration_headers_def] >>
    drule_all supported_hashmap_decl_header >> simp[]) 
  >~ [`value_type_place vt`] >- (
    Cases_on `vt` >> gvs[exprLoweringTheory.value_type_place_def, supported_hashmap_value_def]) 
  >~ [`supported_storage_type tops elem`] >- (
    Cases_on `bound` >> gvs[supported_storage_array_depth]) >>
  metis_tac[supported_storage_field]
QED
