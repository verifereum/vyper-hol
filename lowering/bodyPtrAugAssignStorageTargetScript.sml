Theory bodyPtrAugAssignStorageTarget
Ancestors
  bodyPtrAugAssignStorageArrayPrefix bodyPtrAugAssignStorageArraySuffix
  bodyPtrPopTargetSimRoots bodyPtrPopTargetSimAttribute bodyPtrPopTargetSimMapping
  bodyPtrPopTargetSimCases bodyPtrPopTargetSimBoundary bodyPtrPopTargetDefs
  bodyPtrPreds bodyPtrDefs targetPlaceSim targetPlaceSimDefs targetPlaceSimCasesBase
  supportedTargets supportedExprs stmtSimAugAssignPlaceStorage targetPlaceLive
  vyperAST vyperInterpreter vyperState exprSimHypsDefs exprSimSource list vyperTypeSystem

Theorem augassign_storage_target_sim_ptr:
  !t tops ctx cenv cx env es d PG func.
    body_inv tops ctx cenv cx /\ body_base_target_ptr_ok cx t /\
    target_pre cenv cx env t es /\
    (?nsid. target_root t = TopLevelNameTarget nsid) /\
    EVERY (supported_pure_expr tops) (target_indices t) ==>
    target_sim_ptr d ctx PG func cenv cx env t es
Proof
  recInduct base_assignment_target_induct >> rpt conj_tac >> rpt gen_tac >> strip_tac
  >- gvs[target_root_def]
  >- (rename1 `TopLevelNameTarget ns` >> PairCases_on `ns` >>
      irule target_toplevel_sim_ptr >> simp[])
  >- suspend "subscript" >>
  rpt gen_tac >> strip_tac >>
  irule target_attribute_sim_ptr >> simp[] >> first_x_assum irule >>
  fs[target_root_def, target_indices_def] >>
  metis_tac[target_pre_sub, body_base_target_ptr_ok_def]
QED

Resume augassign_storage_target_sim_ptr[subscript]:
  rpt gen_tac >> strip_tac >>
  `target_sim_ptr d ctx PG func cenv cx env bt es` by
    (first_x_assum irule >> fs[target_root_def, target_indices_def, EVERY_APPEND] >>
     metis_tac[target_pre_sub, body_base_target_ptr_ok_def]) >>
  Cases_on `type_place_target env (SubscriptTarget bt e)`
  >- simp[target_sim_ptr_def] >>
  qpat_x_assum `type_place_target _ (SubscriptTarget _ _) = _` mp_tac >>
  simp[Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >>
  Cases_on `vt` >> gvs[subscript_vtype_def, AllCaseEqs()]
  >- (rename1 `type_place_target env bt = SOME (Type ty)` >>
      Cases_on `ty` >> gvs[subscript_vtype_def, AllCaseEqs()] >>
      irule (MATCH_MP augassign_storage_array_sim_ptr_using_suffix
        augassign_storage_array_normal_suffix_ptr) >>
      fs[target_root_def] >> metis_tac[]) >>
  irule target_mapping_sim_ptr >> metis_tac[]
QED

Finalise augassign_storage_target_sim_ptr
