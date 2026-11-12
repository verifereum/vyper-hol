Theory bodyPtrPopTargetSimCases
Ancestors
  bodyPtrPopTargetSimArrayConstructor bodyPtrPopTargetSimMapping
  bodyPtrPopTargetSimRoots bodyPtrPopTargetSimAttribute
  bodyPtrPopTargetSimBoundary vyperTypeSystem targetPlaceSimDefs targetPlaceSim

Theorem target_subscript_sim_ptr:
  body_inv tops ctx cenv cx /\
  body_base_target_ptr_ok cx (SubscriptTarget bt e) /\
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  (!id. target_root bt = NameTarget id ==>
        local_target_live cx id (SubscriptTarget bt e)) /\
  (!src id. target_root bt = TopLevelNameTarget (src,id) ==>
        EVERY pure_expr (target_indices (SubscriptTarget bt e))) /\
  target_sim_ptr d ctx PG func cenv cx env bt es ==>
  target_sim_ptr d ctx PG func cenv cx env (SubscriptTarget bt e) es
Proof
  strip_tac >>
  Cases_on `type_place_target env (SubscriptTarget bt e)`
  >- simp[bodyPtrPopTargetDefsTheory.target_sim_ptr_def] >>
  qpat_x_assum `type_place_target _ (SubscriptTarget _ _) = _` mp_tac >>
  simp[Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >>
  Cases_on `vt` >> gvs[subscript_vtype_def, AllCaseEqs()]
  >- (rename1 `type_place_target env bt = SOME (Type ty)` >>
      Cases_on `ty` >> gvs[subscript_vtype_def, AllCaseEqs()] >>
      irule target_array_sim_ptr >> metis_tac[]) >>
  irule target_mapping_sim_ptr >> metis_tac[]
QED
