(* Supported assignment targets have only flat storage subscripts. *)
Theory supportedTargetSimPtr
Ancestors
  supportedTargetArrayPtr assignTupleResidualBoundary bodyPtrPopSeamTargetSim
  bodyPtrPopTargetSimMapping bodyPtrPopTargetSimRoots
  bodyPtrPopTargetDefs bodyPtrDefs bodyPtrPreds bodySim
  targetPlaceSim targetPlaceSimDefs targetPlaceLive supportedStmts
  vyperTypeSystem vyperTyping vyperAST list

Theorem supported_target_sim_ptr:
  !bt tops bindings ctx cenv cx env es d PG func.
    supported_target tops bindings bt /\
    body_inv tops ctx cenv cx /\
    body_base_target_ptr_ok cx bt /\
    target_pre cenv cx env bt es ==>
    target_sim_ptr d ctx PG func cenv cx env bt es
Proof
  rpt gen_tac >> strip_tac >> Cases_on `bt`
  >- (irule target_name_sim_ptr >> simp[])
  >- (rename1 `TopLevelNameTarget nsid` >> PairCases_on `nsid` >>
      irule target_toplevel_sim_ptr >> simp[])
  >- (rename1 `SubscriptTarget inner key` >>
      drule supported_subscript_target_base >> strip_tac >> gvs[] >>
      PairCases_on `nsid` >>
      `target_pre cenv cx env (TopLevelNameTarget (nsid0,nsid1)) es` by
        metis_tac[target_pre_sub] >>
      `target_sim_ptr d ctx PG func cenv cx env
        (TopLevelNameTarget (nsid0,nsid1)) es` by
        metis_tac[target_toplevel_sim_ptr] >>
      Cases_on `type_place_target env
        (SubscriptTarget (TopLevelNameTarget (nsid0,nsid1)) key)`
      >- simp[target_sim_ptr_def] >>
      qpat_x_assum `type_place_target _ (SubscriptTarget _ _) = _` mp_tac >>
      simp[Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >>
      Cases_on `vt` >> gvs[subscript_vtype_def, AllCaseEqs()]
      >- (rename1 `type_place_target env _ = SOME (Type ty)` >>
          Cases_on `ty` >> gvs[subscript_vtype_def, AllCaseEqs()] >>
          irule target_toplevel_array_sim_ptr >> metis_tac[]) >>
      irule target_mapping_sim_ptr >> metis_tac[]) >>
  rename1 `AttributeTarget inner fld` >>
  Cases_on `inner` >> fs[supported_target_def] >>
  irule body_target_sim_ptr >>
  simp[target_root_def, target_indices_def] >> metis_tac[]
QED
