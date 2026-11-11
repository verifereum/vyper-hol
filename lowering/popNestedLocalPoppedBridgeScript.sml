Theory popNestedLocalPoppedBridge
Ancestors
  popNestedLocalPoppedPath targetPlaceSim targetPlaceSimCasesBase allocLimits
  vyperTypeSystem vyperAST exprSimHypsDefs loweringStateRelDefs
  finite_map

Theorem local_target_type_only[local]:
  !bt env id vt.
    target_root bt = NameTarget id /\
    type_place_target env bt = SOME vt ==> ?ty. vt = Type ty
Proof
  Induct using base_assignment_target_induct >>
  simp[target_root_def, well_typed_expr_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  Cases_on `ty` >> gvs[subscript_vtype_def] >>
  Cases_on `is_int_type (expr_type e)` >> gvs[]
QED
