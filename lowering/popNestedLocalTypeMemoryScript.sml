(* Static type correspondence for targets rooted in local variables. *)
Theory popNestedLocalTypeMemory
Ancestors
  allocLimits targetPlaceSim stmtSimAssignAttr vyperTypeEnv exprSimHypsDefs
  vyperTypeSystem vyperTypeInvariants

Theorem local_target_place_vtype:
  !bt id vt.
    target_root bt = NameTarget id /\
    expr_sim_inv cenv cx env es /\
    type_place_target env bt = SOME vt ==>
    ?ty. vt = Type ty /\ target_place_type cenv bt = SOME (ValPT ty)
Proof
  measureInduct_on `base_assignment_target_size bt` >>
  Cases_on `bt` >> rpt gen_tac >>
  simp[target_root_def, type_place_target_NameTarget,
       type_place_target_TopLevelNameTarget,
       type_place_target_AttributeTarget,
       type_place_target_SubscriptTarget] >>
  strip_tac
  >- (gvs[target_place_type_def] >> metis_tac[expr_sim_inv_def])
  >- (first_x_assum (qspec_then `b` mp_tac) >> simp[] >>
      strip_tac >> gvs[] >>
      Cases_on `ty` >> gvs[subscript_vtype_def, AllCaseEqs()] >>
      simp[target_place_type_def])
  >> first_x_assum (qspec_then `b` mp_tac) >> simp[] >>
  strip_tac >> gvs[] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  Cases_on `tgt_ty` >>
  gvs[attribute_type_def, AllCaseEqs()] >>
  `attribute_type (get_tenv cx) (StructT p) s = SOME ty` by
    simp[attribute_type_def] >>
  drule_all attribute_type_struct_field >> strip_tac >>
  simp[target_place_type_def]
QED

Theorem pop_nested_local_target_place_type:
  target_root bt = NameTarget id /\
  expr_sim_inv cenv cx env es /\
  type_place_target env bt = SOME (Type ty) ==>
  target_place_type cenv bt = SOME (ValPT ty)
Proof
  strip_tac >> drule_all local_target_place_vtype >> simp[]
QED
