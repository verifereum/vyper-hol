Theory popNestedLocalPoppedBridge
Ancestors
  popNestedLocalPoppedPath targetPlaceSim targetPlaceSimCasesBase allocLimits
  vyperTypeSystem vyperAST exprSimHypsDefs loweringStateRelDefs
  finite_map alist rich_list compileEnv vyperTypeInvariants

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

Theorem local_subscript_type[local]:
  target_root bt = NameTarget id /\
  type_place_target env (SubscriptTarget bt e) = SOME (Type ty) ==>
  ?bd. type_place_target env bt = SOME (Type (ArrayT ty bd)) /\
       well_typed_expr env e /\ is_int_type (expr_type e)
Proof
  simp[Once well_typed_expr_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  drule_all local_target_type_only >> strip_tac >> gvs[] >>
  Cases_on `ty'` >> gvs[subscript_vtype_def, AllCaseEqs()]
QED

Theorem local_target_compile_type:
  !bt cenv cx env es id ty.
    expr_sim_inv cenv cx env es /\
    target_root bt = NameTarget id /\
    type_place_target env bt = SOME (Type ty) ==>
    target_place_type cenv bt = SOME (ValPT ty)
Proof
  Induct using base_assignment_target_induct
  >- (simp[target_root_def, well_typed_expr_def, target_place_type_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >>
      gvs[expr_sim_inv_def] >> metis_tac[])
  >- simp[target_root_def]
  >- (rpt strip_tac >> gvs[target_root_def] >> drule_all local_subscript_type >> strip_tac >>
      simp[target_place_type_def] >>
      first_x_assum drule_all >> simp[])
  >> rpt strip_tac >>
  gvs[target_root_def, Once well_typed_expr_def, AllCaseEqs()] >>
  first_x_assum drule_all >> disch_tac >>
  Cases_on `tgt_ty` >> gvs[attribute_type_def, AllCaseEqs()] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `sfields_tenv_consistent cenv.ce_struct_fields env.type_defs` by
    gvs[expr_sim_inv_def] >>
  qpat_x_assum `sfields_tenv_consistent _ _` mp_tac >>
  simp[sfields_tenv_consistent_def] >> strip_tac >>
  gvs[] >> first_x_assum drule >> strip_tac >>
  simp[target_place_type_def, get_struct_fields_def] >>
  `fields = MAP (\(k,v). (k,FST v)) fields'` by
    (qspec_then `fields` mp_tac listTheory.ZIP_UNZIP >>
     pure_rewrite_tac[listTheory.UNZIP_MAP] >>
     disch_then (fn th => once_rewrite_tac[GSYM th]) >>
     qpat_x_assum `MAP FST fields' = _` (fn th => pure_once_rewrite_tac[GSYM th]) >>
     qpat_x_assum `MAP (FST o SND) fields' = _` (fn th => pure_once_rewrite_tac[GSYM th]) >>
     simp[ZIP_MAP_MAP, combinTheory.o_DEF] >>
     irule listTheory.MAP_CONG >> simp[pairTheory.FORALL_PROD]) >>
  gvs[ALOOKUP_MAP, combinTheory.o_DEF, AllCaseEqs()] >> Cases_on `z` >> simp[]
QED
