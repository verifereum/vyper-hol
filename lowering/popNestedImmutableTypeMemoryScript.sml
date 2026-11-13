(* Compiler/source type agreement along an immutable-rooted target. *)
Theory popNestedImmutableTypeMemory
Ancestors
  allocLimits targetPlaceSim stmtSimAssignAttr vyperTypeEnv exprSimHypsDefs
  vyperTypeSystem vyperTypeInvariants popNestedImmutablePlaceOrigin
  vyperInterpreter vyperPlaceFrames vyperState vyperMisc targetPlaceSimCasesBase

Theorem pop_nested_immutable_target_place_type:
  !bt src id rootty vt.
    target_root bt = TopLevelNameTarget (src,id) /\
    FLOOKUP env.bare_globals (src,id) = SOME rootty /\
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
  >- (PairCases_on `p` >> gvs[type_place_target_TopLevelNameTarget] >>
      fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def,
         bare_globals_layout_def, target_place_type_def] >> metis_tac[])
  >- (first_x_assum (qspec_then `b` mp_tac) >> simp[] >>
      strip_tac >> gvs[] >>
      Cases_on `ty` >> gvs[subscript_vtype_def, AllCaseEqs()] >>
      simp[target_place_type_def]) >>
  first_x_assum (qspec_then `b` mp_tac) >> simp[] >>
  strip_tac >> gvs[] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  Cases_on `tgt_ty` >> gvs[attribute_type_def, AllCaseEqs()] >>
  `attribute_type (get_tenv cx) (StructT p) s = SOME ty` by
    simp[attribute_type_def] >>
  drule_all attribute_type_struct_field >> strip_tac >>
  simp[target_place_type_def]
QED

Theorem pop_nested_immutable_root_bare:
  !bt cenv cx env st vt src id path fin.
    expr_sim_inv cenv cx env st /\
    type_place_target env bt = SOME vt /\
    eval_base_place cx bt st = (INL (PlaceR (ImmutablePlace src id path)),fin) ==>
    target_root bt = TopLevelNameTarget (src,id) /\
    ?ty. FLOOKUP env.bare_globals (src,id) = SOME ty
Proof
  recInduct base_assignment_target_induct >> rpt conj_tac >> rpt gen_tac
  >- (simp[Once evaluate_def, bind_def, get_scopes_def, type_check_def,
           assert_def, ignore_bind_def, return_def, raise_def, AllCaseEqs()])
  >- suspend "root"
  >- suspend "subscript"
  >> suspend "attribute"
QED

Resume pop_nested_immutable_root_bare[root]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  PairCases_on `nsid` >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       option_CASE_rator, prod_CASE_rator, var_decl_info_CASE_rator,
       return_def, raise_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  `env_context_consistent env cx` by
    fs[expr_sim_inv_def, env_consistent_def] >>
  qpat_x_assum `expr_sim_inv _ _ _ _` kall_tac >>
  fs[target_root_def, type_place_target_TopLevelNameTarget,
     env_context_consistent_def]
  >~ [`FLOOKUP env.bare_global_assignable (src,id) = SOME ty`]
  >- (qpat_x_assum `!src id ty. FLOOKUP env.bare_global_assignable _ = _ ==> _`
        drule >> strip_tac >> gvs[]) >>
  Cases_on `vt` >> gvs[]
  >- (qpat_x_assum `!src id ty. _ /\ FLOOKUP env.bare_globals _ = NONE ==> _`
        drule_all >> strip_tac >> gvs[]) >>
  qpat_x_assum `!src id kt vt. FLOOKUP env.toplevel_vtypes _ = SOME (HashMapT _ _) ==> _`
    drule >> strip_tac >> gvs[]
QED

Resume pop_nested_immutable_root_bare[subscript]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[type_place_target_SubscriptTarget] >>
  qpat_x_assum `eval_base_place cx (SubscriptTarget bt e) st = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  drule extend_place_immutable_origin >> strip_tac >> gvs[] >>
  first_x_assum drule_all >> simp[target_root_def]
QED

Resume pop_nested_immutable_root_bare[attribute]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[type_place_target_AttributeTarget] >>
  qpat_x_assum `eval_base_place cx (AttributeTarget bt s) st = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  drule extend_place_immutable_origin >> strip_tac >> gvs[] >>
  first_x_assum drule_all >> simp[target_root_def]
QED

Finalise pop_nested_immutable_root_bare
