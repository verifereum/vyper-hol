Theory popNestedLocalPoppedBridge
Ancestors
  popNestedLocalPoppedPath targetPlaceSim targetPlaceSimCasesBase allocLimits
  vyperTypeSystem vyperAST exprSimHypsDefs loweringStateRelDefs
  finite_map alist rich_list compileEnv vyperTypeInvariants vyperState
  vyperTypeEvalSoundness vyperTypeExprSoundness vyperInterpreter
  vyperTypeEvalStoragePreservation vyperTypeCallStackSoundness

Theorem local_target_type_only:
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

Theorem local_subscript_type:
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

Theorem fixed_shape_path_append:
  !path tv ptv sb.
    fixed_shape_path tv path /\ subscripts_type tv path = SOME ptv /\
    fixed_shape_path ptv [sb] ==> fixed_shape_path tv (path ++ [sb])
Proof
  Induct >> simp[subscripts_type_def] >>
  rpt gen_tac >> Cases_on `tv` >> Cases_on `h` >>
  simp[Once fixed_shape_path_def]
  >~ [`ArrayTV et b`, `ValueSubscript v`]
  >- (Cases_on `b` >> Cases_on `v` >>
      simp[fixed_shape_path_def, subscript_type_def] >>
      strip_tac >> gvs[] >> first_x_assum irule >>
      simp[fixed_shape_path_def]) >>
  rpt strip_tac >> gvs[subscript_type_def, AllCaseEqs()] >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  gvs[fixed_shape_path_def]
QED

Theorem local_base_runtime_path_type:
  !cx bt env ty s t id path entry.
    type_place_target env bt = SOME (Type ty) /\
    runtime_consistent env cx s /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\
    eval_base_place cx bt s = (INL (PlaceR (MemoryPlace id path)),t) /\
    lookup_scopes id t.scopes = SOME entry ==>
    ?tv. evaluate_type env.type_defs ty = SOME tv /\
         subscripts_type entry.type path = SOME tv
Proof
  simp[runtime_consistent_def] >> rpt strip_tac >>
  drule_all (cj 1 (cj 7 eval_scc_type_sound_results_mutual)) >>
  simp[eval_result_typed_def, runtime_place_typed_def,
       place_type_value_def, bind_def, get_scopes_def,
       lift_option_type_def, return_def, raise_def, assert_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  Cases_on `subscripts_type entry.type path` >> gvs[return_def, raise_def]
QED

Theorem fixed_shape_step_from_type[local]:
  !tv sb etv.
    ((?et n. tv = ArrayTV et (Fixed n)) \/ (?fs. tv = StructTV fs)) /\
    subscript_type tv sb = SOME etv ==> fixed_shape_path tv [sb]
Proof
  rpt strip_tac >> gvs[] >> Cases_on `sb` >>
  gvs[subscript_type_def, fixed_shape_path_def, AllCaseEqs()] >>
  Cases_on `v` >> gvs[subscript_type_def, fixed_shape_path_def, AllCaseEqs()]
QED

Theorem local_target_root_var_type:
  !bt env id vt.
    target_root bt = NameTarget id /\ type_place_target env bt = SOME vt ==>
    ?ty. FLOOKUP env.var_types id = SOME ty
Proof
  Induct using base_assignment_target_induct >>
  simp[target_root_def, well_typed_expr_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem local_root_entry_type:
  runtime_consistent env cx s /\ runtime_consistent env cx t /\
  FLOOKUP env.var_types id = SOME ty /\
  lookup_scopes id s.scopes = SOME e1 /\
  lookup_scopes id t.scopes = SOME e2 ==> e1.type = e2.type
Proof
  simp[runtime_consistent_def] >> rpt strip_tac >>
  qpat_assum `env_consistent _ _ s`
    (mp_then Any mp_tac vyperTypeEnvTheory.env_consistent_lookup_var_type) >>
  disch_then drule_all >> strip_tac >>
  qpat_assum `env_consistent _ _ t`
    (mp_then Any mp_tac vyperTypeEnvTheory.env_consistent_lookup_var_type) >>
  disch_then drule_all >> strip_tac >> gvs[]
QED

Theorem extend_place_memory_path:
  extend_place cx pv sb s = (INL (PlaceR (MemoryPlace id path)),t) ==>
  ?p. pv = PlaceR (MemoryPlace id p) /\ path = p ++ [sb] /\ t = s
Proof
  strip_tac >>
  `t = s` by metis_tac[vyperPlaceFramesTheory.extend_place_state] >>
  Cases_on `pv`
  >- gvs[extend_place_def, raise_def]
  >- (drule (exprSimPropsTheory.select_result_memory_place |>
             Q.SPECL [`cx`,`ty`,`PlaceR p`] |> SRULE [select_result_def]) >>
      disch_then (qspecl_then [`id`,`path`] mp_tac) >> simp[] >> metis_tac[]) >>
  Cases_on `sb` >> gvs[extend_place_def, bind_def, return_def,
    raise_def, lift_option_type_def, AllCaseEqs()] >>
  Cases_on `v` >> gvs[return_def, raise_def, bind_def,
    lift_option_type_def, AllCaseEqs()]
QED

Theorem runtime_root_entry:
  runtime_consistent env cx s /\ FLOOKUP env.var_types id = SOME ty ==>
  ?entry. lookup_scopes id s.scopes = SOME entry
Proof
  simp[runtime_consistent_def, env_consistent_def,
       env_scopes_consistent_def] >> metis_tac[optionTheory.IS_SOME_EXISTS]
QED

Theorem local_base_fixed_shape_general:
  !bt cenv cx env es0 s ty id path t entry.
    expr_sim_inv cenv cx env es0 /\ runtime_consistent env cx s /\
    functions_well_typed cx /\
    type_place_target env bt = SOME (Type ty) /\
    target_root bt = NameTarget id /\
    call_evaluation_safe cx (int_calls_target bt) /\
    ~target_through_dynarray cenv bt /\
    eval_base_place cx bt s = (INL (PlaceR (MemoryPlace id path)),t) /\
    lookup_scopes id t.scopes = SOME entry ==>
    fixed_shape_path entry.type path
Proof
  Induct using base_assignment_target_induct
  >- (simp[Once evaluate_def, bind_def, get_scopes_def, type_check_def,
           assert_def, ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[fixed_shape_path_def])
  >- simp[target_root_def]
  >- suspend "subscript"
  >> suspend "attribute"
QED

Resume local_base_fixed_shape_general[subscript]:
      rpt strip_tac >>
      gvs[target_root_def, target_through_dynarray_def] >>
      drule_all local_subscript_type >> strip_tac >>
      qpat_x_assum `eval_base_place _ (SubscriptTarget _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
      drule extend_place_memory_path >> strip_tac >> gvs[] >>
      drule read_result_state >> strip_tac >> gvs[] >>
      rename1 `eval_base_place cx bt s = (INL (PlaceR (MemoryPlace id p)),sbase)` >>
      rename1 `eval_expr cx e sbase = (INL tv,sidx)` >>
      rename1 `read_result cx tv sidx = (INL idx,sidx)` >>
      `call_evaluation_safe cx (int_calls_target bt) /\
       call_evaluation_safe cx (int_calls_expr e)` by
        (conj_tac >> irule call_evaluation_safe_mono >>
         goal_assum (drule_at Any) >> simp[vyperTypeCallGraphTheory.int_calls_expr_def]) >>
      `runtime_consistent env cx sbase` by
        (metis_tac[eval_base_place_preserves_runtime_consistent]) >>
      `runtime_consistent env cx sidx` by
        (metis_tac[eval_expr_preserves_runtime_consistent]) >>
      drule_all local_target_root_var_type >> strip_tac >>
      `?base_entry. lookup_scopes id sbase.scopes = SOME base_entry` by
        (metis_tac[runtime_root_entry]) >>
      `base_entry.type = entry.type` by
        (metis_tac[local_root_entry_type]) >>
      `fixed_shape_path entry.type p` by
        (first_x_assum drule_all >> simp[]) >>
      drule_all local_target_compile_type >> strip_tac >>
      Cases_on `bd` >> gvs[] >>
      `?ptv. evaluate_type env.type_defs (ArrayT ty (Fixed n)) = SOME ptv /\
             subscripts_type entry.type p = SOME ptv` by
        (drule_all local_base_runtime_path_type >> strip_tac >> gvs[] >> metis_tac[]) >>
      drule vyperTypeValuesTheory.evaluate_type_ArrayT_cases >> strip_tac >> gvs[] >>
      `?ftv. evaluate_type env.type_defs ty = SOME ftv /\
             subscripts_type entry.type (p ++ [ValueSubscript idx]) = SOME ftv` by
        (irule local_base_runtime_path_type >>
         qexistsl [`SubscriptTarget bt e`,`cx`,`id`,`s`,`sidx`] >>
         simp[Once evaluate_def, bind_def] >> metis_tac[]) >>
      irule fixed_shape_path_append >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> irule fixed_shape_step_from_type >>
      qpat_x_assum `subscripts_type _ (_ ++ _) = _` mp_tac >>
      drule vyperPlaceResultTypingTheory.subscripts_type_append >>
      disch_then (qspec_then `[ValueSubscript idx]` mp_tac) >>
      simp[subscripts_type_def, AllCaseEqs()] >> metis_tac[]
QED

Resume local_base_fixed_shape_general[attribute]:
  rpt strip_tac >>
  gvs[target_root_def, target_through_dynarray_def] >>
  qpat_x_assum `eval_base_place _ (AttributeTarget _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  drule extend_place_memory_path >> strip_tac >> gvs[] >>
  gvs[vyperTypeCallGraphTheory.int_calls_expr_def] >>
  qpat_x_assum `type_place_target _ (AttributeTarget _ _) = _` mp_tac >>
  simp[Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >>
  drule_all local_target_type_only >> strip_tac >> gvs[] >>
  Cases_on `tgt_ty` >> gvs[attribute_type_def, AllCaseEqs()] >>
  `fixed_shape_path entry.type p` by
    (first_x_assum drule_all >> simp[]) >>
  drule_all local_base_runtime_path_type >> strip_tac >>
  rename1 `eval_base_place cx bt st0 = (INL (PlaceR (MemoryPlace id p)),st1)` >>
  `?ftv. evaluate_type env.type_defs ty = SOME ftv /\
         subscripts_type entry.type (p ++ [AttrSubscript s]) = SOME ftv` by
    (irule local_base_runtime_path_type >>
     qexistsl [`AttributeTarget bt s`,`cx`,`id`,`st0`,`st1`] >>
     simp[Once well_typed_expr_def, attribute_type_def,
          Once evaluate_def, bind_def, vyperTypeCallGraphTheory.int_calls_expr_def] >>
     metis_tac[]) >>
  qpat_x_assum `evaluate_type _ (StructT _) = _` mp_tac >>
  simp[Once vyperValueTheory.evaluate_type_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  irule fixed_shape_path_append >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> irule fixed_shape_step_from_type >>
  qpat_x_assum `subscripts_type _ (_ ++ _) = _` mp_tac >>
  drule vyperPlaceResultTypingTheory.subscripts_type_append >>
  disch_then (qspec_then `[AttrSubscript s]` mp_tac) >>
  simp[subscripts_type_def, AllCaseEqs()] >> metis_tac[]
QED

Finalise local_base_fixed_shape_general

Theorem local_target_fixed_shape:
  !cenv cx env s bt ty id path t entry.
    expr_sim_inv cenv cx env s /\
    type_place_target env bt = SOME (Type ty) /\
    target_root bt = NameTarget id /\
    call_evaluation_safe cx (int_calls_target bt) /\
    ~target_through_dynarray cenv bt /\
    eval_target_place cx bt s = (INL (MemoryPlace id path),t) /\
    lookup_scopes id t.scopes = SOME entry ==>
    fixed_shape_path entry.type path
Proof
  rpt strip_tac >>
  `runtime_consistent env cx s /\ functions_well_typed cx` by
    gvs[expr_sim_inv_def, runtime_consistent_def] >>
  qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_place_def, AllCaseEqs()] >>
  strip_tac >> Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  irule local_base_fixed_shape_general >>
  metis_tac[]
QED
