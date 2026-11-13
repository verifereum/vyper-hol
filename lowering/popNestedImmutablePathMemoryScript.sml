(* Source typing and static readability for immutable target paths. *)
Theory popNestedImmutablePathMemory
Ancestors
  popNestedFixedPathMemory popNestedLocalPathMemory popNestedImmutableTypeMemory
  popNestedImmutablePlaceOrigin
  vyperTypeCallStackSoundness vyperTypeCallGraph exprSimSource vyperTypeEnv
  targetPlaceSim targetPlaceSimCasesBase exprSimHypsDefs
  vyperTypeEvalSoundness vyperPlaceTyping vyperPlaceResultTyping
  vyperPlaceStatePreservation vyperEvalPreservesScopes vyperImmutableMetadataFrame
  exprSimSubscriptArrayOrigin allocLimits list rich_list vyperState
  vyperTypeInvariants vyperPlaceFrames vyperInterpreter vyperValue vyperMisc option finite_map

Theorem pop_nested_immutable_path_typed:
  target_pre cenv cx env bt st /\
  type_place_target env bt = SOME (Type ty) /\
  call_evaluation_safe cx (int_calls_target bt) /\
  eval_base_place cx bt st = (INL (PlaceR (ImmutablePlace src id path)),fin) ==>
  ?imms root a tv. get_immutables cx src fin = (INL imms,fin) /\
    FLOOKUP imms id = SOME (root,a) /\
    evaluate_type env.type_defs ty = SOME tv /\
    subscripts_type root path = SOME tv
Proof
  strip_tac >>
  `env_consistent env cx st /\ state_well_typed st /\
   context_well_typed cx /\ accounts_well_typed st.accounts /\
   functions_well_typed cx` by fs[target_pre_def, expr_sim_inv_def] >>
  drule_all (cj 1 (cj 7 eval_scc_type_sound_results_mutual)) >>
  simp[eval_result_typed_place, runtime_place_typed_immutable] >> metis_tac[]
QED

Theorem pop_nested_immutable_static_index_ready:
  expr_body_pre cenv cx env e mid /\
  get_immutables cx src mid = (INL imms,mid) /\
  FLOOKUP imms id = SOME (root,a) /\
  subscripts_type root path = SOME ptv /\
  (!prefix i suffix et n.
    path = prefix ++ ValueSubscript (IntV i)::suffix ==>
    subscripts_type root prefix <> SOME (ArrayTV et (Dynamic n))) /\
  bind (eval_expr cx e) (read_result cx) mid = (res,fin) ==>
  ?imms' a' w. get_immutables cx src fin = (INL imms',fin) /\
    FLOOKUP imms' id = SOME (root,a') /\
    evaluate_subscripts root a' path = INL w
Proof
  strip_tac >>
  qpat_x_assum `bind _ _ mid = _` mp_tac >>
  simp[bind_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  imp_res_tac read_result_state >> gvs[] >>
  `immutable_metadata_frame mid fin` by
    metis_tac[eval_expr_immutable_metadata_frame] >>
  drule_all immutable_metadata_frame_lookup >> strip_tac >>
  `expr_sim_inv cenv cx env fin` by metis_tac[expr_body_pre_eval_result] >>
  `value_has_type root v' /\ well_formed_type_value root` by
    (irule get_immutables_success_typed >>
     fs[expr_sim_inv_def] >> metis_tac[]) >>
  qexistsl_tac [`imms'`, `v'`] >> simp[] >>
  irule pop_nested_fixed_path_ready >> gvs[APPEND_ASSOC] >> metis_tac[]
QED

Theorem pop_nested_immutable_path_fixed:
  !bt cenv cx env st ty src id path fin imms root a.
    target_pre cenv cx env bt st /\
    type_place_target env bt = SOME (Type ty) /\
    call_evaluation_safe cx (int_calls_target bt) /\
    ~target_through_dynarray cenv bt /\
    eval_base_place cx bt st = (INL (PlaceR (ImmutablePlace src id path)),fin) /\
    get_immutables cx src fin = (INL imms,fin) /\
    FLOOKUP imms id = SOME (root,a) ==>
    !prefix i suffix et n.
      path = prefix ++ ValueSubscript (IntV i)::suffix ==>
      subscripts_type root prefix <> SOME (ArrayTV et (Dynamic n))
Proof
  recInduct base_assignment_target_induct >> rpt conj_tac >> rpt gen_tac
  >- (simp[Once evaluate_def, bind_def, get_scopes_def, type_check_def,
           assert_def, ignore_bind_def, return_def, raise_def, AllCaseEqs()])
  >- suspend "root"
  >- suspend "subscript"
  >> suspend "attribute"
QED

Resume pop_nested_immutable_path_fixed[root]:
  strip_tac >> rpt gen_tac >> strip_tac >> PairCases_on `nsid` >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       option_CASE_rator, prod_CASE_rator, var_decl_info_CASE_rator,
       return_def, raise_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  Cases_on `prefix` >> gvs[]
QED

Resume pop_nested_immutable_path_fixed[subscript]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  imp_res_tac (cj 2 target_pre_sub) >>
  gvs[target_through_dynarray_def, type_place_target_SubscriptTarget] >>
  qpat_x_assum `eval_base_place cx (SubscriptTarget bt e) st = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  drule extend_place_immutable_origin >> strip_tac >> gvs[] >>
  `expr_sim_inv cenv cx env st` by fs[target_pre_def] >>
  drule_all pop_nested_immutable_root_bare >> strip_tac >>
  drule_all pop_nested_immutable_target_place_type >> strip_tac >> gvs[] >>
  `call_evaluation_safe cx (int_calls_target bt)` by
    (fs[int_calls_expr_def] >> metis_tac[call_evaluation_safe_append_left]) >>
  drule_all pop_nested_immutable_path_typed >> strip_tac >>
  imp_res_tac read_result_state >> imp_res_tac extend_place_state >> gvs[] >>
  `immutable_metadata_frame s'' fin` by
    metis_tac[eval_expr_immutable_metadata_frame] >>
  drule_all immutable_metadata_frame_lookup >> strip_tac >> gvs[] >>
  rename1 `read_result cx tv fin = (INL ix,fin)` >>
  `prefix ++ [ValueSubscript (IntV i)] ++ suffix =
   path0 ++ [ValueSubscript ix]` by
    (qpat_x_assum `extend_place _ _ _ _ = _` mp_tac >>
     simp[extend_place_def, bind_def, ignore_bind_def, return_def,
          raise_def, extend_memory_place_def, lift_sum_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[]) >>
  qspecl_then [`path0`, `root`, `ValueSubscript ix`] mp_tac local_path_fixed_snoc >>
  (impl_tac >-
    (conj_tac
     >- (first_x_assum (qspecl_then [`cenv`, `cx`, `env`, `st`] mp_tac) >> simp[]) >>
     Cases_on `ty''` >> gvs[vyperTypeSystemTheory.subscript_vtype_def] >>
     Cases_on `b` >> gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] )) >>
  disch_then (qspecl_then [`prefix`, `i`, `suffix`, `et`, `n`] mp_tac) >>
  qpat_x_assum `_ = path0 ++ _` mp_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  disch_then (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `subscripts_type root prefix = _` (fn th => rewrite_tac[th])
QED

Resume pop_nested_immutable_path_fixed[attribute]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  imp_res_tac (cj 1 target_pre_sub) >>
  gvs[target_through_dynarray_def, type_place_target_AttributeTarget,
      int_calls_expr_def] >>
  qpat_x_assum `eval_base_place cx (AttributeTarget bt s) st = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  drule extend_place_immutable_origin >> strip_tac >> gvs[] >>
  imp_res_tac extend_place_state >> gvs[] >>
  `prefix ++ [ValueSubscript (IntV i)] ++ suffix =
   path0 ++ [AttrSubscript s]` by
    (qpat_x_assum `extend_place _ _ _ _ = _` mp_tac >>
     simp[extend_place_def, bind_def, ignore_bind_def, return_def,
          raise_def, extend_memory_place_def, lift_sum_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[]) >>
  qspecl_then [`path0`, `root`, `AttrSubscript s`] mp_tac local_path_fixed_snoc >>
  (impl_tac >-
    (conj_tac
     >- (first_x_assum (qspecl_then [`cenv`, `cx`, `env`, `st`] mp_tac) >> simp[]) >>
     simp[])) >>
  disch_then (qspecl_then [`prefix`, `i`, `suffix`, `et`, `n`] mp_tac) >>
  qpat_x_assum `_ = path0 ++ _` mp_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  disch_then (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `subscripts_type root prefix = _` (fn th => rewrite_tac[th])
QED

Finalise pop_nested_immutable_path_fixed
