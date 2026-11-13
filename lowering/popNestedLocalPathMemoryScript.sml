(* Source path typing for successful local target evaluation. *)
Theory popNestedLocalPathMemory
Ancestors
  vyperTypeCallStackSoundness vyperTypeCallGraph exprSimSource vyperTypeEnv popNestedLocalTypeMemory targetPlaceSim targetPlaceSimCasesBase exprSimHypsDefs
  vyperTypeEvalSoundness
  vyperPlaceTyping vyperPlaceResultTyping vyperPlaceStatePreservation
  exprSimSubscriptArrayOrigin allocLimits list rich_list vyperState vyperTypeInvariants
  vyperPlaceFrames vyperInterpreter vyperValue option

Theorem pop_nested_local_path_typed:
  target_pre cenv cx env bt st /\
  type_place_target env bt = SOME (Type ty) /\
  call_evaluation_safe cx (int_calls_target bt) /\
  eval_base_place cx bt st = (INL (PlaceR (MemoryPlace id path)),fin) ==>
  ?entry tv. lookup_scopes id fin.scopes = SOME entry /\
    evaluate_type env.type_defs ty = SOME tv /\
    subscripts_type entry.type path = SOME tv
Proof
  strip_tac >>
  `env_consistent env cx st /\ state_well_typed st /\
   context_well_typed cx /\ accounts_well_typed st.accounts /\
   functions_well_typed cx` by fs[target_pre_def, expr_sim_inv_def] >>
  drule_all (cj 1 (cj 7 eval_scc_type_sound_results_mutual)) >>
  simp[eval_result_typed_place, runtime_place_typed_memory] >> metis_tac[]
QED

Theorem local_path_fixed_snoc:
  !path tv sb.
  (!prefix i suffix et n.
    path = prefix ++ ValueSubscript (IntV i)::suffix ==>
    subscripts_type tv prefix <> SOME (ArrayTV et (Dynamic n))) /\
  (!i et n. sb = ValueSubscript (IntV i) ==>
    subscripts_type tv path <> SOME (ArrayTV et (Dynamic n))) ==>
  !prefix i suffix et n.
    path ++ [sb] = prefix ++ ValueSubscript (IntV i)::suffix ==>
    subscripts_type tv prefix <> SOME (ArrayTV et (Dynamic n))
Proof
  Induct >> rpt gen_tac
  >- (strip_tac >> rpt gen_tac >> Cases_on `prefix` >> simp[] >>
      rpt strip_tac >> gvs[] >> metis_tac[]) >>
  strip_tac >> rpt gen_tac >> Cases_on `prefix`
  >- (simp[] >> strip_tac >> gvs[] >>
      qpat_x_assum `!prefix i suffix et n. h::path = _ ==> _`
        (qspecl_then [`[]`, `i`, `path`, `et`, `n`] mp_tac) >> simp[]) >>
  simp[] >> strip_tac >> qpat_x_assum `h = h'` (SUBST_ALL_TAC o SYM) >>
  Cases_on `subscript_type tv h` >> simp[subscripts_type_def] >>
  qpat_x_assum `!tv sb. _` irule >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!prefix i suffix et n. h::path = _ ==> _`
        (qspecl_then [`h::prefix`, `i'`, `suffix'`, `et`, `n`] mp_tac) >>
      simp[subscripts_type_def]) >>
  qexistsl_tac [`i`, `sb`, `suffix`] >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!i et n. sb = _ ==> _` drule >> simp[subscripts_type_def]
QED

Theorem local_entry_type_agrees[local]:
  env_consistent env cx s /\ env_consistent env cx t /\
  lookup_scopes id s.scopes = SOME entry /\
  lookup_scopes id t.scopes = SOME other ==>
  entry.type = other.type
Proof
  simp[env_consistent_def, env_scopes_consistent_def] >>
  rpt strip_tac >> gvs[IS_SOME_EXISTS] >>
  qpat_x_assum `!id entry. lookup_scopes id s.scopes = _ ==> _` drule >>
  strip_tac >>
  qpat_x_assum `!id ty entry. _ /\ lookup_scopes id s.scopes = _ ==> _`
    drule_all >>
  qpat_x_assum `!id ty entry. _ /\ lookup_scopes id t.scopes = _ ==> _`
    drule_all >> simp[]
QED

Theorem pop_nested_local_path_fixed:
  !bt cenv cx env st ty id path fin entry.
    target_root bt = NameTarget id /\
    target_pre cenv cx env bt st /\
    type_place_target env bt = SOME (Type ty) /\
    call_evaluation_safe cx (int_calls_target bt) /\
    ~target_through_dynarray cenv bt /\
    eval_base_place cx bt st = (INL (PlaceR (MemoryPlace id path)),fin) /\
    lookup_scopes id fin.scopes = SOME entry ==>
    !prefix i suffix et n.
      path = prefix ++ ValueSubscript (IntV i)::suffix ==>
      subscripts_type entry.type prefix <> SOME (ArrayTV et (Dynamic n))
Proof
  recInduct base_assignment_target_induct >> rpt conj_tac >> rpt gen_tac
  >- (simp[Once evaluate_def, bind_def, get_scopes_def, type_check_def,
           assert_def, ignore_bind_def, return_def, raise_def, target_root_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >> Cases_on `prefix` >> gvs[])
  >- simp[target_root_def]
  >- suspend "subscript"
  >> suspend "attribute"
QED

Resume pop_nested_local_path_fixed[subscript]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  imp_res_tac (cj 2 target_pre_sub) >>
  gvs[target_root_def, target_through_dynarray_def,
      type_place_target_SubscriptTarget] >>
  qpat_x_assum `eval_base_place cx (SubscriptTarget bt e) st = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_base_place cx bt st` >> rename1 `(r1, s1)` >>
  Cases_on `r1` >> simp[] >>
  Cases_on `eval_expr cx e s1` >> rename1 `(r2,s2)` >>
  Cases_on `r2` >> simp[] >>
  rename1 `eval_expr cx e s1 = (INL rv,s2)` >>
  Cases_on `read_result cx rv s2` >> rename1 `(r3,s3)` >>
  Cases_on `r3` >> simp[] >> strip_tac >> gvs[] >>
  drule exprSimSubscriptArrayOriginTheory.extend_place_memory_origin >>
  strip_tac >> gvs[] >>
  `call_evaluation_safe cx (int_calls_target bt)` by
    (fs[int_calls_expr_def] >> metis_tac[call_evaluation_safe_append_left]) >>
  `env_consistent env cx st /\ state_well_typed st /\
   context_well_typed cx /\ accounts_well_typed st.accounts /\
   functions_well_typed cx` by fs[target_pre_def, expr_sim_inv_def] >>
  drule_all (cj 1 (cj 7 eval_scc_type_sound_results_mutual)) >>
  Cases_on `vt'` >> simp[] >> strip_tac >>
  `expr_sim_inv cenv cx env s1` by metis_tac[eval_base_place_sim_inv] >>
  `expr_body_pre cenv cx env e s1` by
    fs[target_pre_def, target_indices_pre_def] >>
  `expr_sim_inv cenv cx env s2` by metis_tac[expr_body_pre_eval_result] >>
  imp_res_tac read_result_state >> imp_res_tac extend_place_state >> gvs[] >>
  drule_all pop_nested_local_target_place_type >> strip_tac >>
  Cases_on `t` >> gvs[vyperTypeSystemTheory.subscript_vtype_def] >>
  rename1 `evaluate_type env.type_defs (ArrayT aty bd) = SOME tv` >>
  Cases_on `bd` >> gvs[] >>
  gvs[runtime_place_typed_memory] >>
  `env_consistent env cx fin` by fs[expr_sim_inv_def] >>
  `entry.type = entry'.type` by metis_tac[local_entry_type_agrees] >>
  `path = path0 ++ [ValueSubscript x']` by
    (qpat_x_assum `extend_place _ _ _ _ = _` mp_tac >>
     simp[extend_place_def, bind_def, ignore_bind_def, return_def,
          raise_def, extend_memory_place_def, lift_sum_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]) >>
  qpat_x_assum `path = _` SUBST_ALL_TAC >>
  qspecl_then [`path0`, `entry.type`, `ValueSubscript x'`] mp_tac
    local_path_fixed_snoc >>
  (impl_tac >-
    (conj_tac
     >- (qpat_x_assum `entry.type = _` SUBST_ALL_TAC >>
         qpat_x_assum `!cenv' cx' env' st' ty' path' fin' entry'. _`
           (qspecl_then [`cenv`, `cx`, `env`, `st`] mp_tac) >> simp[]) >>
     gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()])) >>
  simp[]
QED

Resume pop_nested_local_path_fixed[attribute]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  imp_res_tac (cj 1 target_pre_sub) >>
  gvs[target_root_def, target_through_dynarray_def,
      type_place_target_AttributeTarget, int_calls_expr_def] >>
  qpat_x_assum `eval_base_place cx (AttributeTarget bt s) st = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_base_place cx bt st` >> rename1 `(r1,s1)` >>
  Cases_on `r1` >> simp[] >> strip_tac >> gvs[] >>
  drule exprSimSubscriptArrayOriginTheory.extend_place_memory_origin >>
  strip_tac >> gvs[] >> imp_res_tac extend_place_state >> gvs[] >>
  `path = path0 ++ [AttrSubscript s]` by
    (qpat_x_assum `extend_place _ _ _ _ = _` mp_tac >>
     simp[extend_place_def, bind_def, ignore_bind_def, return_def,
          raise_def, extend_memory_place_def, lift_sum_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[]) >>
  qpat_x_assum `path = _` SUBST_ALL_TAC >>
  qspecl_then [`path0`, `entry.type`, `AttrSubscript s`] mp_tac
    local_path_fixed_snoc >>
  (impl_tac >-
    (reverse conj_tac >- simp[] >>
     first_x_assum (qspecl_then [`cenv`, `cx`, `env`, `st`] mp_tac) >>
     simp[])) >> simp[]
QED

Finalise pop_nested_local_path_fixed
