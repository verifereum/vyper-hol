(* Frame one immutable binding, rather than the whole immutable store. *)
Theory whitelistForIterImmFrame
Ancestors
  vyperBareGlobalName vyperPlaceFrames vyperState vyperTypeSystem
  stmtSimForArrayFrame vyperStatePreservation supportedExprs supportedExprForms supportedExprTraverse
  vyperTypeInvariants vyperInterpreter vyperAST list rich_list finite_map alist

Theorem lookup_immutable_set_other:
  (src',name') <> (src,name) /\
  set_immutable cx src' name' tv v es = (r,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  simp[set_immutable_def, get_address_immutables_def,
       set_address_immutables_def, bind_def, lift_option_type_def,
       return_def, raise_def] >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >>
  simp[return_def, raise_def] >>
  rpt strip_tac >> gvs[lookup_immutable_def] >>
  Cases_on `src' = src` >>
  gvs[set_source_immutables_def, get_source_immutables_def, FLOOKUP_UPDATE,
      ALOOKUP_ADELKEY]
QED

Theorem lookup_immutable_write_other:
  write_place cx p v es = (r,es') /\
  (!src' name' path. p = ImmutablePlace src' name' path ==>
                      (src',name') <> (src,name)) ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  Cases_on `p`
  >- (strip_tac >> drule write_storage_place_immutables >>
      simp[lookup_immutable_def])
  >- (strip_tac >> drule write_memory_place_immutables >>
      simp[lookup_immutable_def]) >>
  rename1 `write_place cx (ImmutablePlace other_src other_name path)` >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >>
  simp[write_place_def, bind_def, get_immutables_def,
       get_address_immutables_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def] >>
  rename1 `ALOOKUP es.immutables cx.txn.target = SOME imms` >>
  Cases_on `FLOOKUP (get_source_immutables other_src imms) other_name` >>
  simp[return_def, raise_def] >>
  rename1 `FLOOKUP _ _ = SOME tva` >>
  Cases_on `assign_subscripts (FST tva) (SND tva) path (Replace v)` >>
  simp[return_def, raise_def] >>
  rpt strip_tac >> irule lookup_immutable_set_other >>
  goal_assum (drule_at Any) >> simp[]
QED

(* Relate the semantic immutable root to the syntactic write guard. *)
Theorem lookup_global_immutable_root:
  lookup_global cx src id es =
    (INL (PlaceR (ImmutablePlace other_src other_id path)),es') ==>
  other_src = src /\ other_id = id /\ path = []
Proof
  simp[lookup_global_def, vyperMiscTheory.option_CASE_rator,
       vyperMiscTheory.prod_CASE_rator, var_decl_info_CASE_rator,
       bind_def, lift_option_type_def, return_def, raise_def,
       get_immutables_def, get_address_immutables_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[AllCaseEqs(), bind_def, return_def, raise_def]
QED

Theorem extend_place_immutable_root:
  extend_place cx pv sb es =
    (INL (PlaceR (ImmutablePlace src id path)),es') ==>
  ?oldpath. pv = PlaceR (ImmutablePlace src id oldpath)
Proof
  Cases_on `pv` >> Cases_on `sb` >>
  simp[oneline extend_place_def, bind_def, ignore_bind_def,
       lift_option_type_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[bind_def, return_def, raise_def, lift_sum_def,
      value_type_CASE_rator, place_CASE_rator, vyperMiscTheory.sum_CASE_rator,
      vyperMiscTheory.option_CASE_rator, AllCaseEqs(), extend_memory_place_def] >>
  Cases_on `tv` >>
  gvs[oneline extend_storage_place_def, vyperValueTheory.value_CASE_rator,
      bind_def, ignore_bind_def, check_def, assert_def,
      lift_option_type_def, lift_sum_def, return_def, raise_def, AllCaseEqs()] >>
  pairarg_tac >> gvs[return_def]
QED

Theorem immutable_place_access_root_attrs[local]:
  !target attrs. FST (place_access target attrs) = FST (place_access target [])
Proof
  measureInduct_on `base_assignment_target_size target` >>
  Cases_on `target` >> simp[place_access_def] >> rpt strip_tac >>
  first_x_assum irule >> simp[]
QED

Theorem eval_base_place_immutable_root:
  !target cx es src id path es'.
    eval_base_place cx target es =
      (INL (PlaceR (ImmutablePlace src id path)),es') ==>
    FST (place_access target []) = TopLevelNameTarget (src,id)
Proof
  measureInduct_on `base_assignment_target_size target` >>
  Cases_on `target` >> rpt strip_tac
  >~ [`eval_base_place _ (NameTarget _) _ = _`]
  >- gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
         type_check_def, assert_def, return_def, raise_def, AllCaseEqs(),
         place_access_def]
  >~ [`eval_base_place _ (TopLevelNameTarget _) _ = _`]
  >- (rename1 `eval_base_place cx (TopLevelNameTarget nsid) es = _` >>
      PairCases_on `nsid` >> gvs[Once evaluate_def] >>
      drule lookup_global_immutable_root >> simp[place_access_def]) >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  drule extend_place_immutable_root >> strip_tac >> gvs[] >>
  rename1 `eval_base_place cx inner _ = _` >>
  first_x_assum (qspec_then `inner` mp_tac) >> simp[] >>
  disch_then drule >> simp[place_access_def, immutable_place_access_root_attrs]
QED

Theorem eval_target_place_immutable_root:
  eval_target_place cx target es = (INL (ImmutablePlace src id path),es') ==>
  FST (place_access target []) = TopLevelNameTarget (src,id)
Proof
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, get_place_def, return_def,
      raise_def, AllCaseEqs()] >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  metis_tac[eval_base_place_immutable_root]
QED

Theorem typed_guarded_immutable_target_write:
  (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
   type_place_target env (TopLevelNameTarget (src,name)) =
     SOME (Type (ArrayT elem bound))) /\
  type_place_target env target = SOME vt /\
  ~place_contains target (TopLevelNameTarget (src,name)) /\
  eval_target_place cx target es = (INL p,es1) /\
  write_place cx p v es1 = (r,es2) ==>
  lookup_immutable cx es2 src name = lookup_immutable cx es1 src name
Proof
  rpt strip_tac >> irule lookup_immutable_write_other >>
  goal_assum (drule_at Any) >> rpt strip_tac >> gvs[] >>
  drule eval_target_place_immutable_root >> strip_tac >>
  drule_at (Pat `type_place_target env target`) typed_guarded_array_root >>
  simp[] >> metis_tac[]
QED

Theorem supported_pure_immutable_mutual:
  (!tops e. supported_pure_expr tops e ==>
    !cx es res es' src name. eval_expr cx e es = (res,es') ==>
      lookup_immutable cx es' src name = lookup_immutable cx es src name) /\
  (!tops exprs. supported_pure_exprs tops exprs ==>
    !cx es res es' src name. eval_exprs cx exprs es = (res,es') ==>
      lookup_immutable cx es' src name = lookup_immutable cx es src name) /\
  (!tops fields. supported_pure_fields tops fields ==>
    !cx es res es' src name. eval_exprs cx (MAP SND fields) es = (res,es') ==>
      lookup_immutable cx es' src name = lookup_immutable cx es src name) /\
  (!tops e. supported_place_expr tops e ==>
    !cx es res es' src name. eval_expr cx e es = (res,es') ==>
      lookup_immutable cx es' src name = lookup_immutable cx es src name)
Proof
  ho_match_mp_tac supported_pure_expr_ind >> rpt conj_tac >>
  simp[supported_pure_expr_def] >> rpt strip_tac
  >>~- ([`eval_expr _ (Name _ _) _ = _`],
      gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
          type_check_def, assert_def, lift_option_type_def,
          return_def, raise_def, AllCaseEqs()])
  >>~- ([`eval_expr _ (Literal _ _) _ = _`],
      gvs[Once evaluate_def, return_def])
  >>~- ([`eval_expr _ (TopLevelName _ _) _ = _`],
      rename1 `eval_expr cx (TopLevelName ty nsid) es = _` >>
      PairCases_on `nsid` >> gvs[Once evaluate_def] >>
      drule lookup_global_state >> simp[])
  >>~- ([`eval_expr _ (IfExp _ _ _ _) _ = _`], suspend "ifexp")
  >>~- ([`eval_expr _ (StructLit _ _ _) _ = _`], suspend "struct")
  >~ [`eval_expr _ (Subscript _ _ _) _ = _`] >- suspend "subscript1"
  >>~- ([`eval_expr _ (Subscript _ _ _) _ = _`], suspend "subscript2")
  >~ [`eval_expr _ (Attribute _ _ _) _ = _`] >- suspend "attribute1"
  >>~- ([`eval_expr _ (Attribute _ _ _) _ = _`], suspend "attribute2")
  >>~- ([`eval_expr _ (Builtin _ _ _) _ = _`], suspend "builtin")
  >>~- ([`eval_expr _ (TypeBuiltin _ _ _ _) _ = _`], suspend "typebuiltin")
  >>~- ([`eval_exprs _ [] _ = _`], gvs[Once evaluate_def, return_def])
  >> gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def]
  >> imp_res_tac read_result_state >> gvs[]
  >> rename1 `lookup_immutable cx es' protected_src protected_name = _`
  >> first_x_assum drule
  >> disch_then (qspecl_then [`protected_src`, `protected_name`] assume_tac)
  >> first_x_assum drule
  >> disch_then (qspecl_then [`protected_src`, `protected_name`] assume_tac)
  >> gvs[]
QED

Resume supported_pure_immutable_mutual[ifexp]:
  gvs[Once evaluate_def, bind_def, ignore_bind_def, switch_BoolV_def,
      AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac conditional_result_state >> gvs[] >>
  gvs[COND_RATOR, AllCaseEqs(), raise_def] >> metis_tac[]
QED

Resume supported_pure_immutable_mutual[struct]:
  rename1 `eval_expr cx (StructLit ty nsid fields) es = _` >>
  PairCases_on `nsid` >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  metis_tac[]
QED

Resume supported_pure_immutable_mutual[subscript1]:
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac select_result_state >>
  gvs[] >> metis_tac[]
QED

Resume supported_pure_immutable_mutual[subscript2]:
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac select_result_state >>
  gvs[] >> metis_tac[]
QED

Resume supported_pure_immutable_mutual[attribute1]:
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac select_result_state >> gvs[] >> metis_tac[]
QED

Resume supported_pure_immutable_mutual[attribute2]:
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac select_result_state >> gvs[] >> metis_tac[]
QED

Resume supported_pure_immutable_mutual[builtin]:
  `blt <> Len` by
    (Cases_on `blt = Len` >> gvs[supported_builtin_form_def, AllCaseEqs()]) >>
  Cases_on `blt = Env MsgGas` >>
  gvs[Once evaluate_def, type_check_def, assert_def, bind_def,
      ignore_bind_def, return_def, raise_def, AllCaseEqs(), get_accounts_def] >>
  imp_res_tac next_gas_reading_state >>
  imp_res_tac lift_sum_state >>
  imp_res_tac precompile_call_success_state >> gvs[]
  >>~- ([`lookup_immutable cx (es with gas_obs := gobs) src name = _`],
         simp[lookup_immutable_def]) >>
  first_x_assum drule >>
  disch_then (qspecl_then [`src`, `name`] mp_tac) >>
  simp[lookup_immutable_def]
QED

Resume supported_pure_immutable_mutual[typebuiltin]:
  gvs[Once evaluate_def, type_check_def, assert_def, bind_def,
      ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac lift_sum_state >> gvs[] >> metis_tac[]
QED

Finalise supported_pure_immutable_mutual

Theorem immutable_direct_pop_other:
  (other_src,other_name) <> (src,name) /\
  eval_expr cx (Pop ty (TopLevelNameTarget (other_src,other_name))) es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  imp_res_tac lookup_global_state >> gvs[] >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `p`
  >- (drule vyperScopePreservationTheory.pop_storage_place_scopes_immutables >>
      simp[lookup_immutable_def])
  >- metis_tac[lookup_global_not_memory] >>
  drule lookup_global_immutable_root >> strip_tac >> gvs[] >>
  gvs[pop_place_def, bind_def, ignore_bind_def, get_immutables_def, get_address_immutables_def,
      lift_option_type_def, lift_sum_def, return_def, raise_def, AllCaseEqs()] >>
  gvs[vyperMiscTheory.option_CASE_rator, vyperMiscTheory.sum_CASE_rator,
      return_def, raise_def, AllCaseEqs()] >>
  irule lookup_immutable_set_other >> goal_assum (drule_at Any) >> simp[]
QED

Theorem supported_pure_exprs_immutable:
  supported_pure_exprs tops exprs /\ eval_exprs cx exprs es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  metis_tac[supported_pure_immutable_mutual]
QED

Theorem supported_pure_expr_results_immutable:
  !exprs tops cx es res es' src name.
  EVERY (supported_pure_expr tops) exprs /\
  eval_expr_results cx exprs es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  Induct_on `exprs` >> simp[Once evaluate_def, return_def] >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac supported_pure_immutable_mutual >> metis_tac[]
QED

Theorem supported_effect_immutable_mutual:
  (!tops e. supported_effect_expr tops e ==>
    ~supported_expr_exists expr_internal_call_root e ==>
    !cx es res es' src name.
    expr_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))) e /\
    eval_expr cx e es = (res,es') ==>
    lookup_immutable cx es' src name = lookup_immutable cx es src name) /\
  (!tops e. supported_effect_place_expr tops e ==>
    ~supported_expr_exists expr_internal_call_root e ==>
    !cx es res es' src name.
    expr_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))) e /\
    eval_expr cx e es = (res,es') ==>
    lookup_immutable cx es' src name = lookup_immutable cx es src name)
Proof
  ho_match_mp_tac supported_effect_expr_ind >> rpt conj_tac >>
  simp[supported_effect_expr_def, supported_expr_exists_def,
       expr_internal_call_root_def, expr_writes_ok_def] >> rpt strip_tac
  >>~- ([`eval_expr _ (Subscript _ _ _) _ = _`],
    gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
    imp_res_tac read_result_state >> imp_res_tac select_result_state >>
    imp_res_tac supported_pure_immutable_mutual >> gvs[] >> metis_tac[])
  >>~- ([`eval_expr _ (Attribute _ _ _) _ = _`],
    gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
    imp_res_tac select_result_state >> gvs[] >> metis_tac[])
  >~ [`eval_expr _ (Call _ (ExtCall _ _ _ _) _ _) _ = _`]
  >- suspend "external"
  >~ [`eval_expr _ (Call _ (Send F) _ _) _ = _`] >- suspend "send2"
  >~ [`eval_expr _ (Call _ (Send T) _ _) _ = _`] >- suspend "send3"
  >> suspend "pop"
QED

Resume supported_effect_immutable_mutual[external]:
  `!n. supported_pure_exprs tops (TAKE n args)` by
    (gvs[supported_pure_exprs_every] >> metis_tac[EVERY_TAKE]) >>
  `!n. supported_pure_exprs tops (DROP n args)` by
    (gvs[supported_pure_exprs_every] >> metis_tac[EVERY_DROP]) >>
  `!n m. EVERY (supported_pure_expr tops) (TAKE n (DROP m args))` by
    (gvs[supported_pure_exprs_every] >> metis_tac[EVERY_TAKE, EVERY_DROP]) >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac eval_ext_call_preserves_non_accounts >>
  imp_res_tac read_results_state >>
  imp_res_tac supported_pure_exprs_immutable >>
  imp_res_tac supported_pure_expr_results_immutable >>
  gvs[lookup_immutable_def] >> metis_tac[]
QED

Resume supported_effect_immutable_mutual[send2]:
  `supported_pure_exprs tops [a;v]` by simp[supported_pure_expr_def] >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
      assert_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac eval_send_preserves_non_accounts >>
  imp_res_tac supported_pure_immutable_mutual >>
  imp_res_tac read_result_state >> gvs[lookup_immutable_def] >> metis_tac[]
QED

Resume supported_effect_immutable_mutual[send3]:
  `supported_pure_exprs tops [a;v;g]` by simp[supported_pure_expr_def] >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
      assert_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac eval_send_preserves_non_accounts >>
  imp_res_tac supported_pure_immutable_mutual >>
  imp_res_tac read_result_state >> gvs[lookup_immutable_def] >> metis_tac[]
QED

Resume supported_effect_immutable_mutual[pop]:
  rename1 `eval_expr cx (Pop ty (TopLevelNameTarget nsid)) es = _` >>
  PairCases_on `nsid` >>
  irule immutable_direct_pop_other >> goal_assum (drule_at Any) >>
  gvs[place_contains_def, place_access_def]
QED

Finalise supported_effect_immutable_mutual

Theorem supported_expr_immutable:
  supported_expr tops e /\ ~supported_expr_exists expr_internal_call_root e /\
  expr_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))) e /\
  eval_expr cx e es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  simp[supported_expr_def] >>
  metis_tac[supported_pure_immutable_mutual, supported_effect_immutable_mutual]
QED

Theorem supported_exprs_immutable:
  !exprs tops cx es res es' src name.
  EVERY (\e. supported_expr tops e /\
    ~supported_expr_exists expr_internal_call_root e /\
    expr_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))) e) exprs /\
  eval_exprs cx exprs es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  Induct_on `exprs` >> simp[Once evaluate_def, return_def] >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> gvs[] >> metis_tac[supported_expr_immutable]
QED
