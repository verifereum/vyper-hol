(* Frame one immutable binding, rather than the whole immutable store. *)
Theory whitelistForIterImmFrame
Ancestors
  vyperBareGlobalName vyperPlaceFrames vyperState vyperTypeSystem
  stmtSimForArrayFrame vyperStatePreservation supportedExprs supportedExprForms supportedExprTraverse
  vyperTypeInvariants vyperInterpreter vyperCallOutcomeFrame vyperAST list rich_list finite_map alist
  supportedStmts supportedStmtTraverse

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
  Cases_on `blt = Bop In \/ blt = Bop NotIn` >>
  gvs[Once evaluate_def, type_check_def, assert_def, bind_def,
      ignore_bind_def, return_def, raise_def, AllCaseEqs(), get_accounts_def] >>
  imp_res_tac next_gas_reading_state >>
  imp_res_tac lift_option_type_state >>
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

Theorem supported_target_eval_immutable:
  !target tops bindings pt cx es res es' src name.
  supported_target_info tops bindings target = SOME pt /\
  ~supported_target_exists expr_internal_call_root target /\
  target_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))) target /\
  eval_base_place cx target es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  measureInduct_on `base_assignment_target_size target` >>
  Cases_on `target` >> rpt strip_tac
  >~ [`eval_base_place _ (NameTarget _) _ = _`]
  >- gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
         type_check_def, assert_def, return_def, raise_def, AllCaseEqs()]
  >~ [`eval_base_place _ (TopLevelNameTarget _) _ = _`]
  >- (rename1 `eval_base_place cx (TopLevelNameTarget nsid) es = _` >>
      PairCases_on `nsid` >> gvs[Once evaluate_def] >>
      drule lookup_global_state >> simp[]) >>
  gvs[supportedTargetsTheory.supported_target_info_def, supported_expr_exists_def,
      expr_writes_ok_def, AllCaseEqs()] >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  imp_res_tac extend_place_state >> imp_res_tac read_result_state >> gvs[] >>
  rename1 `supported_target_info tops bindings inner = SOME inner_pt` >>
  first_x_assum (qspec_then `inner` mp_tac) >> simp[] >>
  disch_then drule_all >> strip_tac >>
  metis_tac[supported_expr_immutable]
QED

Theorem supported_target_place_immutable:
  supported_target_info tops bindings target = SOME pt /\
  ~supported_target_exists expr_internal_call_root target /\
  target_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))) target /\
  eval_target_place cx target es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  imp_res_tac supported_target_eval_immutable >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >> metis_tac[]
QED

Theorem supported_simple_target_eval_immutable:
  !target tops bindings cx es res es' src name.
  supported_target tops bindings target /\
  ~supported_target_exists expr_internal_call_root target /\
  target_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))) target /\
  eval_base_place cx target es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  Cases_on `target` >>
  simp[supportedStmtsTheory.supported_target_def, supported_expr_exists_def, expr_writes_ok_def] >> rpt strip_tac
  >~ [`eval_base_place _ (NameTarget _) _ = _`]
  >- gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
         type_check_def, assert_def, return_def, raise_def, AllCaseEqs()]
  >>~- ([`eval_base_place _ (TopLevelNameTarget _) _ = _`],
      rename1 `eval_base_place cx (TopLevelNameTarget nsid) es = _` >>
      PairCases_on `nsid` >> gvs[Once evaluate_def] >>
      drule lookup_global_state >> simp[])
  >~ [`eval_base_place _ (SubscriptTarget _ _) _ = _`]
  >- suspend "subscript"
  >> suspend "attribute"
QED

Resume supported_simple_target_eval_immutable[subscript]:
  rename1 `eval_base_place cx (SubscriptTarget inner key) es = _` >>
  Cases_on `inner` >> gvs[expr_writes_ok_def] >>
  rename1 `eval_base_place cx (SubscriptTarget (TopLevelNameTarget nsid) key) es = _` >>
  PairCases_on `nsid` >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  imp_res_tac lookup_global_state >> imp_res_tac read_result_state >>
  imp_res_tac extend_place_state >> gvs[] >> metis_tac[supported_expr_immutable]
QED

Resume supported_simple_target_eval_immutable[attribute]:
  rename1 `eval_base_place cx (AttributeTarget inner fname) es = _` >>
  Cases_on `inner` >> gvs[expr_writes_ok_def] >>
  rename1 `eval_base_place cx (AttributeTarget (TopLevelNameTarget nsid) fname) es = _` >>
  PairCases_on `nsid` >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  imp_res_tac lookup_global_state >> imp_res_tac extend_place_state >> gvs[]
QED

Finalise supported_simple_target_eval_immutable

Theorem supported_any_target_place_immutable:
  (supported_target tops bindings target \/
   (?pt. supported_target_info tops bindings target = SOME pt)) /\
  ~supported_target_exists expr_internal_call_root target /\
  target_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))) target /\
  eval_target_place cx target es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  rpt strip_tac
  >- (gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
      imp_res_tac supported_simple_target_eval_immutable >>
      Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >> metis_tac[]) >>
  metis_tac[supported_target_place_immutable]
QED

Theorem typed_guarded_target_write_immutable:
  (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
   type_place_target env (TopLevelNameTarget (src,name)) = SOME (Type (ArrayT elem bound))) /\
  type_place_target env target = SOME vt /\
  ~place_contains target (TopLevelNameTarget (src,name)) /\
  (supported_target tops bindings target \/
   (?pt. supported_target_info tops bindings target = SOME pt)) /\
  ~supported_target_exists expr_internal_call_root target /\
  target_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))) target /\
  (do p <- eval_target_place cx target; write_place cx p v od) es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  strip_tac >> gvs[bind_def, AllCaseEqs(), raise_def] >>
  imp_res_tac supported_any_target_place_immutable >>
  metis_tac[typed_guarded_immutable_target_write]
QED

Theorem typed_guarded_base_assignment_immutable:
  (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
   type_place_target env (TopLevelNameTarget (src,name)) = SOME (Type (ArrayT elem bound))) /\
  well_typed_atarget env (BaseTarget bt) ty /\
  atarget_writes_ok (\t. ~place_contains t (TopLevelNameTarget (src,name))) (BaseTarget bt) /\
  (supported_target tops bindings bt \/
   (?pt. supported_target_info tops bindings bt = SOME pt)) /\
  ~supported_target_exists expr_internal_call_root bt /\
  assign_tuple_targets cx (BaseTarget bt) v es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  strip_tac >>
  gvs[well_typed_atarget_def, well_typed_target_def, atarget_writes_ok_def] >>
  qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >>
  irule typed_guarded_target_write_immutable >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem typed_guarded_flat_targets_immutable:
  !targets tys env src name elem bound tops bindings cx vs es res es'.
  (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
   type_place_target env (TopLevelNameTarget (src,name)) = SOME (Type (ArrayT elem bound))) /\
  LIST_REL (\tgt ty. well_typed_atarget env tgt ty) targets tys /\
  EVERY (\g. case g of BaseTarget bt => supported_target tops bindings bt
                       | TupleTarget _ => F) targets /\
  EVERY (atarget_writes_ok (\t. ~place_contains t (TopLevelNameTarget (src,name)))) targets /\
  ~supported_assignments_exists expr_internal_call_root targets /\
  assign_tuple_target_list cx targets vs es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  Induct_on `targets` >> Cases_on `vs` >>
  simp[Once evaluate_def, return_def, raise_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `tys` >> gvs[] >>
  rename1 `well_typed_atarget env head head_ty` >>
  Cases_on `head` >> gvs[supportedStmtTraverseTheory.supported_assignment_exists_def] >>
  gvs[ignore_bind_def, bind_def, AllCaseEqs(), raise_def] >>
  drule_at (Pat `assign_tuple_targets _ _ _ _ = _`)
    typed_guarded_base_assignment_immutable >>
  simp[] >> strip_tac >> metis_tac[]
QED

Theorem typed_guarded_assignment_immutable:
  (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
   type_place_target env (TopLevelNameTarget (src,name)) = SOME (Type (ArrayT elem bound))) /\
  well_typed_atarget env target ty /\
  atarget_writes_ok (\t. ~place_contains t (TopLevelNameTarget (src,name))) target /\
  supported_assignment tops bindings target rhs /\
  ~supported_assignment_exists expr_internal_call_root target /\
  assign_tuple_targets cx target v es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  Cases_on `target` >> rpt strip_tac
  >>~- ([`assign_tuple_targets _ (BaseTarget _) _ _ = _`],
      rename1 `assign_tuple_targets cx (BaseTarget bt) v es = _` >>
      gvs[supported_assignment_def, AllCaseEqs(), supported_assignment_exists_def] >>
      irule typed_guarded_base_assignment_immutable >>
      goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[] >>
      qexistsl_tac [`bindings`,`tops`] >> simp[] >>
      Cases_on `supported_target_info tops bindings bt` >> gvs[]) >>
  gvs[well_typed_atarget_def, supported_assignment_def, atarget_writes_ok_def,
      supported_assignment_exists_def] >>
  Cases_on `v` >>
  gvs[Once evaluate_def, raise_def, vyperValueTheory.array_value_CASE_rator,
      AllCaseEqs()] >>
  irule typed_guarded_flat_targets_immutable >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem assign_immutable_frame:
  (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
   type_place_target env (TopLevelNameTarget (src,name)) = SOME (Type (ArrayT elem bound))) /\
  well_typed_atarget env target ty /\
  atarget_writes_ok (\t. ~place_contains t (TopLevelNameTarget (src,name))) target /\
  supported_assignment tops bindings target rhs /\
  ~supported_assignment_exists expr_internal_call_root target /\
  (!s r t. eval_expr cx rhs s = (r,t) ==>
    lookup_immutable cx t src name = lookup_immutable cx s src name) /\
  eval_stmt cx (Assign target rhs) es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  Cases_on `target` >> disch_tac
  >>~- ([`eval_stmt _ (Assign (BaseTarget _) _) _ = _`], suspend "base")
  >> suspend "tuple"
QED

Resume assign_immutable_frame[tuple]:
  pop_assum strip_assume_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> gvs[IgnAsm `!s r t. _`] >>
  first_x_assum drule >> strip_tac >>
  drule_at (Pat `assign_tuple_targets _ _ _ _ = _`) typed_guarded_assignment_immutable >>
  simp[] >> metis_tac[]
QED

Resume assign_immutable_frame[base]:
  pop_assum strip_assume_tac >>
  rename1 `eval_stmt cx (Assign (BaseTarget bt) rhs) es = _` >>
  gvs[well_typed_atarget_def, well_typed_target_def, atarget_writes_ok_def,
      supported_assignment_def, supported_assignment_exists_def, AllCaseEqs()] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> gvs[IgnAsm `!s r t. _`] >>
  first_x_assum drule >> strip_tac >>
  Cases_on `supported_target_info tops bindings bt` >> gvs[] >>
  imp_res_tac supported_any_target_place_immutable >>
  metis_tac[typed_guarded_immutable_target_write]
QED

Finalise assign_immutable_frame

Theorem augassign_immutable_frame:
  (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
   type_place_target env (TopLevelNameTarget (src,name)) = SOME (Type (ArrayT elem bound))) /\
  well_typed_target env bt ty /\ ~place_contains bt (TopLevelNameTarget (src,name)) /\
  (supported_target tops bindings bt \/
   (?pt. supported_target_info tops bindings bt = SOME pt)) /\
  ~supported_target_exists expr_internal_call_root bt /\
  target_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))) bt /\
  (!s r t. eval_expr cx rhs s = (r,t) ==>
    lookup_immutable cx t src name = lookup_immutable cx s src name) /\
  eval_stmt cx (AugAssign ty bt bop rhs) es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  strip_tac >> gvs[well_typed_target_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_place_state >> imp_res_tac place_type_value_state >>
  imp_res_tac read_result_state >> imp_res_tac lift_sum_state >>
  imp_res_tac supported_any_target_place_immutable >>
  gvs[IgnAsm `!s r t. _`] >> first_x_assum drule >> strip_tac >>
  all_tac
  >>~- ([`write_place _ _ _ _ = _`],
    qmatch_asmsub_rename_tac `write_place cx p result write_state` >>
    `lookup_immutable cx es' src name = lookup_immutable cx write_state src name`
      suffices_by metis_tac[] >>
    irule lookup_immutable_write_other >>
    goal_assum (drule_at Any) >> rpt strip_tac >> gvs[] >>
    drule eval_target_place_immutable_root >> strip_tac >>
    drule_at (Pat `type_place_target env bt`) typed_guarded_array_root >>
    simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem append_guarded_immutable_frame:
  append_place cx p v es = (res,es') /\
  (!other_src other_name path. p = ImmutablePlace other_src other_name path ==>
     (other_src,other_name) <> (src,name)) ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  Cases_on `p` >> rpt strip_tac
  >~ [`append_place _ (StoragePlace _ _ _) _ _ = _`]
  >- (drule vyperScopePreservationTheory.append_storage_place_scopes_immutables >>
      simp[lookup_immutable_def]) >>
  gvs[append_place_def, bind_def, AllCaseEqs()] >>
  imp_res_tac read_place_state >> imp_res_tac place_type_value_state >>
  imp_res_tac lift_sum_state >> gvs[] >>
  irule lookup_immutable_write_other >> goal_assum (drule_at Any) >> simp[]
QED


Theorem get_place_state_immutable[local]:
  get_place pv s = (r,t) ==> t = s
Proof
  Cases_on `pv` >> simp[get_place_def, return_def, raise_def] >> strip_tac >> gvs[]
QED

Theorem get_place_success_immutable[local]:
  get_place pv s = (INL p,t) ==> pv = PlaceR p /\ t = s
Proof
  Cases_on `pv` >> simp[get_place_def, return_def, raise_def] >> strip_tac >> gvs[]
QED

Theorem same_immutables_observation[local]:
  t.immutables = s.immutables ==>
  lookup_immutable cx t src name = lookup_immutable cx s src name
Proof
  simp[lookup_immutable_def]
QED

Theorem append_immutable_frame:
  supported_append_target tops bt /\
  ~place_contains bt (TopLevelNameTarget (src,name)) /\
  (!s r t. eval_expr cx rhs s = (r,t) ==>
    lookup_immutable cx t src name = lookup_immutable cx s src name) /\
  eval_stmt cx (Append bt rhs) es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  Cases_on `bt` >> strip_tac >> gvs[supported_append_target_def] >>
  rename1 `eval_stmt cx (Append (TopLevelNameTarget nsid) rhs) es = _` >>
  PairCases_on `nsid` >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  imp_res_tac vyperImmutablesPreservationTheory.lookup_global_immutables >>
  imp_res_tac same_immutables_observation >>
  imp_res_tac get_place_state_immutable >>
  imp_res_tac get_place_success_immutable >>
  imp_res_tac read_result_state >> gvs[IgnAsm `!s r t. _`] >>
  qpat_x_assum `!s r t. eval_expr _ _ _ = _ ==> _` (fn th => imp_res_tac th) >>
  all_tac
  >>~- ([`append_place _ _ _ _ = _`],
    qmatch_asmsub_rename_tac `append_place cx p value mid` >>
    `!other_src other_name path. p = ImmutablePlace other_src other_name path ==>
       (other_src,other_name) <> (src,name)` by
      (rpt strip_tac >> gvs[] >> drule lookup_global_immutable_root >>
       gvs[place_contains_def, place_access_def]) >>
    drule_all append_guarded_immutable_frame >> strip_tac >> metis_tac[]) >>
  metis_tac[]
QED

Theorem typed_assign_immutable_frame:
  (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
   type_place_target env (TopLevelNameTarget (src,name)) = SOME (Type (ArrayT elem bound))) /\
  supported_stmt tops bindings (Assign target rhs) /\
  type_stmt env ret_ty (Assign target rhs) = SOME env' /\
  stmt_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))) (Assign target rhs) /\
  ~supported_stmt_expr_exists expr_internal_call_root (Assign target rhs) /\
  eval_stmt cx (Assign target rhs) es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  strip_tac >>
  gvs[supported_stmt_def, type_stmt_def, stmt_writes_ok_def,
      supported_stmt_expr_exists_def, AllCaseEqs()] >>
  drule_all vyperTypeArgFitsTheory.atarget_accepts_well_typed_atarget >> strip_tac >>
  `supported_expr tops rhs` by
    (Cases_on `target` >> gvs[supported_assignment_def]) >>
  irule assign_immutable_frame >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[supported_expr_immutable]
QED

Theorem typed_augassign_immutable_frame:
  (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
   type_place_target env (TopLevelNameTarget (src,name)) = SOME (Type (ArrayT elem bound))) /\
  supported_stmt tops bindings (AugAssign ty target bop rhs) /\
  type_stmt env ret_ty (AugAssign ty target bop rhs) = SOME env' /\
  stmt_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))) (AugAssign ty target bop rhs) /\
  ~supported_stmt_expr_exists expr_internal_call_root (AugAssign ty target bop rhs) /\
  eval_stmt cx (AugAssign ty target bop rhs) es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  strip_tac >>
  gvs[supported_stmt_def, type_stmt_def, stmt_writes_ok_def,
      supported_stmt_expr_exists_def, AllCaseEqs()] >>
  irule augassign_immutable_frame >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`bindings`,`tops`] >> simp[] >>
  gvs[supported_aug_target_def, AllCaseEqs()] >>
  Cases_on `supported_target_info tops bindings target` >> gvs[] >>
  metis_tac[supported_expr_immutable]
QED

Theorem typed_append_immutable_frame:
  supported_stmt tops bindings (Append target rhs) /\
  type_stmt env ret_ty (Append target rhs) = SOME env' /\
  stmt_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))) (Append target rhs) /\
  ~supported_stmt_expr_exists expr_internal_call_root (Append target rhs) /\
  eval_stmt cx (Append target rhs) es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  strip_tac >>
  gvs[supported_stmt_def, stmt_writes_ok_def, supported_stmt_expr_exists_def] >>
  irule append_immutable_frame >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[supported_pure_immutable_mutual]
QED

Theorem immutable_target_type_extend_local:
  type_place_target (extend_local env id ty assignable) (TopLevelNameTarget (src,name)) =
  type_place_target env (TopLevelNameTarget (src,name))
Proof
  simp[well_typed_expr_def, extend_local_def]
QED

Theorem immutable_target_type_stmt:
  type_stmt env ret_ty stmt = SOME env' ==>
  type_place_target env' (TopLevelNameTarget (src,name)) =
  type_place_target env (TopLevelNameTarget (src,name))
Proof
  strip_tac >> drule vyperTypeEnvExtensionTheory.type_stmt_preserve_nonlocal_fields >>
  strip_tac >> simp[well_typed_expr_def]
QED

Theorem immutable_target_type_stmts:
  type_stmts env ret_ty stmts = SOME env' ==>
  type_place_target env' (TopLevelNameTarget (src,name)) =
  type_place_target env (TopLevelNameTarget (src,name))
Proof
  strip_tac >> drule vyperTypeEnvExtensionTheory.type_stmts_preserve_nonlocal_fields >>
  strip_tac >> simp[well_typed_expr_def]
QED

Theorem finally_pop_immutable_frame:
  (!s r t. action s = (r,t) ==>
    lookup_immutable cx t src name = lookup_immutable cx s src name) /\
  finally action pop_scope es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  strip_tac >>
  gvs[finally_def, ignore_bind_def, bind_def, pop_scope_def,
      return_def, raise_def, AllCaseEqs()] >>
  first_x_assum drule >> strip_tac >>
  gvs[lookup_immutable_def]
QED

Theorem loop_action_immutable_frame:
  !cx body src name es res es'.
  (!s r t. eval_stmts cx body s = (r,t) ==>
    lookup_immutable cx t src name = lookup_immutable cx s src name) /\
  try (do eval_stmts cx body; return F od) handle_loop_exception es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  rpt gen_tac >> strip_tac >>
  gvs[try_def, ignore_bind_def, bind_def, return_def, AllCaseEqs(),
      handle_loop_exception_def, raise_def] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  Cases_on `e = ContinueException` >> Cases_on `e = BreakException` >>
  gvs[return_def, raise_def]
QED

Theorem eval_for_immutable_frame:
  !vs cx tyv id stmts src name es res es'.
  (!s r t. eval_stmts cx stmts s = (r,t) ==>
    lookup_immutable cx t src name = lookup_immutable cx s src name) /\
  eval_for cx tyv id stmts vs es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  Induct_on `vs` >> simp[Once evaluate_def, return_def] >>
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `finally action pop_scope` >>
  `!s r t. action s = (r,t) ==>
    lookup_immutable cx t src name = lookup_immutable cx s src name` by
    (rpt gen_tac >> simp[Abbr `action`] >> strip_tac >>
     irule loop_action_immutable_frame >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `ignore_bind _ _ es = _` mp_tac >>
  simp[push_scope_with_var_def, ignore_bind_def, bind_def, return_def,
       AllCaseEqs()] >> strip_tac >>
  imp_res_tac finally_pop_immutable_frame >>
  gvs[AllCaseEqs(), return_def] >>
  `!f. lookup_immutable cx (es with scopes updated_by f) src name =
     lookup_immutable cx es src name` by simp[lookup_immutable_def] >>
  gvs[] >>~- ([`(if broke then _ else _) _ = _`],
    Cases_on `broke` >> gvs[return_def] >>
    first_x_assum drule_all >> simp[]) >>
  gvs[raise_def]
QED

Theorem for_immutable_frame:
  !cx id typ it n stmts src name es res es'.
    (!s r t. eval_iterator cx it s = (r,t) ==>
      lookup_immutable cx t src name = lookup_immutable cx s src name) /\
    (!s r t. eval_stmts cx stmts s = (r,t) ==>
      lookup_immutable cx t src name = lookup_immutable cx s src name) /\
    eval_stmt cx (For id typ it n stmts) es = (res,es') ==>
    lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  strip_tac >> imp_res_tac lift_option_type_state >> imp_res_tac check_state >>
  gvs[IgnAsm `!s r t. _`] >>
  qpat_x_assum `!s r t. eval_iterator _ _ _ = _ ==> _` drule >> strip_tac
  >~ [`eval_for _ _ _ _ _ _ = _`]
  >- (drule_at (Pat `eval_for _ _ _ _ _ _ = _`) eval_for_immutable_frame >>
      disch_then (qspecl_then [`src`,`name`] mp_tac) >>
      (impl_tac >- simp[]) >> simp[]) >>
  gvs[IgnAsm `!s r t. _`]
QED

Theorem annassign_immutable_frame:
  !cx id typ e src name es res es'.
    (!s r t. eval_expr cx e s = (r,t) ==>
      lookup_immutable cx t src name = lookup_immutable cx s src name) /\
    eval_stmt cx (AnnAssign id typ e) es = (res,es') ==>
    lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac lift_option_type_state >> imp_res_tac read_result_state >>
  gvs[IgnAsm `!s r t. _`] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  qpat_x_assum `new_variable _ _ _ _ = _` mp_tac >>
  simp[new_variable_def, get_scopes_def, set_scopes_def, bind_def,
       ignore_bind_def, type_check_def, assert_def,
       lift_option_type_def, return_def, raise_def, AllCaseEqs()] >>
  strip_tac >> rename1 `lookup_scopes id mid.scopes = NONE` >>
  Cases_on `mid.scopes` >>
  gvs[set_scopes_def, return_def, raise_def, lookup_immutable_def]
QED

Theorem if_immutable_frame:
  !cx e ss1 ss2 src name es res es'.
    (!s r t. eval_expr cx e s = (r,t) ==>
      lookup_immutable cx t src name = lookup_immutable cx s src name) /\
    (!s r t. eval_stmts cx ss1 s = (r,t) ==>
      lookup_immutable cx t src name = lookup_immutable cx s src name) /\
    (!s r t. eval_stmts cx ss2 s = (r,t) ==>
      lookup_immutable cx t src name = lookup_immutable cx s src name) /\
    eval_stmt cx (If e ss1 ss2) es = (res,es') ==>
    lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, ignore_bind_def, push_scope_def,
       get_scopes_def, set_scopes_def, return_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `!s r t. eval_expr _ _ _ = _ ==> _` drule >> strip_tac
  >~ [`v = INR exc`]
  >- gvs[IgnAsm `!s r t. _`] >>
  `!s r t. switch_BoolV cx tv (eval_stmts cx ss1) (eval_stmts cx ss2) s = (r,t) ==>
     lookup_immutable cx t src name = lookup_immutable cx s src name` by
    (rpt gen_tac >>
     simp[switch_BoolV_def, bind_def, AllCaseEqs()] >> strip_tac >>
     imp_res_tac read_result_state >> gvs[] >>
     rename1 `(if value = BoolV T then _ else _) _ = _` >>
     Cases_on `value = BoolV T` >> Cases_on `value = BoolV F` >>
     gvs[raise_def] >> first_x_assum drule >> simp[]) >>
  drule_at (Pat `finally _ _ _ = _`) finally_pop_immutable_frame >>
  disch_then (qspecl_then [`src`,`name`,`cx`] mp_tac) >>
  (impl_tac >- simp[]) >>
  `!f. lookup_immutable cx (s'' with scopes updated_by f) src name =
       lookup_immutable cx s'' src name` by simp[NoAsms, lookup_immutable_def] >>
  simp[]
QED

Theorem range_iterator_immutable_frame:
  !cx a b src name es res es'.
    (!s r t. eval_expr cx a s = (r,t) ==>
      lookup_immutable cx t src name = lookup_immutable cx s src name) /\
    (!s r t. eval_expr cx b s = (r,t) ==>
      lookup_immutable cx t src name = lookup_immutable cx s src name) /\
    eval_iterator cx (Range a b) es = (res,es') ==>
    lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> imp_res_tac lift_sum_state >>
  gvs[return_def] >> metis_tac[]
QED

Theorem array_iterator_immutable_frame:
  !cx e src name es res es'.
    (!s r t. eval_expr cx e s = (r,t) ==>
      lookup_immutable cx t src name = lookup_immutable cx s src name) /\
    eval_iterator cx (Array e) es = (res,es') ==>
    lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> imp_res_tac lift_option_type_state >>
  gvs[return_def] >> metis_tac[]
QED

Theorem literal_immutable_frame[local]:
  eval_expr cx (Literal ty lit) es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  simp[Once evaluate_def, return_def] >> rpt strip_tac >> gvs[]
QED

Theorem name_immutable_frame[local]:
  eval_expr cx (Name ty id) es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  simp[Once evaluate_def, get_scopes_def, type_check_def, assert_def,
       ignore_bind_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem typed_immutable_frames_mutual:
  (!tops bindings stmt. supported_stmt tops bindings stmt ==>
    !env ret_ty env' src name elem bound cx es res es'.
      (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
       type_place_target env (TopLevelNameTarget (src,name)) = SOME (Type (ArrayT elem bound))) /\
      type_stmt env ret_ty stmt = SOME env' /\
      stmt_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))) stmt /\
      ~supported_stmt_expr_exists expr_internal_call_root stmt /\
      eval_stmt cx stmt es = (res,es') ==>
      lookup_immutable cx es' src name = lookup_immutable cx es src name) /\
  (!tops bindings stmts. supported_stmts tops bindings stmts ==>
    !env ret_ty env' src name elem bound cx es res es'.
      (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
       type_place_target env (TopLevelNameTarget (src,name)) = SOME (Type (ArrayT elem bound))) /\
      type_stmts env ret_ty stmts = SOME env' /\
      stmts_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))) stmts /\
      ~supported_stmts_expr_exists expr_internal_call_root stmts /\
      eval_stmts cx stmts es = (res,es') ==>
      lookup_immutable cx es' src name = lookup_immutable cx es src name)
Proof
  ho_match_mp_tac supported_stmt_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac
  >>~- ([`eval_stmt _ Pass _ = _`], gvs[Once evaluate_def, return_def])
  >>~- ([`eval_stmt _ Break _ = _`], gvs[Once evaluate_def, raise_def])
  >>~- ([`eval_stmt _ Continue _ = _`], gvs[Once evaluate_def, raise_def])
  >>~- ([`eval_stmt _ (Return NONE) _ = _`], gvs[Once evaluate_def, raise_def])
  >>~- ([`eval_stmts _ [] _ = _`], gvs[Once evaluate_def, return_def])
  >>~- ([`eval_stmt _ (Assign _ _) _ = _`], metis_tac[typed_assign_immutable_frame])
  >>~- ([`eval_stmt _ (AugAssign _ _ _ _) _ = _`], metis_tac[typed_augassign_immutable_frame])
  >>~- ([`eval_stmt _ (Append _ _) _ = _`], metis_tac[typed_append_immutable_frame])
  >>~- ([`eval_stmt _ (AnnAssign _ _ _) _ = _`],
      gvs[supported_stmt_def, stmt_writes_ok_def, supported_stmt_expr_exists_def] >>
      irule annassign_immutable_frame >> goal_assum (drule_at Any) >>
      metis_tac[supported_expr_immutable])
  >>~- ([`eval_stmt _ (Expr _) _ = _`], suspend "expr")
  >>~- ([`eval_stmt _ (Return (SOME _)) _ = _`], suspend "return")
  >>~- ([`eval_stmt _ (If _ _ _) _ = _`], suspend "if")
  >>~- ([`eval_stmt _ (For _ _ _ _ _) _ = _`], suspend "for")
  >>~- ([`eval_stmt _ (Assert _ _) _ = _`], suspend "assert")
  >>~- ([`eval_stmt _ (Raise _) _ = _`], suspend "raise")
  >>~- ([`eval_stmt _ (Log _ _) _ = _`], suspend "log")
  >> suspend "cons"
QED

Resume typed_immutable_frames_mutual[expr]:
  markerLib.RESUME_TAC >>
  gvs[supported_stmt_def, stmt_writes_ok_def, supported_stmt_expr_exists_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, type_check_def, assert_def,
       ignore_bind_def, return_def, raise_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac supported_expr_immutable >> gvs[]
QED

Resume typed_immutable_frames_mutual[return]:
  markerLib.RESUME_TAC >>
  gvs[supported_stmt_def, stmt_writes_ok_def, supported_expr_exists_def, supported_stmt_expr_exists_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, raise_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac supported_expr_immutable >> imp_res_tac read_result_state >> gvs[]
QED

Resume typed_immutable_frames_mutual[if]:
  rpt gen_tac >> strip_tac >>
  gvs[IgnAsm `!env ret_ty env' src name elem bound cx es res es'. _`,
      supported_stmt_def, type_stmt_def, stmt_writes_ok_def,
      supported_stmt_expr_exists_def, AllCaseEqs()] >>
  fs[IgnAsm `!env ret_ty env' src name elem bound cx es res es'. _`,
     optionTheory.IS_SOME_EXISTS] >>
  (irule if_immutable_frame >> goal_assum (drule_at Any) >>
   (conj_tac >- metis_tac[supported_pure_immutable_mutual]) >>
   conj_tac >> rpt gen_tac >> strip_tac >> metis_tac[])
QED
Resume typed_immutable_frames_mutual[for]:
  rpt gen_tac >> strip_tac >>
  rename1 `eval_stmt cx (For id typ it n stmts) es = _` >>
  gvs[IgnAsm `!env ret_ty env' src name elem bound cx es res es'. _`,
      supported_stmt_def, type_stmt_def, stmt_writes_ok_def,
      supported_stmt_expr_exists_def, AllCaseEqs()] >>
  (irule for_immutable_frame >> goal_assum (drule_at Any) >>
   conj_tac
   >- (rpt gen_tac >> strip_tac >> Cases_on `it`
       >~ [`eval_iterator _ (Array _) _ = _`]
       >- (drule supported_array_iterator_shape >> strip_tac >> gvs[] >>
           irule array_iterator_immutable_frame >> goal_assum (drule_at Any) >>
           metis_tac[name_immutable_frame]) >>
       irule range_iterator_immutable_frame >> goal_assum (drule_at Any) >>
       rename1 `supported_iterator tops typ (Range a b) n` >>
       Cases_on `a`
       >~ [`supported_iterator _ _ (Range (Literal aty alit) _) _`]
       >- (Cases_on `b`
           >~ [`supported_iterator _ _ (Range (Literal _ _) (Literal bty blit)) _`]
           >- (Cases_on `alit` >> Cases_on `blit` >>
               gvs[supported_iterator_def, supported_iterator_exists_def] >>
               metis_tac[literal_immutable_frame, supported_pure_immutable_mutual]) >>
           gvs[supported_iterator_def, supported_iterator_exists_def] >>
           metis_tac[literal_immutable_frame, supported_pure_immutable_mutual]) >>
       gvs[supported_iterator_def, supported_iterator_exists_def] >>
       metis_tac[supported_pure_immutable_mutual]) >>
   rpt gen_tac >> strip_tac >>
   fs[IgnAsm `!env ret_ty env' src name elem bound cx es res es'. _`,
      optionTheory.IS_SOME_EXISTS] >>
   metis_tac[immutable_target_type_extend_local])
QED
Resume typed_immutable_frames_mutual[assert]:
  markerLib.RESUME_TAC >> (  rename1 `eval_stmt cx (Assert cond reason) es = _` >>
  Cases_on `reason` >> gvs[supported_stmt_def, supported_assert_reason_def,
      supported_stmt_expr_exists_def, supported_assert_exists_def]
  >~ [`eval_stmt _ (Assert _ AssertBare) _ = _`]
  >- suspend "assert_bare"
  >~ [`eval_stmt _ (Assert _ AssertUnreachable) _ = _`]
  >- suspend "assert_unreachable"
  >> suspend "assert_reason")
QED
Resume typed_immutable_frames_mutual[raise]:
  markerLib.RESUME_TAC >> (  rename1 `eval_stmt cx (Raise reason) es = _` >>
  Cases_on `reason` >>
  gvs[supported_stmt_def, supported_raise_reason_def,
      supported_stmt_expr_exists_def, supported_raise_exists_def]
  >~ [`eval_stmt _ (Raise RaiseBare) _ = _`]
  >- gvs[Once evaluate_def, raise_def]
  >~ [`eval_stmt _ (Raise RaiseUnreachable) _ = _`]
  >- gvs[Once evaluate_def, raise_def] >>
  rename1 `supported_string_reason tops rhs` >>
  `!s r t. eval_expr cx rhs s = (r,t) ==>
     lookup_immutable cx t src name = lookup_immutable cx s src name` by
    (Cases_on `rhs` >> gvs[supported_string_reason_def] >>
     metis_tac[literal_immutable_frame, supported_pure_immutable_mutual]) >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, raise_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> imp_res_tac lift_option_type_state >>
  gvs[IgnAsm `!s r t. _`] >> first_x_assum drule >> strip_tac >> gvs[])
QED
Resume typed_immutable_frames_mutual[log]:
  markerLib.RESUME_TAC >>
  gvs[supported_stmt_def, supported_log_def,
      supported_stmt_expr_exists_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  Cases_on `cx.txn.is_static` >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac supported_pure_exprs_immutable >> imp_res_tac read_results_state >>
  imp_res_tac lift_option_state >> imp_res_tac push_log_immutables >>
  gvs[] >> metis_tac[same_immutables_observation]
QED
Resume typed_immutable_frames_mutual[cons]:
  markerLib.RESUME_TAC >>
  rpt gen_tac >> strip_tac >>
  fs[supported_stmt_def] >>
  gvs[IgnAsm `!env ret_ty env' src name elem bound cx es res es'. _`,
      stmt_writes_ok_def, supported_stmt_expr_exists_def,
      Once type_stmt_def, AllCaseEqs()] >>
  imp_res_tac immutable_target_type_stmt >>
  qpat_x_assum `eval_stmts _ (_::_) _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, ignore_bind_def, bind_def, AllCaseEqs()] >>
  strip_tac >>
  `lookup_immutable cx s'' src name = lookup_immutable cx es src name` by
    (qpat_assum `!env ret_ty env' src name elem bound cx es res es'.
       _ /\ type_stmt _ _ _ = _ /\ _ ==> _` irule >>
     goal_assum (drule_at Any) >>
     conj_tac >- metis_tac[] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  gvs[] >>
  `lookup_immutable cx es' src name = lookup_immutable cx s'' src name`
    suffices_by metis_tac[] >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  conj_tac >- metis_tac[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
Resume typed_immutable_frames_mutual[assert_bare]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> imp_res_tac supported_pure_immutable_mutual >>
  gvs[return_def, raise_def, AllCaseEqs()] >>
  rename1 `(if v = BoolV T then _ else _) _ = _` >>
  Cases_on `v = BoolV T` >> Cases_on `v = BoolV F` >>
  gvs[return_def, raise_def]
QED

Resume typed_immutable_frames_mutual[assert_unreachable]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> imp_res_tac supported_pure_immutable_mutual >>
  gvs[return_def, raise_def, AllCaseEqs()] >>
  rename1 `(if v = BoolV T then _ else _) _ = _` >>
  Cases_on `v = BoolV T` >> Cases_on `v = BoolV F` >>
  gvs[return_def, raise_def]
QED

Resume typed_immutable_frames_mutual[assert_reason]:
  markerLib.RESUME_TAC >> (
  rename1 `supported_string_reason tops rhs` >>
  `!s r t. eval_expr cx rhs s = (r,t) ==>
     lookup_immutable cx t src name = lookup_immutable cx s src name` by
    (Cases_on `rhs` >> gvs[supported_string_reason_def] >>
     metis_tac[literal_immutable_frame, supported_pure_immutable_mutual]) >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs()] >>
  strip_tac >> imp_res_tac read_result_state >>
  imp_res_tac supported_pure_immutable_mutual >>
  gvs[IgnAsm `!s r t. _`, return_def, raise_def, AllCaseEqs()] >>
  rename1 `(if v = BoolV T then _ else _) _ = _` >>
  Cases_on `v = BoolV T`
  >- (qpat_x_assum `!s r t. _` kall_tac >> gvs[return_def]) >>
  Cases_on `v = BoolV F`
  >- (gvs[IgnAsm `!s r t. _`, bind_def, AllCaseEqs()] >>
      imp_res_tac read_result_state >> imp_res_tac lift_option_type_state >>
      gvs[IgnAsm `!s r t. _`, raise_def] >>
      first_x_assum drule >> strip_tac >> gvs[]) >>
  qpat_x_assum `!s r t. _` kall_tac >> gvs[raise_def])
QED
Finalise typed_immutable_frames_mutual

Theorem typed_stmt_immutable_frame:
  supported_stmt tops bindings stmt /\
  (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
   type_place_target env (TopLevelNameTarget (src,name)) = SOME (Type (ArrayT elem bound))) /\
  type_stmt env ret_ty stmt = SOME env' /\
  stmt_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))) stmt /\
  ~supported_stmt_expr_exists expr_internal_call_root stmt /\
  eval_stmt cx stmt es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  metis_tac[typed_immutable_frames_mutual]
QED

Theorem typed_stmts_immutable_frame:
  supported_stmts tops bindings stmts /\
  (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
   type_place_target env (TopLevelNameTarget (src,name)) = SOME (Type (ArrayT elem bound))) /\
  type_stmts env ret_ty stmts = SOME env' /\
  stmts_writes_ok (\w. ~place_contains w (TopLevelNameTarget (src,name))) stmts /\
  ~supported_stmts_expr_exists expr_internal_call_root stmts /\
  eval_stmts cx stmts es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  metis_tac[typed_immutable_frames_mutual]
QED

Theorem coherent_immutable_array_target_type[local]:
  env_context_consistent env cx /\
  FLOOKUP env.bare_globals (src,name) = SOME (ArrayT elem bound) ==>
  (type_place_target env (TopLevelNameTarget (src,name)) = NONE \/
   type_place_target env (TopLevelNameTarget (src,name)) = SOME (Type (ArrayT elem bound)))
Proof
  strip_tac >>
  Cases_on `FLOOKUP env.bare_global_assignable (src,name)`
  >- simp[well_typed_expr_def] >>
  fs[env_context_consistent_def] >>
  `x = ArrayT elem bound` by metis_tac[optionTheory.SOME_11] >>
  gvs[well_typed_expr_def]
QED

Theorem immutable_array_body_observation:
  env_context_consistent env cx /\
  FLOOKUP env.bare_globals (src,name) = SOME (ArrayT elem bound) /\
  supported_stmts tops bindings stmts /\
  type_stmts env ret_ty stmts = SOME env' /\
  iterator_unmodified (Array (TopLevelName (ArrayT elem bound) (src,name))) stmts /\
  ~supported_stmts_expr_exists expr_internal_call_root stmts /\
  eval_stmts cx stmts es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  rpt strip_tac >>
  drule_all coherent_immutable_array_target_type >> strip_tac >>
  fs[iterator_unmodified_def, expr_place_def] >>
  metis_tac[typed_stmts_immutable_frame]
QED

Theorem immutable_array_body_pop_observation:
  env_context_consistent env cx /\
  FLOOKUP env.bare_globals (src,name) = SOME (ArrayT elem bound) /\
  supported_stmts tops bindings stmts /\
  type_stmts env ret_ty stmts = SOME env' /\
  iterator_unmodified (Array (TopLevelName (ArrayT elem bound) (src,name))) stmts /\
  ~supported_stmts_expr_exists expr_internal_call_root stmts /\
  finally (eval_stmts cx stmts) pop_scope es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  rpt strip_tac >>
  drule_at (Pat `finally _ _ _ = _`) finally_pop_immutable_frame >>
  disch_then irule >> metis_tac[immutable_array_body_observation]
QED
