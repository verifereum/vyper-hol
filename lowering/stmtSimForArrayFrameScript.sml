(* Scope projection frames for the source snapshot of an array iterator. *)
Theory stmtSimForArrayFrame
Ancestors
  list rich_list finite_map vyperState vyperLookup vyperScopePreservation
  supportedStmts vyperPlaceFrames supportedExprs vyperInterpreter vyperCallOutcomeFrame
  vyperStatePreservation supportedExprForms supportedExprTraverse
  vyperEvalExprPreservesScopesDom vyperPlaceResultTyping vyperTypeSystem vyperTypeEnvExtension vyperTypeArgFits

Theorem scope_projection_lookup:
  !a b name.
    MAP (\sc. FLOOKUP sc name) a = MAP (\sc. FLOOKUP sc name) b ==>
    lookup_scopes name a = lookup_scopes name b
Proof
  Induct_on `a`
  >- (Cases_on `b` >> simp[lookup_scopes_def]) >>
  Cases_on `b` >> simp[lookup_scopes_def] >> rpt strip_tac >>
  rename1 `FLOOKUP head name = FLOOKUP other name` >>
  Cases_on `FLOOKUP other name` >> gvs[]
QED

Theorem scope_projection_drop:
  !a b name n.
    MAP (\sc. FLOOKUP sc name) a = MAP (\sc. FLOOKUP sc name) b ==>
    MAP (\sc. FLOOKUP sc name) (DROP n a) =
      MAP (\sc. FLOOKUP sc name) (DROP n b)
Proof
  metis_tac[MAP_DROP]
QED

Theorem scope_projection_update_other:
  !pre sc rest root name entry.
    root <> name ==>
    MAP (\sc. FLOOKUP sc name) (pre ++ (sc |+ (root,entry)) :: rest) =
      MAP (\sc. FLOOKUP sc name) (pre ++ sc :: rest)
Proof
  simp[FLOOKUP_UPDATE]
QED

Theorem write_memory_scope_projection:
  !cx root path v es res es' name.
    root <> name /\ write_place cx (MemoryPlace root path) v es = (res,es') ==>
    MAP (\sc. FLOOKUP sc name) es'.scopes = MAP (\sc. FLOOKUP sc name) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `find_containing_scope root es.scopes`
  >- gvs[write_place_def, bind_def, get_scopes_def, lift_option_type_def,
         return_def, raise_def] >>
  rename1 `find_containing_scope root es.scopes = SOME found` >>
  PairCases_on `found` >>
  drule find_containing_scope_structure >> strip_tac >>
  rename1 `FLOOKUP local root = SOME entry` >>
  Cases_on `replace_memory_entry entry path v` >>
  gvs[write_place_def, bind_def, get_scopes_def, lift_option_type_def,
      ignore_bind_def, lift_sum_def, type_check_def, assert_def,
      set_scopes_def, return_def, raise_def, AllCaseEqs(), FLOOKUP_UPDATE]
QED


Theorem new_variable_tail_projection:
  !id tv v es res es' name.
    es.scopes <> [] /\ new_variable id tv v es = (res,es') ==>
    MAP (\sc. FLOOKUP sc name) (TL es'.scopes) =
      MAP (\sc. FLOOKUP sc name) (TL es.scopes) /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  rpt gen_tac >> Cases_on `es.scopes` >>
  simp[new_variable_def, get_scopes_def, type_check_def, assert_def,
       ignore_bind_def, bind_def, set_scopes_def, return_def, raise_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem finally_pop_scope_projection:
  !f es res es' name.
    es.scopes <> [] /\ finally f pop_scope es = (res,es') /\
    (!r t. f es = (r,t) ==>
      MAP (\sc. FLOOKUP sc name) (TL t.scopes) =
        MAP (\sc. FLOOKUP sc name) (TL es.scopes) /\
      LENGTH t.scopes = LENGTH es.scopes) ==>
    MAP (\sc. FLOOKUP sc name) es'.scopes =
      MAP (\sc. FLOOKUP sc name) (TL es.scopes) /\
    SUC (LENGTH es'.scopes) = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `f es` >> rename1 `f es = (outcome,after)` >>
  fs[] >>
  Cases_on `after.scopes`
  >- gvs[] >>
  Cases_on `outcome` >>
  gvs[finally_def, pop_scope_def, ignore_bind_def, bind_def, return_def, raise_def]
QED

Theorem supported_pure_scopes_mutual:
  (!tops e. supported_pure_expr tops e ==>
    !cx es res es'. eval_expr cx e es = (res,es') ==> es'.scopes = es.scopes) /\
  (!tops exprs. supported_pure_exprs tops exprs ==>
    !cx es res es'. eval_exprs cx exprs es = (res,es') ==> es'.scopes = es.scopes) /\
  (!tops fields. supported_pure_fields tops fields ==>
    !cx es res es'. eval_exprs cx (MAP SND fields) es = (res,es') ==>
      es'.scopes = es.scopes) /\
  (!tops e. supported_place_expr tops e ==>
    !cx es res es'. eval_expr cx e es = (res,es') ==> es'.scopes = es.scopes)
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
      drule lookup_global_scopes >> simp[])
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
  >> imp_res_tac read_result_state >> gvs[] >> metis_tac[]
QED

Resume supported_pure_scopes_mutual[ifexp]:
  gvs[Once evaluate_def, bind_def, ignore_bind_def, switch_BoolV_def,
      AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac conditional_result_state >> gvs[] >>
  gvs[COND_RATOR, AllCaseEqs(), raise_def] >> metis_tac[]
QED

Resume supported_pure_scopes_mutual[struct]:
  rename1 `eval_expr cx (StructLit ty nsid fields) es = _` >>
  PairCases_on `nsid` >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  metis_tac[]
QED

Resume supported_pure_scopes_mutual[subscript1]:
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac select_result_state >>
  gvs[] >> metis_tac[]
QED

Resume supported_pure_scopes_mutual[subscript2]:
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac select_result_state >>
  gvs[] >> metis_tac[]
QED

Resume supported_pure_scopes_mutual[attribute1]:
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac select_result_state >> gvs[] >> metis_tac[]
QED

Resume supported_pure_scopes_mutual[attribute2]:
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac select_result_state >> gvs[] >> metis_tac[]
QED

Resume supported_pure_scopes_mutual[builtin]:
  `blt <> Len` by
    (Cases_on `blt = Len` >> gvs[supported_builtin_form_def, AllCaseEqs()]) >>
  Cases_on `blt = Env MsgGas` >>
  Cases_on `blt = Bop In \/ blt = Bop NotIn` >>
  gvs[Once evaluate_def, type_check_def, assert_def, bind_def,
      ignore_bind_def, return_def, raise_def, AllCaseEqs(), get_accounts_def] >>
  imp_res_tac next_gas_reading_state >>
  imp_res_tac lift_option_type_state >>
  imp_res_tac lift_sum_state >>
  imp_res_tac precompile_call_success_state >> gvs[] >> metis_tac[]
QED

Resume supported_pure_scopes_mutual[typebuiltin]:
  gvs[Once evaluate_def, type_check_def, assert_def, bind_def,
      ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac lift_sum_state >> gvs[] >> metis_tac[]
QED

Finalise supported_pure_scopes_mutual


Theorem supported_pure_exprs_scopes:
  !tops exprs cx es res es'.
    supported_pure_exprs tops exprs /\ eval_exprs cx exprs es = (res,es') ==>
    es'.scopes = es.scopes
Proof
  metis_tac[supported_pure_scopes_mutual]
QED

Theorem supported_pure_expr_results_scopes:
  !exprs tops cx es res es'.
    EVERY (supported_pure_expr tops) exprs /\
    eval_expr_results cx exprs es = (res,es') ==> es'.scopes = es.scopes
Proof
  Induct_on `exprs` >>
  simp[Once evaluate_def, return_def] >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac supported_pure_scopes_mutual >> metis_tac[]
QED

Theorem lookup_global_not_memory:
  !cx src id es es' root path.
    lookup_global cx src id es <> (INL (PlaceR (MemoryPlace root path)),es')
Proof
  rpt strip_tac >>
  gvs[lookup_global_def, vyperMiscTheory.option_CASE_rator,
      vyperMiscTheory.prod_CASE_rator, var_decl_info_CASE_rator,
      bind_def, lift_option_type_def, return_def, raise_def, AllCaseEqs()]
QED

Theorem supported_effect_scopes_mutual:
  (!tops e. supported_effect_expr tops e ==>
    ~supported_expr_exists expr_internal_call_root e ==>
    !cx es res es'. eval_expr cx e es = (res,es') ==> es'.scopes = es.scopes) /\
  (!tops e. supported_effect_place_expr tops e ==>
    ~supported_expr_exists expr_internal_call_root e ==>
    !cx es res es'. eval_expr cx e es = (res,es') ==> es'.scopes = es.scopes)
Proof
  ho_match_mp_tac supported_effect_expr_ind >> rpt conj_tac >>
  simp[supported_effect_expr_def, supported_expr_exists_def,
       expr_internal_call_root_def] >> rpt strip_tac
  >>~- ([`eval_expr _ (Subscript _ _ _) _ = _`],
    gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
    imp_res_tac read_result_state >> imp_res_tac select_result_state >>
    imp_res_tac supported_pure_scopes_mutual >> gvs[] >> metis_tac[])
  >>~- ([`eval_expr _ (Attribute _ _ _) _ = _`],
    gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
    imp_res_tac select_result_state >> gvs[] >> metis_tac[])
  >~ [`eval_expr _ (Call _ (ExtCall _ _ _ _) _ _) _ = _`]
  >- suspend "external"
  >~ [`eval_expr _ (Call _ (Send F) _ _) _ = _`] >- suspend "send2"
  >~ [`eval_expr _ (Call _ (Send T) _ _) _ = _`] >- suspend "send3"
  >> suspend "pop"
QED

Resume supported_effect_scopes_mutual[external]:
  `!n. supported_pure_exprs tops (TAKE n args)` by
    (gvs[supported_pure_exprs_every] >> metis_tac[EVERY_TAKE]) >>
  `!n. supported_pure_exprs tops (DROP n args)` by
    (gvs[supported_pure_exprs_every] >> metis_tac[EVERY_DROP]) >>
  `!n m. EVERY (supported_pure_expr tops) (TAKE n (DROP m args))` by
    (gvs[supported_pure_exprs_every] >> metis_tac[EVERY_TAKE, EVERY_DROP]) >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac eval_ext_call_preserves_non_accounts >>
  imp_res_tac read_results_state >> imp_res_tac supported_pure_scopes_mutual >>
  gvs[] >> metis_tac[supported_pure_exprs_scopes, supported_pure_expr_results_scopes]
QED

Resume supported_effect_scopes_mutual[send2]:
  `supported_pure_exprs tops [a;v]` by simp[supported_pure_expr_def] >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
      assert_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac eval_send_preserves_non_accounts >>
  imp_res_tac supported_pure_scopes_mutual >>
  imp_res_tac read_result_state >> gvs[] >> metis_tac[]
QED

Resume supported_effect_scopes_mutual[send3]:
  `supported_pure_exprs tops [a;v;g]` by simp[supported_pure_expr_def] >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
      assert_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac eval_send_preserves_non_accounts >>
  imp_res_tac supported_pure_scopes_mutual >>
  imp_res_tac read_result_state >> gvs[] >> metis_tac[]
QED

Resume supported_effect_scopes_mutual[pop]:
  rename1 `eval_expr cx (Pop ty (TopLevelNameTarget nsid)) es = _` >>
  PairCases_on `nsid` >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  imp_res_tac lookup_global_scopes >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def, AllCaseEqs()] >>
  metis_tac[pop_nonmemory_scopes, lookup_global_not_memory]
QED

Finalise supported_effect_scopes_mutual


Theorem supported_expr_scopes:
  !tops e cx es res es'.
    supported_expr tops e /\ ~supported_expr_exists expr_internal_call_root e /\
    eval_expr cx e es = (res,es') ==> es'.scopes = es.scopes
Proof
  simp[supported_expr_def] >>
  metis_tac[supported_pure_scopes_mutual, supported_effect_scopes_mutual]
QED

Theorem supported_exprs_scopes:
  !exprs tops cx es res es'.
    EVERY (\e. supported_expr tops e /\
      ~supported_expr_exists expr_internal_call_root e) exprs /\
    eval_exprs cx exprs es = (res,es') ==> es'.scopes = es.scopes
Proof
  Induct_on `exprs` >> simp[Once evaluate_def, return_def] >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> gvs[] >> metis_tac[supported_expr_scopes]
QED


Theorem subscript_write_contains_name[local]:
  !name key.
    place_contains (SubscriptTarget (NameTarget name) key) (NameTarget name)
Proof
  simp[place_contains_def, place_access_def]
QED

Theorem iterator_unmodified_rejects_element_write[local]:
  !name key ty rhs.
    ~iterator_unmodified (Array (Name ty name))
      [Assign (BaseTarget (SubscriptTarget (NameTarget name) key)) rhs]
Proof
  simp[iterator_unmodified_def, expr_place_def, stmt_writes_ok_def,
       atarget_writes_ok_def, subscript_write_contains_name]
QED


Theorem array_name_attribute_target_rejected:
  !env name elem bound field.
    FLOOKUP env.var_types name = SOME (ArrayT elem bound) ==>
    type_place_target env (AttributeTarget (NameTarget name) field) = NONE
Proof
  rpt strip_tac >>
  Cases_on `FLOOKUP env.var_assignable name` >>
  simp[well_typed_expr_def, attribute_type_def, AllCaseEqs()] >>
  rename1 `FLOOKUP env.var_assignable name = SOME assignable` >>
  Cases_on `assignable` >> simp[]
QED

Theorem typed_array_root_access[local]:
  !target env name elem bound vt attrs.
    FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
    type_place_target env target = SOME vt /\
    FST (place_access target attrs) = NameTarget name ==>
    target = NameTarget name \/
    place_access target attrs = (NameTarget name,[])
Proof
  measureInduct_on `base_assignment_target_size target` >> Cases_on `target` >>
  simp[place_access_def, well_typed_expr_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
  >~ [`subscript_vtype _ _ = SOME _`] >- suspend "subscript"
  >> suspend "attribute"
QED

Resume typed_array_root_access[subscript]:
  rename1 `type_place_target env inner = SOME inner_ty` >>
  first_x_assum (qspec_then `inner` mp_tac) >> simp[] >>
  disch_then drule_all >>
  strip_tac >> gvs[place_access_def]
QED

Resume typed_array_root_access[attribute]:
  rename1 `type_place_target env inner = SOME (Type inner_ty)` >>
  first_x_assum (qspec_then `inner` mp_tac) >> simp[] >>
  disch_then drule_all >> strip_tac >> gvs[] >>
  gvs[well_typed_expr_def, AllCaseEqs(), attribute_type_def]
QED

Finalise typed_array_root_access

Theorem typed_guarded_array_target_root:
  !env name elem bound target vt.
    FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
    type_place_target env target = SOME vt /\
    ~place_contains target (NameTarget name) ==>
    FST (place_access target []) <> NameTarget name
Proof
  rpt strip_tac >>
  drule_all typed_array_root_access >>
  strip_tac >> gvs[place_contains_def, place_access_def]
QED

Theorem place_access_root_attrs[local]:
  !target attrs. FST (place_access target attrs) = FST (place_access target [])
Proof
  measureInduct_on `base_assignment_target_size target` >>
  Cases_on `target` >> simp[place_access_def] >> rpt strip_tac >>
  first_x_assum irule >> simp[]
QED

Theorem extend_place_memory_root[local]:
  !cx pv sb es root path es'.
    extend_place cx pv sb es = (INL (PlaceR (MemoryPlace root path)),es') ==>
    ?oldpath. pv = PlaceR (MemoryPlace root oldpath)
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

Theorem eval_base_place_memory_root:
  !target cx es root path es'.
    eval_base_place cx target es = (INL (PlaceR (MemoryPlace root path)),es') ==>
    FST (place_access target []) = NameTarget root
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
      metis_tac[lookup_global_not_memory]) >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  drule extend_place_memory_root >> strip_tac >> gvs[] >>
  rename1 `eval_base_place cx inner _ = _` >>
  first_x_assum (qspec_then `inner` mp_tac) >> simp[] >>
  disch_then drule >> simp[place_access_def, place_access_root_attrs]
QED

Theorem eval_target_place_memory_root:
  !target cx es root path es'.
    eval_target_place cx target es = (INL (MemoryPlace root path),es') ==>
    FST (place_access target []) = NameTarget root
Proof
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, get_place_def, return_def,
      raise_def, AllCaseEqs()] >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  metis_tac[eval_base_place_memory_root]
QED

Theorem typed_guarded_eval_target_root:
  !env name elem bound target vt cx es root path es'.
    FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
    type_place_target env target = SOME vt /\
    ~place_contains target (NameTarget name) /\
    eval_target_place cx target es = (INL (MemoryPlace root path),es') ==>
    root <> name
Proof
  metis_tac[typed_guarded_array_target_root, eval_target_place_memory_root]
QED

Theorem supported_target_eval_scopes:
  !target tops bindings pt cx es res es'.
    supported_target_info tops bindings target = SOME pt /\
    ~supported_target_exists expr_internal_call_root target /\
    eval_base_place cx target es = (res,es') ==> es'.scopes = es.scopes
Proof
  measureInduct_on `base_assignment_target_size target` >>
  Cases_on `target` >> rpt strip_tac
  >~ [`eval_base_place _ (NameTarget _) _ = _`]
  >- gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
         type_check_def, assert_def, return_def, raise_def, AllCaseEqs()]
  >~ [`eval_base_place _ (TopLevelNameTarget _) _ = _`]
  >- (rename1 `eval_base_place cx (TopLevelNameTarget nsid) es = _` >>
      PairCases_on `nsid` >> gvs[Once evaluate_def] >>
      metis_tac[lookup_global_scopes]) >>
  gvs[supportedTargetsTheory.supported_target_info_def,
      supported_expr_exists_def,
      AllCaseEqs()] >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  imp_res_tac extend_place_state >> imp_res_tac read_result_state >> gvs[] >>
  rename1 `supported_target_info tops bindings inner = SOME inner_pt` >>
  first_x_assum (qspec_then `inner` mp_tac) >> simp[] >>
  disch_then drule_all >> strip_tac >>
  metis_tac[supported_expr_scopes]
QED

Theorem supported_target_place_scopes:
  !target tops bindings pt cx es res es'.
    supported_target_info tops bindings target = SOME pt /\
    ~supported_target_exists expr_internal_call_root target /\
    eval_target_place cx target es = (res,es') ==> es'.scopes = es.scopes
Proof
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  imp_res_tac supported_target_eval_scopes >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def]
QED

Theorem write_guarded_place_projection:
  !cx p v es res es' name.
    (!root path. p = MemoryPlace root path ==> root <> name) /\
    write_place cx p v es = (res,es') ==>
    MAP (\sc. FLOOKUP sc name) es'.scopes = MAP (\sc. FLOOKUP sc name) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >> Cases_on `p`
  >~ [`write_place _ (MemoryPlace _ _) _ _ = _`]
  >- (irule write_memory_scope_projection >> goal_assum (drule_at Any) >> simp[]) 
  >~ [`write_place _ (StoragePlace _ _ _) _ _ = _`]
  >- (drule write_storage_place_scopes >> simp[]) >>
  drule write_immutable_place_scopes >> simp[]
QED

Theorem supported_simple_target_eval_scopes:
  !target tops bindings cx es res es'.
    supported_target tops bindings target /\
    ~supported_target_exists expr_internal_call_root target /\
    eval_base_place cx target es = (res,es') ==> es'.scopes = es.scopes
Proof
  Cases_on `target` >>
  simp[supported_target_def, supported_expr_exists_def] >> rpt strip_tac
  >~ [`eval_base_place _ (NameTarget _) _ = _`]
  >- gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
         type_check_def, assert_def, return_def, raise_def, AllCaseEqs()]
  >>~- ([`eval_base_place _ (TopLevelNameTarget _) _ = _`],
      rename1 `eval_base_place cx (TopLevelNameTarget nsid) es = _` >>
      PairCases_on `nsid` >> gvs[Once evaluate_def] >>
      metis_tac[lookup_global_scopes])
  >~ [`eval_base_place _ (SubscriptTarget _ _) _ = _`]
  >- suspend "subscript"
  >> suspend "attribute"
QED

Resume supported_simple_target_eval_scopes[subscript]:
  rename1 `eval_base_place cx (SubscriptTarget inner key) es = _` >>
  Cases_on `inner` >> gvs[] >>
  rename1 `eval_base_place cx (SubscriptTarget (TopLevelNameTarget nsid) key) es = _` >>
  PairCases_on `nsid` >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  imp_res_tac lookup_global_scopes >> imp_res_tac read_result_state >>
  imp_res_tac extend_place_state >> gvs[] >> metis_tac[supported_expr_scopes]
QED

Resume supported_simple_target_eval_scopes[attribute]:
  rename1 `eval_base_place cx (AttributeTarget inner fname) es = _` >>
  Cases_on `inner` >> gvs[] >>
  rename1 `eval_base_place cx (AttributeTarget (TopLevelNameTarget nsid) fname) es = _` >>
  PairCases_on `nsid` >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  imp_res_tac lookup_global_scopes >> imp_res_tac extend_place_state >> gvs[]
QED

Finalise supported_simple_target_eval_scopes

Theorem supported_any_target_place_scopes:
  !target tops bindings cx es res es'.
    (supported_target tops bindings target \/
     (?pt. supported_target_info tops bindings target = SOME pt)) /\
    ~supported_target_exists expr_internal_call_root target /\
    eval_target_place cx target es = (res,es') ==> es'.scopes = es.scopes
Proof
  rpt strip_tac
  >- (gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
      imp_res_tac supported_simple_target_eval_scopes >>
      Cases_on `pv` >> gvs[get_place_def, return_def, raise_def]) >>
  metis_tac[supported_target_place_scopes]
QED

Theorem typed_guarded_target_write_projection:
  !env name elem bound target vt tops bindings cx v es res es'.
    FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
    type_place_target env target = SOME vt /\
    ~place_contains target (NameTarget name) /\
    (supported_target tops bindings target \/
     (?pt. supported_target_info tops bindings target = SOME pt)) /\
    ~supported_target_exists expr_internal_call_root target /\
    (do p <- eval_target_place cx target; write_place cx p v od) es = (res,es') ==>
    MAP (\sc. FLOOKUP sc name) es'.scopes = MAP (\sc. FLOOKUP sc name) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  gvs[bind_def, AllCaseEqs(), raise_def] >>
  imp_res_tac supported_any_target_place_scopes >> gvs[] >>
  rename1 `write_place cx dest v mid = (res,es')` >>
  `!root path. dest = MemoryPlace root path ==> root <> name` by
    (rpt strip_tac >> gvs[] >> metis_tac[typed_guarded_eval_target_root]) >>
  drule_all write_guarded_place_projection >> simp[]
QED

Theorem typed_guarded_base_assignment_projection:
  !env name elem bound bt ty tops bindings cx v es res es'.
    FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
    well_typed_atarget env (BaseTarget bt) ty /\
    atarget_writes_ok (\t. ~place_contains t (NameTarget name)) (BaseTarget bt) /\
    (supported_target tops bindings bt \/
     (?pt. supported_target_info tops bindings bt = SOME pt)) /\
    ~supported_target_exists expr_internal_call_root bt /\
    assign_tuple_targets cx (BaseTarget bt) v es = (res,es') ==>
    MAP (\sc. FLOOKUP sc name) es'.scopes = MAP (\sc. FLOOKUP sc name) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  gvs[well_typed_atarget_def, well_typed_target_def, atarget_writes_ok_def] >>
  qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >>
  irule typed_guarded_target_write_projection >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem typed_guarded_flat_targets_projection:
  !targets tys env name elem bound tops bindings cx vs es res es'.
    FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
    LIST_REL (\tgt ty. well_typed_atarget env tgt ty) targets tys /\
    EVERY (\g. case g of BaseTarget bt => supported_target tops bindings bt
                         | TupleTarget _ => F) targets /\
    EVERY (atarget_writes_ok (\t. ~place_contains t (NameTarget name))) targets /\
    ~supported_assignments_exists expr_internal_call_root targets /\
    assign_tuple_target_list cx targets vs es = (res,es') ==>
    MAP (\sc. FLOOKUP sc name) es'.scopes = MAP (\sc. FLOOKUP sc name) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  Induct_on `targets` >> Cases_on `vs` >>
  simp[Once evaluate_def, return_def, raise_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `tys` >> gvs[] >>
  rename1 `well_typed_atarget env head head_ty` >>
  Cases_on `head` >> gvs[supportedStmtTraverseTheory.supported_assignment_exists_def] >>
  gvs[ignore_bind_def, bind_def, AllCaseEqs(), raise_def] >>
  drule_at (Pat `assign_tuple_targets _ _ _ _ = _`)
    typed_guarded_base_assignment_projection >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`tops`,`bindings`] mp_tac) >>
  simp[] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem typed_guarded_assignment_projection:
  !env name elem bound target ty tops bindings rhs cx v es res es'.
    FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
    well_typed_atarget env target ty /\
    atarget_writes_ok (\t. ~place_contains t (NameTarget name)) target /\
    supported_assignment tops bindings target rhs /\
    ~supported_assignment_exists expr_internal_call_root target /\
    assign_tuple_targets cx target v es = (res,es') ==>
    MAP (\sc. FLOOKUP sc name) es'.scopes = MAP (\sc. FLOOKUP sc name) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  Cases_on `target` >> rpt gen_tac >> strip_tac
  >~ [`assign_tuple_targets _ (BaseTarget _) _ _ = _`]
  >- suspend "base"
  >> suspend "tuple"
QED

Resume typed_guarded_assignment_projection[base]:
  rename1 `assign_tuple_targets cx (BaseTarget bt) v es = _` >>
  gvs[supported_assignment_def, AllCaseEqs(),
      supportedStmtTraverseTheory.supported_assignment_exists_def] >>
  irule typed_guarded_base_assignment_projection >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`bindings`,`tops`] >> simp[] >>
  Cases_on `supported_target_info tops bindings bt` >> gvs[]
QED

Resume typed_guarded_assignment_projection[tuple]:
  gvs[well_typed_atarget_def, supported_assignment_def, atarget_writes_ok_def,
      supportedStmtTraverseTheory.supported_assignment_exists_def] >>
  Cases_on `v` >>
  gvs[Once evaluate_def, raise_def, vyperValueTheory.array_value_CASE_rator,
      AllCaseEqs()] >>
  irule typed_guarded_flat_targets_projection >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Finalise typed_guarded_assignment_projection

Theorem new_variable_other_projection:
  !id tv v es res es' name.
    id <> name /\ new_variable id tv v es = (res,es') ==>
    MAP (\sc. FLOOKUP sc name) es'.scopes = MAP (\sc. FLOOKUP sc name) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >> Cases_on `es.scopes` >>
  gvs[new_variable_def, get_scopes_def, type_check_def, assert_def,
      ignore_bind_def, bind_def, set_scopes_def, return_def, raise_def,
      AllCaseEqs(), FLOOKUP_UPDATE]
QED

Theorem handled_loop_body_projection[local]:
  !cx body name es res es'.
    es.scopes <> [] /\
    (!r t. eval_stmts cx body es = (r,t) ==>
      MAP (\sc. FLOOKUP sc name) t.scopes = MAP (\sc. FLOOKUP sc name) es.scopes /\
      LENGTH t.scopes = LENGTH es.scopes) /\
    try (ignore_bind (eval_stmts cx body) (return F)) handle_loop_exception es =
      (res,es') ==>
    MAP (\sc. FLOOKUP sc name) es'.scopes = MAP (\sc. FLOOKUP sc name) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `eval_stmts cx stmts es` >>
  Cases_on `eval_stmts cx stmts es` >>
  rename1 `eval_stmts cx stmts es = (outcome,after)` >>
  gvs[] >>
  Cases_on `outcome` >>
  gvs[try_def, ignore_bind_def, bind_def, return_def] >>
  rename1 `handle_loop_exception exc after = _` >>
  Cases_on `exc` >> gvs[handle_loop_exception_def, return_def, raise_def]
QED

Theorem balanced_loop_body_projection[local]:
  !cx stmts name es res es'.
    es.scopes <> [] /\
    (!s r t. s.scopes <> [] /\ eval_stmts cx stmts s = (r,t) ==>
      MAP (\sc. FLOOKUP sc name) t.scopes = MAP (\sc. FLOOKUP sc name) s.scopes /\
      LENGTH t.scopes = LENGTH s.scopes) /\
    finally (try (ignore_bind (eval_stmts cx stmts) (return F)) handle_loop_exception)
      pop_scope es = (res,es') ==>
    MAP (\sc. FLOOKUP sc name) es'.scopes = MAP (\sc. FLOOKUP sc name) (TL es.scopes) /\
    SUC (LENGTH es'.scopes) = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  irule (INST_TYPE [``:'a`` |-> ``:bool``] finally_pop_scope_projection) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`try (ignore_bind (eval_stmts cx stmts) (return F)) handle_loop_exception`,
            `res`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `try _ _ _ = _`) handled_loop_body_projection >>
  disch_then (qspec_then `name` mp_tac) >>
  impl_tac >- metis_tac[] >>
  strip_tac >> simp[] >>
  metis_tac[MAP_TL]
QED

Theorem eval_for_projection_frame:
  !vs cx tyv id body name es res es'.
    id <> name /\
    (!s r s'. s.scopes <> [] /\ eval_stmts cx body s = (r,s') ==>
      MAP (\sc. FLOOKUP sc name) s'.scopes = MAP (\sc. FLOOKUP sc name) s.scopes /\
      LENGTH s'.scopes = LENGTH s.scopes) /\
    eval_for cx tyv id body vs es = (res,es') ==>
    MAP (\sc. FLOOKUP sc name) es'.scopes = MAP (\sc. FLOOKUP sc name) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  Induct_on `vs` >> simp[Once evaluate_def, return_def] >>
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `finally action pop_scope` >>
  qpat_x_assum `ignore_bind _ _ es = _` mp_tac >>
  pure_rewrite_tac [push_scope_with_var_def, ignore_bind_def, bind_def, return_def] >>
  strip_tac >> FULL_SIMP_TAC std_ss [pairTheory.pair_case_thm, sumTheory.sum_case_def] >>
  qmatch_asmsub_abbrev_tac `bind (finally action pop_scope) continuation pushed` >>
  Cases_on `finally action pop_scope pushed` >>
  rename1 `finally action pop_scope pushed = (outcome,after)` >>
  fs[Abbr `action`] >>
  drule_at (Pat `finally _ _ _ = _`) balanced_loop_body_projection >>
  disch_then (qspec_then `name` mp_tac) >>
  (impl_tac >- (simp[Abbr `pushed`] >> metis_tac[])) >>
  strip_tac >>
  fs[IgnAsm `!cx tyv id body name es res es'. _`, Abbr `pushed`] >>
  Cases_on `outcome` >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  pure_asm_rewrite_tac [bind_def, pairTheory.pair_case_thm, sumTheory.sum_case_def] >>
  simp[Abbr `continuation`, return_def] >> strip_tac >>
  qpat_x_assum `finally _ _ _ = _` kall_tac
  >~ [`(if broke then _ else _) _ = _`]
  >- (Cases_on `broke`
      >- (qpat_x_assum `!cx tyv id body name es res es'. _` kall_tac >>
          gvs[return_def]) >>
      FULL_SIMP_TAC std_ss [] >>
      first_x_assum drule_all >> simp[]) >>
  qpat_x_assum `!cx tyv id body name es res es'. _` kall_tac >> gvs[]
QED

Theorem range_iterator_scopes[local]:
  !cx a b es res es'.
    (!s r t. eval_expr cx a s = (r,t) ==> t.scopes = s.scopes) /\
    (!s r t. eval_expr cx b s = (r,t) ==> t.scopes = s.scopes) /\
    eval_iterator cx (Range a b) es = (res,es') ==>
    es'.scopes = es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> imp_res_tac lift_sum_state >>
  gvs[return_def] >> metis_tac[]
QED

Theorem array_iterator_scopes[local]:
  !cx e es res es'.
    (!s r t. eval_expr cx e s = (r,t) ==> t.scopes = s.scopes) /\
    eval_iterator cx (Array e) es = (res,es') ==>
    es'.scopes = es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> imp_res_tac lift_option_type_state >>
  gvs[return_def] >> metis_tac[]
QED

Theorem literal_expr_scopes[local]:
  !cx ty lit es res es'.
    eval_expr cx (Literal ty lit) es = (res,es') ==> es'.scopes = es.scopes
Proof
  simp[Once evaluate_def, return_def] >> rpt strip_tac >> gvs[]
QED

Theorem name_expr_scopes[local]:
  !cx ty id es res es'.
    eval_expr cx (Name ty id) es = (res,es') ==> es'.scopes = es.scopes
Proof
  simp[Once evaluate_def, get_scopes_def, type_check_def, assert_def,
       ignore_bind_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem supported_iterator_scopes:
  !tops ty it n cx es res es'.
    supported_iterator tops ty it n /\ eval_iterator cx it es = (res,es') ==>
    es'.scopes = es.scopes
Proof
  Cases_on `it` >> rpt gen_tac >> strip_tac
  >~ [`eval_iterator cx (Array arr) es = _`]
  >- (drule supported_array_iterator_shape >> strip_tac >> gvs[] >>
      irule array_iterator_scopes >> goal_assum (drule_at Any) >>
      metis_tac[name_expr_scopes]) >>
  rename1 `eval_iterator cx (Range a b) es = _` >>
  irule range_iterator_scopes >> goal_assum (drule_at Any) >>
  Cases_on `a`
  >~ [`eval_iterator cx (Range (Literal aty alit) b) es = _`]
  >- (Cases_on `b`
      >~ [`eval_iterator cx (Range (Literal aty alit) (Literal bty blit)) es = _`]
      >- (Cases_on `alit` >> Cases_on `blit` >> gvs[supported_iterator_def] >>
          metis_tac[literal_expr_scopes, cj 1 supported_pure_scopes_mutual]) >>
      gvs[supported_iterator_def] >>
      metis_tac[literal_expr_scopes, cj 1 supported_pure_scopes_mutual]) >>
  gvs[supported_iterator_def] >>
  metis_tac[cj 1 supported_pure_scopes_mutual]
QED

Theorem balanced_conditional_projection[local]:
  !cx tv ss1 ss2 name es res es'.
    es.scopes <> [] /\
    (!s r t. s.scopes <> [] /\ eval_stmts cx ss1 s = (r,t) ==>
      MAP (\sc. FLOOKUP sc name) t.scopes = MAP (\sc. FLOOKUP sc name) s.scopes /\
      LENGTH t.scopes = LENGTH s.scopes) /\
    (!s r t. s.scopes <> [] /\ eval_stmts cx ss2 s = (r,t) ==>
      MAP (\sc. FLOOKUP sc name) t.scopes = MAP (\sc. FLOOKUP sc name) s.scopes /\
      LENGTH t.scopes = LENGTH s.scopes) /\
    finally (switch_BoolV cx tv (eval_stmts cx ss1) (eval_stmts cx ss2))
      pop_scope es = (res,es') ==>
    MAP (\sc. FLOOKUP sc name) es'.scopes =
      MAP (\sc. FLOOKUP sc name) (TL es.scopes) /\
    SUC (LENGTH es'.scopes) = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  irule (INST_TYPE [``:'a`` |-> ``:unit``] finally_pop_scope_projection) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`switch_BoolV cx tv (eval_stmts cx ss1) (eval_stmts cx ss2)`,`res`] >>
  simp[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `switch_BoolV _ _ _ _ _ = _` mp_tac >>
  simp[NoAsms, switch_BoolV_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> gvs[raise_def, AllCaseEqs()] >>
  rename1 `(if v = BoolV T then _ else _) es = _` >>
  Cases_on `v = BoolV T` >> Cases_on `v = BoolV F` >> gvs[raise_def] >>
  first_x_assum drule_all >> strip_tac >> simp[] >> metis_tac[MAP_TL]
QED

Theorem if_projection_frame:
  !cx e ss1 ss2 name es res es'.
    (!s r t. eval_expr cx e s = (r,t) ==> t.scopes = s.scopes) /\
    (!s r t. s.scopes <> [] /\ eval_stmts cx ss1 s = (r,t) ==>
      MAP (\sc. FLOOKUP sc name) t.scopes = MAP (\sc. FLOOKUP sc name) s.scopes /\
      LENGTH t.scopes = LENGTH s.scopes) /\
    (!s r t. s.scopes <> [] /\ eval_stmts cx ss2 s = (r,t) ==>
      MAP (\sc. FLOOKUP sc name) t.scopes = MAP (\sc. FLOOKUP sc name) s.scopes /\
      LENGTH t.scopes = LENGTH s.scopes) /\
    eval_stmt cx (If e ss1 ss2) es = (res,es') ==>
    MAP (\sc. FLOOKUP sc name) es'.scopes = MAP (\sc. FLOOKUP sc name) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, ignore_bind_def, push_scope_def,
       get_scopes_def, set_scopes_def, return_def, AllCaseEqs()] >> strip_tac >>
  first_x_assum drule >> strip_tac
  >~ [`v = INR exc`]
  >- gvs[IgnAsm `!s r t. _`] >>
  drule_at (Pat `finally _ _ _ = _`) balanced_conditional_projection >>
  disch_then (qspec_then `name` mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[]
QED

Theorem annassign_projection_frame:
  !cx id typ e name es res es'.
    id <> name /\
    (!s r t. eval_expr cx e s = (r,t) ==> t.scopes = s.scopes) /\
    eval_stmt cx (AnnAssign id typ e) es = (res,es') ==>
    MAP (\sc. FLOOKUP sc name) es'.scopes = MAP (\sc. FLOOKUP sc name) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac lift_option_type_state >> imp_res_tac read_result_state >>
  gvs[IgnAsm `!s r t. _`] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  drule_all new_variable_other_projection >> simp[]
QED

Theorem for_projection_frame:
  !cx id typ it n stmts name es res es'.
    id <> name /\
    (!s r t. eval_iterator cx it s = (r,t) ==> t.scopes = s.scopes) /\
    (!s r t. s.scopes <> [] /\ eval_stmts cx stmts s = (r,t) ==>
      MAP (\sc. FLOOKUP sc name) t.scopes = MAP (\sc. FLOOKUP sc name) s.scopes /\
      LENGTH t.scopes = LENGTH s.scopes) /\
    eval_stmt cx (For id typ it n stmts) es = (res,es') ==>
    MAP (\sc. FLOOKUP sc name) es'.scopes = MAP (\sc. FLOOKUP sc name) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  strip_tac >> imp_res_tac lift_option_type_state >> imp_res_tac check_state >>
  gvs[IgnAsm `!s r t. _`] >>
  qpat_x_assum `!s r t. eval_iterator _ _ _ = _ ==> _` drule >> strip_tac
  >~ [`eval_for _ _ _ _ _ _ = _`]
  >- (drule_at (Pat `eval_for _ _ _ _ _ _ = _`) eval_for_projection_frame >>
      disch_then (qspec_then `name` mp_tac) >>
      (impl_tac >- metis_tac[]) >> simp[]) >>
  gvs[IgnAsm `!s r t. _`]
QED

Theorem assign_projection_frame:
  !env name elem bound target ty tops bindings rhs cx es res es'.
    FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
    well_typed_atarget env target ty /\
    atarget_writes_ok (\t. ~place_contains t (NameTarget name)) target /\
    supported_assignment tops bindings target rhs /\
    ~supported_assignment_exists expr_internal_call_root target /\
    (!s r t. eval_expr cx rhs s = (r,t) ==> t.scopes = s.scopes) /\
    eval_stmt cx (Assign target rhs) es = (res,es') ==>
    MAP (\sc. FLOOKUP sc name) es'.scopes = MAP (\sc. FLOOKUP sc name) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  Cases_on `target` >> rpt gen_tac >> strip_tac
  >~ [`eval_stmt _ (Assign (BaseTarget _) _) _ = _`]
  >- suspend "base"
  >> suspend "tuple"
QED

Resume assign_projection_frame[tuple]:
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> gvs[IgnAsm `!s r t. _`] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  drule_all typed_guarded_assignment_projection >> simp[]
QED

Resume assign_projection_frame[base]:
  rename1 `eval_stmt cx (Assign (BaseTarget bt) rhs) es = _` >>
  gvs[well_typed_atarget_def, well_typed_target_def, atarget_writes_ok_def,
      supported_assignment_def,
      supportedStmtTraverseTheory.supported_assignment_exists_def, AllCaseEqs()] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> gvs[IgnAsm `!s r t. _`] >>
  first_x_assum drule >> strip_tac >>
  imp_res_tac supported_any_target_place_scopes >>
  Cases_on `supported_target_info tops bindings bt` >> gvs[] >>
  imp_res_tac supported_target_place_scopes >> gvs[] >>
  rename1 `write_place cx dest value mid = (res,es')` >>
  `!root path. dest = MemoryPlace root path ==> root <> name` by
    (rpt strip_tac >> gvs[] >> metis_tac[typed_guarded_eval_target_root]) >>
  drule_all write_guarded_place_projection >> simp[]
QED

Finalise assign_projection_frame

Theorem augassign_projection_frame:
  !env name elem bound bt ty bop rhs tops bindings cx es res es'.
    FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
    well_typed_target env bt ty /\ ~place_contains bt (NameTarget name) /\
    (supported_target tops bindings bt \/
     (?pt. supported_target_info tops bindings bt = SOME pt)) /\
    ~supported_target_exists expr_internal_call_root bt /\
    (!s r t. eval_expr cx rhs s = (r,t) ==> t.scopes = s.scopes) /\
    eval_stmt cx (AugAssign ty bt bop rhs) es = (res,es') ==>
    MAP (\sc. FLOOKUP sc name) es'.scopes = MAP (\sc. FLOOKUP sc name) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  gvs[well_typed_target_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_place_state >> imp_res_tac place_type_value_state >>
  imp_res_tac read_result_state >> imp_res_tac lift_sum_state >>
  imp_res_tac supported_any_target_place_scopes >>
  gvs[IgnAsm `!s r t. _`] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  rename1 `write_place cx dest value mid = (res,es')` >>
  `!root path. dest = MemoryPlace root path ==> root <> name` by
    (rpt strip_tac >> gvs[] >> metis_tac[typed_guarded_eval_target_root]) >>
  drule_all write_guarded_place_projection >> simp[]
QED

Theorem append_nonmemory_scopes[local]:
  !cx p v es res es'.
    (!root path. p <> MemoryPlace root path) /\
    append_place cx p v es = (res,es') ==> es'.scopes = es.scopes
Proof
  Cases_on `p` >> rpt gen_tac >> strip_tac
  >~ [`append_place _ (MemoryPlace _ _) _ _ = _`]
  >- metis_tac[]
  >~ [`append_place _ (StoragePlace _ _ _) _ _ = _`]
  >- metis_tac[append_storage_place_scopes_immutables] >>
  gvs[append_place_def, bind_def, AllCaseEqs()] >>
  imp_res_tac read_place_state >> imp_res_tac place_type_value_state >>
  imp_res_tac lift_sum_state >> imp_res_tac write_immutable_place_scopes >> gvs[]
QED

Theorem append_projection_frame:
  !cx bt rhs tops name es res es'.
    supported_append_target tops bt /\
    (!s r t. eval_expr cx rhs s = (r,t) ==> t.scopes = s.scopes) /\
    eval_stmt cx (Append bt rhs) es = (res,es') ==>
    MAP (\sc. FLOOKUP sc name) es'.scopes = MAP (\sc. FLOOKUP sc name) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  Cases_on `bt` >> rpt gen_tac >> strip_tac >>
  gvs[supported_append_target_def] >>
  rename1 `eval_stmt cx (Append (TopLevelNameTarget nsid) rhs) es = _` >>
  PairCases_on `nsid` >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  imp_res_tac lookup_global_scopes >> imp_res_tac read_result_state >>
  gvs[IgnAsm `!s r t. _`] >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def, AllCaseEqs()] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  imp_res_tac append_nonmemory_scopes >>
  metis_tac[lookup_global_not_memory]
QED

Theorem typed_projection_frames_mutual:
  (!tops bindings stmt. supported_stmt tops bindings stmt ==>
    !env ret_ty env' name elem bound cx es res es'.
      FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
      type_stmt env ret_ty stmt = SOME env' /\
      stmt_writes_ok (\w. ~place_contains w (NameTarget name)) stmt /\
      ~supported_stmt_expr_exists expr_internal_call_root stmt /\
      es.scopes <> [] /\ eval_stmt cx stmt es = (res,es') ==>
      MAP (\sc. FLOOKUP sc name) es'.scopes = MAP (\sc. FLOOKUP sc name) es.scopes /\
      LENGTH es'.scopes = LENGTH es.scopes) /\
  (!tops bindings stmts. supported_stmts tops bindings stmts ==>
    !env ret_ty env' name elem bound cx es res es'.
      FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
      type_stmts env ret_ty stmts = SOME env' /\
      stmts_writes_ok (\w. ~place_contains w (NameTarget name)) stmts /\
      ~supported_stmts_expr_exists expr_internal_call_root stmts /\
      es.scopes <> [] /\ eval_stmts cx stmts es = (res,es') ==>
      MAP (\sc. FLOOKUP sc name) es'.scopes = MAP (\sc. FLOOKUP sc name) es.scopes /\
      LENGTH es'.scopes = LENGTH es.scopes)
Proof
  ho_match_mp_tac supported_stmt_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac
  >~ [`eval_stmt _ Pass _ = _`] >- gvs[Once evaluate_def, return_def]
  >~ [`eval_stmt _ Break _ = _`] >- gvs[Once evaluate_def, raise_def]
  >~ [`eval_stmt _ Continue _ = _`] >- gvs[Once evaluate_def, raise_def]
  >~ [`eval_stmt _ (Return NONE) _ = _`] >- gvs[Once evaluate_def, raise_def]
  >~ [`eval_stmts _ [] _ = _`] >- gvs[Once evaluate_def, return_def]
  >~ [`eval_stmt _ (Expr _) _ = _`] >- suspend "expr"
  >~ [`eval_stmt _ (Return (SOME _)) _ = _`] >- suspend "return"
  >~ [`eval_stmt _ (AnnAssign _ _ _) _ = _`] >- suspend "annassign"
  >~ [`eval_stmt _ (Assign _ _) _ = _`] >- suspend "assign"
  >~ [`eval_stmt _ (AugAssign _ _ _ _) _ = _`] >- suspend "augassign"
  >~ [`eval_stmt _ (Append _ _) _ = _`] >- suspend "append"
  >~ [`eval_stmt _ (If _ _ _) _ = _`] >- suspend "if"
  >~ [`eval_stmt _ (For _ _ _ _ _) _ = _`] >- suspend "for"
  >~ [`eval_stmt _ (Assert _ _) _ = _`] >- suspend "assert"
  >~ [`eval_stmt _ (Raise _) _ = _`] >- suspend "raise"
  >~ [`eval_stmt _ (Log _ _) _ = _`] >- suspend "log"
  >> suspend "cons"
QED

Resume typed_projection_frames_mutual[expr]:
  gvs[supported_stmt_def,
      supportedStmtTraverseTheory.supported_stmt_expr_exists_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, type_check_def, assert_def,
       ignore_bind_def, return_def, raise_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac supported_expr_scopes >> gvs[]
QED

Resume typed_projection_frames_mutual[return]:
  gvs[supported_stmt_def, supported_expr_exists_def,
      supportedStmtTraverseTheory.supported_stmt_expr_exists_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, raise_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac supported_expr_scopes >> imp_res_tac read_result_state >> gvs[]
QED

Resume typed_projection_frames_mutual[annassign]:
  rename1 `eval_stmt cx (AnnAssign id typ rhs) es = (res,es')` >>
  gvs[supported_stmt_def, type_stmt_def,
      supportedStmtTraverseTheory.supported_stmt_expr_exists_def,
      AllCaseEqs()] >>
  rename1 `FLOOKUP env.var_types protected = SOME (ArrayT elem bound)` >>
  `id <> protected` by (strip_tac >> gvs[FLOOKUP_DEF]) >>
  irule annassign_projection_frame >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[supported_expr_scopes]
QED

Resume typed_projection_frames_mutual[append]:
  gvs[supported_stmt_def,
      supportedStmtTraverseTheory.supported_stmt_expr_exists_def] >>
  irule append_projection_frame >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[cj 1 supported_pure_scopes_mutual]
QED

Resume typed_projection_frames_mutual[assign]:
  gvs[supported_stmt_def, type_stmt_def, stmt_writes_ok_def,
      supportedStmtTraverseTheory.supported_stmt_expr_exists_def, AllCaseEqs()] >>
  drule_all atarget_accepts_well_typed_atarget >> strip_tac >>
  `supported_expr tops e` by
    (Cases_on `target` >> gvs[supported_assignment_def]) >>
  irule assign_projection_frame >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[supported_expr_scopes]
QED

Resume typed_projection_frames_mutual[augassign]:
  gvs[supported_stmt_def, type_stmt_def, stmt_writes_ok_def,
      supportedStmtTraverseTheory.supported_stmt_expr_exists_def, AllCaseEqs()] >>
  irule augassign_projection_frame >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`bindings`,`tops`] >> simp[] >>
  gvs[supported_aug_target_def, AllCaseEqs()] >>
  Cases_on `supported_target_info tops bindings target` >> gvs[] >>
  metis_tac[supported_expr_scopes]
QED

Resume typed_projection_frames_mutual[if]:
  rpt gen_tac >> strip_tac >>
  gvs[IgnAsm `!env ret_ty env' name elem bound cx es res es'. _`,
      supported_stmt_def, type_stmt_def, stmt_writes_ok_def,
      supportedStmtTraverseTheory.supported_stmt_expr_exists_def, AllCaseEqs()] >>
  fs[IgnAsm `!env ret_ty env' name elem bound cx es res es'. _`,
     optionTheory.IS_SOME_EXISTS] >>
  irule if_projection_frame >> goal_assum (drule_at Any) >>
  conj_tac >- metis_tac[cj 1 supported_pure_scopes_mutual] >>
  conj_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Resume typed_projection_frames_mutual[for]:
  rpt gen_tac >> strip_tac >>
  rename1 `eval_stmt cx (For id typ it n stmts) es = _` >>
  gvs[IgnAsm `!env ret_ty env' name elem bound cx es res es'. _`,
      supported_stmt_def, type_stmt_def, stmt_writes_ok_def,
      supportedStmtTraverseTheory.supported_stmt_expr_exists_def, AllCaseEqs()] >>
  rename1 `FLOOKUP env.var_types protected = SOME (ArrayT elem bound)` >>
  `id <> protected` by (strip_tac >> gvs[FLOOKUP_DEF]) >>
  irule for_projection_frame >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- metis_tac[supported_iterator_scopes] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- (
    `FLOOKUP (extend_local env id typ F).var_types protected =
       SOME (ArrayT elem bound)` by simp[extend_local_def, FLOOKUP_UPDATE] >>
    goal_assum (drule_at Any) >> simp[] >>
    metis_tac[optionTheory.IS_SOME_EXISTS]) >>
  metis_tac[]
QED

Resume typed_projection_frames_mutual[log]:
  gvs[supported_stmt_def, supported_log_def,
      supportedStmtTraverseTheory.supported_stmt_expr_exists_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  Cases_on `cx.txn.is_static` >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac supported_pure_exprs_scopes >> imp_res_tac read_results_state >>
  imp_res_tac lift_option_state >> imp_res_tac push_log_scopes >> gvs[]
QED

Resume typed_projection_frames_mutual[assert]:
  rename1 `eval_stmt cx (Assert cond reason) es = _` >>
  Cases_on `reason` >> gvs[supported_stmt_def, supported_assert_reason_def]
  >~ [`eval_stmt _ (Assert _ AssertBare) _ = _`]
  >- suspend "assert_bare"
  >~ [`eval_stmt _ (Assert _ AssertUnreachable) _ = _`]
  >- suspend "assert_unreachable"
  >> suspend "assert_reason"
QED

Resume typed_projection_frames_mutual[assert_bare]:
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> imp_res_tac supported_pure_scopes_mutual >>
  gvs[return_def, raise_def, AllCaseEqs()] >>
  rename1 `(if v = BoolV T then _ else _) _ = _` >>
  Cases_on `v = BoolV T` >> Cases_on `v = BoolV F` >>
  gvs[return_def, raise_def]
QED

Resume typed_projection_frames_mutual[assert_unreachable]:
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> imp_res_tac supported_pure_scopes_mutual >>
  gvs[return_def, raise_def, AllCaseEqs()] >>
  rename1 `(if v = BoolV T then _ else _) _ = _` >>
  Cases_on `v = BoolV T` >> Cases_on `v = BoolV F` >>
  gvs[return_def, raise_def]
QED

Resume typed_projection_frames_mutual[assert_reason]:
  rename1 `supported_string_reason tops rhs` >>
  `!s r t. eval_expr cx rhs s = (r,t) ==> t.scopes = s.scopes` by
    (Cases_on `rhs` >> gvs[supported_string_reason_def] >>
     metis_tac[literal_expr_scopes, cj 1 supported_pure_scopes_mutual]) >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs()] >>
  strip_tac >> imp_res_tac read_result_state >>
  imp_res_tac supported_pure_scopes_mutual >>
  gvs[IgnAsm `!s r t. _`, return_def, raise_def, AllCaseEqs()] >>
  rename1 `(if v = BoolV T then _ else _) _ = _` >>
  Cases_on `v = BoolV T`
  >- (qpat_x_assum `!s r t. _` kall_tac >> gvs[return_def]) >>
  Cases_on `v = BoolV F`
  >- (gvs[IgnAsm `!s r t. _`, bind_def, AllCaseEqs()] >>
      imp_res_tac read_result_state >> imp_res_tac lift_option_type_state >>
      gvs[IgnAsm `!s r t. _`, raise_def] >>
      first_x_assum drule >> strip_tac >> gvs[]) >>
  qpat_x_assum `!s r t. _` kall_tac >> gvs[raise_def]
QED

Resume typed_projection_frames_mutual[raise]:
  rename1 `eval_stmt cx (Raise reason) es = _` >>
  Cases_on `reason` >>
  gvs[supported_stmt_def, supported_raise_reason_def]
  >~ [`eval_stmt _ (Raise RaiseBare) _ = _`]
  >- gvs[Once evaluate_def, raise_def]
  >~ [`eval_stmt _ (Raise RaiseUnreachable) _ = _`]
  >- gvs[Once evaluate_def, raise_def] >>
  rename1 `supported_string_reason tops rhs` >>
  `!s r t. eval_expr cx rhs s = (r,t) ==> t.scopes = s.scopes` by
    (Cases_on `rhs` >> gvs[supported_string_reason_def] >>
     metis_tac[literal_expr_scopes, cj 1 supported_pure_scopes_mutual]) >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, raise_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> imp_res_tac lift_option_type_state >>
  gvs[IgnAsm `!s r t. _`] >> first_x_assum drule >> strip_tac >> gvs[]
QED

Resume typed_projection_frames_mutual[cons]:
  rpt gen_tac >> strip_tac >>
  fs[supported_stmt_def] >>
  gvs[IgnAsm `!env ret_ty env' name elem bound cx es res es'. _`,
      stmt_writes_ok_def,
      supportedStmtTraverseTheory.supported_stmt_expr_exists_def,
      Once type_stmt_def, AllCaseEqs()] >>
  drule_all type_stmt_var_types_preserve >> strip_tac >>
  qpat_x_assum `eval_stmts _ (_::_) _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, ignore_bind_def, bind_def, AllCaseEqs()] >> strip_tac >>
  first_x_assum drule_all >> strip_tac
  >~ [`_ = INR _`]
  >- (qpat_x_assum `!env ret_ty env' name elem bound cx es res es'. _` kall_tac >>
      gvs[]) >>
  rename1 `eval_stmts cx stmts mid = _` >>
  `mid.scopes <> []` by (Cases_on `mid.scopes` >> gvs[]) >>
  first_x_assum drule_all >> strip_tac >> gvs[]
QED

Finalise typed_projection_frames_mutual


Theorem typed_stmt_projection_frame:
  supported_stmt tops bindings stmt /\
  FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
  type_stmt env ret_ty stmt = SOME env' /\
  stmt_writes_ok (\w. ~place_contains w (NameTarget name)) stmt /\
  ~supported_stmt_expr_exists expr_internal_call_root stmt /\
  es.scopes <> [] /\ eval_stmt cx stmt es = (res,es') ==>
  MAP (\sc. FLOOKUP sc name) es'.scopes =
    MAP (\sc. FLOOKUP sc name) es.scopes /\
  LENGTH es'.scopes = LENGTH es.scopes
Proof
  metis_tac[cj 1 typed_projection_frames_mutual]
QED

Theorem typed_stmts_projection_frame:
  supported_stmts tops bindings stmts /\
  FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
  type_stmts env ret_ty stmts = SOME env' /\
  stmts_writes_ok (\w. ~place_contains w (NameTarget name)) stmts /\
  ~supported_stmts_expr_exists expr_internal_call_root stmts /\
  es.scopes <> [] /\ eval_stmts cx stmts es = (res,es') ==>
  MAP (\sc. FLOOKUP sc name) es'.scopes =
    MAP (\sc. FLOOKUP sc name) es.scopes /\
  LENGTH es'.scopes = LENGTH es.scopes
Proof
  metis_tac[cj 2 typed_projection_frames_mutual]
QED

(* In the outer For, freshness of its binder preserves this protected lookup
   through extend_local.  The body typing premise is the existing For rule. *)
Theorem array_body_pop_projection:
  !tops bindings body env name elem bound ret_ty env' aty es tmp outer cx res es'.
  supported_stmts tops bindings body /\
  FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
  type_stmts env ret_ty body = SOME env' /\
  iterator_unmodified (Array (Name aty name)) body /\
  ~supported_stmts_expr_exists expr_internal_call_root body /\
  es.scopes = tmp::outer /\
  finally (eval_stmts cx body) pop_scope es = (res,es') ==>
  MAP (\sc. FLOOKUP sc name) es'.scopes =
    MAP (\sc. FLOOKUP sc name) outer /\
  LENGTH es'.scopes = LENGTH outer
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `supported_stmts tops bindings stmts` >>
  `stmts_writes_ok (\w. ~place_contains w (NameTarget name)) stmts` by
    gvs[iterator_unmodified_def, expr_place_def] >>
  `MAP (\sc. FLOOKUP sc name) es'.scopes =
     MAP (\sc. FLOOKUP sc name) (TL es.scopes) /\
   SUC (LENGTH es'.scopes) = LENGTH es.scopes` by
    (qspec_then `eval_stmts cx stmts` mp_tac finally_pop_scope_projection >>
     disch_then irule >> simp[] >>
     rpt gen_tac >> strip_tac >>
     `es.scopes <> []` by simp[] >>
     drule_all typed_stmts_projection_frame >> strip_tac >>
     Cases_on `t.scopes` >> gvs[]) >>
  gvs[]
QED

Theorem array_body_pop_snapshot:
  !tops bindings body env name elem bound ret_ty env' aty es tmp outer cx res es'.
  supported_stmts tops bindings body /\
  FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
  type_stmts env ret_ty body = SOME env' /\
  iterator_unmodified (Array (Name aty name)) body /\
  ~supported_stmts_expr_exists expr_internal_call_root body /\
  es.scopes = tmp::outer /\
  finally (eval_stmts cx body) pop_scope es = (res,es') ==>
  lookup_scopes name es'.scopes = lookup_scopes name outer
Proof
  rpt gen_tac >> strip_tac >> drule_all array_body_pop_projection >> strip_tac >>
  irule scope_projection_lookup >> simp[]
QED
