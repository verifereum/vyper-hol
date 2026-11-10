(* Scope projection frames for the source snapshot of an array iterator. *)
Theory stmtSimForArrayFrame
Ancestors
  list rich_list finite_map vyperState vyperLookup vyperScopePreservation
  supportedStmts vyperPlaceFrames supportedExprs vyperInterpreter vyperCallOutcomeFrame
  vyperStatePreservation supportedExprForms supportedExprTraverse
  vyperEvalExprPreservesScopesDom vyperPlaceResultTyping vyperTypeSystem vyperTypeEnvExtension vyperTypeArgFits vyperCreateFrame

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
  !target env root elem bound vt attrs.
    ((?name. root = NameTarget name) \/
     (?nsid. root = TopLevelNameTarget nsid)) /\
    (type_place_target env root = NONE \/
     type_place_target env root = SOME (Type (ArrayT elem bound))) /\
    type_place_target env target = SOME vt /\
    FST (place_access target attrs) = root ==>
    target = root \/ place_access target attrs = (root,[])
Proof
  measureInduct_on `base_assignment_target_size target` >> Cases_on `target` >>
  simp[place_access_def, well_typed_expr_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `place_access inner access_attrs` >>
  first_x_assum (qspec_then `inner` mp_tac) >> simp[] >>
  disch_then (qspecl_then
    [`env`, `elem`, `bound`, `THE (type_place_target env inner)`, `access_attrs`]
    mp_tac) >>
  simp[Abbr `access_attrs`] >>
  strip_tac >> gvs[place_access_def] >>
  gvs[well_typed_expr_def, AllCaseEqs(), attribute_type_def]
QED

Theorem typed_guarded_array_root:
  !env root elem bound target vt.
    ((?name. root = NameTarget name) \/
     (?nsid. root = TopLevelNameTarget nsid)) /\
    (type_place_target env root = NONE \/
     type_place_target env root = SOME (Type (ArrayT elem bound))) /\
    type_place_target env target = SOME vt /\
    ~place_contains target root ==>
    FST (place_access target []) <> root
Proof
  rpt strip_tac >>
  qspecl_then [`target`, `env`, `root`, `elem`, `bound`, `vt`, `[]`]
    assume_tac typed_array_root_access >>
  gvs[place_contains_def, place_access_def]
QED

Theorem typed_guarded_array_target_root:
  !env name elem bound target vt.
    FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
    type_place_target env target = SOME vt /\
    ~place_contains target (NameTarget name) ==>
    FST (place_access target []) <> NameTarget name
Proof
  rpt gen_tac >> strip_tac >>
  match_mp_tac (Q.SPECL
    [`env`, `NameTarget name`, `elem`, `bound`, `target`, `vt`]
    typed_guarded_array_root) >> simp[] >>
  Cases_on `FLOOKUP env.var_assignable name` >>
  simp[well_typed_expr_def, AllCaseEqs()]
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

(* Frames for the protected array name that need no supported_* premise:
   evaluating an expression or a target leaves the name's projection alone
   when no write goes through the name (expr_writes_ok / target_writes_ok). *)

Theorem pop_place_name_projection:
  !cx p es res es' name.
    (!root path. p = MemoryPlace root path ==> root <> name) /\
    pop_place cx p es = (res,es') ==>
    MAP (\sc. FLOOKUP sc name) es'.scopes = MAP (\sc. FLOOKUP sc name) es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `?root path. p = MemoryPlace root path`
  >- (gvs[] >> drule pop_memory_scope_trace_events >> strip_tac >>
      gvs[scope_pop_trace_def, scope_pop_step_def] >>
      drule find_containing_scope_structure >> strip_tac >>
      gvs[FLOOKUP_UPDATE]) >>
  drule_at (Pat `pop_place _ _ _ = _`) pop_nonmemory_scopes >> gvs[] >>
  metis_tac[]
QED

Theorem writes_ok_typed_root_mutual[local]:
  (!env e. well_typed_expr env e ==>
     !name elem bound. FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
     expr_writes_ok (\w. ~place_contains w (NameTarget name)) e ==>
     expr_writes_ok (\w. FST (place_access w []) <> NameTarget name) e) /\
  (!env e. IS_SOME (type_place_expr env e) ==>
     !name elem bound. FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
     expr_writes_ok (\w. ~place_contains w (NameTarget name)) e ==>
     expr_writes_ok (\w. FST (place_access w []) <> NameTarget name) e) /\
  (!env t. IS_SOME (type_place_target env t) ==>
     !name elem bound. FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
     target_writes_ok (\w. ~place_contains w (NameTarget name)) t ==>
     target_writes_ok (\w. FST (place_access w []) <> NameTarget name) t) /\
  (!env es. well_typed_exprs env es ==>
     !name elem bound. FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
     EVERY (expr_writes_ok (\w. ~place_contains w (NameTarget name))) es ==>
     EVERY (expr_writes_ok (\w. FST (place_access w []) <> NameTarget name)) es) /\
  (!(env:typing_env) (opt:expr option). T) /\
  (!env kes. well_typed_named_exprs env kes ==>
     !name elem bound. FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
     EVERY (expr_writes_ok (\w. ~place_contains w (NameTarget name))) (MAP SND kes) ==>
     EVERY (expr_writes_ok (\w. FST (place_access w []) <> NameTarget name)) (MAP SND kes))
Proof
  ho_match_mp_tac well_typed_expr_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac
  >~ [`well_typed_expr _ (Pop _ _)`]
  >- (gvs[well_typed_expr_def, expr_writes_ok_def] >>
      drule_all typed_guarded_array_target_root >> strip_tac >> simp[] >>
      res_tac) >>
  gvs[well_typed_expr_def, expr_writes_ok_def, AllCaseEqs(), SF ETA_ss,
      optionTheory.IS_SOME_EXISTS] >>
  metis_tac[]
QED

Theorem writes_ok_typed_root:
  FLOOKUP env.var_types name = SOME (ArrayT elem bound) ==>
  (!e. well_typed_expr env e /\
       expr_writes_ok (\w. ~place_contains w (NameTarget name)) e ==>
       expr_writes_ok (\w. FST (place_access w []) <> NameTarget name) e) /\
  (!t. IS_SOME (type_place_target env t) /\
       target_writes_ok (\w. ~place_contains w (NameTarget name)) t ==>
       target_writes_ok (\w. FST (place_access w []) <> NameTarget name) t)
Proof
  metis_tac[writes_ok_typed_root_mutual]
QED
Theorem intcall_scopes_after_args[local]:
  !cx ty src fn es drv st res st'.
  eval_expr cx (Call ty (IntCall (src,fn)) es drv) st = (res,st') ==>
  st'.scopes = st.scopes \/
  ?ts tup r1 s1. ~MEM (src,fn) cx.stk /\ get_module_code cx src = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts = SOME tup /\
    LENGTH es <= LENGTH (FST (SND (SND tup))) /\
    LENGTH (FST (SND (SND tup))) <= LENGTH es + LENGTH (FST (SND (SND (SND tup)))) /\
    eval_expr_results cx es st = (r1,s1) /\ st'.scopes = s1.scopes
Proof
  rpt gen_tac >>
  rewrite_tac[Once evaluate_def, ignore_bind_def] >>
  simp[bind_def, type_check_def, assert_def, lift_option_type_def,
       return_def, raise_def, LET_THM, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[vyperMiscTheory.option_CASE_rator, AllCaseEqs(), return_def, raise_def,
      get_scopes_def, bind_def] >>
  imp_res_tac finally_set_scopes >> imp_res_tac read_results_state >>
  imp_res_tac (SRULE[ignore_bind_def] finally_conditional_lock_scopes) >>
  gvs[lock_if_nr_def, push_function_def, ignore_bind_def, bind_def,
      return_def, raise_def, COND_RATOR, vyperMiscTheory.option_CASE_rator,
      AllCaseEqs()] >>
  imp_res_tac acquire_nonreentrant_lock_scopes >> gvs[]
QED

Theorem eval_name_projection_mutual:
  !name.
  (!(cx:evaluation_context) (s:stmt). T) /\
  (!(cx:evaluation_context) (ss:stmt list). T) /\
  (!(cx:evaluation_context) (it:iterator). T) /\
  (!(cx:evaluation_context) (tyv:type_value) (nm:string) (body:stmt list) (vs:value list). T) /\
  (!cx e. expr_writes_ok (\w. FST (place_access w []) <> NameTarget name) e ==>
    !st res st'. eval_expr cx e st = (res,st') ==>
      MAP (\sc. FLOOKUP sc name) st'.scopes = MAP (\sc. FLOOKUP sc name) st.scopes) /\
  (!cx es. EVERY (expr_writes_ok (\w. FST (place_access w []) <> NameTarget name)) es ==>
    !st res st'. eval_exprs cx es st = (res,st') ==>
      MAP (\sc. FLOOKUP sc name) st'.scopes = MAP (\sc. FLOOKUP sc name) st.scopes) /\
  (!cx bt. target_writes_ok (\w. FST (place_access w []) <> NameTarget name) bt ==>
    !st res st'. eval_base_place cx bt st = (res,st') ==>
      MAP (\sc. FLOOKUP sc name) st'.scopes = MAP (\sc. FLOOKUP sc name) st.scopes) /\
  (!cx bt. target_writes_ok (\w. FST (place_access w []) <> NameTarget name) bt ==>
    !st res st'. eval_target_place cx bt st = (res,st') ==>
      MAP (\sc. FLOOKUP sc name) st'.scopes = MAP (\sc. FLOOKUP sc name) st.scopes) /\
  (!(cx:evaluation_context) (g:assignment_target) (v:value). T) /\
  (!(cx:evaluation_context) (gs:assignment_target list) (vs:value list). T) /\
  (!cx es. EVERY (expr_writes_ok (\w. FST (place_access w []) <> NameTarget name)) es ==>
    !st res st'. eval_expr_results cx es st = (res,st') ==>
      MAP (\sc. FLOOKUP sc name) st'.scopes = MAP (\sc. FLOOKUP sc name) st.scopes)
Proof
  gen_tac >> ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  simp[] >> rpt gen_tac >> rpt strip_tac
  >~ [`eval_expr _ (Call _ (IntCall _) _ _) _ = _`] >- suspend "IntCall"
  >~ [`eval_expr _ (Call _ (ExtCall _ _ _ _) _ _) _ = _`] >- suspend "ExtCall"
  >~ [`eval_expr _ (Call _ (CreateTarget _ _ _ _) _ _) _ = _`] >- suspend "Create"
  >~ [`eval_expr _ (Builtin _ _ _) _ = _`] >- suspend "Builtin"
  >~ [`eval_expr _ (Pop _ _) _ = _`] >- suspend "Pop"
  >~ [`eval_expr _ (IfExp _ _ _ _) _ = _`] >- suspend "IfExp"
  >~ [`eval_expr _ (TopLevelName _ _) _ = _`] >- suspend "TopLevelName"
  >~ [`eval_expr _ (StructLit _ _ _) _ = _`] >- suspend "StructLit"
  >~ [`eval_base_place _ (TopLevelNameTarget _) _ = _`] >- suspend "TopLevelNameTarget"
  >>
  (qpat_x_assum `_ _ _ st = (res,st')` mp_tac >>
   simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(),
        return_def, raise_def, type_check_def, assert_def, get_scopes_def,
        check_def] >>
   rpt strip_tac >>
   gvs[expr_writes_ok_def, SF ETA_ss, type_check_def, assert_def, return_def, raise_def] >>
   imp_res_tac read_result_state >> imp_res_tac select_result_state >>
   imp_res_tac lookup_flag_mem_scopes >> imp_res_tac lift_option_type_state >>
   imp_res_tac lift_sum_state >> imp_res_tac lift_option_state >>
   imp_res_tac extend_place_state >> imp_res_tac get_place_state >>
   imp_res_tac eval_send_preserves_non_accounts >>
   imp_res_tac eval_raw_call_preserves_non_accounts >>
   imp_res_tac push_log_scopes >> imp_res_tac transfer_value_scopes >>
   imp_res_tac get_accounts_scopes >>
   gvs[] >> res_tac >> gvs[])
QED

Resume eval_name_projection_mutual[TopLevelName]:
  rename1 `TopLevelName _ nsid` >> PairCases_on `nsid` >>
  gvs[Once evaluate_def] >> imp_res_tac lookup_global_scopes >> simp[]
QED

Resume eval_name_projection_mutual[TopLevelNameTarget]:
  rename1 `TopLevelNameTarget nsid` >> PairCases_on `nsid` >>
  gvs[Once evaluate_def] >> imp_res_tac lookup_global_scopes >> simp[]
QED

Resume eval_name_projection_mutual[StructLit]:
  rename1 `StructLit _ nsid _` >> PairCases_on `nsid` >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def,
      expr_writes_ok_def, SF ETA_ss] >> res_tac >> gvs[]
QED

Resume eval_name_projection_mutual[IfExp]:
  gvs[Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs(),
      return_def, raise_def, expr_writes_ok_def, SF ETA_ss] >>
  imp_res_tac read_result_state >> imp_res_tac conditional_result_state >>
  gvs[COND_RATOR, AllCaseEqs(), raise_def] >> res_tac >> gvs[]
QED

Resume eval_name_projection_mutual[Pop]:
  rename1 `Pop _ tgt` >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  gvs[expr_writes_ok_def] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  rename1 `pop_place cx p mid = (res,st')` >>
  `!root path. p = MemoryPlace root path ==> root <> name` by
    (rpt strip_tac >> gvs[] >> drule eval_target_place_memory_root >>
     strip_tac >> gvs[]) >>
  drule_all pop_place_name_projection >> simp[]
QED

Resume eval_name_projection_mutual[IntCall]:
  drule intcall_scopes_after_args >> strip_tac >> gvs[] >>
  gvs[expr_writes_ok_def, SF ETA_ss, type_check_def, assert_def,
      lift_option_type_def, return_def, raise_def,
      vyperMiscTheory.option_CASE_rator, AllCaseEqs(), LET_THM] >>
  res_tac >> gvs[]
QED

Resume eval_name_projection_mutual[ExtCall]:
  rename1 `ExtCall _ _ sig _` >> PairCases_on `sig` >>
  `!n m. EVERY (expr_writes_ok (\w. FST (place_access w []) <> NameTarget name)) (TAKE n es) /\
         EVERY (expr_writes_ok (\w. FST (place_access w []) <> NameTarget name)) (DROP n es) /\
         EVERY (expr_writes_ok (\w. FST (place_access w []) <> NameTarget name)) (TAKE n (DROP m es)) /\
         EVERY (expr_writes_ok (\w. FST (place_access w []) <> NameTarget name)) (DROP n (DROP m es))` by
    (gvs[expr_writes_ok_def, SF ETA_ss] >> simp[EVERY_TAKE, EVERY_DROP]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), LET_THM] >>
  rpt strip_tac >> gvs[SF ETA_ss, LET_THM] >>
  imp_res_tac read_results_state >>
  imp_res_tac eval_ext_call_preserves_non_accounts >>
  gvs[] >> res_tac >> gvs[]
QED

Resume eval_name_projection_mutual[Create]:
  rename1 `CreateTarget kind has_salt rof _` >>
  `!n m. EVERY (expr_writes_ok (\w. FST (place_access w []) <> NameTarget name)) (TAKE n es) /\
         EVERY (expr_writes_ok (\w. FST (place_access w []) <> NameTarget name)) (DROP n es) /\
         EVERY (expr_writes_ok (\w. FST (place_access w []) <> NameTarget name)) (TAKE n (DROP m es)) /\
         EVERY (expr_writes_ok (\w. FST (place_access w []) <> NameTarget name)) (DROP n (DROP m es))` by
    (gvs[expr_writes_ok_def, SF ETA_ss] >> simp[EVERY_TAKE, EVERY_DROP]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  Cases_on `kind` >> simp[Once evaluate_def, bind_def, AllCaseEqs(), LET_THM] >>
  rpt strip_tac >> gvs[expr_writes_ok_def, SF ETA_ss, LET_THM] >>
  imp_res_tac read_results_state >>
  imp_res_tac check_create_blueprint_result_state >>
  imp_res_tac eval_create_preserves_scopes_immutables >>
  gvs[] >> res_tac >> gvs[]
QED

Resume eval_name_projection_mutual[Builtin]:
  rename1 `Builtin _ bt es` >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  Cases_on `bt = Len` >> Cases_on `bt = Bop In \/ bt = Bop NotIn` >>
  Cases_on `bt = Env MsgGas` >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(),
       return_def, raise_def, type_check_def, assert_def] >>
  rpt strip_tac >>
  gvs[expr_writes_ok_def, SF ETA_ss, type_check_def, assert_def, return_def,
      raise_def, vyperContextTheory.builtin_args_length_ok_def, LENGTH_EQ_NUM_compute] >>
  imp_res_tac result_array_length_state >> imp_res_tac lift_option_type_state >>
  imp_res_tac lift_sum_state >> imp_res_tac next_gas_reading_state >>
  imp_res_tac get_accounts_scopes >> imp_res_tac precompile_call_success_state >>
  gvs[] >> res_tac >> gvs[]
QED

Finalise eval_name_projection_mutual

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

Theorem projection_length[local]:
  !a b name.
    MAP (\sc. FLOOKUP sc name) a = MAP (\sc. FLOOKUP sc name) b ==>
    LENGTH a = LENGTH b
Proof
  metis_tac[LENGTH_MAP]
QED

Theorem typed_expr_name_projection[local]:
  !env name elem bound e cx st res st'.
    FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
    well_typed_expr env e /\
    expr_writes_ok (\w. ~place_contains w (NameTarget name)) e /\
    eval_expr cx e st = (res,st') ==>
    MAP (\sc. FLOOKUP sc name) st'.scopes = MAP (\sc. FLOOKUP sc name) st.scopes
Proof
  rpt strip_tac >> drule writes_ok_typed_root >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule_all (cj 5 eval_name_projection_mutual) >> simp[]
QED

Theorem typed_exprs_name_projection[local]:
  !env name elem bound es cx st res st'.
    FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
    well_typed_exprs env es /\
    EVERY (expr_writes_ok (\w. ~place_contains w (NameTarget name))) es /\
    eval_exprs cx es st = (res,st') ==>
    MAP (\sc. FLOOKUP sc name) st'.scopes = MAP (\sc. FLOOKUP sc name) st.scopes
Proof
  rpt strip_tac >>
  `EVERY (expr_writes_ok (\w. FST (place_access w []) <> NameTarget name)) es`
    by metis_tac[writes_ok_typed_root_mutual] >>
  drule_all (cj 6 eval_name_projection_mutual) >> simp[]
QED

Theorem typed_custom_error_name_projection[local]:
  !env name elem bound err params es cx st res st'.
    FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
    well_typed_custom_error env err /\
    EVERY (expr_writes_ok (\w. ~place_contains w (NameTarget name)))
      (custom_error_exprs err) /\
    order_custom_error_args params err = SOME es /\
    eval_exprs cx es st = (res,st') ==>
    MAP (\sc. FLOOKUP sc name) st'.scopes = MAP (\sc. FLOOKUP sc name) st.scopes
Proof
  rpt strip_tac >>
  `EVERY (expr_writes_ok (\w. FST (place_access w []) <> NameTarget name))
     (custom_error_exprs err)` by
    metis_tac[writes_ok_typed_root_mutual, well_typed_custom_error_def] >>
  `EVERY (expr_writes_ok (\w. FST (place_access w []) <> NameTarget name)) es`
    by metis_tac[sortingTheory.PERM_EVERY,
                 vyperASTTheory.order_custom_error_args_perm] >>
  drule_all (cj 6 eval_name_projection_mutual) >> simp[]
QED

Theorem typed_target_name_projection[local]:
  !env name elem bound t vt cx st res st'.
    FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
    type_place_target env t = SOME vt /\
    target_writes_ok (\w. ~place_contains w (NameTarget name)) t /\
    eval_target_place cx t st = (res,st') ==>
    MAP (\sc. FLOOKUP sc name) st'.scopes = MAP (\sc. FLOOKUP sc name) st.scopes
Proof
  rpt strip_tac >> drule writes_ok_typed_root >> strip_tac >>
  `target_writes_ok (\w. FST (place_access w []) <> NameTarget name) t`
    by (first_x_assum irule >> simp[]) >>
  drule_all (cj 8 eval_name_projection_mutual) >> simp[]
QED

Theorem typed_guarded_target_write_projection:
  !env name elem bound target vt cx v es res es'.
    FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
    type_place_target env target = SOME vt /\
    ~place_contains target (NameTarget name) /\
    target_writes_ok (\w. ~place_contains w (NameTarget name)) target /\
    (do p <- eval_target_place cx target; write_place cx p v od) es = (res,es') ==>
    MAP (\sc. FLOOKUP sc name) es'.scopes = MAP (\sc. FLOOKUP sc name) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  gvs[bind_def, AllCaseEqs(), raise_def] >>
  drule_all typed_target_name_projection >> strip_tac
  >- (rename1 `write_place cx dest v mid = (res,es')` >>
      `!root path. dest = MemoryPlace root path ==> root <> name` by
        (rpt strip_tac >> gvs[] >> metis_tac[typed_guarded_eval_target_root]) >>
      drule_all write_guarded_place_projection >> strip_tac >>
      simp[] >> metis_tac[projection_length]) >>
  simp[] >> metis_tac[projection_length]
QED

Theorem typed_guarded_base_assignment_projection:
  !env name elem bound bt ty cx v es res es'.
    FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
    well_typed_atarget env (BaseTarget bt) ty /\
    atarget_writes_ok (\t. ~place_contains t (NameTarget name)) (BaseTarget bt) /\
    assign_tuple_targets cx (BaseTarget bt) v es = (res,es') ==>
    MAP (\sc. FLOOKUP sc name) es'.scopes = MAP (\sc. FLOOKUP sc name) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  gvs[well_typed_atarget_def, well_typed_target_def, atarget_writes_ok_def] >>
  qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >>
  drule_all typed_guarded_target_write_projection >> simp[]
QED

Theorem typed_guarded_assignment_projection_mutual[local]:
  (!(cx:evaluation_context) (s:stmt). T) /\
  (!(cx:evaluation_context) (ss:stmt list). T) /\
  (!(cx:evaluation_context) (it:iterator). T) /\
  (!(cx:evaluation_context) (tyv:type_value) (nm:string) (body:stmt list) (vs:value list). T) /\
  (!(cx:evaluation_context) (e:expr). T) /\
  (!(cx:evaluation_context) (es:expr list). T) /\
  (!(cx:evaluation_context) (bt:base_assignment_target). T) /\
  (!(cx:evaluation_context) (bt:base_assignment_target). T) /\
  (!cx target v. !env name elem bound ty es res es'.
    FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
    well_typed_atarget env target ty /\
    atarget_writes_ok (\t. ~place_contains t (NameTarget name)) target /\
    assign_tuple_targets cx target v es = (res,es') ==>
    MAP (\sc. FLOOKUP sc name) es'.scopes = MAP (\sc. FLOOKUP sc name) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes) /\
  (!cx targets vs. !env name elem bound tys es res es'.
    FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
    LIST_REL (\tgt ty. well_typed_atarget env tgt ty) targets tys /\
    EVERY (atarget_writes_ok (\t. ~place_contains t (NameTarget name))) targets /\
    assign_tuple_target_list cx targets vs es = (res,es') ==>
    MAP (\sc. FLOOKUP sc name) es'.scopes = MAP (\sc. FLOOKUP sc name) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes) /\
  (!(cx:evaluation_context) (es:expr list). T)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> simp[] >>
  rpt gen_tac >> rpt strip_tac
  >>~- ([`assign_tuple_targets _ (BaseTarget _) _ _ = _`],
      gvs[well_typed_atarget_def, well_typed_target_def, atarget_writes_ok_def] >>
      qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
      simp[Once evaluate_def] >> strip_tac >>
      drule_all typed_guarded_target_write_projection >> simp[])
  >>~- ([`assign_tuple_targets _ (TupleTarget _) _ _ = _`],
      gvs[well_typed_atarget_def, atarget_writes_ok_def, SF ETA_ss] >>
      qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, raise_def, vyperValueTheory.value_CASE_rator,
           vyperValueTheory.array_value_CASE_rator, AllCaseEqs()] >>
      strip_tac >> gvs[] >> res_tac >> gvs[]) >>
  qpat_x_assum `assign_tuple_target_list _ _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, ignore_bind_def, bind_def, return_def, raise_def,
       AllCaseEqs()] >>
  strip_tac >> gvs[LIST_REL_CONS1, SF ETA_ss] >> res_tac >> gvs[]
QED

Theorem typed_guarded_assignment_projection:
  !env name elem bound target ty cx v es res es'.
    FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
    well_typed_atarget env target ty /\
    atarget_writes_ok (\t. ~place_contains t (NameTarget name)) target /\
    assign_tuple_targets cx target v es = (res,es') ==>
    MAP (\sc. FLOOKUP sc name) es'.scopes = MAP (\sc. FLOOKUP sc name) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  metis_tac[typed_guarded_assignment_projection_mutual]
QED

Theorem append_place_name_projection[local]:
  !cx p v es res es' name.
    (!root path. p = MemoryPlace root path ==> root <> name) /\
    append_place cx p v es = (res,es') ==>
    MAP (\sc. FLOOKUP sc name) es'.scopes = MAP (\sc. FLOOKUP sc name) es.scopes
Proof
  Cases_on `p` >> rpt gen_tac >> strip_tac
  >~ [`append_place _ (StoragePlace _ _ _) _ _ = _`]
  >- metis_tac[append_storage_place_scopes_immutables] >>
  gvs[append_place_def, bind_def, AllCaseEqs()] >>
  imp_res_tac read_place_state >> imp_res_tac place_type_value_state >>
  imp_res_tac lift_sum_state >> gvs[] >>
  drule_at (Pat `write_place _ _ _ _ = _`) write_guarded_place_projection >>
  simp[]
QED

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
    (!s r t. eval_expr cx e s = (r,t) ==>
      MAP (\sc. FLOOKUP sc name) t.scopes = MAP (\sc. FLOOKUP sc name) s.scopes) /\
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
  >- (gvs[IgnAsm `!s r t. _`] >> imp_res_tac projection_length >> gvs[]) >>
  drule_at (Pat `finally _ _ _ = _`) balanced_conditional_projection >>
  disch_then (qspec_then `name` mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[] >> strip_tac >>
  imp_res_tac projection_length >> gvs[]
QED

Theorem annassign_projection_frame:
  !cx id typ e name es res es'.
    id <> name /\
    (!s r t. eval_expr cx e s = (r,t) ==>
      MAP (\sc. FLOOKUP sc name) t.scopes = MAP (\sc. FLOOKUP sc name) s.scopes) /\
    eval_stmt cx (AnnAssign id typ e) es = (res,es') ==>
    MAP (\sc. FLOOKUP sc name) es'.scopes = MAP (\sc. FLOOKUP sc name) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac lift_option_type_state >> imp_res_tac read_result_state >>
  gvs[IgnAsm `!s r t. _`] >>
  first_x_assum drule >> strip_tac
  >~ [`new_variable _ _ _ _ = _`]
  >- (drule_all new_variable_other_projection >> strip_tac >>
      metis_tac[projection_length]) >>
  metis_tac[projection_length]
QED

Theorem for_projection_frame:
  !cx id typ it n stmts name es res es'.
    id <> name /\
    (!s r t. eval_iterator cx it s = (r,t) ==>
      MAP (\sc. FLOOKUP sc name) t.scopes = MAP (\sc. FLOOKUP sc name) s.scopes) /\
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
      (impl_tac >- metis_tac[]) >> strip_tac >>
      imp_res_tac projection_length >> gvs[]) >>
  gvs[IgnAsm `!s r t. _`] >> imp_res_tac projection_length >> gvs[]
QED

Theorem assign_projection_frame:
  !env name elem bound target ty rhs cx es res es'.
    FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
    well_typed_atarget env target ty /\
    atarget_writes_ok (\t. ~place_contains t (NameTarget name)) target /\
    (!s r t. eval_expr cx rhs s = (r,t) ==>
      MAP (\sc. FLOOKUP sc name) t.scopes = MAP (\sc. FLOOKUP sc name) s.scopes) /\
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
  first_x_assum drule >> strip_tac
  >~ [`assign_tuple_targets _ _ _ _ = _`]
  >- (drule_all typed_guarded_assignment_projection >> strip_tac >>
      metis_tac[projection_length]) >>
  metis_tac[projection_length]
QED

Resume assign_projection_frame[base]:
  rename1 `eval_stmt cx (Assign (BaseTarget bt) rhs) es = _` >>
  gvs[well_typed_atarget_def, well_typed_target_def, atarget_writes_ok_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> gvs[IgnAsm `!s r t. _`] >>
  first_x_assum drule >> strip_tac >>
  imp_res_tac typed_target_name_projection >> gvs[]
  >~ [`write_place _ _ _ _ = _`]
  >- (rename1 `write_place cx dest value mid = (res,es')` >>
      `!root path. dest = MemoryPlace root path ==> root <> name` by
        (rpt strip_tac >> gvs[] >> metis_tac[typed_guarded_eval_target_root]) >>
      drule_all write_guarded_place_projection >> strip_tac >>
      metis_tac[projection_length]) >>
  metis_tac[projection_length]
QED

Finalise assign_projection_frame

Theorem augassign_projection_frame:
  !env name elem bound bt ty bop rhs cx es res es'.
    FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
    well_typed_target env bt ty /\ ~place_contains bt (NameTarget name) /\
    target_writes_ok (\w. ~place_contains w (NameTarget name)) bt /\
    (!s r t. eval_expr cx rhs s = (r,t) ==>
      MAP (\sc. FLOOKUP sc name) t.scopes = MAP (\sc. FLOOKUP sc name) s.scopes) /\
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
  imp_res_tac typed_target_name_projection >>
  gvs[IgnAsm `!s r t. _`] >> res_tac
  >~ [`write_place _ _ _ _ = _`]
  >- (rename1 `write_place cx dest value mid = (res,es')` >>
      `!root path. dest = MemoryPlace root path ==> root <> name` by
        (rpt strip_tac >> gvs[] >> metis_tac[typed_guarded_eval_target_root]) >>
      drule_all write_guarded_place_projection >> strip_tac >>
      metis_tac[projection_length]) >>
  metis_tac[projection_length]
QED

Theorem append_projection_frame:
  !cx bt rhs name es res es'.
    FST (place_access bt []) <> NameTarget name /\
    target_writes_ok (\w. FST (place_access w []) <> NameTarget name) bt /\
    (!s r t. eval_expr cx rhs s = (r,t) ==>
      MAP (\sc. FLOOKUP sc name) t.scopes = MAP (\sc. FLOOKUP sc name) s.scopes) /\
    eval_stmt cx (Append bt rhs) es = (res,es') ==>
    MAP (\sc. FLOOKUP sc name) es'.scopes = MAP (\sc. FLOOKUP sc name) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >>
  imp_res_tac (cj 8 eval_name_projection_mutual) >>
  gvs[IgnAsm `!s r t. _`] >> res_tac
  >~ [`append_place _ _ _ _ = _`]
  >- (rename1 `append_place cx dest value mid = (res,es')` >>
      `!root path. dest = MemoryPlace root path ==> root <> name` by
        (rpt strip_tac >> gvs[] >> metis_tac[eval_target_place_memory_root]) >>
      drule_all append_place_name_projection >> strip_tac >>
      metis_tac[projection_length]) >>
  metis_tac[projection_length]
QED

Theorem typed_iterator_projection[local]:
  !env typ it name elem bound cx st res st'.
    FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
    well_typed_iterator env typ it /\
    (case it of
     | Array e => expr_writes_ok (\w. ~place_contains w (NameTarget name)) e
     | Range x y => expr_writes_ok (\w. ~place_contains w (NameTarget name)) x /\
                    expr_writes_ok (\w. ~place_contains w (NameTarget name)) y) /\
    eval_iterator cx it st = (res,st') ==>
    MAP (\sc. FLOOKUP sc name) st'.scopes = MAP (\sc. FLOOKUP sc name) st.scopes
Proof
  Cases_on `it` >> rpt gen_tac >> strip_tac >>
  gvs[well_typed_iterator_def] >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> imp_res_tac lift_option_type_state >>
  imp_res_tac lift_sum_state >> gvs[return_def] >>
  imp_res_tac typed_expr_name_projection >> gvs[]
QED

Theorem typed_projection_frames_mutual:
  (!env ret_ty stmt env' name elem bound cx es res es'.
    FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
    type_stmt env ret_ty stmt = SOME env' /\
    stmt_writes_ok (\w. ~place_contains w (NameTarget name)) stmt /\
    es.scopes <> [] /\ eval_stmt cx stmt es = (res,es') ==>
    MAP (\sc. FLOOKUP sc name) es'.scopes = MAP (\sc. FLOOKUP sc name) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes) /\
  (!env ret_ty stmts env' name elem bound cx es res es'.
    FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
    type_stmts env ret_ty stmts = SOME env' /\
    stmts_writes_ok (\w. ~place_contains w (NameTarget name)) stmts /\
    es.scopes <> [] /\ eval_stmts cx stmts es = (res,es') ==>
    MAP (\sc. FLOOKUP sc name) es'.scopes = MAP (\sc. FLOOKUP sc name) es.scopes /\
    LENGTH es'.scopes = LENGTH es.scopes)
Proof
  ho_match_mp_tac type_stmt_ind >> rpt conj_tac >>
  rpt (gen_tac ORELSE disch_then strip_assume_tac)
  >~ [`eval_stmt _ Pass _ = _`] >- gvs[Once evaluate_def, return_def]
  >~ [`eval_stmt _ Break _ = _`] >- gvs[Once evaluate_def, raise_def]
  >~ [`eval_stmt _ Continue _ = _`] >- gvs[Once evaluate_def, raise_def]
  >~ [`eval_stmt _ (Return NONE) _ = _`] >- gvs[Once evaluate_def, raise_def]
  >~ [`eval_stmt _ (Raise RaiseBare) _ = _`] >- gvs[Once evaluate_def, raise_def]
  >~ [`eval_stmt _ (Raise RaiseUnreachable) _ = _`]
  >- gvs[Once evaluate_def, raise_def]
  >~ [`eval_stmts _ [] _ = _`] >- gvs[Once evaluate_def, return_def]
  >~ [`eval_stmt _ (Expr _) _ = _`] >- suspend "expr"
  >~ [`eval_stmt _ (Return (SOME _)) _ = _`] >- suspend "return"
  >~ [`eval_stmt _ (Raise (RaiseReason _)) _ = _`] >- suspend "raise_reason"
  >~ [`eval_stmt _ (Raise (RaiseCustomError _)) _ = _`] >- suspend "raise_custom"
  >~ [`eval_stmt _ (Assert _ AssertBare) _ = _`] >- suspend "assert_bare"
  >~ [`eval_stmt _ (Assert _ AssertUnreachable) _ = _`]
  >- suspend "assert_unreachable"
  >~ [`eval_stmt _ (Assert _ (AssertReason _)) _ = _`] >- suspend "assert_reason"
  >~ [`eval_stmt _ (Assert _ (AssertCustomError _)) _ = _`]
  >- suspend "assert_custom"
  >~ [`eval_stmt _ (Log _ _) _ = _`] >- suspend "log"
  >~ [`eval_stmt _ (AnnAssign _ _ _) _ = _`] >- suspend "annassign"
  >~ [`eval_stmt _ (Append _ _) _ = _`] >- suspend "append"
  >~ [`eval_stmt _ (Assign _ _) _ = _`] >- suspend "assign"
  >~ [`eval_stmt _ (AugAssign _ _ _ _) _ = _`] >- suspend "augassign"
  >~ [`eval_stmt _ (If _ _ _) _ = _`] >- suspend "if"
  >~ [`eval_stmt _ (For _ _ _ _ _) _ = _`] >- suspend "for"
  >~ [`eval_stmts _ (_::_) _ = _`] >- suspend "cons"
QED

Resume typed_projection_frames_mutual[expr]:
  gvs[type_stmt_def, stmt_writes_ok_def, AllCaseEqs()] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, type_check_def, assert_def,
       ignore_bind_def, return_def, raise_def, AllCaseEqs()] >> strip_tac >>
  drule_all typed_expr_name_projection >> strip_tac >> gvs[] >>
  metis_tac[projection_length]
QED

Resume typed_projection_frames_mutual[return]:
  gvs[type_stmt_def, stmt_writes_ok_def, AllCaseEqs()] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, raise_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >>
  drule_all typed_expr_name_projection >> strip_tac >> gvs[] >>
  metis_tac[projection_length]
QED

Resume typed_projection_frames_mutual[raise_reason]:
  gvs[type_stmt_def, stmt_writes_ok_def, AllCaseEqs()] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, raise_def, AllCaseEqs()] >> strip_tac >>
  imp_res_tac read_result_state >> imp_res_tac lift_option_type_state >>
  drule_all typed_expr_name_projection >> strip_tac >> gvs[] >>
  metis_tac[projection_length]
QED

Resume typed_projection_frames_mutual[raise_custom]:
  rename1 `Raise (RaiseCustomError err)` >>
  gvs[type_stmt_def, stmt_writes_ok_def, AllCaseEqs()] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  Cases_on `err` >>
  simp[Once evaluate_def, bind_def, raise_def,
       vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >> strip_tac >>
  gvs[] >> imp_res_tac lift_option_state >>
  drule_all typed_custom_error_name_projection >> strip_tac >> gvs[] >>
  metis_tac[projection_length]
QED

Resume typed_projection_frames_mutual[assert_bare]:
  gvs[type_stmt_def, stmt_writes_ok_def, AllCaseEqs()] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs()] >>
  strip_tac >>
  drule_all typed_expr_name_projection >> strip_tac >>
  imp_res_tac read_result_state >>
  gvs[return_def, raise_def, COND_RATOR, AllCaseEqs()] >>
  metis_tac[projection_length]
QED

Resume typed_projection_frames_mutual[assert_unreachable]:
  gvs[type_stmt_def, stmt_writes_ok_def, AllCaseEqs()] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs()] >>
  strip_tac >>
  drule_all typed_expr_name_projection >> strip_tac >>
  imp_res_tac read_result_state >>
  gvs[return_def, raise_def, COND_RATOR, AllCaseEqs()] >>
  metis_tac[projection_length]
QED

Resume typed_projection_frames_mutual[assert_reason]:
  rename1 `Assert cond (AssertReason msg)` >>
  gvs[type_stmt_def, stmt_writes_ok_def, AllCaseEqs()] >>
  `!s r t. eval_expr cx msg s = (r,t) ==>
     MAP (\sc. FLOOKUP sc name) t.scopes = MAP (\sc. FLOOKUP sc name) s.scopes` by
    (rpt strip_tac >> drule_all typed_expr_name_projection >> simp[]) >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs()] >>
  strip_tac >>
  drule_all typed_expr_name_projection >> strip_tac >>
  imp_res_tac read_result_state >>
  gvs[IgnAsm `!s r t. _`, return_def, raise_def, COND_RATOR, bind_def,
      AllCaseEqs()] >>
  imp_res_tac read_result_state >> imp_res_tac lift_option_type_state >>
  res_tac >> gvs[] >> metis_tac[projection_length]
QED

Resume typed_projection_frames_mutual[assert_custom]:
  rename1 `Assert cond (AssertCustomError err)` >>
  gvs[type_stmt_def, stmt_writes_ok_def, AllCaseEqs()] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  Cases_on `err` >>
  simp[Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs()] >>
  strip_tac >>
  drule_all typed_expr_name_projection >> strip_tac >>
  imp_res_tac read_result_state >>
  gvs[return_def, raise_def, COND_RATOR, bind_def,
      vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >>
  imp_res_tac lift_option_state >> gvs[]
  >>~- ([`eval_exprs _ _ _ = _`],
        drule_all typed_custom_error_name_projection >> strip_tac >>
        imp_res_tac projection_length >> gvs[]) >>
  imp_res_tac projection_length >> gvs[]
QED

Resume typed_projection_frames_mutual[log]:
  gvs[type_stmt_def, stmt_writes_ok_def, AllCaseEqs()] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  Cases_on `cx.txn.is_static` >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs()] >>
  strip_tac >>
  drule_all typed_exprs_name_projection >> strip_tac >>
  imp_res_tac lift_option_state >> imp_res_tac push_log_scopes >>
  gvs[] >> metis_tac[projection_length]
QED

Resume typed_projection_frames_mutual[annassign]:
  rename1 `eval_stmt cx (AnnAssign id typ rhs) es = (res,es')` >>
  gvs[type_stmt_def, stmt_writes_ok_def, AllCaseEqs()] >>
  `id <> name` by (strip_tac >> gvs[FLOOKUP_DEF]) >>
  `!s r t. eval_expr cx rhs s = (r,t) ==>
     MAP (\sc. FLOOKUP sc name) t.scopes = MAP (\sc. FLOOKUP sc name) s.scopes` by
    (rpt strip_tac >> drule_all typed_expr_name_projection >> simp[]) >>
  drule_all annassign_projection_frame >> simp[]
QED

Resume typed_projection_frames_mutual[append]:
  rename1 `eval_stmt cx (Append bt rhs) es = (res,es')` >>
  gvs[type_stmt_def, stmt_writes_ok_def, AllCaseEqs()] >>
  `FST (place_access bt []) <> NameTarget name` by
    (drule_all typed_guarded_array_target_root >> simp[]) >>
  `target_writes_ok (\w. FST (place_access w []) <> NameTarget name) bt` by
    (drule writes_ok_typed_root >> strip_tac >> first_x_assum irule >> simp[]) >>
  `!s r t. eval_expr cx rhs s = (r,t) ==>
     MAP (\sc. FLOOKUP sc name) t.scopes = MAP (\sc. FLOOKUP sc name) s.scopes` by
    (rpt strip_tac >> drule_all typed_expr_name_projection >> simp[]) >>
  drule_all append_projection_frame >> simp[]
QED

Resume typed_projection_frames_mutual[assign]:
  rename1 `eval_stmt cx (Assign target rhs) es = (res,es')` >>
  gvs[type_stmt_def, stmt_writes_ok_def, AllCaseEqs()] >>
  drule_all atarget_accepts_well_typed_atarget >> strip_tac >>
  `!s r t. eval_expr cx rhs s = (r,t) ==>
     MAP (\sc. FLOOKUP sc name) t.scopes = MAP (\sc. FLOOKUP sc name) s.scopes` by
    (rpt strip_tac >> drule_all typed_expr_name_projection >> simp[]) >>
  drule_all assign_projection_frame >> simp[]
QED

Resume typed_projection_frames_mutual[augassign]:
  rename1 `eval_stmt cx (AugAssign ty bt bop rhs) es = (res,es')` >>
  gvs[type_stmt_def, stmt_writes_ok_def, AllCaseEqs()] >>
  `!s r t. eval_expr cx rhs s = (r,t) ==>
     MAP (\sc. FLOOKUP sc name) t.scopes = MAP (\sc. FLOOKUP sc name) s.scopes` by
    (rpt strip_tac >> drule_all typed_expr_name_projection >> simp[]) >>
  drule_all augassign_projection_frame >> simp[]
QED

Resume typed_projection_frames_mutual[if]:
  rename1 `eval_stmt cx (If e ss1 ss2) es = (res,es')` >>
  gvs[type_stmt_def, stmt_writes_ok_def, optionTheory.IS_SOME_EXISTS,
      AllCaseEqs()] >>
  `!s r t. eval_expr cx e s = (r,t) ==>
     MAP (\sc. FLOOKUP sc name) t.scopes = MAP (\sc. FLOOKUP sc name) s.scopes` by
    (rpt strip_tac >> drule_all typed_expr_name_projection >> simp[]) >>
  `!s r t. s.scopes <> [] /\ eval_stmts cx ss1 s = (r,t) ==>
     MAP (\sc. FLOOKUP sc name) t.scopes = MAP (\sc. FLOOKUP sc name) s.scopes /\
     LENGTH t.scopes = LENGTH s.scopes` by
    (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  `!s r t. s.scopes <> [] /\ eval_stmts cx ss2 s = (r,t) ==>
     MAP (\sc. FLOOKUP sc name) t.scopes = MAP (\sc. FLOOKUP sc name) s.scopes /\
     LENGTH t.scopes = LENGTH s.scopes` by
    (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  drule_all if_projection_frame >> simp[]
QED

Resume typed_projection_frames_mutual[for]:
  gvs[type_stmt_def, stmt_writes_ok_def, optionTheory.IS_SOME_EXISTS,
      AllCaseEqs()] >>
  `id <> name` by (strip_tac >> gvs[FLOOKUP_DEF]) >>
  `FLOOKUP (extend_local env id typ F).var_types name = SOME (ArrayT elem bound)`
    by simp[extend_local_def, FLOOKUP_UPDATE] >>
  `!s r t. eval_iterator cx it s = (r,t) ==>
     MAP (\sc. FLOOKUP sc name) t.scopes = MAP (\sc. FLOOKUP sc name) s.scopes` by
    (rpt strip_tac >> drule_all typed_iterator_projection >> simp[]) >>
  `!s r t. s.scopes <> [] /\ eval_stmts cx stmts s = (r,t) ==>
     MAP (\sc. FLOOKUP sc name) t.scopes = MAP (\sc. FLOOKUP sc name) s.scopes /\
     LENGTH t.scopes = LENGTH s.scopes` by
    (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  drule_all for_projection_frame >> simp[]
QED

Resume typed_projection_frames_mutual[cons]:
  rename1 `eval_stmts cx (s::ss) es = (res,es')` >>
  qpat_x_assum `type_stmts _ _ (_::_) = _` mp_tac >>
  simp[Once type_stmt_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `stmts_writes_ok _ (_::_)` mp_tac >>
  simp[stmt_writes_ok_def] >> strip_tac >>
  drule_all type_stmt_var_types_preserve >> strip_tac >>
  qpat_x_assum `eval_stmts _ (_::_) _ = _` mp_tac >>
  simp[NoAsms, Once evaluate_def, ignore_bind_def, bind_def, AllCaseEqs()] >>
  strip_tac >>
  first_x_assum drule_all >> strip_tac
  >~ [`eval_stmts _ ss _ = _`]
  >- (rename1 `eval_stmts cx ss mid = _` >>
      `mid.scopes <> []` by (Cases_on `mid.scopes` >> gvs[]) >>
      first_x_assum drule_all >> strip_tac >> gvs[]) >>
  gvs[]
QED

Finalise typed_projection_frames_mutual

Theorem typed_stmt_projection_frame:
  FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
  type_stmt env ret_ty stmt = SOME env' /\
  stmt_writes_ok (\w. ~place_contains w (NameTarget name)) stmt /\
  es.scopes <> [] /\ eval_stmt cx stmt es = (res,es') ==>
  MAP (\sc. FLOOKUP sc name) es'.scopes =
    MAP (\sc. FLOOKUP sc name) es.scopes /\
  LENGTH es'.scopes = LENGTH es.scopes
Proof
  metis_tac[cj 1 typed_projection_frames_mutual]
QED

Theorem typed_stmts_projection_frame:
  FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
  type_stmts env ret_ty stmts = SOME env' /\
  stmts_writes_ok (\w. ~place_contains w (NameTarget name)) stmts /\
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
  !body env name elem bound ret_ty env' aty es tmp outer cx res es'.
  FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
  type_stmts env ret_ty body = SOME env' /\
  iterator_unmodified (Array (Name aty name)) body /\
  es.scopes = tmp::outer /\
  finally (eval_stmts cx body) pop_scope es = (res,es') ==>
  MAP (\sc. FLOOKUP sc name) es'.scopes =
    MAP (\sc. FLOOKUP sc name) outer /\
  LENGTH es'.scopes = LENGTH outer
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `type_stmts env ret_ty stmts = SOME env'` >>
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
  !body env name elem bound ret_ty env' aty es tmp outer cx res es'.
  FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
  type_stmts env ret_ty body = SOME env' /\
  iterator_unmodified (Array (Name aty name)) body /\
  es.scopes = tmp::outer /\
  finally (eval_stmts cx body) pop_scope es = (res,es') ==>
  lookup_scopes name es'.scopes = lookup_scopes name outer
Proof
  rpt gen_tac >> strip_tac >> drule_all array_body_pop_projection >> strip_tac >>
  irule scope_projection_lookup >> simp[]
QED
