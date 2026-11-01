(*
 * Soundness lemmas for global/toplevel expression lookup.
 *)

Theory vyperTypeGlobalLookupSoundness
Ancestors
  list rich_list pred_set prim_rec arithmetic finite_map option pair sum
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperInterpreter vyperState vyperContext vyperStorage vyperTyping
  vyperEncodeDecode vyperArith vyperTypeSystem vyperTypeInvariants vyperTypeValues
  vyperTypeEnv vyperTypeEnvExtension vyperTypeEnvPreservation vyperTypeScopePop
  vyperTypeABI vyperTypeBindArguments vyperTypeExprResult vyperTypeStmtResult
  vyperTypeBuiltins vyperTypeExprSoundness vyperTypeAssignSoundness vyperPlaceTyping
  vyperExprNoControl vyperScopePreservation vyperEvalPreservesScopes
  vyperEvalMisc vyperStatePreservation vyperAssignPreservesType vyperTypeStatePreservation
Libs
  wordsLib markerLib intLib

Theorem get_immutables_success:
  !cx src st imms st'.
    get_immutables cx src st = (INL imms, st') ==>
    imms = get_source_immutables src
      (case ALOOKUP st.immutables cx.txn.target of NONE => [] | SOME m => m) /\
    st' = st
Proof
  rw[get_immutables_def, get_address_immutables_def, bind_def, return_def,
     lift_option_type_def, lift_option_def, raise_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[return_def, raise_def]
QED
Theorem get_immutables_error:
  !cx src st e st'.
    get_immutables cx src st = (INR e, st') ==>
    ALOOKUP st.immutables cx.txn.target = NONE /\
    e = Error (TypeError "get_address_immutables") /\ st' = st
Proof
  rw[get_immutables_def, get_address_immutables_def, bind_def,
     lift_option_type_def, return_def, raise_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[return_def, raise_def]
QED


Theorem TopLevelName_nonbare_find_NONE_contradiction:
  !env cx st src id ty ts.
    env_consistent env cx st /\
    FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) /\
    FLOOKUP env.bare_globals (src,id) = NONE /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = NONE ==>
    F
Proof
  rpt strip_tac >>
  drule_all env_consistent_toplevel_storage_static >>
  strip_tac >>
  gvs[]
QED

Theorem TopLevelName_current_bare_global_immutable_exists:
  !env cx st id ty.
    env_consistent env cx st /\
    FLOOKUP env.bare_globals (env.current_src,id) = SOME ty ==>
    IS_SOME (FLOOKUP
      (get_source_immutables env.current_src
        (case ALOOKUP st.immutables cx.txn.target of NONE => [] | SOME m => m)) id)
Proof
  metis_tac[env_consistent_bare_global_ready]
QED

Theorem TopLevelName_toplevel_vtypes_Type:
  !env cx st src id ty.
    well_typed_expr env (TopLevelName ty (src,id)) /\
    env_consistent env cx st ==>
    FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty)
Proof
  rpt strip_tac >>
  Cases_on `FLOOKUP env.bare_globals (src,id)` >-
    gvs[well_typed_expr_def] >>
  gvs[well_typed_expr_def] >>
  drule_all env_consistent_bare_global_find_NONE >>
  strip_tac >> gvs[]
QED

Theorem TopLevelName_missing_immutable_branch_characterisation:
  !env cx st src id ty ts.
    well_typed_expr env (TopLevelName ty (src,id)) /\
    env_consistent env cx st /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = NONE /\
    ~IS_SOME (FLOOKUP
      (get_source_immutables src
        (case ALOOKUP st.immutables cx.txn.target of NONE => [] | SOME m => m))
      id) ==>
    FLOOKUP env.bare_globals (src,id) <> NONE /\ src <> env.current_src
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `FLOOKUP env.bare_globals (src,id)` >- (
    `FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty)` by
      gvs[well_typed_expr_def] >>
    drule_all TopLevelName_nonbare_find_NONE_contradiction >> simp[]) >>
  conj_tac >- simp[] >>
  strip_tac >> gvs[] >>
  drule_all TopLevelName_current_bare_global_immutable_exists >>
  simp[]
QED

Theorem TopLevelName_missing_immutable_impossible:
  !env cx st src id ty code.
    well_typed_expr env (TopLevelName ty (src,id)) /\
    env_consistent env cx st /\
    functions_well_typed cx /\
    get_module_code cx src = SOME code /\
    find_var_decl_by_name id code = NONE /\
    ~IS_SOME (FLOOKUP
      (get_source_immutables src
        (case ALOOKUP st.immutables cx.txn.target of NONE => [] | SOME m => m))
      id) ==>
    F
Proof
  rpt gen_tac >> strip_tac >>
  drule_all TopLevelName_missing_immutable_branch_characterisation >>
  strip_tac >>
  Cases_on `FLOOKUP env.bare_globals (src,id)` >> gvs[] >>
  drule_all env_consistent_bare_global_ready_src >>
  simp[]
QED

Theorem lookup_global_TopLevelName_find_NONE_no_type_error:
  !env cx st src id ty code res st'.
    well_typed_expr env (TopLevelName ty (src,id)) /\
    env_consistent env cx st /\
    functions_well_typed cx /\
    get_module_code cx src = SOME code /\
    find_var_decl_by_name id code = NONE /\
    lookup_global cx src id st = (res,st') ==>
    no_type_error_result res
Proof
  rpt strip_tac >>
  qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
  simp[lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def] >>
  Cases_on `get_immutables cx src st` >> Cases_on `q`
  >- (simp[bind_def, return_def, raise_def] >>
      Cases_on `FLOOKUP x id`
      >- (strip_tac >> gvs[] >>
          drule get_immutables_success >> strip_tac >> gvs[] >>
          `F` by (
            qspecl_then [`env`, `cx`, `r`, `src`, `id`, `ty`, `code`] mp_tac
              TopLevelName_missing_immutable_impossible >>
            simp[]) >>
          simp[]) >>
      strip_tac >> gvs[return_def, no_type_error_result_def]) >>
  simp[bind_def, return_def, raise_def] >>
  strip_tac >>
  drule get_immutables_error >> strip_tac >> gvs[] >>
  `F` by (
    qspecl_then [`env`, `cx`, `r`, `src`, `id`, `ty`, `code`] mp_tac
      TopLevelName_missing_immutable_impossible >>
    simp[get_source_immutables_def]) >>
  simp[]
QED
Theorem lookup_global_TopLevelName_find_NONE_success_typed:
  !env cx st src id ty code tvl st'.
    well_typed_expr env (TopLevelName ty (src,id)) /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    get_module_code cx src = SOME code /\
    find_var_decl_by_name id code = NONE /\
    lookup_global cx src id st = (INL tvl,st') ==>
    eval_result_typed (env,cx,st') tvl (Type ty)
Proof
  rpt strip_tac >>
  `FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty)` by (
    Cases_on `FLOOKUP env.bare_globals (src,id)` >-
      gvs[well_typed_expr_def] >>
    gvs[well_typed_expr_def] >>
    drule_all env_consistent_bare_global_find_NONE >> gvs[]) >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
  simp[lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def] >>
  Cases_on `get_immutables cx src st` >> Cases_on `q`
  >- (simp[bind_def, return_def, raise_def] >>
      Cases_on `FLOOKUP x id`
      >- (strip_tac >> gvs[] >>
          drule get_immutables_success >> strip_tac >> gvs[] >>
          `F` by (
            qspecl_then [`env`, `cx`, `r`, `src`, `id`, `ty`, `code`] mp_tac
              TopLevelName_missing_immutable_impossible >>
            simp[]) >>
          simp[]) >>
      strip_tac >> gvs[return_def] >>
      PairCases_on `x'` >> rename1 `SOME (imm_tv,imm_v)` >> gvs[] >>
      simp[eval_result_typed_def] >>
      qexists_tac `imm_tv` >> simp[] >>
      conj_tac >- (
        drule get_immutables_success >> strip_tac >> gvs[] >>
        qpat_x_assum `env_consistent env cx r` mp_tac >>
        simp[env_consistent_def, env_immutables_consistent_def] >>
        strip_tac >>
        qpat_x_assum `!src' id ty' ts. _`
          (qspecl_then [`src`, `id`, `ty`, `code`] mp_tac) >>
        simp[] >> strip_tac >>
        first_x_assum (qspecl_then [`id`, `imm_tv`, `imm_v`] mp_tac) >>
        simp[]) >>
      simp[runtime_place_typed_immutable, subscripts_type_def] >>
      conj_tac
      >- metis_tac[vyperPlaceTypingTheory.get_immutables_success_typed] >>
      goal_assum (drule_at Any) >>
      metis_tac[get_immutables_success]) >>
  simp[bind_def, return_def, raise_def]
QED

Theorem TopLevelName_nonbare_storage_decl_context:
  !env cx st src id ty code is_transient typ id_str.
    well_typed_expr env (TopLevelName ty (src,id)) /\
    env_consistent env cx st /\
    FLOOKUP env.bare_globals (src,id) = NONE /\
    get_module_code cx src = SOME code /\
    find_var_decl_by_name id code =
      SOME (StorageVarDecl is_transient typ,id_str) ==>
    typ = ty /\
    IS_SOME (evaluate_type (get_tenv cx) typ) /\
    IS_SOME (lookup_var_slot_from_layout cx is_transient src id_str)
Proof
  rpt strip_tac >>
  `FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty)` by
    metis_tac[TopLevelName_toplevel_vtypes_Type] >>
  drule_all env_consistent_toplevel_storage_static >>
  strip_tac >> gvs[]
QED

Theorem TopLevelName_storage_decl_type_eq:
  !env cx st src id ty code is_transient typ id_str.
    well_typed_expr env (TopLevelName ty (src,id)) /\
    env_consistent env cx st /\
    get_module_code cx src = SOME code /\
    find_var_decl_by_name id code =
      SOME (StorageVarDecl is_transient typ,id_str) ==>
    typ = ty
Proof
  rpt strip_tac >>
  `FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty)` by
    metis_tac[TopLevelName_toplevel_vtypes_Type] >>
  gvs[env_consistent_def, env_immutables_consistent_def] >>
  qpat_x_assum `!src id ty ts. _`
    (qspecl_then [`src`, `id`, `ty`, `code`] mp_tac) >>
  simp[] >> strip_tac >>
  first_x_assum (qspecl_then [`is_transient`, `typ`, `id_str`] mp_tac) >>
  simp[]
QED
Theorem lookup_global_StorageVarDecl_no_type_error:
  !cx src n st res st' code is_transient typ id_str slot tv.
    get_module_code cx src = SOME code /\
    find_var_decl_by_name n code = SOME (StorageVarDecl is_transient typ,id_str) /\
    lookup_var_slot_from_layout cx is_transient src id_str = SOME slot /\
    evaluate_type (get_tenv cx) typ = SOME tv /\
    lookup_global cx src n st = (res,st') ==>
    no_type_error_result res
Proof
  rpt strip_tac >>
  qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
  simp[lookup_global_def, bind_def, lift_option_type_def, return_def, raise_def,
       LET_THM, option_CASE_rator, var_decl_info_CASE_rator, prod_CASE_rator,
       type_value_CASE_rator, AllCaseEqs()] >>
  Cases_on `tv` >> simp[return_def, no_type_error_result_def] >>
  rpt strip_tac >> gvs[] >>
  drule read_storage_slot_error >> strip_tac >> gvs[]
QED

Theorem lookup_global_TopLevelName_storage_success_typed:
  !env cx st src id ty code is_transient typ id_str tvl st'.
    well_typed_expr env (TopLevelName ty (src,id)) /\
    env_consistent env cx st /\
    state_well_typed st /\
    context_well_typed cx /\
    accounts_well_typed st.accounts /\
    functions_well_typed cx /\
    get_module_code cx src = SOME code /\
    find_var_decl_by_name id code =
      SOME (StorageVarDecl is_transient typ,id_str) /\
    lookup_global cx src id st = (INL tvl,st') ==>
    eval_result_typed (env,cx,st') tvl (Type ty)
Proof
  rpt strip_tac >>
  `typ = ty` by metis_tac[TopLevelName_storage_decl_type_eq] >> gvs[] >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
  simp[lookup_global_def, bind_def, lift_option_type_def, return_def, raise_def,
       LET_THM, option_CASE_rator, var_decl_info_CASE_rator, prod_CASE_rator,
       type_value_CASE_rator, AllCaseEqs()] >>
  Cases_on `lookup_var_slot_from_layout cx is_transient src id_str` >> gvs[] >>
  Cases_on `evaluate_type (get_tenv cx) ty` >> gvs[] >>
  rename1 `evaluate_type (get_tenv cx) ty = SOME tv` >>
  rpt strip_tac >> gvs[eval_result_typed_def] >>
  metis_tac[evaluate_type_well_formed_type_value]
QED

Theorem TopLevelName_Type_HashMapVarDecl_impossible:
  !env cx st src id ty code is_transient kt vt id_str.
    well_typed_expr env (TopLevelName ty (src,id)) /\
    env_consistent env cx st /\
    state_well_typed st /\
    context_well_typed cx /\
    accounts_well_typed st.accounts /\
    get_module_code cx src = SOME code /\
    find_var_decl_by_name id code =
      SOME (HashMapVarDecl is_transient kt vt,id_str) ==>
    F
Proof
  rpt strip_tac >>
  `FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty)` by
    metis_tac[TopLevelName_toplevel_vtypes_Type] >>
  `runtime_consistent env cx st` by simp[runtime_consistent_def] >>
  metis_tac[top_level_Type_not_hashmap_decl]
QED


Theorem TopLevelName_bare_storage_decl_impossible:
  !env cx st src id ty code is_transient typ id_str bare.
    well_typed_expr env (TopLevelName ty (src,id)) /\
    env_consistent env cx st /\
    get_module_code cx src = SOME code /\
    find_var_decl_by_name id code =
      SOME (StorageVarDecl is_transient typ,id_str) /\
    FLOOKUP env.bare_globals (src,id) = SOME bare ==>
    F
Proof
  rpt strip_tac >>
  drule_all env_consistent_bare_global_find_NONE >>
  strip_tac >>
  gvs[]
QED


Theorem lookup_global_TopLevelName_no_type_error:
  !env cx st src id ty res st'.
    well_typed_expr env (TopLevelName ty (src,id)) /\
    env_consistent env cx st /\
    state_well_typed st /\
    context_well_typed cx /\
    accounts_well_typed st.accounts /\
    functions_well_typed cx /\
    lookup_global cx src id st = (res,st') ==>
    no_type_error_result res
Proof
  rpt strip_tac >>
  `FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty)` by
    metis_tac[TopLevelName_toplevel_vtypes_Type] >>
  `?code. get_module_code cx src = SOME code` by (
    Cases_on `FLOOKUP env.bare_globals (src,id)` >>
    metis_tac[env_consistent_toplevel_storage_static, env_consistent_def,
              env_context_consistent_def]) >>
  Cases_on `find_var_decl_by_name id code`
  >- metis_tac[lookup_global_TopLevelName_find_NONE_no_type_error] >>
  PairCases_on `x` >> Cases_on `x0` >> gvs[]
  >- (Cases_on `FLOOKUP env.bare_globals (src,id)`
      >- (drule_all TopLevelName_nonbare_storage_decl_context >>
          strip_tac >> gvs[IS_SOME_EXISTS] >>
          metis_tac[lookup_global_StorageVarDecl_no_type_error]) >>
      metis_tac[TopLevelName_bare_storage_decl_impossible]) >>
  metis_tac[TopLevelName_Type_HashMapVarDecl_impossible]
QED

Theorem lookup_global_TopLevelName_success_typed:
  !env cx st src id ty tvl st'.
    well_typed_expr env (TopLevelName ty (src,id)) /\
    env_consistent env cx st /\
    state_well_typed st /\
    context_well_typed cx /\
    accounts_well_typed st.accounts /\
    functions_well_typed cx /\
    lookup_global cx src id st = (INL tvl,st') ==>
    eval_result_typed (env,cx,st') tvl (Type ty)
Proof
  rpt strip_tac >>
  `FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty)` by
    metis_tac[TopLevelName_toplevel_vtypes_Type] >>
  `?code. get_module_code cx src = SOME code` by (
    Cases_on `FLOOKUP env.bare_globals (src,id)` >>
    metis_tac[env_consistent_toplevel_storage_static, env_consistent_def,
              env_context_consistent_def]) >>
  Cases_on `find_var_decl_by_name id code`
  >- metis_tac[lookup_global_TopLevelName_find_NONE_success_typed] >>
  PairCases_on `x` >> Cases_on `x0` >> gvs[]
  >- metis_tac[lookup_global_TopLevelName_storage_success_typed] >>
  metis_tac[TopLevelName_Type_HashMapVarDecl_impossible]
QED

Theorem lookup_global_TopLevelName_sound:
  !env cx st src id ty res st'.
    well_typed_expr env (TopLevelName ty (src,id)) /\
    env_consistent env cx st /\
    state_well_typed st /\
    context_well_typed cx /\
    accounts_well_typed st.accounts /\
    functions_well_typed cx /\
    lookup_global cx src id st = (res,st') ==>
    no_type_error_result res /\
    (case res of
     | INL tvl => eval_result_typed (env,cx,st') tvl (Type ty)
     | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac >- metis_tac[lookup_global_TopLevelName_no_type_error] >>
  Cases_on `res` >> simp[] >>
  metis_tac[lookup_global_TopLevelName_success_typed]
QED

Theorem lookup_global_TopLevelName_place_sound:
  !env cx st src id ann vt res st'.
    type_place_expr env (TopLevelName ann (src,id)) = SOME vt /\
    env_consistent env cx st /\
    state_well_typed st /\
    context_well_typed cx /\
    accounts_well_typed st.accounts /\
    functions_well_typed cx /\
    lookup_global cx src id st = (res,st') ==>
    no_type_error_result res /\
    (case res of
     | INL tvl => eval_result_typed (env,cx,st') tvl vt
     | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_place_expr _ _ = SOME _` mp_tac >>
  simp[well_typed_expr_def, vtype_annotation_ok_def] >>
  Cases_on `vt` >> simp[] >> strip_tac >> gvs[AllCaseEqs()]
  >- (
    rename1 `FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type t)` >>
    Cases_on `FLOOKUP env.bare_globals (src,id)`
    >- (
      `?code is_transient typ id_str.
          get_module_code cx src = SOME code /\
          find_var_decl_by_name id code =
            SOME (StorageVarDecl is_transient typ,id_str) /\
          typ = t /\
          IS_SOME (evaluate_type (get_tenv cx) typ) /\
          IS_SOME (lookup_var_slot_from_layout cx is_transient src id_str)` by
        (drule_all env_consistent_toplevel_storage_static >>
         strip_tac >>
         qexistsl [`ts`, `is_transient`, `t`, `id_str`] >>
         gvs[]) >>
      gvs[IS_SOME_EXISTS] >>
      `env.type_defs = get_tenv cx` by
        gvs[env_consistent_def, env_context_consistent_def] >>
      conj_tac >- metis_tac[lookup_global_StorageVarDecl_no_type_error] >>
      Cases_on `res` >> simp[] >>
      rename1 `lookup_global cx src id st = (INL tvl,st')` >>
      qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
      simp[lookup_global_def, bind_def, lift_option_type_def, return_def, raise_def,
           LET_THM, option_CASE_rator, var_decl_info_CASE_rator, prod_CASE_rator,
           type_value_CASE_rator, AllCaseEqs()] >>
      rpt strip_tac >> gvs[return_def, eval_result_typed_def] >>
      metis_tac[evaluate_type_well_formed_type_value]) >>
    `well_formed_type env.type_defs t` by
      metis_tac[env_consistent_def, env_context_consistent_def,
                well_formed_vtype_def] >>
    `t <> NoneT` by (
      drule_all env_consistent_bare_global_find_NONE >>
      strip_tac >> gvs[]) >>
    `well_typed_expr env (TopLevelName t (src,id))` by
      simp[well_typed_expr_def] >>
    drule_all lookup_global_TopLevelName_sound >> strip_tac >>
    conj_tac >- simp[] >>
    Cases_on `res` >> gvs[]) >>
  rename1 `FLOOKUP env.toplevel_vtypes (src,id) = SOME (HashMapT kt vt)` >>
  `?code is_transient id_str.
      get_module_code cx src = SOME code /\
      find_var_decl_by_name id code =
        SOME (HashMapVarDecl is_transient kt vt,id_str) /\
      IS_SOME (lookup_var_slot_from_layout cx is_transient src id_str)` by
    (drule_all env_consistent_toplevel_hashmap_static >>
     strip_tac >>
     qexistsl [`ts`, `is_transient`, `id_str`] >>
     gvs[]) >>
  gvs[IS_SOME_EXISTS] >>
  drule_all lookup_global_HashMapVarDecl_returns_HashMapRef >>
  strip_tac >> gvs[no_type_error_result_def, eval_result_typed_def]
QED
