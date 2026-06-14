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
  vyperTypeBuiltins vyperTypeExprSoundness vyperTypeAssignSoundness
  vyperAssignTarget vyperExprNoControl vyperScopePreservation vyperEvalPreservesScopes
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
     lift_option_def, raise_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[return_def, raise_def]
QED
Theorem get_immutables_no_type_error:
  !cx src st e st' msg.
    get_immutables cx src st = (INR e, st') ==>
    e <> Error (TypeError msg)
Proof
  rw[get_immutables_def, get_address_immutables_def, bind_def,
     lift_option_def, return_def, raise_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[return_def, raise_def]
QED


Theorem find_var_decl_by_num_NONE_id:
  !n ts. find_var_decl_by_num n ts = NONE ==> find_var_decl_by_num n ts = NONE
Proof
  simp[]
QED
Theorem TopLevelName_nonbare_find_NONE_contradiction:
  !env cx st src n ty ts.
    env_consistent env cx st /\
    FLOOKUP env.toplevel_vtypes (src,n) = SOME (Type ty) /\
    FLOOKUP env.bare_globals (src,n) = NONE /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_num n ts = NONE ==>
    F
Proof
  rpt strip_tac >>
  drule_all env_consistent_toplevel_storage_static >>
  strip_tac >> gvs[]
QED

Theorem TopLevelName_current_bare_global_immutable_exists:
  !env cx st n ty.
    env_consistent env cx st /\
    FLOOKUP env.bare_globals (env.current_src,n) = SOME ty ==>
    IS_SOME (FLOOKUP
      (get_source_immutables env.current_src
        (case ALOOKUP st.immutables cx.txn.target of NONE => [] | SOME m => m)) n)
Proof
  metis_tac[env_consistent_bare_global_ready]
QED

Theorem TopLevelName_missing_immutable_branch_characterisation:
  !env cx st src id ty ts.
    well_typed_expr env (TopLevelName ty (src,id)) /\
    env_consistent env cx st /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_num (string_to_num id) ts = NONE /\
    ~IS_SOME (FLOOKUP
      (get_source_immutables src
        (case ALOOKUP st.immutables cx.txn.target of NONE => [] | SOME m => m))
      (string_to_num id)) ==>
    FLOOKUP env.bare_globals (src,string_to_num id) <> NONE /\ src <> env.current_src
Proof
  rpt gen_tac >> strip_tac >>
  `FLOOKUP env.toplevel_vtypes (src,string_to_num id) = SOME (Type ty)` by
    gvs[well_typed_expr_def] >>
  conj_tac
  >- (Cases_on `FLOOKUP env.bare_globals (src,string_to_num id)` >>
      gvs[] >>
      drule_all TopLevelName_nonbare_find_NONE_contradiction >>
      simp[]) >>
  strip_tac >> gvs[] >>
  Cases_on `FLOOKUP env.bare_globals (env.current_src,string_to_num id)`
  >- (gvs[] >> drule_all TopLevelName_nonbare_find_NONE_contradiction >> simp[]) >>
  gvs[] >>
  drule_all TopLevelName_current_bare_global_immutable_exists >>
  simp[]
QED

Theorem TopLevelName_missing_address_immutables_RuntimeError:
  !cx st src id ty code.
    get_module_code cx src = SOME code /\
    find_var_decl_by_num (string_to_num id) code = NONE /\
    ALOOKUP st.immutables cx.txn.target = NONE ==>
    eval_expr cx (TopLevelName ty (src,id)) st =
      (INR (Error (RuntimeError "get_address_immutables")), st)
Proof
  simp[Once evaluate_def, Once lookup_global_def, bind_def,
       lift_option_type_def, get_immutables_def, get_address_immutables_def,
       lift_option_def, return_def, raise_def]
QED

Theorem TopLevelName_missing_immutable_branch_TypeError:
  !cx st src id ty code imms.
    get_module_code cx src = SOME code /\
    find_var_decl_by_num (string_to_num id) code = NONE /\
    ALOOKUP st.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables src imms) (string_to_num id) = NONE ==>
    ?msg.
      eval_expr cx (TopLevelName ty (src,id)) st =
        (INR (Error (TypeError msg)), st)
Proof
  rpt strip_tac >>
  qexists_tac `"lookup_global: var not found"` >>
  simp[Once evaluate_def, Once lookup_global_def, bind_def,
       lift_option_type_def, get_immutables_def, get_address_immutables_def,
       lift_option_def, return_def, raise_def]
QED

Theorem TopLevelName_missing_address_immutables_characterisation:
  !env cx st src id ty code.
    well_typed_expr env (TopLevelName ty (src,id)) /\
    env_consistent env cx st /\
    functions_well_typed cx /\
    get_module_code cx src = SOME code /\
    find_var_decl_by_num (string_to_num id) code = NONE /\
    ALOOKUP st.immutables cx.txn.target = NONE ==>
    FLOOKUP env.bare_globals (src,string_to_num id) <> NONE /\
    src <> env.current_src
Proof
  rpt strip_tac >>
  `~IS_SOME (FLOOKUP
      (get_source_immutables src
        (case ALOOKUP st.immutables cx.txn.target of NONE => [] | SOME m => m))
      (string_to_num id))` by simp[get_source_immutables_def] >>
  drule_all TopLevelName_missing_immutable_branch_characterisation >>
  simp[]
QED

Theorem TopLevelName_missing_source_immutable_characterisation:
  !env cx st src id ty code imms.
    well_typed_expr env (TopLevelName ty (src,id)) /\
    env_consistent env cx st /\
    functions_well_typed cx /\
    get_module_code cx src = SOME code /\
    find_var_decl_by_num (string_to_num id) code = NONE /\
    ALOOKUP st.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables src imms) (string_to_num id) = NONE ==>
    FLOOKUP env.bare_globals (src,string_to_num id) <> NONE /\
    src <> env.current_src
Proof
  rpt gen_tac >> strip_tac >>
  `~IS_SOME (FLOOKUP
      (get_source_immutables src
        (case ALOOKUP st.immutables cx.txn.target of NONE => [] | SOME m => m))
      (string_to_num id))` by simp[] >>
  drule_all TopLevelName_missing_immutable_branch_characterisation >>
  simp[]
QED

Theorem TopLevelName_missing_immutable_impossible:
  !env cx st src id ty code.
    well_typed_expr env (TopLevelName ty (src,id)) /\
    env_consistent env cx st /\
    functions_well_typed cx /\
    get_module_code cx src = SOME code /\
    find_var_decl_by_num (string_to_num id) code = NONE /\
    ~IS_SOME (FLOOKUP
      (get_source_immutables src
        (case ALOOKUP st.immutables cx.txn.target of NONE => [] | SOME m => m))
      (string_to_num id)) ==>
    F
Proof
  rpt gen_tac >> strip_tac >>
  drule_all TopLevelName_missing_immutable_branch_characterisation >>
  strip_tac >>
  Cases_on `FLOOKUP env.bare_globals (src,string_to_num id)` >> gvs[] >>
  drule_all env_consistent_bare_global_ready_src >>
  simp[]
QED

Theorem lookup_global_TopLevelName_find_NONE_no_type_error:
  !env cx st src id ty code res st'.
    well_typed_expr env (TopLevelName ty (src,id)) /\
    env_consistent env cx st /\
    functions_well_typed cx /\
    get_module_code cx src = SOME code /\
    find_var_decl_by_num (string_to_num id) code = NONE /\
    lookup_global cx src (string_to_num id) st = (res,st') ==>
    no_type_error_result res
Proof
  rpt strip_tac >>
  qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
  simp[lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def] >>
  Cases_on `get_immutables cx src st` >> Cases_on `q`
  >- (simp[bind_def, return_def, raise_def] >>
      Cases_on `FLOOKUP x (string_to_num id)`
      >- (strip_tac >> gvs[] >>
          drule get_immutables_success >> strip_tac >> gvs[] >>
          `F` by (
            qspecl_then [`env`, `cx`, `r`, `src`, `id`, `ty`, `code`] mp_tac
              TopLevelName_missing_immutable_impossible >>
            simp[]) >>
          simp[]) >>
      strip_tac >> gvs[return_def, no_type_error_result_def]) >>
  simp[bind_def, return_def, raise_def] >>
  strip_tac >> gvs[no_type_error_result_def] >>
  metis_tac[get_immutables_no_type_error]
QED
Theorem lookup_global_TopLevelName_find_NONE_success_typed:
  !env cx st src id ty code tvl st'.
    well_typed_expr env (TopLevelName ty (src,id)) /\
    env_consistent env cx st /\
    state_well_typed st /\
    functions_well_typed cx /\
    get_module_code cx src = SOME code /\
    find_var_decl_by_num (string_to_num id) code = NONE /\
    lookup_global cx src (string_to_num id) st = (INL tvl,st') ==>
    expr_result_typed env (TopLevelName ty (src,id)) tvl
Proof
  rpt strip_tac >>
  `FLOOKUP env.toplevel_vtypes (src,string_to_num id) = SOME (Type ty)` by
    gvs[well_typed_expr_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
  simp[lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def] >>
  Cases_on `get_immutables cx src st` >> Cases_on `q`
  >- (simp[bind_def, return_def, raise_def] >>
      Cases_on `FLOOKUP x (string_to_num id)`
      >- (strip_tac >> gvs[] >>
          drule get_immutables_success >> strip_tac >> gvs[] >>
          `F` by (
            qspecl_then [`env`, `cx`, `r`, `src`, `id`, `ty`, `code`] mp_tac
              TopLevelName_missing_immutable_impossible >>
            simp[]) >>
          simp[]) >>
      strip_tac >> gvs[return_def] >>
      PairCases_on `x'` >> rename1 `SOME (imm_tv,imm_v)` >> gvs[] >>
      simp[expr_result_typed_def, expr_runtime_typed_def, expr_type_def,
           toplevel_value_typed_Value] >>
      qexists_tac `imm_tv` >> simp[] >>
      conj_tac >- (
        drule get_immutables_success >> strip_tac >> gvs[] >>
        qpat_x_assum `env_consistent env cx r` mp_tac >>
        simp[env_consistent_def, env_immutables_consistent_def] >>
        strip_tac >>
        qpat_x_assum `!src' id ty' ts. _`
          (qspecl_then [`src`, `string_to_num id`, `ty`, `code`] mp_tac) >>
        simp[] >> strip_tac >>
        first_x_assum (qspecl_then [`imm_tv`, `imm_v`] mp_tac) >>
        simp[]) >>
      drule get_immutables_success >> strip_tac >> gvs[] >>
      `imms_well_typed
         (case ALOOKUP r.immutables cx.txn.target of NONE => [] | SOME m => m)` by
        (irule current_immutables_well_typed >> simp[]) >>
      drule_all imms_well_typed_get_source_immutables >>
      simp[]) >>
  simp[bind_def, return_def, raise_def]
QED

Theorem TopLevelName_nonbare_storage_decl_context:
  !env cx st src id ty code is_transient typ id_str.
    well_typed_expr env (TopLevelName ty (src,id)) /\
    env_consistent env cx st /\
    FLOOKUP env.bare_globals (src,string_to_num id) = NONE /\
    get_module_code cx src = SOME code /\
    find_var_decl_by_num (string_to_num id) code =
      SOME (StorageVarDecl is_transient typ,id_str) ==>
    typ = ty /\
    IS_SOME (evaluate_type (get_tenv cx) typ) /\
    IS_SOME (lookup_var_slot_from_layout cx is_transient src id_str)
Proof
  rpt strip_tac >>
  `FLOOKUP env.toplevel_vtypes (src,string_to_num id) = SOME (Type ty)` by
    gvs[well_typed_expr_def] >>
  drule_all env_consistent_toplevel_storage_static >>
  strip_tac >> gvs[]
QED

Theorem TopLevelName_storage_decl_type_eq:
  !env cx st src id ty code is_transient typ id_str.
    well_typed_expr env (TopLevelName ty (src,id)) /\
    env_consistent env cx st /\
    get_module_code cx src = SOME code /\
    find_var_decl_by_num (string_to_num id) code =
      SOME (StorageVarDecl is_transient typ,id_str) ==>
    typ = ty
Proof
  rpt strip_tac >>
  `FLOOKUP env.toplevel_vtypes (src,string_to_num id) = SOME (Type ty)` by
    gvs[well_typed_expr_def] >>
  gvs[env_consistent_def, env_immutables_consistent_def] >>
  qpat_x_assum `!src id ty ts. _`
    (qspecl_then [`src`, `string_to_num id`, `ty`, `code`] mp_tac) >>
  simp[] >> strip_tac >>
  first_x_assum (qspecl_then [`is_transient`, `typ`, `id_str`] mp_tac) >>
  simp[]
QED
Theorem lookup_global_StorageVarDecl_no_type_error:
  !cx src n st res st' code is_transient typ id_str slot tv.
    get_module_code cx src = SOME code /\
    find_var_decl_by_num n code = SOME (StorageVarDecl is_transient typ,id_str) /\
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
    find_var_decl_by_num (string_to_num id) code =
      SOME (StorageVarDecl is_transient typ,id_str) /\
    lookup_global cx src (string_to_num id) st = (INL tvl,st') ==>
    expr_result_typed env (TopLevelName ty (src,id)) tvl
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
  Cases_on `tv` >> simp[return_def] >>
  rpt strip_tac >> gvs[expr_result_typed_def, expr_runtime_typed_def, expr_type_def,
                       toplevel_value_typed_def]
  >- (`well_formed_type_value (BaseTV b)` by metis_tac[evaluate_type_well_formed_type_value] >>
      drule_all read_storage_slot_success_type >> simp[])
  >- (`well_formed_type_value (TupleTV l)` by metis_tac[evaluate_type_well_formed_type_value] >>
      drule_all read_storage_slot_success_type >> simp[])
  >- (`well_formed_type_value (StructTV l)` by metis_tac[evaluate_type_well_formed_type_value] >>
      drule_all read_storage_slot_success_type >> simp[])
  >- (`well_formed_type_value (FlagTV n)` by metis_tac[evaluate_type_well_formed_type_value] >>
      drule_all read_storage_slot_success_type >> simp[]) >>
  `well_formed_type_value NoneTV` by metis_tac[evaluate_type_well_formed_type_value] >>
  drule_all read_storage_slot_success_type >> strip_tac >>
  gvs[value_has_type_NoneTV]
QED

Theorem TopLevelName_Type_HashMapVarDecl_impossible:
  !env cx st src id ty code is_transient kt vt id_str.
    well_typed_expr env (TopLevelName ty (src,id)) /\
    env_consistent env cx st /\
    state_well_typed st /\
    context_well_typed cx /\
    accounts_well_typed st.accounts /\
    get_module_code cx src = SOME code /\
    find_var_decl_by_num (string_to_num id) code =
      SOME (HashMapVarDecl is_transient kt vt,id_str) ==>
    F
Proof
  rpt strip_tac >>
  `FLOOKUP env.toplevel_vtypes (src,string_to_num id) = SOME (Type ty)` by
    gvs[well_typed_expr_def] >>
  `runtime_consistent env cx st` by simp[runtime_consistent_def] >>
  metis_tac[top_level_Type_not_hashmap_decl]
QED

Theorem duplicate_storage_and_immutable_scanners_probe:
  !id typ imm_typ.
    find_var_decl_by_num (string_to_num id)
      [VariableDecl Private Storage id typ NONE;
       VariableDecl Private Immutable id imm_typ NONE] =
      SOME (StorageVarDecl F typ,id) /\
    is_immutable_decl (string_to_num id)
      [VariableDecl Private Storage id typ NONE;
       VariableDecl Private Immutable id imm_typ NONE]
Proof
  simp[find_var_decl_by_num_def, is_immutable_decl_def]
QED

Theorem TopLevelName_bare_storage_decl_eval_type_probe:
  !env cx st src id ty code is_transient typ id_str bare.
    well_typed_expr env (TopLevelName ty (src,id)) /\
    env_consistent env cx st /\
    get_module_code cx src = SOME code /\
    find_var_decl_by_num (string_to_num id) code =
      SOME (StorageVarDecl is_transient typ,id_str) /\
    FLOOKUP env.bare_globals (src,string_to_num id) = SOME bare ==>
    ?tv. evaluate_type (get_tenv cx) typ = SOME tv
Proof
  rpt strip_tac >>
  `typ = ty` by metis_tac[TopLevelName_storage_decl_type_eq] >> gvs[] >>
  `FLOOKUP env.toplevel_vtypes (src,string_to_num id) = SOME (Type ty)` by
    gvs[well_typed_expr_def] >>
  gvs[env_consistent_def, env_context_consistent_def,
      env_immutables_consistent_def, IS_SOME_EXISTS] >>
  qpat_x_assum `!src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty ==> ?ts. _`
    (qspecl_then [`src`, `string_to_num id`, `bare`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  `bare = ty` by metis_tac[] >> gvs[] >>
  qpat_x_assum `!src' id ty'. FLOOKUP env.bare_globals (src',id) = SOME ty' ==> ?x. _`
    (qspecl_then [`src`, `string_to_num id`, `ty`] mp_tac) >>
  simp[] >> strip_tac >>
  PairCases_on `x` >>
  qexists `x0` >>
  qpat_x_assum `!src id ty tv v. _`
    (qspecl_then [`src`, `string_to_num id`, `bare`, `x0`, `x1`] mp_tac) >>
  simp[]
QED

Theorem TopLevelName_bare_storage_decl_impossible:
  !env cx st src id ty code is_transient typ id_str bare.
    well_typed_expr env (TopLevelName ty (src,id)) /\
    env_consistent env cx st /\
    get_module_code cx src = SOME code /\
    find_var_decl_by_num (string_to_num id) code =
      SOME (StorageVarDecl is_transient typ,id_str) /\
    FLOOKUP env.bare_globals (src,string_to_num id) = SOME bare ==>
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
    lookup_global cx src (string_to_num id) st = (res,st') ==>
    no_type_error_result res
Proof
  rpt strip_tac >>
  `FLOOKUP env.toplevel_vtypes (src,string_to_num id) = SOME (Type ty)` by
    gvs[well_typed_expr_def] >>
  `?code. get_module_code cx src = SOME code` by (
    Cases_on `FLOOKUP env.bare_globals (src,string_to_num id)` >>
    metis_tac[env_consistent_toplevel_storage_static, env_consistent_def,
              env_context_consistent_def]) >>
  Cases_on `find_var_decl_by_num (string_to_num id) code`
  >- metis_tac[lookup_global_TopLevelName_find_NONE_no_type_error] >>
  PairCases_on `x` >> Cases_on `x0` >> gvs[]
  >- (Cases_on `FLOOKUP env.bare_globals (src,string_to_num id)`
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
    lookup_global cx src (string_to_num id) st = (INL tvl,st') ==>
    expr_result_typed env (TopLevelName ty (src,id)) tvl
Proof
  rpt strip_tac >>
  `FLOOKUP env.toplevel_vtypes (src,string_to_num id) = SOME (Type ty)` by
    gvs[well_typed_expr_def] >>
  `?code. get_module_code cx src = SOME code` by (
    Cases_on `FLOOKUP env.bare_globals (src,string_to_num id)` >>
    metis_tac[env_consistent_toplevel_storage_static, env_consistent_def,
              env_context_consistent_def]) >>
  Cases_on `find_var_decl_by_num (string_to_num id) code`
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
    lookup_global cx src (string_to_num id) st = (res,st') ==>
    no_type_error_result res /\
    (case res of
     | INL tvl => expr_result_typed env (TopLevelName ty (src,id)) tvl
     | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac >- metis_tac[lookup_global_TopLevelName_no_type_error] >>
  Cases_on `res` >> simp[] >>
  metis_tac[lookup_global_TopLevelName_success_typed]
QED

Theorem expr_result_typed_TopLevelName_Type_place:
  expr_result_typed env (TopLevelName ty (src,id)) tvl /\
  type_place_expr env (TopLevelName ty (src,id)) = SOME (Type ty) ==>
  place_expr_result_typed env tvl (Type ty)
Proof
  rw[expr_result_typed_def, expr_runtime_typed_def,
     place_expr_result_typed_def, expr_type_def] >>
  qexists_tac `tv` >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem lookup_global_TopLevelName_place_sound:
  !env cx st src id ann vt res st'.
    type_place_expr env (TopLevelName ann (src,id)) = SOME vt /\
    env_consistent env cx st /\
    state_well_typed st /\
    context_well_typed cx /\
    accounts_well_typed st.accounts /\
    functions_well_typed cx /\
    lookup_global cx src (string_to_num id) st = (res,st') ==>
    no_type_error_result res /\
    (case res of
     | INL tvl => place_expr_result_typed env tvl vt
     | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_place_expr _ _ = SOME _` mp_tac >>
  simp[well_typed_expr_def, vtype_annotation_ok_def] >>
  Cases_on `vt` >> simp[] >> strip_tac >> gvs[AllCaseEqs()]
  >- (
    rename1 `FLOOKUP env.toplevel_vtypes (src,string_to_num id) = SOME (Type t)` >>
    Cases_on `FLOOKUP env.bare_globals (src,string_to_num id)`
    >- (
      `?code is_transient typ id_str.
          get_module_code cx src = SOME code /\
          find_var_decl_by_num (string_to_num id) code =
            SOME (StorageVarDecl is_transient typ,id_str) /\
          typ = t /\
          IS_SOME (evaluate_type (get_tenv cx) typ) /\
          IS_SOME (lookup_var_slot_from_layout cx is_transient src id_str)` by
        metis_tac[env_consistent_toplevel_storage_static] >>
      gvs[IS_SOME_EXISTS] >>
      `env.type_defs = get_tenv cx` by
        gvs[env_consistent_def, env_context_consistent_def] >>
      conj_tac >- metis_tac[lookup_global_StorageVarDecl_no_type_error] >>
      Cases_on `res` >> simp[] >>
      rename1 `lookup_global cx src (string_to_num id) st = (INL tvl,st')` >>
      qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
      simp[lookup_global_def, bind_def, lift_option_type_def, return_def, raise_def,
           LET_THM, option_CASE_rator, var_decl_info_CASE_rator, prod_CASE_rator,
           type_value_CASE_rator, AllCaseEqs()] >>
      Cases_on `x` >> simp[return_def] >>
      rpt strip_tac >> gvs[place_expr_result_typed_def, toplevel_value_typed_def,
                           is_HashMapRef_def]
      >- (`well_formed_type_value (BaseTV b)` by metis_tac[evaluate_type_well_formed_type_value] >>
          drule_all read_storage_slot_success_type >> simp[])
      >- (`well_formed_type_value (TupleTV l)` by metis_tac[evaluate_type_well_formed_type_value] >>
          drule_all read_storage_slot_success_type >> simp[])
      >- (`well_formed_type_value (StructTV l)` by metis_tac[evaluate_type_well_formed_type_value] >>
          drule_all read_storage_slot_success_type >> simp[])
      >- (`well_formed_type_value (FlagTV n)` by metis_tac[evaluate_type_well_formed_type_value] >>
          drule_all read_storage_slot_success_type >> simp[]) >>
      `well_formed_type_value NoneTV` by metis_tac[evaluate_type_well_formed_type_value] >>
      drule_all read_storage_slot_success_type >> simp[]) >>
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
    Cases_on `res` >>
    gvs[place_expr_result_typed_def, expr_result_typed_def,
        expr_runtime_typed_def, expr_type_def] >>
    strip_tac >> gvs[well_typed_expr_def, vtype_annotation_ok_def]) >>
  rename1 `FLOOKUP env.toplevel_vtypes (src,string_to_num id) = SOME (HashMapT kt vt)` >>
  `?code is_transient id_str.
      get_module_code cx src = SOME code /\
      find_var_decl_by_num (string_to_num id) code =
        SOME (HashMapVarDecl is_transient kt vt,id_str) /\
      IS_SOME (lookup_var_slot_from_layout cx is_transient src id_str)` by
    metis_tac[env_consistent_toplevel_hashmap_static] >>
  gvs[IS_SOME_EXISTS] >>
  drule_all lookup_global_HashMapVarDecl_returns_HashMapRef >>
  strip_tac >> gvs[no_type_error_result_def, place_expr_result_typed_def]
QED

