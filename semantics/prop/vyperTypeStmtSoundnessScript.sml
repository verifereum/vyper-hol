(*
 * Statement and statement-list type soundness skeleton for the fresh executable
 * Vyper type system.
 *)

Theory vyperTypeStmtSoundness
Ancestors
  list rich_list pred_set prim_rec arithmetic finite_map option pair sum
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperInterpreter vyperState vyperContext vyperStorage vyperTyping
  vyperEncodeDecode vyperArith vyperTypeSystem vyperTypeValues
  vyperTypeEnv vyperTypeEnvExtension vyperTypeEnvPreservation vyperTypeScopePop
  vyperTypeBuiltins vyperTypeExprSoundness vyperTypeAssignSoundness
  vyperAssignTarget vyperExprNoControl vyperScopePreservation vyperEvalPreservesScopes
  vyperEvalMisc vyperStatePreservation vyperAssignPreservesType vyperTypeStatePreservation
Libs
  wordsLib markerLib intLib

(* ===== Exception/result typing ===== *)

Definition return_exception_typed_def:
  return_exception_typed env ret_ty exn <=>
    case exn of
    | ReturnException v => value_runtime_typed env ret_ty v
    | _ => T
End

Definition stmt_error_ok_def:
  stmt_error_ok env ret_ty r <=>
    no_type_error_result r /\
    (case r of INR exn => return_exception_typed env ret_ty exn | _ => T)
End

Theorem return_exception_typed_INR_case:
  return_exception_typed env ret_ty y ==>
  (case INR y of INL v => T | INR exn => return_exception_typed env ret_ty exn)
Proof
  Cases_on `y` >> simp[return_exception_typed_def]
QED

Theorem return_exception_typed_INR_case_eq:
  (case INR y of INL v => T | INR exn => return_exception_typed env ret_ty exn) =
  return_exception_typed env ret_ty y
Proof
  Cases_on `y` >> simp[return_exception_typed_def]
QED

Theorem return_exception_typed_INR_unit_case_elim:
  (case (INR exn : unit + vyperState$exception) of
   | INL _ => T
   | INR exn0 => return_exception_typed env ret_ty exn0) ==>
  return_exception_typed env ret_ty exn
Proof
  Cases_on `exn` >> simp[return_exception_typed_def]
QED

Theorem return_exception_typed_ReturnException_case:
  return_exception_typed env ret_ty (ReturnException rv) ==>
  (case ReturnException rv of
   | ReturnException v => value_runtime_typed env ret_ty v
   | _ => T)
Proof
  simp[return_exception_typed_def]
QED

Theorem return_exception_typed_ReturnException_value:
  return_exception_typed env ret_ty (ReturnException rv) ==>
  value_runtime_typed env ret_ty rv
Proof
  simp[return_exception_typed_def]
QED

Theorem no_type_error_result_INR_not_type_error:
  no_type_error_result (INR y) ==> y <> Error (TypeError msg)
Proof
  simp[no_type_error_result_def]
QED

Theorem no_control_exc_return_exception_typed:
  no_control_exc exn ==> return_exception_typed env ret_ty exn
Proof
  Cases_on `exn` >> rw[no_control_exc_def, return_exception_typed_def]
QED

Definition expr_result_typed_def:
  expr_result_typed env e tv <=>
    expr_runtime_typed env e tv /\
    (is_HashMapRef tv ==> ?kt vt. type_place_expr env e = SOME (HashMapT kt vt))
End

Definition place_expr_result_typed_def:
  place_expr_result_typed env tv vt <=>
    case vt of
    | Type ty => ?tyv. evaluate_type env.type_defs ty = SOME tyv /\
                         toplevel_value_typed tv tyv /\ ~is_HashMapRef tv
    | HashMapT kt vt' => ?is_t slot. tv = HashMapRef is_t slot kt vt'
End

Theorem well_typed_expr_not_hashmap_place:
  !e env kt vt.
    well_typed_expr env e ==>
    type_place_expr env e <> SOME (HashMapT kt vt)
Proof
  Induct >>
  rw[well_typed_expr_def, vtype_annotation_ok_def] >>
  gvs[well_typed_expr_def, vtype_annotation_ok_def, AllCaseEqs()] >>
  TRY (PairCases_on `p` >>
       gvs[well_typed_expr_def, vtype_annotation_ok_def, AllCaseEqs()] >>
       NO_TAC) >>
  TRY (Cases_on `expr_type e` >> gvs[subscript_type_ok_def] >>
       Cases_on `vt'` >> gvs[subscript_vtype_def] >>
       Cases_on `t'` >> gvs[subscript_vtype_def] >>
       NO_TAC) >>
  metis_tac[]
QED

Theorem expr_result_typed_materialise_no_type_error:
  well_typed_expr env e /\
  expr_result_typed env e tv /\
  materialise cx tv st = (INR err, st') ==>
  !msg. err <> Error (TypeError msg)
Proof
  rw[] >>
  spose_not_then assume_tac >>
  gvs[] >>
  drule_then assume_tac materialise_type_error_imp_HashMapRef >>
  gvs[expr_result_typed_def] >>
  metis_tac[well_typed_expr_not_hashmap_place]
QED

Theorem lookup_scopes_val_SOME[local]:
  !id sc v.
    lookup_scopes_val id sc = SOME v <=>
    ?entry. lookup_scopes id sc = SOME entry /\ entry.value = v
Proof
  Induct_on `sc` >> simp[lookup_scopes_val_def, lookup_scopes_def] >>
  rpt gen_tac >> Cases_on `FLOOKUP h id` >> simp[]
QED

Theorem get_immutables_success[local]:
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
Theorem get_immutables_no_type_error[local]:
  !cx src st e st' msg.
    get_immutables cx src st = (INR e, st') ==>
    e <> Error (TypeError msg)
Proof
  rw[get_immutables_def, get_address_immutables_def, bind_def,
     lift_option_def, return_def, raise_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[return_def, raise_def]
QED


Theorem find_var_decl_by_num_NONE_id[local]:
  !n ts. find_var_decl_by_num n ts = NONE ==> find_var_decl_by_num n ts = NONE
Proof
  simp[]
QED
Theorem TopLevelName_nonbare_find_NONE_contradiction[local]:
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

Theorem TopLevelName_current_bare_global_immutable_exists[local]:
  !env cx st n ty.
    env_consistent env cx st /\
    FLOOKUP env.bare_globals (env.current_src,n) = SOME ty ==>
    IS_SOME (FLOOKUP
      (get_source_immutables env.current_src
        (case ALOOKUP st.immutables cx.txn.target of NONE => [] | SOME m => m)) n)
Proof
  metis_tac[env_consistent_bare_global_ready]
QED

Theorem TopLevelName_missing_immutable_branch_characterisation[local]:
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

Theorem TopLevelName_missing_address_immutables_RuntimeError[local]:
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

Theorem TopLevelName_missing_immutable_branch_TypeError[local]:
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

Theorem TopLevelName_missing_address_immutables_characterisation[local]:
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

Theorem TopLevelName_missing_source_immutable_characterisation[local]:
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

Theorem TopLevelName_missing_immutable_impossible[local]:
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

Theorem lookup_global_TopLevelName_find_NONE_no_type_error[local]:
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
Theorem lookup_global_TopLevelName_find_NONE_success_typed[local]:
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

Theorem TopLevelName_nonbare_storage_decl_context[local]:
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

Theorem TopLevelName_storage_decl_type_eq[local]:
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
Theorem lookup_global_StorageVarDecl_no_type_error[local]:
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

Theorem lookup_global_TopLevelName_storage_success_typed[local]:
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

Theorem TopLevelName_Type_HashMapVarDecl_impossible[local]:
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

Theorem duplicate_storage_and_immutable_scanners_probe[local]:
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

Theorem TopLevelName_bare_storage_decl_eval_type_probe[local]:
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

Theorem TopLevelName_bare_storage_decl_impossible[local]:
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


Theorem lookup_global_TopLevelName_no_type_error[local]:
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

Theorem lookup_global_TopLevelName_success_typed[local]:
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

Theorem lookup_global_TopLevelName_sound[local]:
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

Theorem expr_result_typed_TopLevelName_Type_place[local]:
  expr_result_typed env (TopLevelName ty (src,id)) tvl /\
  type_place_expr env (TopLevelName ty (src,id)) = SOME (Type ty) ==>
  place_expr_result_typed env tvl (Type ty)
Proof
  rw[expr_result_typed_def, expr_runtime_typed_def,
     place_expr_result_typed_def, expr_type_def] >>
  qexists_tac `tv` >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem lookup_global_TopLevelName_place_sound[local]:
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

Theorem eval_expr_exception_return_typed:
  eval_expr cx e st = (INR exn, st') ==> return_exception_typed env ret_ty exn
Proof
  strip_tac >>
  drule (cj 1 eval_expr_no_control) >>
  rw[no_control_exc_return_exception_typed]
QED

Theorem eval_exprs_exception_return_typed:
  eval_exprs cx es st = (INR exn, st') ==> return_exception_typed env ret_ty exn
Proof
  strip_tac >>
  drule (cj 2 eval_expr_no_control) >>
  rw[no_control_exc_return_exception_typed]
QED

Theorem eval_target_no_control:
  (!tgt cx st exn st'.
    eval_target cx tgt st = (INR exn, st') ==> no_control_exc exn) /\
  (!tgts cx st exn st'.
    eval_targets cx tgts st = (INR exn, st') ==> no_control_exc exn) /\
  (!cx bt st exn st'.
    eval_base_target cx bt st = (INR exn, st') ==> no_control_exc exn)
Proof
  rewrite_tac[CONJ_ASSOC] >>
  reverse conj_asm2_tac >- (
    rpt strip_tac >>
    drule_then irule (cj 1 eval_expr_no_control_with_bt)  ) >>
  ho_match_mp_tac (TypeBase.induction_of``:assignment_target``) >>
  simp[evaluate_def, bind_apply, ignore_bind_apply, AllCaseEqs(),
       EXISTS_PROD, bind_def] >>
  rpt strip_tac >> gvs[return_def] >>
  metis_tac[]
QED

Theorem eval_iterator_no_control:
  !cx it st exn st'.
    eval_iterator cx it st = (INR exn, st') ==> no_control_exc exn
Proof
  Cases_on `it` >>
  rw[evaluate_def, bind_def, return_def, raise_def, lift_option_type_def,
     lift_sum_def, option_CASE_rator, sum_CASE_rator, AllCaseEqs()] >>
  TRY (drule (cj 1 eval_expr_no_control) >> simp[] >> NO_TAC) >>
  TRY (drule materialise_no_control >> simp[] >> NO_TAC) >>
  TRY (drule get_Value_no_control >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs(), option_CASE_rator, sum_CASE_rator,
      return_def, raise_def, no_control_exc_def]
QED


Theorem value_runtime_typed_env_static:
  env'.type_defs = env.type_defs /\ value_runtime_typed env' ty v ==>
  value_runtime_typed env ty v
Proof
  rw[value_runtime_typed_def] >> metis_tac[]
QED

Theorem return_exception_typed_env_static:
  env'.type_defs = env.type_defs /\ return_exception_typed env' ret_ty exn ==>
  return_exception_typed env ret_ty exn
Proof
  Cases_on `exn` >> rw[return_exception_typed_def] >>
  metis_tac[value_runtime_typed_env_static]
QED

Theorem materialise_preserves_value_type:
  state_well_typed st /\ toplevel_value_typed tvl tv /\ well_formed_type_value tv /\
  materialise cx tvl st = (INL v, st') ==>
  value_has_type tv v
Proof
  metis_tac[materialise_preserves_type]
QED

Theorem expr_result_typed_materialise_preserves_value_type:
  state_well_typed st /\ expr_result_typed env e tvl /\
  evaluate_type env.type_defs (expr_type e) = SOME tyv /\
  materialise cx tvl st = (INL v, st') ==>
  value_has_type tyv v
Proof
  rw[expr_result_typed_def, expr_runtime_typed_def] >> gvs[] >>
  irule materialise_preserves_value_type >> simp[] >>
  metis_tac[evaluate_type_well_formed_type_value]
QED
Theorem annassign_new_variable_after_materialise_sound[local]:
  env_consistent env cx st /\ state_well_typed st /\ accounts_well_typed st.accounts /\
  get_tenv cx = env.type_defs /\ evaluate_type env.type_defs typ = SOME tyv /\
  expr_type e = typ /\ expr_result_typed env e tvl /\
  string_to_num id NOTIN FDOM env.var_types /\
  materialise cx tvl st = (INL v, st1) /\
  new_variable id tyv v st1 = (res, st') ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts /\ no_type_error_result res /\
  case res of
  | INL u => env_consistent (extend_local env (string_to_num id) typ T) cx st'
  | INR exn => env_consistent env cx st' /\ return_exception_typed env ret_ty exn
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule materialise_state >> strip_tac >> gvs[] >>
  `value_has_type tyv v` by
    metis_tac[expr_result_typed_materialise_preserves_value_type] >>
  conj_tac
  >- metis_tac[new_variable_preserves_state_well_typed_result] >>
  conj_tac >- (drule new_variable_accounts >> rw[]) >>
  Cases_on `res` >> gvs[no_type_error_result_def]
  >- metis_tac[extend_local_env_consistent_after_new_variable] >>
  conj_asm1_tac
  >- (rpt strip_tac >> gvs[] >>
      drule_at(Pat`new_variable`) new_variable_no_type_error >>
      simp[] >> goal_assum drule_all) >>
  gvs[new_variable_def, bind_apply, AllCaseEqs(),
      ignore_bind_apply, list_CASE_rator, raise_def,
      get_scopes_def, return_def, type_check_def,
      assert_def, set_scopes_def]
QED
Theorem annassign_eval_success_new_variable_eq[local]:
  evaluate_type env.type_defs typ = SOME tyv /\
  eval_expr cx e st = (INL tvl, st1) /\
  materialise cx tvl st1 = (INL v, st2) /\
  (let tenv = env.type_defs in
     do
       tyv <- lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type";
       tv <- eval_expr cx e;
       v <- materialise cx tv;
       new_variable id tyv v
     od) st = (res, st') ==>
  new_variable id tyv v st2 = (res, st')
Proof
  rw[bind_def, raise_def, lift_option_type_def, pairTheory.UNCURRY] >>
  qpat_x_assum `(case return tyv st of _ => _) = _` mp_tac >>
  simp[return_def] >> gvs[]
QED

Theorem annassign_eval_materialise_error_eq[local]:
  evaluate_type env.type_defs typ = SOME tyv /\
  eval_expr cx e st = (INL tvl, st1) /\
  materialise cx tvl st1 = (INR exn, st2) /\
  (let tenv = env.type_defs in
     do
       tyv <- lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type";
       tv <- eval_expr cx e;
       v <- materialise cx tv;
       new_variable id tyv v
     od) st = (res, st') ==>
  res = INR exn /\ st' = st2
Proof
  rw[bind_def, raise_def, lift_option_type_def, pairTheory.UNCURRY] >>
  qpat_x_assum `(case return tyv st of _ => _) = _` mp_tac >>
  simp[return_def] >> gvs[]
QED
Theorem annassign_eval_stmt_success_new_variable[local]:
  get_tenv cx = env.type_defs /\ evaluate_type env.type_defs typ = SOME tyv /\
  eval_expr cx e st = (INL tvl, st1) /\
  materialise cx tvl st1 = (INL v, st2) /\
  eval_stmt cx (AnnAssign id typ e) st = (res, st') ==>
  new_variable id tyv v st2 = (res, st')
Proof
  rw[Once evaluate_def, bind_def, raise_def,
     lift_option_type_def, pairTheory.UNCURRY] >>
  qpat_x_assum `(case return tyv st of _ => _) = _` mp_tac >>
  simp[return_def] >> gvs[]
QED

Theorem annassign_eval_stmt_materialise_error[local]:
  get_tenv cx = env.type_defs /\ evaluate_type env.type_defs typ = SOME tyv /\
  eval_expr cx e st = (INL tvl, st1) /\
  materialise cx tvl st1 = (INR exn, st2) /\
  eval_stmt cx (AnnAssign id typ e) st = (res, st') ==>
  res = INR exn /\ st' = st2
Proof
  rw[Once evaluate_def, bind_def, raise_def,
     lift_option_type_def, pairTheory.UNCURRY] >>
  qpat_x_assum `(case return tyv st of _ => _) = _` mp_tac >>
  simp[return_def] >> gvs[]
QED

Theorem annassign_eval_stmt_success_sound[local]:
  env_consistent env cx st1 /\ state_well_typed st1 /\ accounts_well_typed st1.accounts /\
  get_tenv cx = env.type_defs /\ evaluate_type env.type_defs typ = SOME tyv /\
  expr_type e = typ /\ expr_result_typed env e tvl /\
  string_to_num id NOTIN FDOM env.var_types /\
  eval_expr cx e st = (INL tvl, st1) /\
  materialise cx tvl st1 = (INL v, st2) /\
  eval_stmt cx (AnnAssign id typ e) st = (res, st') ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts /\ no_type_error_result res /\
  case res of
  | INL u => env_consistent (extend_local env (string_to_num id) typ T) cx st'
  | INR exn => env_consistent env cx st' /\ return_exception_typed env ret_ty exn
Proof
  rpt gen_tac >> strip_tac >>
  `new_variable id tyv v st2 = (res,st')` by
    metis_tac[annassign_eval_stmt_success_new_variable] >>
  metis_tac[annassign_new_variable_after_materialise_sound]
QED

Theorem annassign_eval_stmt_materialise_error_sound[local]:
  get_tenv cx = env.type_defs /\ evaluate_type env.type_defs typ = SOME tyv /\
  well_typed_expr env e /\ expr_result_typed env e tvl /\
  eval_expr cx e st = (INL tvl, st1) /\
  materialise cx tvl st1 = (INR exn, st2) /\
  eval_stmt cx (AnnAssign id typ e) st = (res, st') ==>
  res = INR exn /\ st' = st2 /\ no_type_error_result res /\
  return_exception_typed env ret_ty exn
Proof
  rpt gen_tac >> strip_tac >>
  `res = INR exn /\ st' = st2` by
    metis_tac[annassign_eval_stmt_materialise_error] >>
  gvs[no_type_error_result_def] >>
  `!msg. exn <> Error (TypeError msg)` by
    metis_tac[expr_result_typed_materialise_no_type_error] >>
  drule materialise_no_control >>
  rw[no_control_exc_return_exception_typed]
QED

Theorem annassign_statement_sound_from_expr_ih[local]:
  (!env st res st'.
     env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
     accounts_well_typed st.accounts /\ functions_well_typed cx /\
     eval_expr cx e st = (res, st') ==>
     well_typed_expr env e ==>
     state_well_typed st' /\ env_consistent env cx st' /\
     accounts_well_typed st'.accounts /\ no_type_error_result res /\
     case res of INL tv => expr_result_typed env e tv | INR v1 => T) /\
  env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
  accounts_well_typed st.accounts /\ functions_well_typed cx /\
  well_typed_expr env e /\ assignable_type env.type_defs typ /\ expr_type e = typ /\
  string_to_num id NOTIN FDOM env.var_types /\
  get_tenv cx = env.type_defs /\ evaluate_type env.type_defs typ = SOME tyv /\
  eval_stmt cx (AnnAssign id typ e) st = (res, st') ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts /\ no_type_error_result res /\
  case res of
  | INL u => env_consistent (extend_local env (string_to_num id) typ T) cx st'
  | INR exn => env_consistent env cx st' /\ return_exception_typed env ret_ty exn
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_stmt cx (AnnAssign id typ e) st = (res,st')` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, lift_option_type_def,
                       return_def, raise_def] >>
  asm_rewrite_tac[] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (expr_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `expr_res` >> gvs[no_type_error_result_def]
  >- (
    rename1 `eval_expr cx e st = (INL tvl, st1)` >>
    Cases_on `materialise cx tvl st1` >> rename1 `materialise cx tvl st1 = (mat_res, st2)` >>
    Cases_on `mat_res` >> gvs[no_type_error_result_def]
    >- (
      rename1 `materialise cx tvl st1 = (INL v, st2)` >>
      strip_tac >>
      `new_variable id tyv v st2 = (res,st')` by (
        qpat_x_assum `do tyv <- return tyv; tv <- eval_expr cx e; v <- materialise cx tv; new_variable id tyv v od st = (res,st')` mp_tac >>
        simp[bind_def, return_def, pairTheory.UNCURRY]) >>
      metis_tac[annassign_new_variable_after_materialise_sound,
                no_type_error_result_def]) >>
    rename1 `materialise cx tvl st1 = (INR exn, st2)` >>
    strip_tac >>
    `res = INR exn /\ st' = st2` by (
      qpat_x_assum `do tyv <- return tyv; tv <- eval_expr cx e; v <- materialise cx tv; new_variable id tyv v od st = (res,st')` mp_tac >>
      simp[bind_def, return_def, raise_def, pairTheory.UNCURRY]) >>
    gvs[no_type_error_result_def] >>
    `!msg. exn <> Error (TypeError msg)` by
      metis_tac[expr_result_typed_materialise_no_type_error] >>
    drule materialise_state >> strip_tac >> gvs[] >>
    drule materialise_no_control >>
    rw[no_control_exc_return_exception_typed]) >>
  rename1 `eval_expr cx e st = (INR exn, st1)` >>
  strip_tac >>
  `res = INR exn /\ st' = st1` by (
    qpat_x_assum `do tyv <- return tyv; tv <- eval_expr cx e; v <- materialise cx tv; new_variable id tyv v od st = (res,st')` mp_tac >>
    simp[bind_def, return_def, raise_def, pairTheory.UNCURRY]) >>
  gvs[no_type_error_result_def] >>
  drule eval_expr_exception_return_typed >> rw[]
QED




Theorem location_runtime_typed_rebuild[local]:
  !env cx st loc vt st'.
    location_runtime_typed env cx st loc vt /\
    runtime_consistent env cx st' ==>
    location_runtime_typed env cx st' loc vt
Proof
  rw[] >> Cases_on `loc` >> gvs[location_runtime_typed_def, runtime_consistent_def,
                                     env_consistent_def, env_scopes_consistent_def,
                                     env_immutables_consistent_def]
  >- (
    rename1 `FLOOKUP env.var_types (string_to_num s) = SOME var_ty` >>
    `?entry'. lookup_scopes (string_to_num s) st'.scopes = SOME entry'` by metis_tac[IS_SOME_EXISTS] >>
    `env.type_defs = get_tenv cx` by fs[env_context_consistent_def] >>
    `evaluate_type (get_tenv cx) var_ty = SOME entry'.type` by metis_tac[] >>
    `entry'.type = entry.type` by gvs[] >>
    qexists_tac `entry'` >> simp[]) >>
  rename1 `FLOOKUP env.bare_globals (_,string_to_num s) = SOME imm_ty` >>
  `env.current_src = current_module cx` by fs[env_context_consistent_def] >> gvs[] >>
  `?pair. FLOOKUP (get_source_immutables (current_module cx)
      (case ALOOKUP st'.immutables cx.txn.target of NONE => [] | SOME m => m))
      (string_to_num s) = SOME pair` by metis_tac[IS_SOME_EXISTS] >>
  PairCases_on `pair` >>
  `env.type_defs = get_tenv cx` by fs[env_context_consistent_def] >>
  `evaluate_type (get_tenv cx) imm_ty = SOME pair0` by metis_tac[] >>
  qexists_tac `get_source_immutables (current_module cx)
      (case ALOOKUP st'.immutables cx.txn.target of NONE => [] | SOME m => m)` >>
  qexists_tac `pair1` >>
  Cases_on `ALOOKUP st'.immutables cx.txn.target` >>
  Cases_on `ALOOKUP x (current_module cx)` >>
  gvs[get_immutables_def, get_address_immutables_def, bind_def, return_def,
      lift_option_def, get_source_immutables_def, AllCaseEqs()]
QED

Theorem subscript_vtype_index_get_Value_no_type_error[local]:
  !base_vt idx_ty result_vt env e tv st res st'.
    subscript_vtype base_vt idx_ty = SOME result_vt /\
    expr_result_typed env e tv /\ expr_type e = idx_ty /\
    get_Value tv st = (res, st') ==>
    no_type_error_result res
Proof
  rw[expr_result_typed_def, expr_runtime_typed_def] >>
  irule get_Value_no_type_error >>
  qexistsl_tac [`st`, `st'`, `tv`, `tv'`] >> simp[] >>
  Cases_on `base_vt` >> gvs[subscript_vtype_def]
  >- (Cases_on `t` >> gvs[subscript_vtype_def] >>
      Cases_on `expr_type e` >> gvs[is_int_type_def, evaluate_type_def, AllCaseEqs()]) >>
  Cases_on `expr_type e` >> gvs[hashmap_key_type_def, evaluate_type_def, AllCaseEqs(), LET_THM]
QED
Theorem get_Value_INR_no_type_error[local]:
  !tv tyv st y st'.
    toplevel_value_typed tv tyv /\ tyv <> NoneTV /\
    (!t b. tyv <> ArrayTV t b) /\
    get_Value tv st = (INR y, st') ==>
    !msg. y <> Error (TypeError msg)
Proof
  rw[] >>
  drule_all get_Value_no_type_error >>
  gvs[no_type_error_result_def]
QED


Theorem subscript_vtype_value_step_type[local]:
  !base_vt idx_ty result_vt env e tv st st' v loc_vt sbs.
    subscript_vtype base_vt idx_ty = SOME result_vt /\
    expr_result_typed env e tv /\ expr_type e = idx_ty /\
    get_Value tv st = (INL v, st') /\
    target_path_type env loc_vt sbs base_vt ==>
    target_path_type env loc_vt (ValueSubscript v::sbs) result_vt
Proof
  rw[expr_result_typed_def, expr_runtime_typed_def] >>
  irule target_path_type_subscript_cons >>
  qexistsl_tac [`expr_type e`, `base_vt`] >> simp[] >>
  Cases_on `base_vt` >> gvs[subscript_vtype_def]
  >- (Cases_on `t` >> gvs[subscript_vtype_def] >>
      Cases_on `expr_type e` >> gvs[is_int_type_def, evaluate_type_def, AllCaseEqs()] >>
      Cases_on `tv` >> gvs[get_Value_def, return_def, toplevel_value_typed_def] >>
      Cases_on `v` >> gvs[value_has_type_def]) >>
  Cases_on `expr_type e` >> gvs[hashmap_key_type_def, evaluate_type_def, AllCaseEqs(), LET_THM] >>
  Cases_on `tv` >> gvs[get_Value_def, return_def, toplevel_value_typed_def] >>
  Cases_on `v` >> gvs[value_has_type_def]
QED

(* ===== C5.2 Bridge lemmas: derive shape and assignable context for statement
   assignment branches from evaluation/target-typing/runtime-consistency facts
   actually available at the call site. ===== *)

Theorem assign_target_assignable_context_ScopedVar_equals_assignable:
  assign_target_assignable_context cx (BaseTargetV (ScopedVar id) sbs) st =
   assign_target_assignable (BaseTargetV (ScopedVar id) sbs) st
Proof
  simp[assign_target_assignable_context_def]
QED

Theorem assign_target_assignable_context_ImmutableVar[simp]:
  assign_target_assignable_context cx (BaseTargetV (ImmutableVar id) sbs) st = T
Proof
  simp[assign_target_assignable_context_def, assign_target_assignable_def]
QED

(* ===== Static assignable context predicate ===== *)
(* This predicate captures exactly the cx-dependent (non-dynamic, non-st-dependent)
   part of assign_target_assignable_context for already-evaluated assignment values.
   For ScopedVar/ImmutableVar it is trivial. For TopLevelVar it requires
   get_module_code, find_var_decl_by_num, evaluate_type, and lookup_var_slot_from_layout
   to return SOME — these are the preconditions that assign_target checks before
   proceeding, so they hold at INL-success sites and must be supplied as a premise
   at INR/no-TypeError sites. *)

Definition assignment_value_static_assignable_context_def:
  (assignment_value_static_assignable_context cx (BaseTargetV (TopLevelVar src id) sbs) =
     ?code p. get_module_code cx src = SOME code ∧
              find_var_decl_by_num (string_to_num id) code = SOME p ∧
              (case FST p of
                | StorageVarDecl is_transient typ =>
                    IS_SOME (evaluate_type (get_tenv cx) typ) ∧
                    IS_SOME (lookup_var_slot_from_layout cx is_transient src (SND p))
                | HashMapVarDecl is_transient kt vt =>
                    sbs <> [] ∧
                    IS_SOME (lookup_var_slot_from_layout cx is_transient src (SND p)))) ∧
  (assignment_value_static_assignable_context cx (BaseTargetV (ScopedVar _) sbs) = T) ∧
  (assignment_value_static_assignable_context cx (BaseTargetV (ImmutableVar _) sbs) = T) ∧
  (assignment_value_static_assignable_context cx (TupleTargetV tgts) =
     EVERY (assignment_value_static_assignable_context cx) tgts)
End

Theorem assignment_value_static_assignable_context_ScopedVar[simp]:
  assignment_value_static_assignable_context cx (BaseTargetV (ScopedVar id) sbs) = T
Proof
  simp[assignment_value_static_assignable_context_def]
QED

Theorem assignment_value_static_assignable_context_ImmutableVar[simp]:
  assignment_value_static_assignable_context cx (BaseTargetV (ImmutableVar id) sbs) = T
Proof
  simp[assignment_value_static_assignable_context_def]
QED

Theorem assignment_value_static_assignable_context_TupleTargetV[simp]:
  assignment_value_static_assignable_context cx (TupleTargetV gvs) =
  EVERY (assignment_value_static_assignable_context cx) gvs
Proof
  simp[assignment_value_static_assignable_context_def] >>
  metis_tac[ETA_AX]
QED

Theorem assignment_value_static_assignable_context_TopLevelVar:
  assignment_value_static_assignable_context cx (BaseTargetV (TopLevelVar src id) sbs) ⇔
    ∃code p. get_module_code cx src = SOME code ∧
             find_var_decl_by_num (string_to_num id) code = SOME p ∧
             (case FST p of
               | StorageVarDecl is_transient typ =>
                   IS_SOME (evaluate_type (get_tenv cx) typ) ∧
                   IS_SOME (lookup_var_slot_from_layout cx is_transient src (SND p))
               | HashMapVarDecl is_transient kt vt =>
                   sbs ≠ [] ∧
                   IS_SOME (lookup_var_slot_from_layout cx is_transient src (SND p)))
Proof
  simp[assignment_value_static_assignable_context_def]
QED

(* Bridge lemma C5.2.3 (mutual form): runtime typed target + env_consistent +
   static context implies the full assign_target_assignable_context.
   Uses recInduct on target_runtime_typed_ind so that the tuple branch
   gets the IH for sub-targets automatically. *)
Theorem target_runtime_typed_static_imp_assignable_context_mutual:
  (!env cx st tgt ty gv.
     target_runtime_typed env cx st tgt ty gv ∧
     env_consistent env cx st ∧
     assignment_value_static_assignable_context cx gv ==>
     assign_target_assignable_context cx gv st) ∧
  (!env cx st tgts tys gvs.
     target_values_runtime_typed env cx st tgts tys gvs ∧
     env_consistent env cx st ∧
     EVERY (assignment_value_static_assignable_context cx) gvs ==>
     EVERY (λgv. assign_target_assignable_context cx gv st) gvs)
Proof
  ho_match_mp_tac target_runtime_typed_ind >> rpt strip_tac
  >- (Cases_on `loc`
      >- metis_tac[target_runtime_typed_ScopedVar_imp_assignable_context]
      >- simp[assign_target_assignable_context_def, assign_target_assignable_def]
      >- (simp[assign_target_assignable_context_def, assign_target_assignable_def] >>
          irule (iffLR (GEN_ALL assignment_value_static_assignable_context_TopLevelVar)) >>
          metis_tac[]))
  >- gvs[target_runtime_typed_def]
  >- gvs[target_runtime_typed_def]
  >- (gvs[target_runtime_typed_def, assign_target_assignable_context_def] >>
      first_x_assum (qspecl_then [`tys`] mp_tac) >> simp[] >> metis_tac[])
  >- simp[]
  >- (fs[target_runtime_typed_def] >> metis_tac[])
  >- gvs[target_runtime_typed_def]
  >- gvs[target_runtime_typed_def]
  >- gvs[target_runtime_typed_def]
  >- gvs[target_runtime_typed_def]
QED

(* Projected single-target form for convenient use *)
Theorem target_runtime_typed_static_imp_assignable_context:
  !env cx st tgt ty gv.
    target_runtime_typed env cx st tgt ty gv ∧
    env_consistent env cx st ∧
    assignment_value_static_assignable_context cx gv ==>
    assign_target_assignable_context cx gv st
Proof
  metis_tac[cj 1 target_runtime_typed_static_imp_assignable_context_mutual]
QED

(* Projected list form for convenient use *)
Theorem target_values_runtime_typed_static_imp_EVERY_assignable_context:
  !env cx st tgts tys gvs.
    target_values_runtime_typed env cx st tgts tys gvs ∧
    env_consistent env cx st ∧
    EVERY (assignment_value_static_assignable_context cx) gvs ==>
    EVERY (λgv. assign_target_assignable_context cx gv st) gvs
Proof
  metis_tac[cj 2 target_runtime_typed_static_imp_assignable_context_mutual]
QED

(* C5.4.3: Static assignable context for evaluated TopLevelVar targets.
   This produces the missing premise for C5.2.3 in INR statement branches. *)

(* Helper: TopLevelVar locations with well-typed base targets are not bare globals.
   Uses type_place_target (any vtype) rather than well_typed_target (Type ty only)
   because SubscriptTarget/AttributeTarget recursion may give HashMapT etc. *)
Theorem base_target_value_shape_TopLevelVar_imp_bare_globals_none:
  !env bt loc sbs vt.
    base_target_value_shape env bt loc sbs ==>
    type_place_target env bt = SOME vt ==>
    !src id. loc = TopLevelVar src id ==>
    FLOOKUP env.bare_globals (src, string_to_num id) = NONE
Proof
  recInduct base_target_value_shape_ind >>
  rw[] >>
  gvs[base_target_value_shape_def]
  >- (* TopLevelNameTarget case *)
     fs[type_place_target_TopLevelNameTarget]
  >- (* AttributeTarget case *)
     metis_tac[type_place_target_AttributeTarget]
  >- (* SubscriptTarget case *)
     metis_tac[type_place_target_SubscriptTarget]
QED

(* Specialized corollary where loc is already TopLevelVar, avoiding
   the nested universal quantifier that makes irule/drule matching hard. *)
Theorem base_target_value_shape_TopLevelVar_imp_bare_globals_none_spec[local]:
  !env bt src id sbs vt.
    base_target_value_shape env bt (TopLevelVar src id) sbs ==>
    type_place_target env bt = SOME vt ==>
    FLOOKUP env.bare_globals (src, string_to_num id) = NONE
Proof
  metis_tac[base_target_value_shape_TopLevelVar_imp_bare_globals_none]
QED

Theorem target_runtime_typed_TopLevelVar_imp_static_context[local]:
  !env cx st bt ty src id sbs.
    target_runtime_typed env cx st (BaseTarget bt) ty (BaseTargetV (TopLevelVar src id) sbs) /\
    env_consistent env cx st ==>
    assignment_value_static_assignable_context cx (BaseTargetV (TopLevelVar src id) sbs)
Proof
  rpt strip_tac >>
  fs[target_runtime_typed_def] >>
  fs[target_value_shape_def, well_typed_atarget_def] >>
  fs[well_typed_target_def] >>
  `FLOOKUP env.bare_globals (src, string_to_num id) = NONE`
    by metis_tac[base_target_value_shape_TopLevelVar_imp_bare_globals_none_spec] >>
  (* Expand location_runtime_typed to expose the FLOOKUP for drule/metis *)
  fs[location_runtime_typed_def] >>
  Cases_on `vt` >> fs[]
  >- (* Type: use env_consistent projection then the TopLevelVar biconditional *)
     (drule_all env_consistent_toplevel_storage_static >> strip_tac >>
      rw[assignment_value_static_assignable_context_TopLevelVar] >>
      qexists_tac `ts` >> qexists_tac `(StorageVarDecl is_transient typ, id_str)` >>
      simp[])
  >- (* HashMapT: similar but sbs <> [] from target_path_type *)
     (drule_all env_consistent_toplevel_hashmap_static >> strip_tac >>
      rw[assignment_value_static_assignable_context_TopLevelVar] >>
      metis_tac[target_path_type_HashMapT_not_nil])
QED

Theorem target_runtime_typed_imp_static_assignable_context_mutual:
  (!env cx st tgt ty gv.
     target_runtime_typed env cx st tgt ty gv /\
     env_consistent env cx st ==>
     assignment_value_static_assignable_context cx gv) /\
  (!env cx st tgts tys gvs.
     target_values_runtime_typed env cx st tgts tys gvs /\
     env_consistent env cx st ==>
     EVERY (assignment_value_static_assignable_context cx) gvs)
Proof
  ho_match_mp_tac target_runtime_typed_ind >> rpt strip_tac
  (* Goal 1: BaseTarget / BaseTargetV *)
  >- (Cases_on `loc` >> simp[]
      >- metis_tac[target_runtime_typed_TopLevelVar_imp_static_context])
  (* Goal 2: BaseTarget / TupleTargetV *)
  >- gvs[target_runtime_typed_def]
  (* Goal 3: TupleTarget / BaseTargetV *)
  >- gvs[target_runtime_typed_def]
  (* Goal 4: TupleTarget / TupleTargetV *)
  >- (fs[target_runtime_typed_def] >>
      simp[assignment_value_static_assignable_context_TupleTargetV] >>
      metis_tac[])
  (* Goal 5: target_values_runtime_typed [] [] [] *)
  >- simp[]
  (* Goal 6: target_values_runtime_typed cons case *)
  >- (fs[target_runtime_typed_def] >> metis_tac[])
  (* Remaining goals: mismatched length cases *)
  >- gvs[target_runtime_typed_def]
  >- gvs[target_runtime_typed_def]
  >- gvs[target_runtime_typed_def]
  >- gvs[target_runtime_typed_def]
QED

Theorem target_runtime_typed_imp_static_assignable_context:
  !env cx st tgt ty gv.
    target_runtime_typed env cx st tgt ty gv ==>
    env_consistent env cx st ==>
    assignment_value_static_assignable_context cx gv
Proof
  metis_tac[cj 1 target_runtime_typed_imp_static_assignable_context_mutual]
QED

Theorem target_values_runtime_typed_imp_EVERY_static_assignable_context:
  !env cx st tgts tys gvs.
    target_values_runtime_typed env cx st tgts tys gvs ==>
    env_consistent env cx st ==>
    EVERY (assignment_value_static_assignable_context cx) gvs
Proof
  metis_tac[cj 2 target_runtime_typed_imp_static_assignable_context_mutual]
QED

(* C5.4.4: Direct bridges from target_runtime_typed + env_consistent to
   assign_target_assignable_context, combining C5.4.3 (static context
   derivation) with C5.2.3 (static+runtime → assignable context). *)

Theorem target_runtime_typed_imp_assignable_context:
  !env cx st tgt ty gv.
    target_runtime_typed env cx st tgt ty gv ==>
    env_consistent env cx st ==>
    assign_target_assignable_context cx gv st
Proof
  metis_tac[target_runtime_typed_imp_static_assignable_context,
            target_runtime_typed_static_imp_assignable_context]
QED

Theorem target_values_runtime_typed_imp_EVERY_assignable_context:
  !env cx st tgts tys gvs.
    target_values_runtime_typed env cx st tgts tys gvs ==>
    env_consistent env cx st ==>
    EVERY (\gv. assign_target_assignable_context cx gv st) gvs
Proof
  metis_tac[target_values_runtime_typed_imp_EVERY_static_assignable_context,
            target_values_runtime_typed_static_imp_EVERY_assignable_context]
QED



(* C2.2: exact assignment-operation bridge lemmas for statement assignment call sites. *)
Theorem stmt_assign_operation_runtime_typed_Update_from_value_runtime_typed_binop:
  !env ty bop rhs_ty v.
    value_runtime_typed env rhs_ty v /\ well_typed_binop ty bop ty rhs_ty ==>
    assign_operation_runtime_typed env ty (Update ty bop v)
Proof
  rw[assign_operation_runtime_typed_def] >> metis_tac[]
QED

Theorem stmt_assign_operation_runtime_typed_Append_from_value_has_type:
  !env elem_ty n elem_tv v.
    evaluate_type env.type_defs elem_ty = SOME elem_tv /\ value_has_type elem_tv v ==>
    assign_operation_runtime_typed env (ArrayT elem_ty (Dynamic n)) (AppendOp v)
Proof
  rw[assign_operation_runtime_typed_def] >> metis_tac[]
QED

Theorem stmt_assign_operation_runtime_typed_Pop_from_dynamic_array:
  !env elem_ty n elem_tv.
    evaluate_type env.type_defs elem_ty = SOME elem_tv ==>
    assign_operation_runtime_typed env (ArrayT elem_ty (Dynamic n)) PopOp
Proof
  rw[assign_operation_runtime_typed_def] >> metis_tac[]
QED

Theorem well_typed_expr_Pop_dynamic_target[local]:
  !env ty tgt.
    well_typed_expr env (Pop ty tgt) ==>
    ?n. type_place_target env tgt = SOME (Type (ArrayT ty (Dynamic n)))
Proof
  simp[Once well_typed_expr_def] >> metis_tac[]
QED

Theorem well_typed_expr_Pop_dynamic_target_assignable[local]:
  !env ty tgt.
    well_typed_expr env (Pop ty tgt) ==>
    ?n. type_place_target env tgt = SOME (Type (ArrayT ty (Dynamic n))) /\
        assignable_type env.type_defs (ArrayT ty (Dynamic n))
Proof
  simp[Once well_typed_expr_def]
QED


Theorem stmt_assign_operation_matches_target_shape_BaseTargetV:
  !loc sbs op. assign_operation_matches_target_shape (BaseTargetV loc sbs) op
Proof
  rw[assign_operation_matches_target_shape_def]
QED

Theorem stmt_assign_operation_matches_target_shape_Update_BaseTargetV:
  !loc sbs ty bop v.
    assign_operation_matches_target_shape (BaseTargetV loc sbs) (Update ty bop v)
Proof
  rw[assign_operation_matches_target_shape_def]
QED

Theorem stmt_assign_operation_matches_target_shape_Append_BaseTargetV:
  !loc sbs v.
    assign_operation_matches_target_shape (BaseTargetV loc sbs) (AppendOp v)
Proof
  rw[assign_operation_matches_target_shape_def]
QED

Theorem stmt_assign_operation_matches_target_shape_Pop_BaseTargetV:
  !loc sbs. assign_operation_matches_target_shape (BaseTargetV loc sbs) PopOp
Proof
  rw[assign_operation_matches_target_shape_def]
QED
Theorem assign_target_TopLevelVar_INL_imp_assignable_context:
  !cx src id sbs op st res st'.
    assign_target cx (BaseTargetV (TopLevelVar src id) sbs) op st = (INL res, st') ==>
    assign_target_assignable_context cx (BaseTargetV (TopLevelVar src id) sbs) st
Proof
  rpt gen_tac >> strip_tac >>
  (* For TopLevelVar, assign_target_assignable is T (wildcard case), so
     assign_target_assignable_context reduces to just the static context existential. *)
  simp[assign_target_assignable_context_def, assign_target_assignable_def] >>
  (* Goal: ∃code p. get_module_code cx src = SOME code ∧
                    find_var_decl_by_num (string_to_num id) code = SOME p ∧
                    (case FST p of StorageVarDecl ... | HashMapVarDecl ...) *)
  drule assign_target_TopLevelVar_success_imp_lookup_global_INL >> strip_tac >>
  drule lookup_global_INL_imp_decl_facts >> strip_tac >>
  (* Now have: get_module_code cx src = SOME code *)
  qexists `code` >>
  (* Now need ∃p. find_var_decl_by_num ... = SOME p ∧ (case FST p of ...)
     Use metis_tac to resolve the universally quantified helper lemma against assumptions *)
  `?p. find_var_decl_by_num (string_to_num id) code = SOME p`
    by metis_tac[assign_target_TopLevelVar_INL_imp_find_decl_SOME] >>
  (* p is now in scope; provide it as the existential witness *)
  qexists `p` >> simp[] >>
  (* Remaining goal: case FST p of StorageVarDecl => IS_SOME ... | HashMapVarDecl => ... *)
  PairCases_on `p` >> gvs[] >>
  Cases_on `p0` >> gvs[]
  >- (
    (* StorageVarDecl: need IS_SOME (evaluate_type) and IS_SOME (lookup_var_slot_from_layout)
       metis_tac handles instantiation of universally quantified antecedents *)
    metis_tac[lookup_global_INL_StorageVarDecl_imp_IS_SOME])
  >- (
    (* HashMapVarDecl: need sbs ≠ [] and IS_SOME (lookup_var_slot_from_layout) *)
    conj_tac
    >- metis_tac[assign_target_TopLevelVar_INL_HashMapVarDecl_imp_sbs_ne] >>
    metis_tac[lookup_global_INL_HashMapVarDecl_imp_IS_SOME])
QED


(* C5.2.5 was removed: the theorems assign_target_INL_imp_assignable_context_stmt_ind
   and assign_target_INL_imp_assignable_context_stmt had zero downstream consumers
   and the TupleTargetV branch was cheated. Deleted to eliminate CHEAT warning. *)


(* ===== Environment threading facts for executable statement typing ===== *)

(* Generic static env-extension facts moved to vyperTypeEnvExtension. *)

Theorem env_extends_return_exception_typed:
  env_extends env env' /\ return_exception_typed env' ret_ty exn ==>
  return_exception_typed env ret_ty exn
Proof
  strip_tac >>
  Cases_on `exn` >> gvs[return_exception_typed_def] >>
  metis_tac[value_runtime_typed_env_static, env_extends_def]
QED

(* Generic scope-pop env-consistency facts moved to vyperTypeScopePop. *)

Theorem extend_local_F_env_extends:
  env_maps_wf env /\
  id NOTIN FDOM env.var_types ==>
  env_extends env (extend_local env id ty F)
Proof
  rw[env_extends_def, extend_local_def, FLOOKUP_UPDATE] >>
  Cases_on `id = id'` >> gvs[TO_FLOOKUP] >>
  fs[env_maps_wf_def] >>
  first_x_assum (qspec_then `id` mp_tac) >> simp[]
QED

Theorem return_exception_typed_extend_local_F:
  env_maps_wf env /\
  id NOTIN FDOM env.var_types /\
  env_extends (extend_local env id ty F) env_exn /\
  return_exception_typed env_exn ret_ty y ==>
  return_exception_typed env ret_ty y
Proof
  strip_tac >>
  irule env_extends_return_exception_typed >>
  qexists_tac `env_exn` >> simp[] >>
  irule env_extends_trans >>
  qexists_tac `extend_local env id ty F` >> simp[] >>
  irule extend_local_F_env_extends >> simp[]
QED

Theorem return_exception_typed_extend_local_F_exists:
  env_maps_wf env /\
  id NOTIN FDOM env.var_types /\
  (∃env_exn.
     env_extends (extend_local env id ty F) env_exn /\
     env_consistent env_exn cx st_body /\
     return_exception_typed env_exn ret_ty y) ==>
  return_exception_typed env ret_ty y
Proof
  metis_tac[return_exception_typed_extend_local_F]
QED

Theorem return_exception_typed_extend_local_F_exists_imp:
  env_maps_wf env ==>
  id NOTIN FDOM env.var_types ==>
  (∃env_exn.
     env_extends (extend_local env id ty F) env_exn /\
     env_consistent env_exn cx st_body /\
     return_exception_typed env_exn ret_ty y) ==>
  return_exception_typed env ret_ty y
Proof
  metis_tac[return_exception_typed_extend_local_F_exists]
QED

Theorem return_exception_typed_extend_local_F_imp:
  env_maps_wf env ==>
  id NOTIN FDOM env.var_types ==>
  env_extends (extend_local env id ty F) env_exn ==>
  return_exception_typed env_exn ret_ty y ==>
  return_exception_typed env ret_ty y
Proof
  rpt strip_tac >>
  irule env_extends_return_exception_typed >>
  qexists_tac `env_exn` >> simp[] >>
  irule env_extends_trans >>
  qexists_tac `extend_local env id ty F` >> simp[] >>
  irule extend_local_F_env_extends >> simp[]
QED

Theorem value_runtime_typed_extend_local_F_ReturnException:
  env_extends (extend_local env id ty F) env_exn /\
  return_exception_typed env_exn ret_ty (ReturnException rv) ==>
  value_runtime_typed env ret_ty rv
Proof
  strip_tac >>
  irule value_runtime_typed_env_static >>
  qexists_tac `env_exn` >>
  gvs[env_extends_def, extend_local_def, return_exception_typed_def]
QED


Theorem return_exception_typed_extend_local_F_ReturnException:
  env_extends (extend_local env id ty F) env_exn /\
  return_exception_typed env_exn ret_ty (ReturnException rv) ==>
  return_exception_typed env ret_ty (ReturnException rv)
Proof
  strip_tac >>
  simp[return_exception_typed_def] >>
  irule value_runtime_typed_env_static >>
  qexists_tac `env_exn` >>
  gvs[env_extends_def, extend_local_def, return_exception_typed_def]
QED

Theorem return_exception_typed_extend_local_F_ReturnException_imp:
  env_extends (extend_local env id ty F) env_exn ==>
  return_exception_typed env_exn ret_ty (ReturnException rv) ==>
  return_exception_typed env ret_ty (ReturnException rv)
Proof
  rpt strip_tac >>
  drule return_exception_typed_extend_local_F_ReturnException >>
  simp[]
QED

Theorem return_exception_typed_extend_local_env_extends:
  env_extends (extend_local env id ty assignable) env_exn /\
  return_exception_typed env_exn ret_ty exn ==>
  return_exception_typed env ret_ty exn
Proof
  Cases_on `exn` >> simp[return_exception_typed_def] >>
  strip_tac >>
  irule value_runtime_typed_env_static >>
  qexists_tac `env_exn` >>
  gvs[env_extends_def, extend_local_def]
QED

Theorem for_cons_ordinary_exception_conclusion:
  state_well_typed stpopped ==>
  accounts_well_typed stpopped.accounts ==>
  env_consistent env cx stpopped ==>
  no_type_error_result (INR exn) ==>
  (env_extends (extend_local env id ty F) env_exn /\
   return_exception_typed env_exn ret_ty exn) ==>
  state_well_typed stpopped /\
  accounts_well_typed stpopped.accounts /\
  env_consistent env cx stpopped /\
  no_type_error_result (INR exn) /\
  return_exception_typed env ret_ty exn
Proof
  rpt gen_tac >>
  strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac >- fs[no_type_error_result_def] >>
  irule return_exception_typed_extend_local_env_extends >>
  qexists_tac `F` >>
  qexists_tac `env_exn` >>
  qexists_tac `id` >>
  qexists_tac `ty` >>
  fs[]
QED

Theorem for_cons_ordinary_exception_conclusion_exists:
  (∃env_exn.
     env_extends (extend_local env id ty F) env_exn /\
     env_consistent env_exn cx stbody /\
     return_exception_typed env_exn ret_ty exn) ==>
  state_well_typed stpopped ==>
  accounts_well_typed stpopped.accounts ==>
  env_consistent env cx stpopped ==>
  no_type_error_result (INR exn) ==>
  state_well_typed stpopped /\
  accounts_well_typed stpopped.accounts /\
  env_consistent env cx stpopped /\
  no_type_error_result (INR exn) /\
  return_exception_typed env ret_ty exn
Proof
  rpt gen_tac >> strip_tac >> ntac 4 strip_tac >>
  irule for_cons_ordinary_exception_conclusion >>
  simp[] >>
  qexists_tac `env_exn` >>
  qexists_tac `id` >>
  qexists_tac `ty` >>
  simp[]
QED

Theorem for_cons_ordinary_exception_final_from_body_noerr:
  (∃env_exn.
     env_extends (extend_local env id ty F) env_exn /\
     env_consistent env_exn cx stbody /\
     return_exception_typed env_exn ret_ty exn) ==>
  state_well_typed stpopped ==>
  accounts_well_typed stpopped.accounts ==>
  env_consistent env cx stpopped ==>
  no_type_error_result (INR exn) ==>
  state_well_typed stpopped /\
  accounts_well_typed stpopped.accounts /\
  env_consistent env cx stpopped /\
  no_type_error_result (INR exn) /\
  return_exception_typed env ret_ty exn
Proof
  metis_tac[for_cons_ordinary_exception_conclusion_exists]
QED

Theorem for_cons_ordinary_exception_conclusion_exists_bundle:
  ((∃env_exn.
      env_extends (extend_local env id ty F) env_exn /\
      env_consistent env_exn cx stbody /\
      return_exception_typed env_exn ret_ty exn) /\
   state_well_typed stpopped /\
   accounts_well_typed stpopped.accounts /\
   env_consistent env cx stpopped /\
   no_type_error_result (INR exn)) ==>
  state_well_typed stpopped /\
  accounts_well_typed stpopped.accounts /\
  env_consistent env cx stpopped /\
  no_type_error_result (INR exn) /\
  return_exception_typed env ret_ty exn
Proof
  metis_tac[for_cons_ordinary_exception_conclusion_exists]
QED

Theorem for_cons_body_exception_noerr_package_generalises:
  (?env_exn.
     env_extends (extend_local env id ty F) env_exn /\
     env_consistent env_exn cx stbody /\
     return_exception_typed env_exn ret_ty exn) ==>
  no_type_error_result (INR exn) ==>
  (?id0 stbody0 ty0 env_exn.
     env_extends (extend_local env id0 ty0 F) env_exn /\
     env_consistent env_exn cx stbody0 /\
     return_exception_typed env_exn ret_ty exn) /\
  no_type_error_result (INR exn)
Proof
  rw[no_type_error_result_def] >-
   (qexists_tac `id` >> qexists_tac `stbody` >>
    qexists_tac `ty` >> qexists_tac `env_exn` >> simp[]) >>
  first_x_assum (qspec_then `msg` mp_tac) >> simp[]
QED

Theorem for_cons_body_exception_named_package:
  (?env_exn.
     env_extends (extend_local env id ty F) env_exn /\
     env_consistent env_exn cx stbody /\
     return_exception_typed env_exn ret_ty exn) ==>
  no_type_error_result (INR exn) ==>
  (!msg. exn <> Error (TypeError msg)) /\
  (?id0 stbody0 ty0 env_exn.
     env_extends (extend_local env id0 ty0 F) env_exn /\
     env_consistent env_exn cx stbody0 /\
     return_exception_typed env_exn ret_ty exn)
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  conj_tac >- (
    fs[no_type_error_result_def] >>
    gen_tac >> first_x_assum (qspec_then `msg` mp_tac) >> simp[]) >>
  qexists_tac `id` >> qexists_tac `stbody` >>
  qexists_tac `ty` >> qexists_tac `env_exn` >> simp[]
QED
Theorem for_cons_body_exception_noerr_package_same_body:
  (∃env_exn.
      env_extends (extend_local env id ty F) env_exn /\
      env_consistent env_exn cx stbody /\
      return_exception_typed env_exn ret_ty exn) ==>
  no_type_error_result (INR exn) ==>
  (∃id0 ty0 env_exn.
      env_extends (extend_local env id0 ty0 F) env_exn /\
      env_consistent env_exn cx stbody /\
      return_exception_typed env_exn ret_ty exn) /\
  no_type_error_result (INR exn)
Proof
  rw[no_type_error_result_def] >-
   (qexists_tac `id` >> qexists_tac `ty` >>
    qexists_tac `env_exn` >> simp[]) >>
  first_x_assum (qspec_then `msg` mp_tac) >> simp[]
QED

Theorem for_cons_body_exception_noerr_package_generalises_bundle:
  ((∃env_exn.
      env_extends (extend_local env id ty F) env_exn /\
      env_consistent env_exn cx stbody /\
      return_exception_typed env_exn ret_ty exn) /\
   no_type_error_result (INR exn)) ==>
  (∃id0 stbody0 ty0 env_exn.
      env_extends (extend_local env id0 ty0 F) env_exn /\
      env_consistent env_exn cx stbody0 /\
      return_exception_typed env_exn ret_ty exn) /\
  no_type_error_result (INR exn)
Proof
  metis_tac[for_cons_body_exception_noerr_package_generalises]
QED

Theorem for_cons_ordinary_exception_conclusion_from_body_package:
  ((∃env_exn.
      env_extends (extend_local env id ty F) env_exn /\
      env_consistent env_exn cx stbody /\
      return_exception_typed env_exn ret_ty exn) /\
   state_well_typed stpopped /\
   accounts_well_typed stpopped.accounts /\
   env_consistent env cx stpopped /\
   no_type_error_result (INR exn)) ==>
  state_well_typed stpopped /\
  accounts_well_typed stpopped.accounts /\
  env_consistent env cx stpopped /\
  no_type_error_result (INR exn) /\
  return_exception_typed env ret_ty exn
Proof
  metis_tac[for_cons_ordinary_exception_conclusion_exists_bundle]
QED


Theorem for_cons_ordinary_exception_conclusion_named_noerr:
  state_well_typed stpopped ==>
  accounts_well_typed stpopped.accounts ==>
  env_consistent env cx stpopped ==>
  (!msg. exn <> Error (TypeError msg)) ==>
  env_extends (extend_local env id ty F) env_exn ==>
  return_exception_typed env_exn ret_ty exn ==>
  state_well_typed stpopped /\
  accounts_well_typed stpopped.accounts /\
  env_consistent env cx stpopped /\
  no_type_error_result (INR exn) /\
  return_exception_typed env ret_ty exn
Proof
  rpt gen_tac >>
  ntac 6 strip_tac >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[no_type_error_result_def] >>
  irule return_exception_typed_extend_local_env_extends >>
  qexists_tac `F` >>
  qexists_tac `env_exn` >>
  qexists_tac `id` >>
  qexists_tac `ty` >>
  simp[]
QED

Theorem for_cons_ordinary_exception_conclusion_from_body_ex:
  (∃env_exn.
     env_extends (extend_local env id ty F) env_exn /\
     env_consistent env_exn cx stbody /\
     return_exception_typed env_exn ret_ty exn) ==>
  state_well_typed stpopped ==>
  accounts_well_typed stpopped.accounts ==>
  env_consistent env cx stpopped ==>
  (!msg. exn <> Error (TypeError msg)) ==>
  state_well_typed stpopped /\
  accounts_well_typed stpopped.accounts /\
  env_consistent env cx stpopped /\
  no_type_error_result (INR exn) /\
  return_exception_typed env ret_ty exn
Proof
  rpt gen_tac >> strip_tac >> ntac 4 strip_tac >>
  irule for_cons_ordinary_exception_conclusion_named_noerr >>
  simp[] >>
  qexistsl [`env_exn`, `id`, `ty`] >>
  simp[]
QED

Theorem for_cons_ordinary_exception_conclusion_from_body_noerr:
  (∃env_exn.
     env_extends (extend_local env id ty F) env_exn /\
     env_consistent env_exn cx stbody /\
     return_exception_typed env_exn ret_ty exn) ==>
  state_well_typed stpopped ==>
  accounts_well_typed stpopped.accounts ==>
  env_consistent env cx stpopped ==>
  no_type_error_result (INR exn) ==>
  state_well_typed stpopped /\
  accounts_well_typed stpopped.accounts /\
  env_consistent env cx stpopped /\
  no_type_error_result (INR exn) /\
  return_exception_typed env ret_ty exn
Proof
  rw[no_type_error_result_def] >>
  metis_tac[return_exception_typed_extend_local_env_extends]
QED

Theorem for_cons_ordinary_exception_final_case_from_body_noerr:
  (∃env_exn.
     env_extends (extend_local env id ty F) env_exn /\
     env_consistent env_exn cx stbody /\
     return_exception_typed env_exn ret_ty exn) ==>
  state_well_typed stpopped ==>
  accounts_well_typed stpopped.accounts ==>
  env_consistent env cx stpopped ==>
  no_type_error_result (INR exn) ==>
  state_well_typed stpopped /\
  accounts_well_typed stpopped.accounts /\
  env_consistent env cx stpopped /\
  no_type_error_result (INR exn) /\
  (case INR exn of INL v => T | INR exn0 => return_exception_typed env ret_ty exn0)
Proof
  once_rewrite_tac[return_exception_typed_INR_case_eq] >>
  rw[no_type_error_result_def] >>
  metis_tac[return_exception_typed_extend_local_env_extends]
QED

Theorem for_cons_ordinary_exception_final_case_noerr_first:
  no_type_error_result (INR exn) ==>
  (∃env_exn.
     env_extends (extend_local env id ty F) env_exn /\
     env_consistent env_exn cx stbody /\
     return_exception_typed env_exn ret_ty exn) ==>
  state_well_typed stpopped ==>
  accounts_well_typed stpopped.accounts ==>
  env_consistent env cx stpopped ==>
  state_well_typed stpopped /\
  accounts_well_typed stpopped.accounts /\
  env_consistent env cx stpopped /\
  no_type_error_result (INR exn) /\
  (case INR exn of INL v => T | INR exn0 => return_exception_typed env ret_ty exn0)
Proof
  rpt gen_tac >> strip_tac >> strip_tac >> ntac 3 strip_tac >>
  once_rewrite_tac[return_exception_typed_INR_case_eq] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- (
    qpat_x_assum `no_type_error_result (INR exn)` mp_tac >>
    simp[no_type_error_result_def] >> rpt strip_tac >>
    first_x_assum (qspec_then `msg` mp_tac) >> simp[]) >>
  irule return_exception_typed_extend_local_env_extends >>
  qexists_tac `F` >> qexists_tac `env_exn` >>
  qexists_tac `id` >> qexists_tac `ty` >>
  simp[]
QED

Theorem for_cons_ordinary_exception_final_case_from_witness:
  no_type_error_result (INR y) ==>
  env_extends (extend_local env id ty F) env_exn ==>
  env_consistent env_exn cx st_body ==>
  return_exception_typed env_exn ret_ty y ==>
  state_well_typed stpopped ==>
  accounts_well_typed stpopped.accounts ==>
  env_consistent env cx stpopped ==>
  state_well_typed stpopped /\
  accounts_well_typed stpopped.accounts /\
  env_consistent env cx stpopped /\
  no_type_error_result (INR y) /\
  (case INR y of INL v => T | INR exn => return_exception_typed env ret_ty exn)
Proof
  rpt gen_tac >> ntac 7 strip_tac >>
  irule for_cons_ordinary_exception_final_case_noerr_first >>
  simp[] >>
  qexists_tac `id` >> qexists_tac `st_body` >>
  qexists_tac `ty` >> qexists_tac `env_exn` >>
  simp[]
QED

Theorem for_cons_ordinary_exception_final_case_from_case_premise:
  no_type_error_result (INR y) ==>
  (case (INR y : value + vyperState$exception) of
   | INL v => env_consistent env_after cx stbody
   | INR exn =>
       ?env_exn.
         env_extends (extend_local env id ty F) env_exn /\
         env_consistent env_exn cx stbody /\
         return_exception_typed env_exn ret_ty exn) ==>
  state_well_typed stpopped ==>
  accounts_well_typed stpopped.accounts ==>
  env_consistent env cx stpopped ==>
  state_well_typed stpopped /\
  accounts_well_typed stpopped.accounts /\
  env_consistent env cx stpopped /\
  no_type_error_result (INR y) /\
  (case INR y of INL v => T | INR exn => return_exception_typed env ret_ty exn)
Proof
  rpt gen_tac >> strip_tac >> strip_tac >> ntac 3 strip_tac >>
  irule for_cons_ordinary_exception_final_case_noerr_first >>
  simp[] >>
  qpat_x_assum `case (INR y : value + vyperState$exception) of
               | INL (v:value) => env_consistent env_after cx stbody
               | INR exn =>
                 ?env_exn.
                   env_extends (extend_local env id ty F) env_exn /\
                   env_consistent env_exn cx stbody /\
                   return_exception_typed env_exn ret_ty exn` mp_tac >>
  simp[] >> strip_tac >>
  qexists_tac `id` >> qexists_tac `stbody` >> qexists_tac `ty` >>
  qexists_tac `env_exn` >> simp[]
QED

Theorem for_cons_ordinary_exception_full_suffix_from_case_premise:
  no_type_error_result (INR y) ==>
  (case (INR y : value + vyperState$exception) of
   | INL (u:value) => env_consistent env_after cx st_body
   | INR exn =>
       ?env_exn.
         env_extends (extend_local env id ty F) env_exn /\
         env_consistent env_exn cx st_body /\
         return_exception_typed env_exn ret_ty exn) ==>
  state_well_typed stfinal ==>
  accounts_well_typed stfinal.accounts ==>
  env_consistent env cx stfinal ==>
  state_well_typed stfinal /\
  accounts_well_typed stfinal.accounts /\
  env_consistent env cx stfinal /\
  no_type_error_result (INR y) /\
  (case INR y of INL v => T | INR exn => return_exception_typed env ret_ty exn)
Proof
  rpt gen_tac >> strip_tac >> strip_tac >> ntac 3 strip_tac >>
  irule for_cons_ordinary_exception_final_case_noerr_first >>
  simp[] >>
  qpat_x_assum `case (INR y : value + vyperState$exception) of
               | INL (u:value) => env_consistent env_after cx st_body
               | INR exn =>
                 ?env_exn.
                   env_extends (extend_local env id ty F) env_exn /\
                   env_consistent env_exn cx st_body /\
                   return_exception_typed env_exn ret_ty exn` mp_tac >>
  simp[] >> strip_tac >>
  qexists_tac `id` >> qexists_tac `st_body` >> qexists_tac `ty` >>
  qexists_tac `env_exn` >> simp[]
QED

Theorem for_cons_ordinary_exception_return_typed_from_case_premise:
  (case (INR y : value + vyperState$exception) of
   | INL (u:value) => env_consistent env_after cx st_body
   | INR exn =>
       ?env_exn.
         env_extends (extend_local env id ty F) env_exn /\
         env_consistent env_exn cx st_body /\
         return_exception_typed env_exn ret_ty exn) ==>
  return_exception_typed env ret_ty y
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `case (INR y : value + vyperState$exception) of
               | INL (u:value) => env_consistent env_after cx st_body
               | INR exn =>
                 ?env_exx.
                   env_extends (extend_local env id ty F) env_exx /\
                   env_consistent env_exx cx st_body /\
                   return_exception_typed env_exx ret_ty exn` mp_tac >>
  simp[] >> strip_tac >>
  irule return_exception_typed_extend_local_env_extends >>
  qexists_tac `F` >> qexists_tac `env_exn` >>
  qexists_tac `id` >> qexists_tac `ty` >>
  simp[]
QED

Theorem for_cons_ordinary_exception_return_typed_from_body_ih:
  env_consistent (extend_local env id ty F) cx stp /\
  state_well_typed stp /\
  accounts_well_typed stp.accounts /\
  eval_stmts cx body_stmts stp = (INR y, st_body) /\
  (!stp0 res_body st_body0.
     env_consistent (extend_local env id ty F) cx stp0 /\
     state_well_typed stp0 /\
     accounts_well_typed stp0.accounts /\
     eval_stmts cx body_stmts stp0 = (res_body, st_body0) ==>
     state_well_typed st_body0 /\
     accounts_well_typed st_body0.accounts /\
     no_type_error_result res_body /\
     (case res_body of
      | INL u => env_consistent env_after cx st_body0
      | INR exn =>
          ?env_exn.
            env_extends (extend_local env id ty F) env_exn /\
            env_consistent env_exn cx st_body0 /\
            return_exception_typed env_exn ret_ty exn)) ==>
  return_exception_typed env ret_ty y
Proof
  strip_tac >>
  irule for_cons_ordinary_exception_return_typed_from_case_premise >>
  qexists_tac `cx` >> qexists_tac `env_after` >>
  qexists_tac `id` >> qexists_tac `st_body` >>
  qexists_tac `ty` >>
  qpat_x_assum `!stp0 res_body st_body0. _`
    (qspecl_then [`stp`, `INR y`, `st_body`] mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >>
  qpat_x_assum `case (INR y) of
       INL u => env_consistent env_after cx st_body
     | INR exn =>
       ?env_exn.
         env_extends (extend_local env id ty F) env_exn /\
         env_consistent env_exn cx st_body /\
         return_exception_typed env_exn ret_ty exn` mp_tac >>
  simp[]
QED

Theorem for_cons_ordinary_exception_full_suffix_for_popped_body_from_case:
  no_type_error_result (INR y) ==>
  (case (INR y : value + vyperState$exception) of
   | INL (u:value) => env_consistent env_after cx st_body
   | INR exn =>
       ?env_exn.
         env_extends (extend_local env id ty F) env_exn /\
         env_consistent env_exn cx st_body /\
         return_exception_typed env_exn ret_ty exn) ==>
  state_well_typed (st_body with scopes := TL st_body.scopes) ==>
  accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts ==>
  env_consistent env cx (st_body with scopes := TL st_body.scopes) ==>
  state_well_typed (st_body with scopes := TL st_body.scopes) /\
  accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
  env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
  no_type_error_result (INR y) /\
  (case INR y of INL v => T | INR exn => return_exception_typed env ret_ty exn)
Proof
  rpt gen_tac >> strip_tac >> strip_tac >> ntac 3 strip_tac >>
  simp[] >>
  conj_tac >- fs[no_type_error_result_def] >>
  irule for_cons_ordinary_exception_return_typed_from_case_premise >>
  qexists_tac `cx` >> qexists_tac `env_after` >>
  qexists_tac `id` >> qexists_tac `st_body` >>
  qexists_tac `ty` >> simp[]
QED

Theorem for_cons_ordinary_exception_full_suffix_for_popped_body_visible_bundle:
  state_well_typed (st_body with scopes := TL st_body.scopes) /\
  accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
  env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
  no_type_error_result (INR y) /\
  (case (INR y : value + vyperState$exception) of
   | INL (u:value) => env_consistent env_after cx st_body
   | INR exn =>
       ?env_exn.
         env_extends (extend_local env id ty F) env_exn /\
         env_consistent env_exn cx st_body /\
         return_exception_typed env_exn ret_ty exn) ==>
  state_well_typed (st_body with scopes := TL st_body.scopes) /\
  accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
  env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
  no_type_error_result (INR y) /\
  (case INR y of INL v => T | INR exn => return_exception_typed env ret_ty exn)
Proof
  strip_tac >> simp[] >>
  conj_tac >- fs[no_type_error_result_def] >>
  irule for_cons_ordinary_exception_return_typed_from_case_premise >>
  qexists_tac `cx` >> qexists_tac `env_after` >>
  qexists_tac `id` >> qexists_tac `st_body` >>
  qexists_tac `ty` >> simp[]
QED

Theorem for_cons_ordinary_exception_return_typed_from_INR_witness:
  (?env_exn.
     env_extends (extend_local env id ty F) env_exn /\
     env_consistent env_exn cx st_body /\
     return_exception_typed env_exn ret_ty y) ==>
  return_exception_typed env ret_ty y
Proof
  strip_tac >>
  irule return_exception_typed_extend_local_env_extends >>
  qexists_tac `F` >> qexists_tac `env_exn` >>
  qexists_tac `id` >> qexists_tac `ty` >>
  simp[]
QED

Theorem for_cons_ordinary_exception_full_suffix_from_INR_witness:
  no_type_error_result (INR y) ==>
  (?env_exn.
     env_extends (extend_local env id ty F) env_exn /\
     env_consistent env_exn cx st_body /\
     return_exception_typed env_exn ret_ty y) ==>
  state_well_typed stfinal ==>
  accounts_well_typed stfinal.accounts ==>
  env_consistent env cx stfinal ==>
  state_well_typed stfinal /\
  accounts_well_typed stfinal.accounts /\
  env_consistent env cx stfinal /\
  no_type_error_result (INR y) /\
  (case INR y of INL v => T | INR exn => return_exception_typed env ret_ty exn)
Proof
  rpt gen_tac >> strip_tac >> strip_tac >> ntac 3 strip_tac >>
  simp[] >>
  conj_tac >- fs[no_type_error_result_def] >>
  irule for_cons_ordinary_exception_return_typed_from_INR_witness >>
  qexists_tac `cx` >> qexists_tac `id` >> qexists_tac `st_body` >>
  qexists_tac `ty` >> qexists_tac `env_exn` >> simp[]
QED

Theorem for_cons_ordinary_exception_full_suffix_from_INR_witness_bundle:
  no_type_error_result (INR y) /\
  (?env_exn.
     env_extends (extend_local env id ty F) env_exn /\
     env_consistent env_exn cx st_body /\
     return_exception_typed env_exn ret_ty y) /\
  state_well_typed stfinal /\
  accounts_well_typed stfinal.accounts /\
  env_consistent env cx stfinal ==>
  state_well_typed stfinal /\
  accounts_well_typed stfinal.accounts /\
  env_consistent env cx stfinal /\
  no_type_error_result (INR y) /\
  (case INR y of INL v => T | INR exn => return_exception_typed env ret_ty exn)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[] >>
  conj_tac >- fs[no_type_error_result_def] >>
  irule for_cons_ordinary_exception_return_typed_from_INR_witness >>
  qexists_tac `cx` >> qexists_tac `id` >> qexists_tac `st_body` >>
  qexists_tac `ty` >> qexists_tac `env_exn` >> simp[]
QED

Theorem for_cons_ordinary_exception_return_exception_suffix_from_env_witness:
  no_type_error_result (INR (ReturnException v)) /\
  state_well_typed stfinal /\
  accounts_well_typed stfinal.accounts /\
  env_consistent env cx stfinal /\
  env_extends (extend_local env id ty F) env_exn /\
  return_exception_typed env_exn ret_ty (ReturnException v) ==>
  state_well_typed stfinal /\
  accounts_well_typed stfinal.accounts /\
  env_consistent env cx stfinal /\
  no_type_error_result (INR (ReturnException v)) /\
  return_exception_typed env ret_ty (ReturnException v)
Proof
  strip_tac >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac >- fs[no_type_error_result_def] >>
  irule return_exception_typed_extend_local_env_extends >>
  qexists_tac `F` >> qexists_tac `env_exn` >>
  qexists_tac `id` >> qexists_tac `ty` >>
  simp[]
QED

Theorem for_cons_ordinary_exception_return_exception_suffix_from_case:
  no_type_error_result (INR (ReturnException v)) /\
  (case (INR (ReturnException v) : value + vyperState$exception) of
   | INL (u:value) => env_consistent env_after cx st_body
   | INR exn =>
       ?env_exn.
         env_extends (extend_local env id ty F) env_exn /\
         env_consistent env_exn cx st_body /\
         return_exception_typed env_exn ret_ty exn) /\
  state_well_typed stfinal /\
  accounts_well_typed stfinal.accounts /\
  env_consistent env cx stfinal ==>
  state_well_typed stfinal /\
  accounts_well_typed stfinal.accounts /\
  env_consistent env cx stfinal /\
  no_type_error_result (INR (ReturnException v)) /\
  return_exception_typed env ret_ty (ReturnException v)
Proof
  strip_tac >> gvs[] >>
  conj_tac >- fs[no_type_error_result_def] >>
  irule return_exception_typed_extend_local_env_extends >>
  qexists_tac `F` >> qexists_tac `env_exn` >>
  qexists_tac `id` >> qexists_tac `ty` >>
  simp[]
QED

Theorem for_cons_ordinary_exception_return_exception_typed_from_case:
  (case (INR (ReturnException v) : value + vyperState$exception) of
   | INL (u:value) => env_consistent env_after cx st_body
   | INR exn =>
       ?env_exn.
         env_extends (extend_local env id ty F) env_exn /\
         env_consistent env_exn cx st_body /\
         return_exception_typed env_exn ret_ty exn) ==>
  return_exception_typed env ret_ty (ReturnException v)
Proof
  strip_tac >> gvs[] >>
  irule return_exception_typed_extend_local_env_extends >>
  qexists_tac `F` >> qexists_tac `env_exn` >>
  qexists_tac `id` >> qexists_tac `ty` >> simp[]
QED

Theorem for_cons_ordinary_exception_full_suffix_from_case_bundle:
  no_type_error_result (INR y) /\
  (case (INR y : value + vyperState$exception) of
   | INL (u:value) => env_consistent env_after cx st_body
   | INR exn =>
       ?env_exn.
         env_extends (extend_local env id ty F) env_exn /\
         env_consistent env_exn cx st_body /\
         return_exception_typed env_exn ret_ty exn) /\
  state_well_typed stfinal /\
  accounts_well_typed stfinal.accounts /\
  env_consistent env cx stfinal ==>
  state_well_typed stfinal /\
  accounts_well_typed stfinal.accounts /\
  env_consistent env cx stfinal /\
  no_type_error_result (INR y) /\
  (case INR y of INL v => T | INR exn => return_exception_typed env ret_ty exn)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[] >>
  conj_tac >- fs[no_type_error_result_def] >>
  irule for_cons_ordinary_exception_return_typed_from_INR_witness >>
  qexists_tac `cx` >> qexists_tac `id` >> qexists_tac `st_body` >>
  qexists_tac `ty` >> qexists_tac `env_exn` >> simp[]
QED

Theorem for_cons_ordinary_exception_residual_from_case_premise:
  no_type_error_result (INR y) ==>
  (case (INR y : value + vyperState$exception) of
   | INL (u:value) => env_consistent env_after cx st_body
   | INR exn =>
       ?env_exn.
         env_extends (extend_local env id ty F) env_exn /\
         env_consistent env_exn cx st_body /\
         return_exception_typed env_exn ret_ty exn) ==>
  no_type_error_result (INR y) /\
  ?id' stbody ty' env_exn.
    env_extends (extend_local env id' ty' F) env_exn /\
    env_consistent env_exn cx stbody /\
    return_exception_typed env_exn ret_ty y
Proof
  rw[no_type_error_result_def] >> metis_tac[]
QED

Theorem for_cons_ordinary_exception_full_suffix_from_case_bundle_direct:
  no_type_error_result (INR y) ==>
  (case (INR y : value + vyperState$exception) of
   | INL (u:value) => env_consistent env_after cx st_body
   | INR exn =>
       ?env_exn.
         env_extends (extend_local env id ty F) env_exn /\
         env_consistent env_exn cx st_body /\
         return_exception_typed env_exn ret_ty exn) ==>
  state_well_typed stfinal ==>
  accounts_well_typed stfinal.accounts ==>
  env_consistent env cx stfinal ==>
  state_well_typed stfinal /\
  accounts_well_typed stfinal.accounts /\
  env_consistent env cx stfinal /\
  no_type_error_result (INR y) /\
  (case INR y of INL v => T | INR exn => return_exception_typed env ret_ty exn)
Proof
  rpt gen_tac >> strip_tac >> strip_tac >> ntac 3 strip_tac >>
  irule for_cons_ordinary_exception_full_suffix_from_case_bundle >>
  simp[] >>
  metis_tac[for_cons_ordinary_exception_residual_from_case_premise]
QED

Theorem for_cons_ordinary_exception_full_suffix_from_residual_bundle:
  (?id' st_body' ty' env_exn.
     env_extends (extend_local env id' ty' F) env_exn /\
     env_consistent env_exn cx st_body' /\
     return_exception_typed env_exn ret_ty y) /\
  no_type_error_result (INR y) /\
  state_well_typed stfinal /\
  accounts_well_typed stfinal.accounts /\
  env_consistent env cx stfinal ==>
  state_well_typed stfinal /\
  accounts_well_typed stfinal.accounts /\
  env_consistent env cx stfinal /\
  no_type_error_result (INR y) /\
  (case INR y of INL v => T | INR exn => return_exception_typed env ret_ty exn)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[] >>
  conj_tac >- fs[no_type_error_result_def] >>
  irule for_cons_ordinary_exception_return_typed_from_INR_witness >>
  qexists_tac `cx` >> qexists_tac `id'` >> qexists_tac `st_body'` >>
  qexists_tac `ty'` >> qexists_tac `env_exn` >> simp[]
QED
Theorem for_cons_return_exception_typed_from_body_ex:
  (∃env_exn.
     env_extends (extend_local env id ty F) env_exn /\
     env_consistent env_exn cx stbody /\
     return_exception_typed env_exn ret_ty exn) ==>
  return_exception_typed env ret_ty exn
Proof
  rw[] >>
  irule return_exception_typed_extend_local_env_extends >>
  qexists_tac `F` >>
  qexists_tac `env_exn` >>
  qexists_tac `id` >>
  qexists_tac `ty` >>
  simp[]
QED

Theorem for_cons_body_exception_typed_from_body_soundness:
  (!stp res_body st_body.
    env_consistent (extend_local env id ty F) cx stp /\
    state_well_typed stp /\ accounts_well_typed stp.accounts /\
    eval_stmts cx body_stmts stp = (res_body, st_body) ==>
    state_well_typed st_body /\ accounts_well_typed st_body.accounts /\
    no_type_error_result res_body /\
    case res_body of
    | INL _ => env_consistent env_after cx st_body
    | INR exn => ?env_exn.
        env_extends (extend_local env id ty F) env_exn /\
        env_consistent env_exn cx st_body /\
        return_exception_typed env_exn ret_ty exn) /\
  env_consistent (extend_local env id ty F) cx stp /\
  state_well_typed stp /\ accounts_well_typed stp.accounts /\
  eval_stmts cx body_stmts stp = (INR exn, st_body) ==>
  return_exception_typed env ret_ty exn
Proof
  strip_tac >>
  qpat_x_assum `!stp res_body st_body.
       env_consistent (extend_local env id ty F) cx stp /\
       state_well_typed stp /\ accounts_well_typed stp.accounts /\
       eval_stmts cx body_stmts stp = (res_body,st_body) ==> _`
    (qspecl_then [`stp`, `INR exn`, `st_body`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> gvs[] >>
  irule for_cons_return_exception_typed_from_body_ex >>
  qexists_tac `cx` >> qexists_tac `id` >> qexists_tac `st_body` >>
  qexists_tac `ty` >> qexists_tac `env_exn` >> simp[]
QED

Theorem for_cons_body_result_return_exception_typed:
  state_well_typed st_body /\
  accounts_well_typed st_body.accounts /\
  no_type_error_result (INR (ReturnException v)) /\
  (case (INR (ReturnException v) : value + vyperState$exception) of
   | INL u => env_consistent env_after cx st_body
   | INR exn =>
       ?env_exn.
         env_extends (extend_local env id ty F) env_exn /\
         env_consistent env_exn cx st_body /\
         return_exception_typed env_exn ret_ty exn) ==>
  return_exception_typed env ret_ty (ReturnException v)
Proof
  strip_tac >> gvs[] >>
  irule return_exception_typed_extend_local_env_extends >>
  qexists_tac `F` >> qexists_tac `env_exn` >>
  qexists_tac `id` >> qexists_tac `ty` >> simp[]
QED

Theorem for_cons_body_result_return_exception_typed_case:
  state_well_typed st_body ==>
  accounts_well_typed st_body.accounts ==>
  no_type_error_result (INR (ReturnException v)) ==>
  (case (INR (ReturnException v) : value + vyperState$exception) of
   | INL u => env_consistent env_after cx st_body
   | INR exn =>
       ?env_exn.
         env_extends (extend_local env id ty F) env_exn /\
         env_consistent env_exn cx st_body /\
         return_exception_typed env_exn ret_ty exn) ==>
  return_exception_typed env ret_ty (ReturnException v)
Proof
  rpt strip_tac >>
  irule for_cons_body_result_return_exception_typed >>
  rpt conj_tac >> simp[] >>
  qexists_tac `cx` >> qexists_tac `id` >> qexists_tac `st_body` >>
  qexists_tac `ty` >> simp[] >>
  qpat_x_assum `case INR (ReturnException v) of INL u => _ | INR exn => _` mp_tac >>
  pure_rewrite_tac[sum_case_def] >>
  BETA_TAC >>
  strip_tac >>
  qexists_tac `env_exn` >> simp[]
QED

Theorem for_cons_body_result_return_exception_case_exn:
  !env env_after cx id ty st_body ret_ty v.
    (case (INR (ReturnException v) : value + vyperState$exception) of
     | INL u => env_consistent env_after cx st_body
     | INR exn =>
         ?env_exn.
           env_extends (extend_local env id ty F) env_exn /\
           env_consistent env_exn cx st_body /\
           return_exception_typed env_exn ret_ty exn) ==>
    ?env_exn.
      env_extends (extend_local env id ty F) env_exn /\
      env_consistent env_exn cx st_body /\
      return_exception_typed env_exn ret_ty (ReturnException v)
Proof
  simp[sum_case_def]
QED

Theorem for_cons_body_result_return_exception_typed_exn_spec:
  !env cx id ty st_body ret_ty v.
    state_well_typed st_body ==>
    accounts_well_typed st_body.accounts ==>
    no_type_error_result (INR (ReturnException v)) ==>
    (?env_exn.
       env_extends (extend_local env id ty F) env_exn /\
       env_consistent env_exn cx st_body /\
       return_exception_typed env_exn ret_ty (ReturnException v)) ==>
    return_exception_typed env ret_ty (ReturnException v)
Proof
  rpt strip_tac >>
  irule return_exception_typed_extend_local_env_extends >>
  qexists_tac `F` >> qexists_tac `env_exn` >>
  qexists_tac `id` >> qexists_tac `ty` >> simp[]
QED

Theorem for_cons_body_result_return_exception_typed_case_spec:
  !env env_after cx id ty st_body ret_ty v.
    state_well_typed st_body ==>
    accounts_well_typed st_body.accounts ==>
    no_type_error_result (INR (ReturnException v)) ==>
    (case (INR (ReturnException v) : value + vyperState$exception) of
     | INL u => env_consistent env_after cx st_body
     | INR exn =>
         ?env_exn.
           env_extends (extend_local env id ty F) env_exn /\
           env_consistent env_exn cx st_body /\
           return_exception_typed env_exn ret_ty exn) ==>
    return_exception_typed env ret_ty (ReturnException v)
Proof
  rpt strip_tac >>
  irule for_cons_body_result_return_exception_typed >>
  rpt conj_tac >> simp[] >>
  qexists_tac `cx` >> qexists_tac `id` >> qexists_tac `st_body` >>
  qexists_tac `ty` >> simp[] >>
  qpat_x_assum `case INR (ReturnException v) of INL u => _ | INR exn => _` mp_tac >>
  pure_rewrite_tac[sum_case_def] >>
  BETA_TAC >>
  strip_tac >>
  qexists_tac `env_exn` >> simp[]
QED

Theorem for_cons_body_ih_return_exception_typed:
  !env env_after cx id ty ret_ty body_stmts stp st_body v.
    state_well_typed stp ==>
    accounts_well_typed stp.accounts ==>
    env_consistent (extend_local env id ty F) cx stp ==>
    eval_stmts cx body_stmts stp = (INR (ReturnException v), st_body) ==>
    (!stp0 res_body st_body0.
       env_consistent (extend_local env id ty F) cx stp0 /\
       state_well_typed stp0 /\
       accounts_well_typed stp0.accounts /\
       eval_stmts cx body_stmts stp0 = (res_body, st_body0) ==>
       state_well_typed st_body0 /\
       accounts_well_typed st_body0.accounts /\
       no_type_error_result res_body /\
       (case res_body of
        | INL u => env_consistent env_after cx st_body0
        | INR exn =>
            ?env_exn.
              env_extends (extend_local env id ty F) env_exn /\
              env_consistent env_exn cx st_body0 /\
              return_exception_typed env_exn ret_ty exn)) ==>
    return_exception_typed env ret_ty (ReturnException v)
Proof
  rpt strip_tac >>
  qpat_x_assum `!stp0 res_body st_body0.
       env_consistent (extend_local env id ty F) cx stp0 /\
       state_well_typed stp0 /\
       accounts_well_typed stp0.accounts /\
       eval_stmts cx body_stmts stp0 = (res_body,st_body0) ==> _`
    (qspecl_then [`stp`, `INR (ReturnException v)`, `st_body`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> gvs[sum_case_def, no_type_error_result_def] >>
  irule return_exception_typed_extend_local_env_extends >>
  qexists_tac `F` >> qexists_tac `env_exn` >>
  qexists_tac `id` >> qexists_tac `ty` >> simp[]
QED

Theorem for_cons_return_exception_suffix:
  !env env_after cx id ty ret_ty body_stmts stp st_body v.
    state_well_typed (st_body with scopes := TL st_body.scopes) /\
    accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
    env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
    state_well_typed stp /\
    accounts_well_typed stp.accounts /\
    env_consistent (extend_local env id ty F) cx stp /\
    eval_stmts cx body_stmts stp = (INR (ReturnException v), st_body) /\
    (!stp0 res_body st_body0.
       env_consistent (extend_local env id ty F) cx stp0 /\
       state_well_typed stp0 /\
       accounts_well_typed stp0.accounts /\
       eval_stmts cx body_stmts stp0 = (res_body, st_body0) ==>
       state_well_typed st_body0 /\
       accounts_well_typed st_body0.accounts /\
       no_type_error_result res_body /\
       (case res_body of
        | INL u => env_consistent env_after cx st_body0
        | INR exn =>
            ?env_exn.
              env_extends (extend_local env id ty F) env_exn /\
              env_consistent env_exn cx st_body0 /\
              return_exception_typed env_exn ret_ty exn)) ==>
    state_well_typed (st_body with scopes := TL st_body.scopes) /\
    accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
    env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
    no_type_error_result (INR (ReturnException v)) /\
    (case (INR (ReturnException v) : unit + vyperState$exception) of
     | INL _ => T
     | INR exn => return_exception_typed env ret_ty exn)
Proof
  rpt strip_tac >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- simp[no_type_error_result_def] >>
  simp[sum_case_def] >>
  qspecl_then [`env`, `env_after`, `cx`, `id`, `ty`, `ret_ty`,
               `body_stmts`, `stp`, `st_body`, `v`] mp_tac
    for_cons_body_ih_return_exception_typed >>
  rpt (impl_tac >- (first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

Theorem for_cons_body_ih_same_shape:
  !env env_after cx id ty ret_ty body_stmts.
    (!stp res_body st_body.
       env_consistent (extend_local env id ty F) cx stp /\
       state_well_typed stp /\
       accounts_well_typed stp.accounts /\
       eval_stmts cx body_stmts stp = (res_body, st_body) ==>
       state_well_typed st_body /\
       accounts_well_typed st_body.accounts /\
       no_type_error_result res_body /\
       (case res_body of
        | INL v => env_consistent env_after cx st_body
        | INR exn =>
            ?env_exn.
              env_extends (extend_local env id ty F) env_exn /\
              env_consistent env_exn cx st_body /\
              return_exception_typed env_exn ret_ty exn)) ==>
    (!stp0 res_body st_body0.
       env_consistent (extend_local env id ty F) cx stp0 /\
       state_well_typed stp0 /\
       accounts_well_typed stp0.accounts /\
       eval_stmts cx body_stmts stp0 = (res_body, st_body0) ==>
       state_well_typed st_body0 /\
       accounts_well_typed st_body0.accounts /\
       no_type_error_result res_body /\
       (case res_body of
        | INL u => env_consistent env_after cx st_body0
        | INR exn0 =>
            ?env_exn.
              env_extends (extend_local env id ty F) env_exn /\
              env_consistent env_exn cx st_body0 /\
              return_exception_typed env_exn ret_ty exn0))
Proof
  metis_tac[sum_case_def]
QED

Theorem for_cons_body_ih_exception_projection:
  !env env_after cx id ty ret_ty body_stmts stp st_body exn.
    state_well_typed stp /\
    accounts_well_typed stp.accounts /\
    env_consistent (extend_local env id ty F) cx stp /\
    eval_stmts cx body_stmts stp = (INR exn, st_body) /\
    (!stp0 res_body st_body0.
       env_consistent (extend_local env id ty F) cx stp0 /\
       state_well_typed stp0 /\
       accounts_well_typed stp0.accounts /\
       eval_stmts cx body_stmts stp0 = (res_body, st_body0) ==>
       state_well_typed st_body0 /\
       accounts_well_typed st_body0.accounts /\
       no_type_error_result res_body /\
       (case res_body of
        | INL u => env_consistent env_after cx st_body0
        | INR exn0 =>
            ?env_exn.
              env_extends (extend_local env id ty F) env_exn /\
              env_consistent env_exn cx st_body0 /\
              return_exception_typed env_exn ret_ty exn0)) ==>
    state_well_typed st_body /\
    accounts_well_typed st_body.accounts /\
    no_type_error_result (INR exn) /\
    (case (INR exn : unit + vyperState$exception) of
     | INL u => env_consistent env_after cx st_body
     | INR exn0 =>
         ?env_exn.
           env_extends (extend_local env id ty F) env_exn /\
           env_consistent env_exn cx st_body /\
           return_exception_typed env_exn ret_ty exn0)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!stp0 res_body st_body0.
       env_consistent (extend_local env id ty F) cx stp0 /\
       state_well_typed stp0 /\
       accounts_well_typed stp0.accounts /\
       eval_stmts cx body_stmts stp0 = (res_body,st_body0) ==> _`
    (qspecl_then [`stp`, `INR exn`, `st_body`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  rpt conj_tac
  >- simp[]
  >- simp[]
  >- fs[no_type_error_result_def] >>
  simp[]
QED

Theorem for_cons_non_loop_exception_suffix:
  !env env_after cx id ty ret_ty body_stmts stp st_body exn.
    state_well_typed (st_body with scopes := TL st_body.scopes) /\
    accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
    env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
    state_well_typed stp /\
    accounts_well_typed stp.accounts /\
    env_consistent (extend_local env id ty F) cx stp /\
    eval_stmts cx body_stmts stp = (INR exn, st_body) /\
    exn <> ContinueException /\
    exn <> BreakException /\
    (!stp0 res_body st_body0.
       env_consistent (extend_local env id ty F) cx stp0 /\
       state_well_typed stp0 /\
       accounts_well_typed stp0.accounts /\
       eval_stmts cx body_stmts stp0 = (res_body, st_body0) ==>
       state_well_typed st_body0 /\
       accounts_well_typed st_body0.accounts /\
       no_type_error_result res_body /\
       (case res_body of
        | INL u => env_consistent env_after cx st_body0
        | INR exn0 =>
            ?env_exn.
              env_extends (extend_local env id ty F) env_exn /\
              env_consistent env_exn cx st_body0 /\
              return_exception_typed env_exn ret_ty exn0)) ==>
    state_well_typed (st_body with scopes := TL st_body.scopes) /\
    accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
    env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
    no_type_error_result (INR exn) /\
    (case (INR exn : unit + vyperState$exception) of
     | INL _ => T
     | INR exn0 => return_exception_typed env ret_ty exn0)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`env`, `env_after`, `cx`, `id`, `ty`, `ret_ty`,
               `body_stmts`, `stp`, `st_body`, `exn`] mp_tac
    for_cons_body_ih_exception_projection >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  gvs[sum_case_def, no_type_error_result_def] >>
  irule return_exception_typed_extend_local_env_extends >>
  qexists_tac `F` >> qexists_tac `env_exn` >>
  qexists_tac `id` >> qexists_tac `ty` >> simp[]
QED

Theorem for_cons_non_loop_exception_suffix_projected_explicit:
  !env cx id ty ret_ty st_body exn env_exn.
    state_well_typed (st_body with scopes := TL st_body.scopes) /\
    accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
    env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
    no_type_error_result (INR exn) /\
    env_extends (extend_local env id ty F) env_exn /\
    env_consistent env_exn cx st_body /\
    return_exception_typed env_exn ret_ty exn ==>
    state_well_typed (st_body with scopes := TL st_body.scopes) /\
    accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
    env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
    no_type_error_result (INR exn) /\
    (case (INR exn : unit + vyperState$exception) of
     | INL _ => T
     | INR exn0 => return_exception_typed env ret_ty exn0)
Proof
  metis_tac[for_cons_ordinary_exception_conclusion, sum_case_def]
QED

Theorem for_cons_non_loop_exception_suffix_projected:
  !env env_after cx id ty ret_ty st_body exn.
    state_well_typed (st_body with scopes := TL st_body.scopes) /\
    accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
    env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
    no_type_error_result (INR exn) /\
    (case (INR exn : unit + vyperState$exception) of
     | INL u => env_consistent env_after cx st_body
     | INR exn0 =>
         ?env_exn.
           env_extends (extend_local env id ty F) env_exn /\
           env_consistent env_exn cx st_body /\
           return_exception_typed env_exn ret_ty exn0) ==>
    state_well_typed (st_body with scopes := TL st_body.scopes) /\
    accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
    env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
    no_type_error_result (INR exn) /\
    (case (INR exn : unit + vyperState$exception) of
     | INL _ => T
     | INR exn0 => return_exception_typed env ret_ty exn0)
Proof
  rpt strip_tac >>
  gvs[sum_case_def] >>
  qspecl_then [`env`,`cx`,`id`,`ty`,`ret_ty`,`st_body`,`exn`,`env_exn`] mp_tac
    for_cons_non_loop_exception_suffix_projected_explicit >>
  simp[]
QED

Theorem for_cons_body_exception_case_premise_transport:
  !env env_after cx id ty ret_ty st_body y.
    (case (INR y : unit + vyperState$exception) of
       INL v => env_consistent env_after cx st_body
     | INR exn =>
         ?env_exn.
           env_extends (extend_local env id ty F) env_exn /\
           env_consistent env_exn cx st_body /\
           return_exception_typed env_exn ret_ty exn) ==>
    (case (INR y : unit + vyperState$exception) of
       INL u => env_consistent env_after cx st_body
     | INR exn0 =>
         ?env_exn.
           env_extends (extend_local env id ty F) env_exn /\
           env_consistent env_exn cx st_body /\
           return_exception_typed env_exn ret_ty exn0)
Proof
  simp[sum_case_def]
QED

Theorem for_cons_body_ih_conclusion_transport:
  !env env_after cx id ty ret_ty res_body st_body0.
    state_well_typed st_body0 /\
    accounts_well_typed st_body0.accounts /\
    no_type_error_result res_body /\
    (case res_body of
     | INL v => env_consistent env_after cx st_body0
     | INR exn =>
         ?env_exn.
           env_extends (extend_local env id ty F) env_exn /\
           env_consistent env_exn cx st_body0 /\
           return_exception_typed env_exn ret_ty exn) ==>
    state_well_typed st_body0 /\
    accounts_well_typed st_body0.accounts /\
    no_type_error_result res_body /\
    (case res_body of
     | INL u => env_consistent env_after cx st_body0
     | INR exn0 =>
         ?env_exn.
           env_extends (extend_local env id ty F) env_exn /\
           env_consistent env_exn cx st_body0 /\
           return_exception_typed env_exn ret_ty exn0)
Proof
  rpt gen_tac >> strip_tac >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- qpat_assum `accounts_well_typed st_body0.accounts` ACCEPT_TAC
  >- first_assum ACCEPT_TAC >>
  Cases_on `res_body` >> gvs[] >>
  qexists `env_exn` >> simp[]
QED

Theorem for_cons_body_ih_premise_transport:
  !env env_after cx id ty ret_ty body_stmts.
    (!stp0 res_body st_body0.
       env_consistent (extend_local env id ty F) cx stp0 /\
       state_well_typed stp0 /\
       accounts_well_typed stp0.accounts /\
       eval_stmts cx body_stmts stp0 = (res_body,st_body0) ==>
       state_well_typed st_body0 /\
       accounts_well_typed st_body0.accounts /\
       no_type_error_result res_body /\
       (case res_body of
        | INL v => env_consistent env_after cx st_body0
        | INR exn =>
            ?env_exn.
              env_extends (extend_local env id ty F) env_exn /\
              env_consistent env_exn cx st_body0 /\
              return_exception_typed env_exn ret_ty exn)) ==>
    (!stp0 res_body st_body0.
       env_consistent (extend_local env id ty F) cx stp0 /\
       state_well_typed stp0 /\
       accounts_well_typed stp0.accounts /\
       eval_stmts cx body_stmts stp0 = (res_body,st_body0) ==>
       state_well_typed st_body0 /\
       accounts_well_typed st_body0.accounts /\
       no_type_error_result res_body /\
       (case res_body of
        | INL u => env_consistent env_after cx st_body0
        | INR exn0 =>
            ?env_exn.
              env_extends (extend_local env id ty F) env_exn /\
              env_consistent env_exn cx st_body0 /\
              return_exception_typed env_exn ret_ty exn0))
Proof
  rpt strip_tac >>
  first_x_assum (qspecl_then [`stp0`, `res_body`, `st_body0`] mp_tac) >>
  simp[] >>
  metis_tac[for_cons_body_ih_conclusion_transport]
QED


Theorem for_body_env_extends_consistent_after_pop:
  env_maps_wf env /\
  env_consistent env cx st /\
  id NOTIN FDOM env.var_types /\
  env_extends (extend_local env id ty F) env_body /\
  env_consistent env_body cx st_body /\
  eval_stmts cx body_stmts
    (st with scopes updated_by CONS
       (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>))) =
    (res, st_body) ==>
  env_consistent env cx (st_body with scopes := TL st_body.scopes)
Proof
  strip_tac >>
  Cases_on `st_body.scopes` >> gvs[]
  >- (drule eval_stmts_preserves_scopes_len >> simp[] >>
      fs[env_consistent_def, env_scopes_consistent_def]) >>
  rename1 `st_body.scopes = h::tl` >>
  irule env_extends_env_consistent_after_pop >> simp[] >>
  conj_tac >- (
    drule eval_stmts_preserves_scopes_len >> simp[] >> strip_tac >>
    fs[env_consistent_def, env_scopes_consistent_def] >>
    Cases_on `st.scopes` >> gvs[] >>
    Cases_on `tl` >> gvs[]) >>
  conj_tac >- (
    conj_tac >> rpt strip_tac
    >- (irule scope_bracket_var_type_head_none >>
        qexists_tac `cx` >> qexists_tac `env` >> qexists_tac `res` >>
        qexists_tac `FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)` >>
        qexists_tac `body_stmts` >> qexists_tac `st` >> qexists_tac `st_body` >>
        qexists_tac `tl` >> qexists_tac `ty'` >>
        simp[FLOOKUP_UPDATE, FDOM_FUPDATE]) >>
    `IS_SOME (FLOOKUP env.var_types id')` by fs[env_maps_wf_def] >>
    Cases_on `FLOOKUP env.var_types id'` >> gvs[] >>
    irule scope_bracket_var_type_head_none >>
    qexists_tac `cx` >> qexists_tac `env` >> qexists_tac `res` >>
    qexists_tac `FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)` >>
    qexists_tac `body_stmts` >> qexists_tac `st` >> qexists_tac `st_body` >>
    qexists_tac `tl` >> qexists_tac `x` >>
    simp[FLOOKUP_UPDATE, FDOM_FUPDATE]) >>
  conj_tac >- (
    qexists_tac `env_body` >> simp[] >>
    conj_tac >- (
      rpt strip_tac >>
      irule scope_bracket_new_var_tail_none >>
      qexists_tac `cx` >> qexists_tac `env` >> qexists_tac `h` >>
      qexists_tac `res` >>
      qexists_tac `FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)` >>
      qexists_tac `body_stmts` >> qexists_tac `st` >> qexists_tac `st_body` >> simp[]) >>
    irule env_extends_trans >>
    qexists_tac `extend_local env id ty F` >> simp[] >>
    irule extend_local_F_env_extends >> simp[]) >>
  qexists_tac `st` >> simp[] >>
  `st_body with scopes := tl =
   st_body with scopes := TL st_body.scopes` by simp[] >>
  pop_assum SUBST1_TAC >>
  irule eval_stmts_scope_bracket_gen_preserves_tv >> simp[] >>
  qexists_tac `res` >>
  qexists_tac `FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)` >>
  qexists_tac `body_stmts` >> simp[] >>
  irule (cj 2 eval_preserves_tv) >>
  qexists_tac `res` >> qexists_tac `body_stmts` >> simp[]
QED


Theorem for_cons_ordinary_exception_tail_conclusion:
  stp = st with scopes updated_by
          CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)) /\
  eval_stmts cx body_stmts stp = (INR exn, st_body) /\
  env_maps_wf env /\
  env_consistent env cx st /\
  id NOTIN FDOM env.var_types /\
  state_well_typed st_body /\
  accounts_well_typed st_body.accounts /\
  no_type_error_result (INR exn) /\
  env_extends (extend_local env id ty F) env_exn /\
  env_consistent env_exn cx st_body /\
  return_exception_typed env_exn ret_ty exn ==>
  state_well_typed (st_body with scopes := TL st_body.scopes) /\
  accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
  env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
  no_type_error_result (INR exn) /\
  return_exception_typed env ret_ty exn
Proof
  strip_tac >>
  qpat_x_assum `stp = _` SUBST_ALL_TAC >>
  `state_well_typed (st_body with scopes := TL st_body.scopes)` by (
    irule scope_bracket_preserves_swt >> simp[] >>
    qexists_tac `cx` >> qexists_tac `INR exn` >>
    qexists_tac `FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)` >>
    qexists_tac `body_stmts` >> qexists_tac `st` >> simp[]) >>
  `accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts` by
    simp[evaluation_state_component_equality] >>
  `env_consistent env cx (st_body with scopes := TL st_body.scopes)` by (
    irule for_body_env_extends_consistent_after_pop >> simp[] >>
    qexists_tac `body_stmts` >> qexists_tac `env_exn` >>
    qexists_tac `id` >> qexists_tac `INR exn` >> qexists_tac `st` >>
    qexists_tac `ty` >> qexists_tac `tyv` >> qexists_tac `v` >> simp[]) >>
  irule for_cons_ordinary_exception_conclusion >>
  simp[] >>
  qexists_tac `env_exn` >> simp[] >>
  qexists_tac `id` >> qexists_tac `ty` >> simp[]
QED

Theorem for_cons_ordinary_exception_tail_exists:
  stp = st with scopes updated_by
          CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)) /\
  eval_stmts cx body_stmts stp = (INR exn, st_body) /\
  env_maps_wf env /\
  env_consistent env cx st /\
  id NOTIN FDOM env.var_types /\
  state_well_typed st_body /\
  accounts_well_typed st_body.accounts /\
  no_type_error_result (INR exn) /\
  (∃env_exn.
     env_extends (extend_local env id ty F) env_exn /\
     env_consistent env_exn cx st_body /\
     return_exception_typed env_exn ret_ty exn) ==>
  state_well_typed (st_body with scopes := TL st_body.scopes) /\
  accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
  env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
  no_type_error_result (INR exn) /\
  return_exception_typed env ret_ty exn
Proof
  strip_tac >>
  qpat_x_assum `stp = _` SUBST_ALL_TAC >>
  irule for_cons_ordinary_exception_tail_conclusion >>
  simp[] >>
  qexists_tac `body_stmts` >> qexists_tac `env_exn` >> qexists_tac `id` >>
  qexists_tac `st` >> qexists_tac `ty` >> qexists_tac `tyv` >>
  qexists_tac `v` >> simp[]
QED

Theorem for_cons_ordinary_exception_tail_exists_forward:
  eval_stmts cx body_stmts stp = (INR exn, st_body) ==>
  stp = st with scopes updated_by
          CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)) ==>
  env_maps_wf env ==>
  env_consistent env cx st ==>
  id NOTIN FDOM env.var_types ==>
  state_well_typed st_body ==>
  accounts_well_typed st_body.accounts ==>
  no_type_error_result (INR exn) ==>
  (∃env_exn.
     env_extends (extend_local env id ty F) env_exn /\
     env_consistent env_exn cx st_body /\
     return_exception_typed env_exn ret_ty exn) ==>
  state_well_typed (st_body with scopes := TL st_body.scopes) /\
  accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
  env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
  no_type_error_result (INR exn) /\
  return_exception_typed env ret_ty exn
Proof
  ntac 8 strip_tac >> disch_tac >>
  qpat_x_assum `stp = _` SUBST_ALL_TAC >>
  irule for_cons_ordinary_exception_tail_exists >>
  simp[] >>
  qexists_tac `body_stmts` >> qexists_tac `id` >> qexists_tac `st` >>
  qexists_tac `ty` >> qexists_tac `tyv` >> qexists_tac `v` >> simp[]
QED

Theorem for_cons_popped_env_consistent_from_stmt_case:
  (case (INR exn : unit + vyperState$exception) of
   | INL u => inl_post u
   | INR exn0 =>
       ?env_exn.
         env_extends (extend_local env id ty F) env_exn /\
         env_consistent env_exn cx st_body /\
         return_exception_typed env_exn ret_ty exn0) ==>
  env_consistent env cx st ==>
  id NOTIN FDOM env.var_types ==>
  eval_stmts cx body_stmts
    (st with scopes updated_by CONS
       (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>))) =
    (INR exn, st_body) ==>
  env_consistent env cx (st_body with scopes := TL st_body.scopes)
Proof
  simp[] >> rpt strip_tac >>
  irule for_body_env_extends_consistent_after_pop >> simp[] >>
  conj_tac >- metis_tac[env_consistent_env_maps_wf] >>
  qexists_tac `body_stmts` >> qexists_tac `env_exn` >>
  qexists_tac `id` >> qexists_tac `INR exn` >> qexists_tac `st` >>
  qexists_tac `ty` >> qexists_tac `tyv` >> qexists_tac `v` >> simp[]
QED
Theorem for_cons_inr_case_premise_extract:
  (case (INR y : value + vyperState$exception) of
   | INL v => env_consistent env_after cx st_body
   | INR exn =>
       ?env_exn.
         env_extends (extend_local env id ty F) env_exn /\
         env_consistent env_exn cx st_body /\
         return_exception_typed env_exn ret_ty exn) ==>
  ?env_exn.
    env_extends (extend_local env id ty F) env_exn /\
    env_consistent env_exn cx st_body /\
    return_exception_typed env_exn ret_ty y
Proof
  simp[]
QED

Theorem for_cons_ordinary_exception_tail_goal_from_case_premise:
  no_type_error_result (INR y) /\
  (case (INR y : value + vyperState$exception) of
   | INL v => env_consistent env_after cx st_body
   | INR exn =>
       ?env_exn.
         env_extends (extend_local env id ty F) env_exn /\
         env_consistent env_exn cx st_body /\
         return_exception_typed env_exn ret_ty exn) ==>
  no_type_error_result (INR y) /\
  ?id' st_body' ty' env_exn.
    env_extends (extend_local env id' ty' F) env_exn /\
    env_consistent env_exn cx st_body' /\
    return_exception_typed env_exn ret_ty y
Proof
  simp[] >> strip_tac >>
  conj_tac >- fs[no_type_error_result_def] >>
  qexists_tac `id` >> qexists_tac `st_body` >> qexists_tac `ty` >>
  qexists_tac `env_exn` >> simp[]
QED

Theorem for_cons_ordinary_exception_tail_goal_from_case_premise_exists_first:
  no_type_error_result (INR y) /\
  (case (INR y : value + vyperState$exception) of
   | INL v => env_consistent env_after cx st_body
   | INR exn =>
       ?env_exn.
         env_extends (extend_local env id ty F) env_exn /\
         env_consistent env_exn cx st_body /\
         return_exception_typed env_exn ret_ty exn) ==>
  (?id' st_body' ty' env_exn.
     env_extends (extend_local env id' ty' F) env_exn /\
     env_consistent env_exn cx st_body' /\
     return_exception_typed env_exn ret_ty y) /\
  no_type_error_result (INR y)
Proof
  simp[] >> strip_tac >>
  conj_tac >- (
    qexists_tac `id` >> qexists_tac `st_body` >> qexists_tac `ty` >>
    qexists_tac `env_exn` >> simp[]) >>
  fs[no_type_error_result_def]
QED

Theorem for_cons_ordinary_exception_witness_goal_from_case_premise:
  (case (INR y : value + vyperState$exception) of
   | INL v => env_consistent env_after cx st_body
   | INR exn =>
       ?env_exn.
         env_extends (extend_local env id ty F) env_exn /\
         env_consistent env_exn cx st_body /\
         return_exception_typed env_exn ret_ty exn) ==>
  ?id' st_body' ty' env_exn.
    env_extends (extend_local env id' ty' F) env_exn /\
    env_consistent env_exn cx st_body' /\
    return_exception_typed env_exn ret_ty y
Proof
  simp[] >> strip_tac >>
  qexists_tac `id` >> qexists_tac `st_body` >> qexists_tac `ty` >>
  qexists_tac `env_exn` >> simp[]
QED


Theorem for_cons_ordinary_exception_tail_from_stmt_case:
  (case (INR exn : unit + vyperState$exception) of
   | INL u => inl_post u
   | INR exn0 =>
       ?env_exn.
         env_extends (extend_local env id ty F) env_exn /\
         env_consistent env_exn cx st_body /\
         return_exception_typed env_exn ret_ty exn0) ==>
  state_well_typed stpopped ==>
  accounts_well_typed stpopped.accounts ==>
  env_consistent env cx stpopped ==>
  no_type_error_result (INR exn) ==>
  state_well_typed stpopped /\
  accounts_well_typed stpopped.accounts /\
  env_consistent env cx stpopped /\
  no_type_error_result (INR exn) /\
  (case INR exn of INL v => T | INR exn0 => return_exception_typed env ret_ty exn0)
Proof
  rw[no_type_error_result_def] >>
  metis_tac[return_exception_typed_extend_local_env_extends]
QED

Theorem for_cons_ordinary_exception_tail_conclusion_premises:
  eval_stmts cx body_stmts
    (st with scopes updated_by
       CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>))) =
    (INR exn, st_body) /\
  env_maps_wf env /\
  env_consistent env cx st /\
  id NOTIN FDOM env.var_types /\
  state_well_typed st_body /\
  accounts_well_typed st_body.accounts /\
  no_type_error_result (INR exn) /\
  env_extends (extend_local env id ty F) env_exn /\
  env_consistent env_exn cx st_body /\
  return_exception_typed env_exn ret_ty exn ==>
  state_well_typed (st_body with scopes := TL st_body.scopes) /\
  accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
  env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
  no_type_error_result (INR exn) /\
  return_exception_typed env ret_ty exn
Proof
  strip_tac >>
  irule for_cons_ordinary_exception_tail_conclusion >>
  simp[] >>
  qexists_tac `body_stmts` >> qexists_tac `env_exn` >> qexists_tac `id` >>
  qexists_tac `st` >> qexists_tac `ty` >> qexists_tac `tyv` >>
  qexists_tac `v` >> simp[]
QED

Theorem for_cons_ordinary_exception_tail_residual:
  eval_stmts cx body_stmts
    (st with scopes updated_by
       CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>))) =
    (INR exn, st_body) /\
  env_consistent env cx st /\
  id NOTIN FDOM env.var_types /\
  no_type_error_result (INR exn) /\
  env_extends (extend_local env id ty F) env_exn /\
  env_consistent env_exn cx st_body /\
  return_exception_typed env_exn ret_ty exn ==>
  no_type_error_result (INR exn) /\
  ∃body_stmts' env_exn' id' st' ty' tyv' v'.
    id' NOTIN FDOM env.var_types /\
    eval_stmts cx body_stmts'
      (st' with scopes updated_by
         CONS (FEMPTY |+ (id', <|assignable := F; type := tyv'; value := v'|>))) =
      (INR exn, st_body) /\
    env_extends (extend_local env id' ty' F) env_exn' /\
    env_consistent env cx st' /\
    env_consistent env_exn' cx st_body /\
    return_exception_typed env_exn' ret_ty exn
Proof
  strip_tac >>
  conj_tac >- (simp[no_type_error_result_def] >> gen_tac >> CCONTR_TAC >> gvs[no_type_error_result_def]) >>
  qexists_tac `body_stmts` >> qexists_tac `env_exn` >> qexists_tac `id` >>
  qexists_tac `st` >> qexists_tac `ty` >> qexists_tac `tyv` >>
  qexists_tac `v` >> simp[]
QED

Theorem for_cons_ordinary_exception_tail_residual_context:
  stp = st with scopes updated_by
          CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)) /\
  eval_stmts cx body_stmts stp = (INR exn, st_body) /\
  env_consistent env cx st /\
  id NOTIN FDOM env.var_types /\
  no_type_error_result (INR exn) /\
  env_extends (extend_local env id ty F) env_exn /\
  env_consistent env_exn cx st_body /\
  return_exception_typed env_exn ret_ty exn ==>
  no_type_error_result (INR exn) /\
  ∃body_stmts' env_exn' id' st' ty' tyv' v'.
    id' NOTIN FDOM env.var_types /\
    eval_stmts cx body_stmts'
      (st' with scopes updated_by
         CONS (FEMPTY |+ (id', <|assignable := F; type := tyv'; value := v'|>))) =
      (INR exn, st_body) /\
    env_extends (extend_local env id' ty' F) env_exn' /\
    env_consistent env cx st' /\
    env_consistent env_exn' cx st_body /\
    return_exception_typed env_exn' ret_ty exn
Proof
  strip_tac >>
  qpat_x_assum `stp = _` SUBST_ALL_TAC >>
  conj_tac >- (simp[no_type_error_result_def] >> gen_tac >> CCONTR_TAC >> gvs[no_type_error_result_def]) >>
  qexists_tac `body_stmts` >> qexists_tac `env_exn` >> qexists_tac `id` >>
  qexists_tac `st` >> qexists_tac `ty` >> qexists_tac `tyv` >>
  qexists_tac `v` >> simp[]
QED

Theorem for_cons_ordinary_exception_tail_residual_context_exists:
  stp = st with scopes updated_by
          CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)) /\
  eval_stmts cx body_stmts stp = (INR exn, st_body) /\
  env_consistent env cx st /\
  id NOTIN FDOM env.var_types /\
  no_type_error_result (INR exn) /\
  env_extends (extend_local env id ty F) env_exn /\
  env_consistent env_exn cx st_body /\
  return_exception_typed env_exn ret_ty exn ==>
  ∃body_stmts' env_exn' id' st' ty' tyv' v'.
    id' NOTIN FDOM env.var_types /\
    eval_stmts cx body_stmts'
      (st' with scopes updated_by
         CONS (FEMPTY |+ (id', <|assignable := F; type := tyv'; value := v'|>))) =
    (INR exn, st_body) /\
    env_extends (extend_local env id' ty' F) env_exn' /\
    env_consistent env cx st' /\
    env_consistent env_exn' cx st_body /\
    return_exception_typed env_exn' ret_ty exn
Proof
  strip_tac >>
  qpat_x_assum `stp = _` SUBST_ALL_TAC >>
  qexists_tac `body_stmts` >> qexists_tac `env_exn` >> qexists_tac `id` >>
  qexists_tac `st` >> qexists_tac `ty` >> qexists_tac `tyv` >>
  qexists_tac `v` >> simp[]
QED

Theorem for_cons_ordinary_exception_tail_residual_nested:
  eval_stmts cx body_stmts
    (st with scopes updated_by
       CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>))) =
    (INR exn, st_body) /\
  env_consistent env cx st /\
  id NOTIN FDOM env.var_types /\
  no_type_error_result (INR exn) /\
  (∃env_exn.
     env_extends (extend_local env id ty F) env_exn /\
     env_consistent env_exn cx st_body /\
     return_exception_typed env_exn ret_ty exn) ==>
  no_type_error_result (INR exn) /\
  ∃body_stmts' id' st' ty' tyv' v'.
    (∃env_exn.
       env_extends (extend_local env id' ty' F) env_exn /\
       env_consistent env_exn cx st_body /\
       return_exception_typed env_exn ret_ty exn) /\
    id' NOTIN FDOM env.var_types /\
    eval_stmts cx body_stmts'
      (st' with scopes updated_by
         CONS (FEMPTY |+ (id', <|assignable := F; type := tyv'; value := v'|>))) =
    (INR exn, st_body) /\
    env_consistent env cx st'
Proof
  metis_tac[for_cons_ordinary_exception_tail_residual]
QED

Theorem for_cons_ordinary_exception_tail_resume_nested_context:
  stp = st with scopes updated_by
          CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)) /\
  eval_stmts cx body_stmts stp = (INR exn, st_body) /\
  env_maps_wf env /\
  env_consistent env cx st /\
  id NOTIN FDOM env.var_types /\
  state_well_typed st_body /\
  accounts_well_typed st_body.accounts /\
  no_type_error_result (INR exn) /\
  (∃env_exn.
     env_extends (extend_local env id ty F) env_exn /\
     env_consistent env_exn cx st_body /\
     return_exception_typed env_exn ret_ty exn) ==>
  state_well_typed (st_body with scopes := TL st_body.scopes) /\
  accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
  env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
  no_type_error_result (INR exn) /\
  (∃body_stmts' id' st' ty' tyv' v'.
    (∃env_exn.
       env_extends (extend_local env id' ty' F) env_exn /\
       env_consistent env_exn cx st_body /\
       return_exception_typed env_exn ret_ty exn) /\
    id' NOTIN FDOM env.var_types /\
    eval_stmts cx body_stmts'
      (st' with scopes updated_by
         CONS (FEMPTY |+ (id', <|assignable := F; type := tyv'; value := v'|>))) =
    (INR exn, st_body) /\
    env_consistent env cx st') /\
  return_exception_typed env ret_ty exn
Proof
  strip_tac >>
  metis_tac[for_cons_ordinary_exception_tail_exists,
            for_cons_ordinary_exception_tail_residual_nested]
QED

Theorem for_cons_ordinary_exception_tail_resume_exists_context:
  stp = st with scopes updated_by
          CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)) /\
  eval_stmts cx body_stmts stp = (INR exn, st_body) /\
  env_maps_wf env /\
  env_consistent env cx st /\
  id NOTIN FDOM env.var_types /\
  state_well_typed st_body /\
  accounts_well_typed st_body.accounts /\
  no_type_error_result (INR exn) /\
  (∃env_exn.
     env_extends (extend_local env id ty F) env_exn /\
     env_consistent env_exn cx st_body /\
     return_exception_typed env_exn ret_ty exn) ==>
  state_well_typed (st_body with scopes := TL st_body.scopes) /\
  accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
  env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
  no_type_error_result (INR exn) /\
  (∃body_stmts' env_exn' id' st' ty' tyv' v'.
    id' NOTIN FDOM env.var_types /\
    eval_stmts cx body_stmts'
      (st' with scopes updated_by
         CONS (FEMPTY |+ (id', <|assignable := F; type := tyv'; value := v'|>))) =
      (INR exn, st_body) /\
    env_extends (extend_local env id' ty' F) env_exn' /\
    env_consistent env cx st' /\
    env_consistent env_exn' cx st_body /\
    return_exception_typed env_exn' ret_ty exn) /\
  return_exception_typed env ret_ty exn
Proof
  strip_tac >>
  `state_well_typed (st_body with scopes := TL st_body.scopes) /\
   accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
   env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
   no_type_error_result (INR exn) /\
   return_exception_typed env ret_ty exn` by
    metis_tac[for_cons_ordinary_exception_tail_exists] >>
  `no_type_error_result (INR exn) /\
   ∃body_stmts' env_exn' id' st' ty' tyv' v'.
     id' NOTIN FDOM env.var_types /\
     eval_stmts cx body_stmts'
       (st' with scopes updated_by
          CONS (FEMPTY |+ (id', <|assignable := F; type := tyv'; value := v'|>))) =
       (INR exn,st_body) /\
     env_extends (extend_local env id' ty' F) env_exn' /\
     env_consistent env cx st' /\
     env_consistent env_exn' cx st_body /\
     return_exception_typed env_exn' ret_ty exn` by
    metis_tac[for_cons_ordinary_exception_tail_residual] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- (simp[no_type_error_result_def] >> gen_tac >> CCONTR_TAC >> gvs[no_type_error_result_def]) >>
  conj_tac >- (
    qexists_tac `body_stmts'` >> qexists_tac `env_exn'` >> qexists_tac `id'` >>
    qexists_tac `st'` >> qexists_tac `ty'` >> qexists_tac `tyv'` >>
    qexists_tac `v'` >> simp[]) >>
  simp[]
QED

Theorem for_cons_ordinary_exception_tail_resume_goal:
  eval_stmts cx body_stmts
    (st with scopes updated_by
       CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>))) =
    (INR exn, st_body) ==>
  id NOTIN FDOM env.var_types ==>
  env_consistent env cx st ==>
  env_extends (extend_local env id ty F) env_exn ==>
  env_consistent env_exn cx st_body ==>
  return_exception_typed env_exn ret_ty exn ==>
  state_well_typed (st_body with scopes := TL st_body.scopes) ==>
  accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts ==>
  env_consistent env cx (st_body with scopes := TL st_body.scopes) ==>
  no_type_error_result (INR exn) ==>
  state_well_typed (st_body with scopes := TL st_body.scopes) /\
  accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
  env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
  no_type_error_result (INR exn) /\
  (?body_stmts' env_exn' id' st' ty' tyv' v'.
    id' NOTIN FDOM env.var_types /\
    eval_stmts cx body_stmts'
      (st' with scopes updated_by
         CONS (FEMPTY |+ (id', <|assignable := F; type := tyv'; value := v'|>))) =
      (INR exn, st_body) /\
    env_extends (extend_local env id' ty' F) env_exn' /\
    env_consistent env cx st' /\
    env_consistent env_exn' cx st_body /\
    return_exception_typed env_exn' ret_ty exn) /\
  return_exception_typed env ret_ty exn
Proof
  rpt gen_tac >> ntac 10 strip_tac >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- (simp[no_type_error_result_def] >> gen_tac >> CCONTR_TAC >> gvs[no_type_error_result_def]) >>

  conj_tac >- (
    qexists_tac `body_stmts` >> qexists_tac `env_exn` >> qexists_tac `id` >>
    qexists_tac `st` >> qexists_tac `ty` >> qexists_tac `tyv` >>
    qexists_tac `v` >> simp[]) >>
  irule return_exception_typed_extend_local_env_extends >>
  qexists_tac `F` >> qexists_tac `env_exn` >>
  qexists_tac `id` >> qexists_tac `ty` >> simp[]
QED

Theorem for_cons_ordinary_exception_tail_forward:
  eval_stmts cx body_stmts stp = (INR exn, st_body) ==>
  stp = st with scopes updated_by
          CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)) ==>
  env_maps_wf env ==>
  env_consistent env cx st ==>
  id NOTIN FDOM env.var_types ==>
  state_well_typed st_body ==>
  accounts_well_typed st_body.accounts ==>
  no_type_error_result (INR exn) ==>
  env_extends (extend_local env id ty F) env_exn ==>
  env_consistent env_exn cx st_body ==>
  return_exception_typed env_exn ret_ty exn ==>
  state_well_typed (st_body with scopes := TL st_body.scopes) /\
  accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
  env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
  no_type_error_result (INR exn) /\
  return_exception_typed env ret_ty exn
Proof
  ntac 11 strip_tac >>
  qpat_x_assum `stp = _` SUBST_ALL_TAC >>
  irule for_cons_ordinary_exception_tail_conclusion >>
  simp[] >>
  qexists_tac `body_stmts` >> qexists_tac `env_exn` >> qexists_tac `id` >>
  qexists_tac `st` >> qexists_tac `ty` >> qexists_tac `tyv` >>
  qexists_tac `v` >> simp[]
QED

Theorem for_cons_ordinary_exception_tail_context_conj:
  stp = st with scopes updated_by
          CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)) /\
  eval_stmts cx body_stmts stp = (INR exn, st_body) /\
  env_maps_wf env /\
  env_consistent env cx st /\
  id NOTIN FDOM env.var_types /\
  state_well_typed st_body /\
  accounts_well_typed st_body.accounts /\
  no_type_error_result (INR exn) /\
  env_extends (extend_local env id ty F) env_exn /\
  env_consistent env_exn cx st_body /\
  return_exception_typed env_exn ret_ty exn ==>
  state_well_typed (st_body with scopes := TL st_body.scopes) /\
  accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
  env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
  no_type_error_result (INR exn) /\
  return_exception_typed env ret_ty exn
Proof
  strip_tac >>
  qpat_x_assum `stp = _` SUBST_ALL_TAC >>
  irule for_cons_ordinary_exception_tail_conclusion >>
  simp[] >>
  qexists_tac `body_stmts` >> qexists_tac `env_exn` >> qexists_tac `id` >>
  qexists_tac `st` >> qexists_tac `ty` >> qexists_tac `tyv` >>
  qexists_tac `v` >> simp[]
QED

Theorem for_cons_ordinary_exception_tail_full_context_conj:
  stp = st with scopes updated_by
          CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)) /\
  eval_stmts cx body_stmts stp = (INR exn, st_body) /\
  env_maps_wf env /\
  env_consistent env cx st /\
  id NOTIN FDOM env.var_types /\
  state_well_typed st_body /\
  accounts_well_typed st_body.accounts /\
  no_type_error_result (INR exn) /\
  env_extends (extend_local env id ty F) env_exn /\
  env_consistent env_exn cx st_body /\
  return_exception_typed env_exn ret_ty exn ==>
  state_well_typed (st_body with scopes := TL st_body.scopes) /\
  accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
  env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
  no_type_error_result (INR exn) /\
  (?body_stmts' env_exn' id' st' ty' tyv' v'.
     id' NOTIN FDOM env.var_types /\
     eval_stmts cx body_stmts'
       (st' with scopes updated_by
          CONS (FEMPTY |+ (id', <|assignable := F; type := tyv'; value := v'|>))) =
     (INR exn, st_body) /\
     env_extends (extend_local env id' ty' F) env_exn' /\
     env_consistent env cx st' /\
     env_consistent env_exn' cx st_body /\
     return_exception_typed env_exn' ret_ty exn) /\
  return_exception_typed env ret_ty exn
Proof
  strip_tac >>
  drule_all for_cons_ordinary_exception_tail_context_conj >>
  strip_tac >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- (
    qpat_x_assum `stp = _` SUBST_ALL_TAC >>
    qexists_tac `body_stmts` >> qexists_tac `env_exn` >> qexists_tac `id` >>
    qexists_tac `st` >> qexists_tac `ty` >> qexists_tac `tyv` >>
    qexists_tac `v` >> simp[]) >>
  simp[]
QED

Theorem for_cons_ordinary_exception_tail_resume_from_exists:
  (?body_stmts id st ty tyv v.
     (?env_exn.
        env_extends (extend_local env id ty F) env_exn /\
        env_consistent env_exn cx st_body /\
        return_exception_typed env_exn ret_ty exn) /\
     no_type_error_result (INR exn) /\
     id NOTIN FDOM env.var_types /\
     eval_stmts cx body_stmts
       (st with scopes updated_by
          CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>))) =
       (INR exn, st_body) /\
     env_consistent env cx st) /\
  env_maps_wf env /\
  state_well_typed st_body /\
  accounts_well_typed st_body.accounts ==>
  state_well_typed (st_body with scopes := TL st_body.scopes) /\
  accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
  env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
  no_type_error_result (INR exn) /\
  return_exception_typed env ret_ty exn
Proof
  metis_tac[for_cons_ordinary_exception_tail_context_conj]
QED

Theorem for_cons_ordinary_exception_tail_resume_from_exists_no_type_last:
  (?body_stmts id st ty tyv v.
     (?env_exn.
        env_extends (extend_local env id ty F) env_exn /\
        env_consistent env_exn cx st_body /\
        return_exception_typed env_exn ret_ty exn) /\
     id NOTIN FDOM env.var_types /\
     eval_stmts cx body_stmts
       (st with scopes updated_by
          CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>))) =
       (INR exn, st_body) /\
     env_consistent env cx st /\
     no_type_error_result (INR exn)) /\
  env_maps_wf env /\
  state_well_typed st_body /\
  accounts_well_typed st_body.accounts ==>
  state_well_typed (st_body with scopes := TL st_body.scopes) /\
  accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
  env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
  no_type_error_result (INR exn) /\
  return_exception_typed env ret_ty exn
Proof
  metis_tac[for_cons_ordinary_exception_tail_resume_from_exists]
QED

Theorem for_cons_ordinary_exception_tail_resume_from_no_type:
  no_type_error_result (INR exn) ==>
  (?body_stmts id st ty tyv v.
     (?env_exn.
        env_extends (extend_local env id ty F) env_exn /\
        env_consistent env_exn cx st_body /\
        return_exception_typed env_exn ret_ty exn) /\
     id NOTIN FDOM env.var_types /\
     eval_stmts cx body_stmts
       (st with scopes updated_by
          CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>))) =
       (INR exn, st_body) /\
     env_consistent env cx st) /\
  env_maps_wf env /\
  state_well_typed st_body /\
  accounts_well_typed st_body.accounts ==>
  state_well_typed (st_body with scopes := TL st_body.scopes) /\
  accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
  env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
  no_type_error_result (INR exn) /\
  return_exception_typed env ret_ty exn
Proof
  metis_tac[for_cons_ordinary_exception_tail_resume_from_exists]
QED

Theorem for_cons_ordinary_exception_tail_resume_site_from_stp:
  stp = st with scopes updated_by
          CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)) /\
  eval_stmts cx body_stmts stp = (INR exn, st_body) /\
  (?env_exn.
     env_extends (extend_local env id ty F) env_exn /\
     env_consistent env_exn cx st_body /\
     return_exception_typed env_exn ret_ty exn) /\
  no_type_error_result (INR exn) /\
  id NOTIN FDOM env.var_types /\
  env_consistent env cx st /\
  env_maps_wf env /\
  state_well_typed st_body /\
  accounts_well_typed st_body.accounts ==>
  state_well_typed (st_body with scopes := TL st_body.scopes) /\
  accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
  env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
  no_type_error_result (INR exn) /\
  return_exception_typed env ret_ty exn
Proof
  metis_tac[for_cons_ordinary_exception_tail_resume_from_no_type]
QED

Theorem for_cons_ordinary_exception_tail_visible_finish:
  state_well_typed stpopped ==>
  accounts_well_typed stpopped.accounts ==>
  env_consistent env cx stpopped ==>
  no_type_error_result (INR exn) ==>
  env_extends (extend_local env id ty F) env_exn ==>
  return_exception_typed env_exn ret_ty exn ==>
  state_well_typed stpopped /\
  accounts_well_typed stpopped.accounts /\
  env_consistent env cx stpopped /\
  no_type_error_result (INR exn) /\
  return_exception_typed env ret_ty exn
Proof
  ntac 6 strip_tac >>
  (conj_tac >- simp[]) >>
  (conj_tac >- simp[]) >>
  (conj_tac >- simp[]) >>
  (conj_tac >- fs[no_type_error_result_def]) >>
  irule return_exception_typed_extend_local_env_extends >>
  qexists_tac `F` >> qexists_tac `env_exn` >>
  qexists_tac `id` >> qexists_tac `ty` >> simp[]
QED

Theorem for_cons_ordinary_exception_tail_visible_finish_from_ext:
  env_extends ext_env env_exn ==>
  ext_env = extend_local env id ty F ==>
  return_exception_typed env_exn ret_ty exn ==>
  state_well_typed stpopped ==>
  accounts_well_typed stpopped.accounts ==>
  env_consistent env cx stpopped ==>
  no_type_error_result (INR exn) ==>
  state_well_typed stpopped /\
  accounts_well_typed stpopped.accounts /\
  env_consistent env cx stpopped /\
  no_type_error_result (INR exn) /\
  return_exception_typed env ret_ty exn
Proof
  metis_tac[for_cons_ordinary_exception_tail_visible_finish]
QED

Theorem for_body_env_consistent_after_pop:
  env_maps_wf env /\
  env_consistent env cx st /\
  id NOTIN FDOM env.var_types /\
  type_stmts (extend_local env id ty F) ret_ty body_stmts = SOME env_after /\
  env_consistent env_after cx st_body /\
  eval_stmts cx body_stmts
    (st with scopes updated_by CONS
       (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>))) =
    (res, st_body) ==>
  env_consistent env cx (st_body with scopes := TL st_body.scopes)
Proof
  strip_tac >>
  irule for_body_env_extends_consistent_after_pop >> simp[] >>
  qexists_tac `body_stmts` >> qexists_tac `env_after` >>
  qexists_tac `id` >> qexists_tac `res` >> qexists_tac `st` >>
  qexists_tac `ty` >> qexists_tac `tyv` >> qexists_tac `v` >> simp[] >>
  irule type_stmts_env_extends >> simp[] >>
  conj_tac >- (irule extend_local_env_maps_wf >> simp[]) >>
  qexists_tac `ret_ty` >> qexists_tac `body_stmts` >> simp[]
QED

(* ===== Statement soundness ===== *)

(* TOP-LEVEL WORKHORSE: mutual no-TypeError proof for statements, statement
 * lists, and for-loops.  This follows the evaluator recursion and is the
 * intended final shape for removing the no-TypeError cheats. *)

(* ===== Scope-bracket helpers for block statements ===== *)

Theorem scope_bracket_decompose:
  (!q st_body. body_fun (st with scopes updated_by CONS FEMPTY) = (q, st_body) ==> st_body.scopes <> []) /\
  (do push_scope; finally body_fun pop_scope od) st = (res, st') ==>
  ?q st_body.
    body_fun (st with scopes updated_by CONS FEMPTY) = (q, st_body) /\
    st' = st_body with scopes := TL st_body.scopes /\
    (((?x. q = INL x) ==> ?u. res = INL u) /\
     (!e. q = INR e ==> res = INR e))
Proof
  rpt strip_tac >>
  gvs[push_scope_def, finally_def, pop_scope_def,
      return_def, raise_def, bind_def, ignore_bind_def,
      AllCaseEqs()] >>
  Cases_on `body_fun (st with scopes updated_by CONS FEMPTY)` >>
  Cases_on `q` >>
  gvs[AllCaseEqs(), pop_scope_def, return_def, raise_def] >>
  imp_res_tac eval_stmts_preserves_scopes_len >>
  Cases_on `r.scopes` >> gvs[return_def, raise_def,
    evaluation_state_component_equality]
QED

Theorem scope_bracket_preserves:
  env_maps_wf env /\
  env_consistent env cx st /\
  type_stmts env ret_ty ss = SOME env_after /\
  eval_stmts cx ss (st with scopes updated_by CONS FEMPTY) = (q, st_body) /\
  state_well_typed st_body /\
  env_consistent env_after cx st_body /\
  accounts_well_typed st_body.accounts ==>
  state_well_typed (st_body with scopes := TL st_body.scopes) /\
  env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
  accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts
Proof
  strip_tac
  >> conj_tac >- (drule scope_bracket_preserves_swt >> simp[])
  >> conj_tac >- (irule scope_bracket_preserves_ec >>
      conj_tac >- rw[] >>
      goal_assum(drule_at(Pat`type_stmts`)) >>
      goal_assum(drule_at(Pat`eval_stmts`)) >>
      simp[])
  >> simp[evaluation_state_component_equality]
QED

Theorem scope_bracket_result_post:
  (!e. q = INR e ==> res = INR e) /\
  ((?x. q = INL x) ==> res = INL ()) /\
  no_type_error_result q /\
  (case q of INR exn => return_exception_typed env ret_ty exn | _ => T) ==>
  no_type_error_result res /\
  (case res of INR exn => return_exception_typed env ret_ty exn | _ => T)
Proof
  CASE_TAC >> strip_tac >> gvs[no_type_error_result_def]
QED

Theorem for_body_decompose:
  !cx body_stmts st sc res st'.
    finally (try do eval_stmts cx body_stmts; return F od handle_loop_exception)
      pop_scope (st with scopes updated_by CONS sc) = (res, st') ==>
    ?res_body st_body.
      eval_stmts cx body_stmts (st with scopes updated_by CONS sc) =
        (res_body, st_body) /\
      st' = st_body with scopes := TL st_body.scopes /\
      ((?x. res_body = INL x) ==> res = INL F) /\
      (res_body = INR ContinueException ==> res = INL F) /\
      (res_body = INR BreakException ==> res = INL T) /\
      (!e. res_body = INR e /\
           e <> ContinueException /\ e <> BreakException ==>
           res = INR e) /\
      (!e. res = INR e ==> res_body = INR e)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [finally_def, bind_apply, ignore_bind_apply,
    try_def, return_def, pop_scope_def, raise_def,
    handle_loop_exception_def] >>
  Cases_on `eval_stmts cx body_stmts (st with scopes updated_by CONS sc)` >>
  `?hd tl. r.scopes = hd :: tl` by (
    imp_res_tac eval_stmts_preserves_scopes_len >>
    Cases_on `r.scopes` >> gvs[]) >>
  Cases_on `q` >> gvs[] >>
  Cases_on `y = ContinueException` >> gvs[return_def] >>
  Cases_on `y = BreakException` >> gvs[return_def, raise_def] >>
  strip_tac >> gvs[]
QED

Theorem for_body_decompose_exact[local]:
  !cx body_stmts st sc res st' stp.
    stp = st with scopes updated_by CONS sc /\
    finally (try do eval_stmts cx body_stmts; return F od handle_loop_exception)
      pop_scope stp = (res, st') ==>
    ?res_body st_body.
      eval_stmts cx body_stmts stp = (res_body, st_body) /\
      st' = st_body with scopes := TL st_body.scopes /\
      ((?x. res_body = INL x) ==> res = INL F) /\
      (res_body = INR ContinueException ==> res = INL F) /\
      (res_body = INR BreakException ==> res = INL T) /\
      (!e. res_body = INR e /\
           e <> ContinueException /\ e <> BreakException ==>
           res = INR e) /\
      (!e. res = INR e ==> res_body = INR e)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  qspecl_then [`cx`, `body_stmts`, `st`, `sc`, `res`, `st'`]
    mp_tac for_body_decompose >>
  simp[]
QED

Theorem for_body_decompose_any[local]:
  !cx body_stmts stp res st'.
    stp.scopes <> [] /\
    finally (try do eval_stmts cx body_stmts; return F od handle_loop_exception)
      pop_scope stp = (res, st') ==>
    ?res_body st_body.
      eval_stmts cx body_stmts stp = (res_body, st_body) /\
      st' = st_body with scopes := TL st_body.scopes /\
      ((?x. res_body = INL x) ==> res = INL F) /\
      (res_body = INR ContinueException ==> res = INL F) /\
      (res_body = INR BreakException ==> res = INL T) /\
      (!e. res_body = INR e /\
           e <> ContinueException /\ e <> BreakException ==>
           res = INR e) /\
      (!e. res = INR e ==> res_body = INR e)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [finally_def, bind_apply, ignore_bind_apply,
    try_def, return_def, pop_scope_def, raise_def,
    handle_loop_exception_def] >>
  Cases_on `eval_stmts cx body_stmts stp` >>
  `?hd tl. r.scopes = hd :: tl` by (
    imp_res_tac eval_stmts_preserves_scopes_len >>
    Cases_on `r.scopes` >> gvs[]) >>
  Cases_on `q` >> gvs[] >>
  Cases_on `y = ContinueException` >> gvs[return_def] >>
  Cases_on `y = BreakException` >> gvs[return_def, raise_def] >>
  strip_tac >> gvs[]
QED
Theorem for_body_decompose_for_cons_pushed[local]:
  !cx body_stmts st id tyv v res st' stp.
    stp =
      st with scopes updated_by
        CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)) /\
    finally (try do eval_stmts cx body_stmts; return F od handle_loop_exception)
      pop_scope stp = (res, st') ==>
    ?res_body st_body.
      eval_stmts cx body_stmts stp = (res_body, st_body) /\
      st' = st_body with scopes := TL st_body.scopes /\
      ((?x. res_body = INL x) ==> res = INL F) /\
      (res_body = INR ContinueException ==> res = INL F) /\
      (res_body = INR BreakException ==> res = INL T) /\
      (!e. res_body = INR e /\
           e <> ContinueException /\ e <> BreakException ==>
           res = INR e) /\
      (!e. res = INR e ==> res_body = INR e)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`cx`, `body_stmts`, `stp`, `res`, `st'`]
    mp_tac for_body_decompose_any >>
  impl_tac >- (
    conj_tac >- gvs[] >>
    qpat_assum `finally _ _ _ = _` ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED
Theorem is_int_type_evaluate_type_not_None_Array[local]:
  !tdefs ty tv.
    is_int_type ty /\ evaluate_type tdefs ty = SOME tv ==>
    tv <> NoneTV /\ (!t bd. tv <> ArrayTV t bd)
Proof
  rw[] >>
  Cases_on `ty` >> gvs[is_int_type_def, evaluate_type_def, AllCaseEqs()] >>
  Cases_on `b` >> gvs[is_int_type_def, evaluate_type_def]
QED


Theorem for_cons_pushed_state_well_typed[local]:
  state_well_typed st /\ value_has_type tyv v /\ well_formed_type_value tyv ==>
  state_well_typed
    (st with scopes updated_by
       CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)))
Proof
  rw[state_well_typed_def, scope_well_typed_def, FLOOKUP_UPDATE]
QED

Theorem for_cons_return_exception_typed_from_pushed_original_body:
  (!stp res_body st_body.
    env_consistent (extend_local env id ty F) cx stp /\
    state_well_typed stp /\ accounts_well_typed stp.accounts /\
    eval_stmts cx body_stmts stp = (res_body, st_body) ==>
    state_well_typed st_body /\ accounts_well_typed st_body.accounts /\
    no_type_error_result res_body /\
    case res_body of
    | INL _ => env_consistent env_after cx st_body
    | INR exn => ?env_exn.
        env_extends (extend_local env id ty F) env_exn /\
        env_consistent env_exn cx st_body /\
        return_exception_typed env_exn ret_ty exn) /\
  env.type_defs = get_tenv cx /\
  env_consistent (extend_local env id ty F) cx
    (st with scopes updated_by
       CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>))) /\
  accounts_well_typed st.accounts /\ state_well_typed st /\
  evaluate_type env.type_defs ty = SOME tyv /\
  value_has_type tyv v /\
  eval_stmts cx body_stmts
    (st with scopes updated_by
       CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>))) =
    (INR (ReturnException vret), st_body) ==>
  return_exception_typed env ret_ty (ReturnException vret)
Proof
  rpt gen_tac >> strip_tac >>
  `env.type_defs = get_tenv cx` by fs[env_consistent_def, env_context_consistent_def] >>
  qabbrev_tac `stp =
    st with scopes updated_by
      CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>))` >>
  drule evaluate_type_well_formed_type_value >> strip_tac >>
  `state_well_typed stp` by (
    qunabbrev_tac `stp` >>
    irule for_cons_pushed_state_well_typed >> simp[]) >>
  `accounts_well_typed stp.accounts` by (
    qunabbrev_tac `stp` >> simp[evaluation_state_component_equality]) >>
  irule for_cons_body_exception_typed_from_body_soundness >>
  qexists_tac `body_stmts` >> qexists_tac `cx` >> qexists_tac `env_after` >>
  qexists_tac `id` >> qexists_tac `st_body` >> qexists_tac `stp` >>
  qexists_tac `ty` >>
  conj_tac >- (
    qpat_assum `!stp res_body st_body.
       env_consistent (extend_local env id ty F) cx stp /\
       state_well_typed stp /\ accounts_well_typed stp.accounts /\
       eval_stmts cx body_stmts stp = (res_body,st_body) ==> _` ACCEPT_TAC) >>
  simp[Abbr`stp`]
QED


Theorem scope_bracket_post:
  env_maps_wf env /\
  env_consistent env cx st /\
  (!q st_body. body_fun (st with scopes updated_by CONS FEMPTY) = (q, st_body) ==> st_body.scopes <> []) /\
  (do push_scope; finally body_fun pop_scope od) st = (res, st_final) /\
  (!q st_body.
     body_fun (st with scopes updated_by CONS FEMPTY) = (q, st_body) ==>
     state_well_typed st_body /\ accounts_well_typed st_body.accounts /\
     no_type_error_result q /\
     case q of
     | INL _ => env_consistent env cx (st_body with scopes := TL st_body.scopes)
     | INR exn => env_consistent env cx (st_body with scopes := TL st_body.scopes) /\ return_exception_typed env ret_ty exn) ==>
  state_well_typed st_final /\ accounts_well_typed st_final.accounts /\ no_type_error_result res /\
  case res of
  | INL _ => env_consistent env cx st_final
  | INR exn => env_consistent env cx st_final /\ return_exception_typed env ret_ty exn
Proof
  strip_tac >>
  qpat_x_assum `do push_scope; finally body_fun pop_scope od st = (res,st_final)` mp_tac >>
  qpat_x_assum `!q st_body. body_fun _ = _ ==> st_body.scopes <> []` mp_tac >>
  strip_tac >> strip_tac >>
  `?q st_body.
     body_fun (st with scopes updated_by CONS FEMPTY) = (q, st_body) /\
     st_final = st_body with scopes := TL st_body.scopes /\
     (((?x. q = INL x) ==> ?u. res = INL u) /\
      (!e. q = INR e ==> res = INR e))` by
    (irule scope_bracket_decompose >> simp[]) >>
  gvs[] >>
  qmatch_assum_rename_tac`no_type_error_result r1` >>
  Cases_on `st_body.scopes` >> gvs[] >>
  `state_well_typed (st_body with scopes := t)` by (
    drule pop_scope_preserves_state_well_typed >>
    simp[pop_scope_def, return_def, raise_def]) >>
  Cases_on`r1` >> gvs[no_type_error_result_def]
QED
Theorem leaf_type_append:
  !base_tv xs ys.
    leaf_type base_tv (xs ++ ys) = leaf_type (leaf_type base_tv xs) ys
Proof
  Induct_on `xs` >> simp[leaf_type_def] >>
  Cases_on `h` >> simp[leaf_type_def] >>
  TRY(Cases_on `v` >> simp[leaf_type_def]) >>
  Cases_on `base_tv` >> simp[leaf_type_def] >>
  TRY(Cases_on `b` >> simp[leaf_type_def]) >>
  TRY(Cases_on `ALOOKUP l s` >> simp[leaf_type_def]) >>
  Cases_on `ys` >> simp[leaf_type_def]
QED



(* Helper: OPT_MMAP + ALOOKUP on ZIP *)
Theorem OPT_MMAP_ALOOKUP_ZIP:
  !f (args:('k # 'a) list) ys field_id ty.
    OPT_MMAP f (MAP SND args) = SOME ys /\
    ALOOKUP args field_id = SOME ty ==>
    ?tv. f ty = SOME tv /\
         ALOOKUP (ZIP(MAP FST args, ys)) field_id = SOME tv
Proof
  Induct_on `args` >> simp[] >>
  Cases >> simp[OPT_MMAP_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `q = field_id` >> gvs[]
QED

Theorem evaluate_type_mono:
  (!tenv ty tv k.
    evaluate_type (tenv \\ k) ty = SOME tv ==>
    evaluate_type tenv ty = SOME tv) /\
  (!tenv ts acc tvs k.
    evaluate_types (tenv \\ k) ts acc = SOME tvs ==>
    evaluate_types tenv ts acc = SOME tvs)
Proof
  ho_match_mp_tac evaluate_type_ind
  >> conj_tac >- simp[evaluate_type_def]
  >> conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[evaluate_type_def, AllCaseEqs()] >>
    first_x_assum drule >> simp[])
  >> conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[evaluate_type_def, AllCaseEqs()] >>
    first_x_assum drule >> simp[])
  >> conj_tac >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    gvs[evaluate_type_def, AllCaseEqs(), DOMSUB_FLOOKUP_THM, DOMSUB_COMMUTES] >>
    first_x_assum drule >>
    strip_tac >> goal_assum drule >> gvs[])
  >> conj_tac >- (
    rpt gen_tac >> rpt gen_tac >>
    simp[evaluate_type_def, AllCaseEqs(), DOMSUB_FLOOKUP_THM] >>
    rpt strip_tac >> gvs[])
  >> conj_tac >- simp[evaluate_type_def]
  >> conj_tac >- simp[evaluate_type_def]
  >> rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[evaluate_type_def, AllCaseEqs()] >>
  strip_tac >>
  first_x_assum (fn th => drule (cj 1 th)) >> strip_tac >> simp[] >>
  first_x_assum drule >> simp[] >>
  disch_then irule >> goal_assum drule
QED

(* attribute_type + evaluate_type gives ALOOKUP on evaluated struct fields *)
Theorem attribute_type_evaluates:
  !tenv struct_ty field_id result_ty ftypes.
    attribute_type tenv struct_ty field_id = SOME result_ty /\
    evaluate_type tenv struct_ty = SOME (StructTV ftypes) ==>
    ?tv. evaluate_type tenv result_ty = SOME tv /\
         ALOOKUP ftypes field_id = SOME tv
Proof
  Cases_on `struct_ty` >> simp[attribute_type_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs(), LET_THM, evaluate_types_OPT_MMAP] >>
  Cases_on `ALOOKUP args field_id` >> gvs[] >>
  drule_all OPT_MMAP_ALOOKUP_ZIP >> strip_tac >>
  metis_tac[evaluate_type_mono]
QED

Theorem target_runtime_typed_imp_shape[local]:
  !env cx st tgt ty gv.
    target_runtime_typed env cx st tgt ty gv ==>
    target_value_shape env tgt gv
Proof
  Cases_on `tgt` >> Cases_on `gv` >>
  rw[target_runtime_typed_def, target_value_shape_def]
QED

Theorem target_values_runtime_typed_imp_shape[local]:
  !env cx st tgts tys gvs.
    target_values_runtime_typed env cx st tgts tys gvs ==>
    target_values_shape env tgts gvs
Proof
  Induct_on `tgts` >> Cases_on `tys` >> Cases_on `gvs` >>
  simp[target_runtime_typed_def, target_value_shape_def] >>
  metis_tac[target_runtime_typed_imp_shape]
QED

Theorem extract_elements_well_typed[local]:
  !arr_tv av elem_tv bd vs.
    value_has_type (ArrayTV elem_tv bd) (ArrayV av) /\
    well_formed_type_value (ArrayTV elem_tv bd) /\
    extract_elements (ArrayTV elem_tv bd) (ArrayV av) = SOME vs ==>
    EVERY (value_has_type elem_tv) vs
Proof
  rpt gen_tac >>
  simp[extract_elements_def] >>
  Cases_on `av` >> simp[value_has_type_inv]
  >- (rpt strip_tac >> gvs[array_elements_def, all_have_type_EVERY])
  >- (rpt strip_tac >> gvs[] >>
      fs[array_elements_def, LET_THM, EVERY_GENLIST] >>
      rpt strip_tac >>
      Cases_on `ALOOKUP l i` >> simp[]
      >- (match_mp_tac default_value_well_typed >> fs[well_formed_type_value_def]) >>
      metis_tac[ALOOKUP_sparse_has_type])
QED

Theorem Num_pos_le[local]:
  !x (m:num). 0 <= x ==> (Num x <= m <=> x <= &m)
Proof
  rpt strip_tac >>
  `&(Num x) = x` by metis_tac[integerTheory.INT_OF_NUM] >>
  pop_assum (fn th => REWRITE_TAC[GSYM integerTheory.INT_LE, th])
QED

Theorem within_int_bound_convex[local]:
  !b n1 n2 k.
    within_int_bound b n1 /\ within_int_bound b n2 /\
    n1 <= n2 /\ &k < n2 - n1 ==>
    within_int_bound b (n1 + &k)
Proof
  Cases_on `b` >> simp[within_int_bound_def] >> rpt strip_tac
  >- (
    Cases_on `n = 0` >- gvs[] >>
    gvs[] >>
    Cases_on `n1 + &k < 0` >> simp[]
    >- (
      `n1 < 0` by intLib.ARITH_TAC >> fs[] >>
      `0 <= -(n1 + &k)` by intLib.ARITH_TAC >>
      `0 <= -n1` by intLib.ARITH_TAC >>
      `-(n1 + &k) <= -n1` by intLib.ARITH_TAC >>
      fs[Num_pos_le] >> intLib.ARITH_TAC) >>
    Cases_on `n2 < 0`
    >- (`n1 + &k < n2` by intLib.ARITH_TAC >> intLib.ARITH_TAC) >>
    fs[] >>
    `0 <= n1 + &k` by intLib.ARITH_TAC >>
    `0 <= n2` by intLib.ARITH_TAC >>
    `n1 + &k < n2` by intLib.ARITH_TAC >>
    `Num (n1 + &k) < Num n2` by simp[integerTheory.NUM_LT] >>
    simp[]) >>
  `0 <= n1 + &k` by intLib.ARITH_TAC >>
  `0 <= n2` by intLib.ARITH_TAC >>
  `n1 + &k < n2` by intLib.ARITH_TAC >>
  `Num (n1 + &k) < Num n2` by simp[integerTheory.NUM_LT] >>
  simp[]
QED

Theorem range_values_well_typed[local]:
  !n1 n2 count tyv.
    value_has_type tyv (IntV n1) /\
    value_has_type tyv (IntV n2) /\
    get_range_limits (IntV n1) (IntV n2) = INL (n1, count) ==>
    EVERY (value_has_type tyv) (GENLIST (\n. IntV (n1 + &n)) count)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[get_range_limits_def] >>
  simp[EVERY_GENLIST] >> rpt strip_tac >>
  `0 <= n2 - n1` by intLib.ARITH_TAC >>
  `&n < n2 - n1` by (
    `&(Num (n2 - n1)) = n2 - n1` by metis_tac[integerTheory.INT_OF_NUM] >>
    intLib.ARITH_TAC) >>
  Cases_on `tyv` >> gvs[value_has_type_def] >>
  Cases_on `b` >> gvs[value_has_type_def]
  >- (
    `0 <= n1 + &n` by intLib.ARITH_TAC >>
    `0 <= n2` by intLib.ARITH_TAC >>
    `n1 + &n < n2` by intLib.ARITH_TAC >>
    `Num (n1 + &n) < Num n2` by simp[integerTheory.NUM_LT] >>
    simp[]) >>
  metis_tac[within_int_bound_convex]
QED

Theorem iterator_range_tail_sound[local]:
  !tv i1 i2 rl st.
    value_has_type tv (IntV i1) /\
    value_has_type tv (IntV i2) /\
    lift_sum (get_range_limits (IntV i1) (IntV i2)) st = (INL rl,st) ==>
    no_type_error_result (INL (GENLIST (\n. IntV (FST rl + &n)) (SND rl))) /\
    EVERY (value_has_type tv) (GENLIST (\n. IntV (FST rl + &n)) (SND rl))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `lift_sum _ _ = _` mp_tac >>
  simp[lift_sum_def, get_range_limits_def] >>
  COND_CASES_TAC >> simp[return_def, raise_def] >>
  strip_tac >> gvs[] >>
  conj_tac >- simp[no_type_error_result_def] >>
  irule range_values_well_typed >>
  conj_tac >- simp[] >>
  qexists_tac `i2` >> simp[get_range_limits_def]
QED
Theorem iterator_range_tail_eval_sound[local]:
  !type_defs expr_ty tyv i1 i2 range_res st st_tail res st_final.
    evaluate_type type_defs expr_ty = SOME tyv /\
    value_has_type tyv (IntV i1) /\
    value_has_type tyv (IntV i2) /\
    lift_sum (get_range_limits (IntV i1) (IntV i2)) st = (range_res, st_tail) /\
    (case range_res of
     | INL rl => return (GENLIST (\n. IntV (FST rl + &n)) (SND rl)) st_tail
     | INR err => raise err st_tail) = (res, st_final) ==>
    st_final = st /\
    no_type_error_result res /\
    (case res of
     | INL vs => ?tyv'. evaluate_type type_defs expr_ty = SOME tyv' /\ EVERY (value_has_type tyv') vs
     | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  drule lift_sum_state >> strip_tac >> gvs[] >>
  Cases_on `range_res` >> gvs[return_def, raise_def]
  >- (
    rename1 `lift_sum (get_range_limits (IntV i1) (IntV i2)) st = (INL rl,st)` >>
    qspecl_then [`tyv`, `i1`, `i2`, `rl`, `st`] mp_tac iterator_range_tail_sound >>
    simp[]) >>
  qpat_x_assum `lift_sum _ _ = _` mp_tac >>
  simp[lift_sum_def, get_range_limits_def, return_def, raise_def] >>
  Cases_on `i1 <= i2` >> gvs[return_def, raise_def, no_type_error_result_def]
QED


Theorem iterator_range_first_get_value_error_eq[local]:
  !cx e' tv1 st1 y res st'.
    get_Value tv1 st1 = (INR y, st1) /\
    (case (INL tv1,st1) of
       (INL tv1,s'') =>
         (case get_Value tv1 s'' of
            (INL v1,s'') =>
              (case eval_expr cx e' s'' of
                 (INL tv2,s'') =>
                   (case get_Value tv2 s'' of
                      (INL v2,s'') =>
                        (case lift_sum (get_range_limits v1 v2) s'' of
                           (INL rl,s'') =>
                             (let n1 = FST rl; n2 = SND rl in
                                return (GENLIST (\n. IntV (n1 + &n)) n2)) s''
                         | (INR err,s'') => (INR err,s''))
                    | (INR err,s'') => (INR err,s''))
               | (INR err,s'') => (INR err,s''))
          | (INR err,s'') => (INR err,s''))
     | (INR err,s'') => (INR err,s'')) = (res,st') ==>
    res = INR y /\ st' = st1
Proof
  rpt strip_tac >>
  qpat_x_assum `(case (INL tv1,st1) of _ => _ | _ => _) = (res,st')` mp_tac >>
  simp[]
QED

Theorem iterator_range_expr_error_eq[local]:
  !cx e' y st1 res st'.
    (case (INR y,st1) of
       (INL tv1,s'') =>
         (case get_Value tv1 s'' of
            (INL v1,s'') =>
              (case eval_expr cx e' s'' of
                 (INL tv2,s'') =>
                   (case get_Value tv2 s'' of
                      (INL v2,s'') =>
                        (case lift_sum (get_range_limits v1 v2) s'' of
                           (INL rl,s'') =>
                             (let n1 = FST rl; n2 = SND rl in
                                return (GENLIST (\n. IntV (n1 + &n)) n2)) s''
                         | (INR err,s'') => (INR err,s''))
                    | (INR err,s'') => (INR err,s''))
               | (INR err,s'') => (INR err,s''))
          | (INR err,s'') => (INR err,s''))
     | (INR err,s'') => (INR err,s'')) = (res,st') ==>
    res = INR y /\ st' = st1
Proof
  rpt strip_tac >>
  qpat_x_assum `(case (INR y,st1) of _ => _ | _ => _) = (res,st')` mp_tac >>
  simp[]
QED

Theorem int_expr_get_Value_INR_no_type_error[local]:
  !env e tv ty st y st'.
    expr_result_typed env e tv /\ expr_type e = ty /\ is_int_type ty /\
    get_Value tv st = (INR y, st') ==>
    no_type_error_result (INR y)
Proof
  rw[expr_result_typed_def, expr_runtime_typed_def, no_type_error_result_def] >>
  irule get_Value_INR_no_type_error >>
  qexistsl_tac [`st`, `st'`, `tv`, `tv'`] >> simp[] >>
  drule_all is_int_type_evaluate_type_not_None_Array >> simp[]
QED

Theorem eval_all_type_sound_mutual:
  (!cx s. !env ret_ty env' st res st'.
    type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_stmt cx s st = (res, st') ==>
    state_well_typed st' /\ accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL _ => env_consistent env' cx st'
    | INR exn => env_consistent env cx st' /\ return_exception_typed env ret_ty exn) /\
  (!cx ss. !env ret_ty env' st res st'.
    type_stmts env ret_ty ss = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_stmts cx ss st = (res, st') ==>
    state_well_typed st' /\ accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL _ => env_consistent env' cx st'
    | INR exn => ?env_exn. env_extends env env_exn /\ env_consistent env_exn cx st' /\
                           return_exception_typed env_exn ret_ty exn) /\
  (!cx it. !env ty st res st'.
    well_typed_iterator env ty it /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_iterator cx it st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of
    | INL vs => ?tyv. evaluate_type env.type_defs ty = SOME tyv /\ EVERY (value_has_type tyv) vs
    | INR _ => T) /\
  (!cx tgt. !env ty st res st'.
    well_typed_atarget env tgt ty /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_target cx tgt st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of
    | INL gv => target_runtime_typed env cx st' tgt ty gv
    | INR _ => T) /\
  (!cx tgts. !env tys st res st'.
    LIST_REL (\t ty. well_typed_atarget env t ty) tgts tys /\
    env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_targets cx tgts st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of
    | INL gvs => LIST_REL3 (\t ty gv. target_runtime_typed env cx st' t ty gv) tgts tys gvs
    | INR _ => T) /\
  (!cx bt. !env vt st res st'.
    type_place_target env bt = SOME vt /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_base_target cx bt st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of
    | INL (loc,sbs) =>
        base_target_value_shape env bt loc sbs /\
        ?loc_vt. location_runtime_typed env cx st' loc loc_vt /\
          target_path_type env loc_vt sbs vt
    | INR _ => T) /\
  (!cx tyv id body vs. !env ret_ty ty env_after st res st'.
    evaluate_type env.type_defs ty = SOME tyv /\ EVERY (value_has_type tyv) vs /\
    id NOTIN FDOM env.var_types /\
    type_stmts (extend_local env id ty F) ret_ty body = SOME env_after /\
    env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_for cx tyv id body vs st = (res, st') ==>
    state_well_typed st' /\ accounts_well_typed st'.accounts /\ env_consistent env cx st' /\
    no_type_error_result res /\
    case res of
    | INR exn => return_exception_typed env ret_ty exn
    | INL _ => T) /\
  (!cx e. !env st res st'.
    env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_expr cx e st = (res, st') ==>
    ((well_typed_expr env e ==>
      state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
      no_type_error_result res /\
      case res of
      | INL tv => expr_result_typed env e tv
      | INR _ => T) /\
     (!vt. type_place_expr env e = SOME vt ==>
      state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
      no_type_error_result res /\
      case res of
      | INL tv => place_expr_result_typed env tv vt
      | INR _ => T))) /\
  (!cx es. !env st res st'.
    well_typed_exprs env es /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_exprs cx es st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of
    | INL vs => exprs_runtime_typed env es vs
    | INR _ => T)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  TRY(rename1 `Pass` >> suspend "Pass") >>
  TRY(rename1 `Continue` >> suspend "Continue") >>
  TRY(rename1 `Break` >> suspend "Break") >>
  TRY(rename1 `Return NONE` >> suspend "Return_NONE") >>
  TRY(rename1 `Return (SOME _)` >> suspend "Return_SOME") >>
  TRY(rename1 `Raise RaiseBare` >> suspend "RaiseBare") >>
  TRY(rename1 `Raise RaiseUnreachable` >> suspend "RaiseUnreachable") >>
  TRY(rename1 `Raise (RaiseReason _)` >> suspend "RaiseReason") >>
  TRY(rename1 `AssertBare` >> suspend "AssertBare") >>
  TRY(rename1 `AssertUnreachable` >> suspend "AssertUnreachable") >>
  TRY(rename1 `AssertReason` >> suspend "AssertReason") >>
  TRY(rename1 `Log` >> suspend "Log") >>
  TRY(rename1 `AnnAssign` >> suspend "AnnAssign") >>
  TRY(rename1 `Append` >> suspend "Append") >>
  TRY(rename1 `Assign` >> suspend "Assign") >>
  TRY(rename1 `AugAssign` >> suspend "AugAssign") >>
  TRY(rename1 `If` >> suspend "If") >>
  TRY(rename1 `For` >> suspend "For") >>
  TRY(rename1 `Expr` >> suspend "Expr") >>
  TRY(rename1 `eval_stmts _ []` >> suspend "Stmts_nil") >>
  TRY(rename1 `eval_stmts _ (_::_)` >> suspend "Stmts_cons") >>
  TRY(rename1 `eval_for _ _ _ _ []` >> suspend "For_nil") >>
  TRY(rename1 `eval_for _ _ _ _ (_::_)` >> suspend "For_cons") >>
  TRY(rename1 `Array` >> suspend "Iterator_Array") >>
  TRY(rename1 `Range` >> suspend "Iterator_Range") >>
  TRY(rename1 `BaseTarget` >> suspend "Target_Base") >>
  TRY(rename1 `TupleTarget` >> suspend "Target_Tuple") >>
  TRY(rename1 `eval_targets _ []` >> suspend "Targets_nil") >>
  TRY(rename1 `eval_targets _ (_::_)` >> suspend "Targets_cons") >>
  TRY(rename1 `NameTarget` >> suspend "BaseTarget_Name") >>
  TRY(rename1 `BareGlobalNameTarget` >> suspend "BaseTarget_BareGlobal") >>
  TRY(rename1 `TopLevelNameTarget` >> suspend "BaseTarget_TopLevel") >>
  TRY(rename1 `SubscriptTarget` >> suspend "BaseTarget_Subscript") >>
  TRY(rename1 `AttributeTarget` >> suspend "BaseTarget_Attribute") >>
  TRY(rename1 `Name` >> suspend "Expr_Name") >>
  TRY(rename1 `BareGlobalName` >> suspend "Expr_BareGlobalName") >>
  TRY(rename1 `TopLevelName` >> suspend "Expr_TopLevelName") >>
  TRY(rename1 `FlagMember` >> suspend "Expr_FlagMember") >>
  TRY(rename1 `IfExp` >> suspend "Expr_IfExp") >>
  TRY(rename1 `Literal` >> suspend "Expr_Literal") >>
  TRY(rename1 `StructLit` >> suspend "Expr_StructLit") >>
  TRY(rename1 `Subscript` >> suspend "Expr_Subscript") >>
  TRY(rename1 `Attribute` >> suspend "Expr_Attribute") >>
  TRY(rename1 `Builtin` >> suspend "Expr_Builtin") >>
  TRY(rename1 `TypeBuiltin` >> suspend "Expr_TypeBuiltin") >>
  TRY(rename1 `Pop` >> suspend "Expr_Pop") >>
  TRY(rename1 `IntCall` >> suspend "Expr_Call_IntCall") >>
  TRY(rename1 `ExtCall` >> suspend "Expr_Call_ExtCall") >>
  TRY(rename1 `Send` >> suspend "Expr_Call_Send") >>
  TRY(rename1 `RawCallTarget` >> suspend "Expr_Call_RawCallTarget") >>
  TRY(rename1 `RawLog` >> suspend "Expr_Call_RawLog") >>
  TRY(rename1 `RawRevert` >> suspend "Expr_Call_RawRevert") >>
  TRY(rename1 `SelfDestructTarget` >> suspend "Expr_Call_SelfDestructTarget") >>
  TRY(rename1 `CreateTarget` >> suspend "Expr_Call_CreateTarget") >>
  TRY(rename1 `eval_exprs _ []` >> suspend "Exprs_nil") >>
  TRY(rename1 `eval_exprs _ (_::_)` >> suspend "Exprs_cons")
QED

Resume eval_all_type_sound_mutual[Pass]:
  gvs[evaluate_def, return_def, no_type_error_result_def, type_stmt_def]
QED

Resume eval_all_type_sound_mutual[Continue]:
  gvs[evaluate_def, raise_def, no_type_error_result_def, type_stmt_def,
      return_exception_typed_def]
QED

Resume eval_all_type_sound_mutual[Break]:
  gvs[evaluate_def, raise_def, no_type_error_result_def, type_stmt_def,
      return_exception_typed_def]
QED

Resume eval_all_type_sound_mutual[Return_NONE]:
  gvs[evaluate_def, raise_def, no_type_error_result_def, type_stmt_def,
      return_exception_typed_def, value_runtime_typed_def, value_has_type_def,
      evaluate_type_def]
QED

Resume eval_all_type_sound_mutual[Return_SOME]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_apply] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (er,s1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `er` >> gvs[no_type_error_result_def]
  >- (
    rename1 `eval_expr cx e st = (INL tv,s1)` >>
    Cases_on `materialise cx tv s1` >>
    rename1 `materialise cx tv s1 = (mr,s2)` >>
    Cases_on `mr` >> gvs[raise_def, no_type_error_result_def]
    >- (
      drule materialise_state >> strip_tac >> gvs[] >>
      strip_tac >> gvs[] >>
      gvs[expr_result_typed_def, expr_runtime_typed_def, return_exception_typed_def,
          value_runtime_typed_def] >>
      irule materialise_preserves_value_type >>
      simp[] >>
      metis_tac[evaluate_type_well_formed_type_value]) >>
    drule materialise_state >> strip_tac >> gvs[] >>
    strip_tac >> gvs[] >>
    conj_tac >- (
      gvs[expr_result_typed_def, expr_runtime_typed_def] >>
      drule_all evaluate_type_not_NoneT_imp_not_NoneTV >> strip_tac >>
      drule_all materialise_typed_non_none_no_type_error >> simp[]) >>
    drule materialise_no_control >> strip_tac >>
    Cases_on `y` >> gvs[no_control_exc_def, return_exception_typed_def]) >>
  strip_tac >> gvs[] >>
  drule_all eval_expr_exception_return_typed >> simp[]
QED

Resume eval_all_type_sound_mutual[RaiseBare]:
  gvs[evaluate_def, raise_def, no_type_error_result_def, type_stmt_def,
      return_exception_typed_def]
QED

Resume eval_all_type_sound_mutual[RaiseUnreachable]:
  gvs[evaluate_def, raise_def, no_type_error_result_def, type_stmt_def,
      return_exception_typed_def]
QED

Resume eval_all_type_sound_mutual[RaiseReason]:
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum `eval_stmt` mp_tac >>
  simp_tac(srw_ss())[evaluate_def, bind_def, return_def, raise_def,
       AllCaseEqs(), PULL_EXISTS] >>
  qhdtm_x_assum `type_stmt` mp_tac >>
  simp_tac(srw_ss())[type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  rpt gen_tac >> reverse strip_tac >- (
    rpt BasicProvers.VAR_EQ_TAC >>
    first_x_assum drule_all >> simp[] >>
    drule_all eval_expr_exception_return_typed >>
    rw[] >> gvs[no_type_error_result_def]) >>
  BasicProvers.VAR_EQ_TAC >>
  first_x_assum drule_all >> simp[] >> strip_tac >>
  qhdtm_x_assum `expr_result_typed` mp_tac >>
  asm_rewrite_tac[expr_result_typed_def, expr_runtime_typed_def] >>
  simp[evaluate_type_def] >> strip_tac >>
  drule toplevel_value_typed_StringTV >> strip_tac >> gvs[] >>
  gvs[get_Value_def, return_def, dest_StringV_def,
      lift_option_type_def, no_type_error_result_def, return_exception_typed_def] >>
  imp_res_tac raise_state >> gvs[]
QED

Resume eval_all_type_sound_mutual[AssertBare]:
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum `type_stmt` mp_tac >>
  simp_tac(srw_ss())[type_stmt_def] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qhdtm_x_assum `eval_stmt` mp_tac >>
  simp_tac(srw_ss())[evaluate_def, bind_def, return_def, raise_def,
       AllCaseEqs(), PULL_EXISTS] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `expr_res` >> gvs[no_type_error_result_def]
  >- (
    qhdtm_x_assum `expr_result_typed` mp_tac >>
    asm_rewrite_tac[expr_result_typed_def, expr_runtime_typed_def] >>
    simp[evaluate_type_def] >> strip_tac >>
    drule toplevel_value_typed_BoolTV >> strip_tac >>
    Cases_on `b` >> gvs[switch_BoolV_def, return_def, raise_def,
        no_type_error_result_def, return_exception_typed_def] >>
    metis_tac[return_state, raise_state]) >>
  strip_tac >> gvs[] >>
  drule_all eval_expr_exception_return_typed >> simp[]
QED

Resume eval_all_type_sound_mutual[AssertUnreachable]:
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum `type_stmt` mp_tac >>
  simp_tac(srw_ss())[type_stmt_def] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qhdtm_x_assum `eval_stmt` mp_tac >>
  simp_tac(srw_ss())[evaluate_def, bind_def, return_def, raise_def,
       AllCaseEqs(), PULL_EXISTS] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `expr_res` >> gvs[no_type_error_result_def]
  >- (
    qhdtm_x_assum `expr_result_typed` mp_tac >>
    asm_rewrite_tac[expr_result_typed_def, expr_runtime_typed_def] >>
    simp[evaluate_type_def] >> strip_tac >>
    drule toplevel_value_typed_BoolTV >> strip_tac >>
    Cases_on `b` >> gvs[switch_BoolV_def, return_def, raise_def,
        no_type_error_result_def, return_exception_typed_def] >>
    metis_tac[return_state, raise_state]) >>
  strip_tac >> gvs[] >>
  drule_all eval_expr_exception_return_typed >> simp[]
QED

Resume eval_all_type_sound_mutual[AssertReason]:
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum `type_stmt` mp_tac >>
  simp_tac(srw_ss())[type_stmt_def] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qhdtm_x_assum `eval_stmt` mp_tac >>
  simp_tac(srw_ss())[evaluate_def, bind_def, return_def, raise_def,
       AllCaseEqs(), PULL_EXISTS] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `well_typed_expr env e ==> _` (drule_then strip_assume_tac) >>
  Cases_on `expr_res` >> rewrite_tac[no_type_error_result_def]
  >- (
    `expr_result_typed env e x` by (
      qpat_x_assum `case INL x of INL tv => expr_result_typed env e tv | INR v1 => T` mp_tac >>
      simp[]) >>
    qhdtm_x_assum `expr_result_typed` mp_tac >>
    asm_rewrite_tac[expr_result_typed_def, expr_runtime_typed_def] >>
    rewrite_tac[Once evaluate_type_def] >> strip_tac >>
    `tv = BaseTV BoolT` by
      (qpat_x_assum `_ = SOME tv` mp_tac >>
       rewrite_tac[Once evaluate_type_def] >> simp[]) >>
    qpat_x_assum `tv = BaseTV BoolT` SUBST_ALL_TAC >>
    drule toplevel_value_typed_BoolTV >> strip_tac >>
    qpat_x_assum `x = Value (BoolV b)` SUBST_ALL_TAC >>
    Cases_on `b` >> rewrite_tac[switch_BoolV_def, return_def]
    >- (
      qpat_x_assum `!s'' tv t. _` kall_tac >>
      qpat_x_assum `!vt. _` kall_tac >>
      rpt strip_tac >> gvs[return_def, no_type_error_result_def]) >>
    Cases_on `eval_expr cx e' st1` >>
    rename1 `eval_expr cx e' st1 = (reason_res, st2)` >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `reason_res` >> gvs[no_type_error_result_def]
    >- (
      qhdtm_x_assum `expr_result_typed` mp_tac >>
      asm_rewrite_tac[expr_result_typed_def, expr_runtime_typed_def] >>
      simp[evaluate_type_def] >> strip_tac >>
      drule toplevel_value_typed_StringTV >> strip_tac >>
      gvs[bind_def, get_Value_def, return_def, dest_StringV_def,
          lift_option_type_def, raise_def, no_type_error_result_def,
          return_exception_typed_def] >>
      rw[] >> gvs[]) >>
    gvs[bind_def, no_type_error_result_def] >>
    rw[] >>
    drule eval_expr_exception_return_typed >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!s'' tv t. _` kall_tac >>
  qpat_x_assum `!vt. _` kall_tac >>
  gvs[no_type_error_result_def] >>
  drule_all eval_expr_exception_return_typed >> simp[]
QED

Resume eval_all_type_sound_mutual[Log]:
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum `type_stmt` mp_tac >>
  simp_tac(srw_ss())[type_stmt_def] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qhdtm_x_assum `eval_stmt` mp_tac >>
  simp_tac(srw_ss())[evaluate_def, bind_def, return_def, push_log_def,
       no_type_error_result_def, AllCaseEqs()] >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (exprs_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `exprs_res` >> gvs[no_type_error_result_def]
  >- (
    strip_tac >> gvs[state_well_typed_def, accounts_well_typed_def] >>
    irule env_consistent_preserved_by_frame >>
    qexists_tac `st1` >> simp[preserves_tv_eq]) >>
  strip_tac >> gvs[] >>
  drule eval_exprs_exception_return_typed >> simp[]
QED

Resume eval_all_type_sound_mutual[AnnAssign]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  `get_tenv cx = env.type_defs` by fs[env_consistent_def, env_context_consistent_def] >>
  `?tyv. evaluate_type env.type_defs typ = SOME tyv` by
    (qspecl_then [`env.type_defs`,`typ`] mp_tac assignable_type_well_formed >>
     simp[] >> rewrite_tac[well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
  pop_assum strip_assume_tac >>
  irule annassign_statement_sound_from_expr_ih >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- (qexists_tac `tyv` >> simp[]) >>
  conj_tac >- simp[] >>
  qexists_tac `e` >> qexists_tac `st` >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!tenv s'' tyv t. _`
        (qspecl_then [`env.type_defs`, `st`, `tyv`, `st`] mp_tac) >>
      simp[lift_option_type_def, return_def] >>
      disch_then drule_all >> strip_tac >>
      qpat_x_assum `well_typed_expr env' e ==> _` (drule_then strip_assume_tac) >>
      simp[]) >>
  rpt conj_tac >> asm_rewrite_tac[]
QED

Resume eval_all_type_sound_mutual[Append]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >>
  Cases_on `type_place_target env bt` >- simp[NoAsms] >>
  simp[NoAsms] >>
  rename1 `type_place_target env bt = SOME vt` >>
  Cases_on `vt` >> simp[NoAsms] >>
  rename1 `type_place_target env bt = SOME (Type ty)` >>
  Cases_on `ty` >> simp[NoAsms] >>
  rename1 `type_place_target env bt = SOME (Type (ArrayT elem_ty bd))` >>
  Cases_on `bd` >- simp[NoAsms] >>
  simp[NoAsms] >>
  rename1 `type_place_target env bt = SOME (Type (ArrayT elem_ty (Dynamic n)))` >>
  strip_tac >>
  qpat_x_assum `env = env'` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `expr_type e = elem_ty` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_base_target cx bt st` >>
  rename1 `eval_base_target cx bt st = (bt_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `bt_res`
  >- (
    PairCases_on `x` >>
    qpat_x_assum `case INL _ of _ => _ | _ => _` mp_tac >> rewrite_tac[] >> strip_tac >>
    Cases_on `eval_expr cx e st1` >>
    rename1 `eval_expr cx e st1 = (expr_res, st2)` >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `expr_res` >> gvs[no_type_error_result_def]
    >- (
      rename1 `eval_expr cx e st1 = (INL tvl, st2)` >>
      Cases_on `materialise cx tvl st2` >>
      rename1 `materialise cx tvl st2 = (mat_res, st3)` >>
      Cases_on `mat_res` >> gvs[no_type_error_result_def]
      >- (
        rename1 `materialise cx tvl st2 = (INL v, st3)` >>
        qpat_x_assum `do _ od _ = _` mp_tac >>
        simp[bind_apply, bind_def, return_def, ignore_bind_apply] >>
        Cases_on `assign_target cx (BaseTargetV x0 x1) (AppendOp v) st3` >>
        rename1 `assign_target cx (BaseTargetV loc sbs) (AppendOp v) st3 = (assign_res, st4)` >>
        Cases_on `assign_res` >> simp[return_def, ignore_bind_apply, no_type_error_result_def] >>
        strip_tac >> gvs[] >>
        imp_res_tac materialise_state >> gvs[] >>
        `?elem_tv. evaluate_type env.type_defs (expr_type e) = SOME elem_tv` by (
          drule assignable_type_well_formed >>
          rw[well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
        `well_formed_type_value elem_tv` by
          metis_tac[evaluate_type_well_formed_type_value] >>
        `value_has_type elem_tv v` by (
          gvs[expr_result_typed_def, expr_runtime_typed_def] >>
          drule_at(Pat`materialise`) materialise_preserves_value_type >>
          simp[] >> disch_then irule >> simp[]) >>
        `target_runtime_typed env cx st1 (BaseTarget bt)
           (ArrayT (expr_type e) (Dynamic n)) (BaseTargetV loc sbs)` by (
          rw[target_runtime_typed_def, target_value_shape_def,
             well_typed_atarget_def, well_typed_target_def] >>
          metis_tac[]) >>
        `runtime_consistent env cx st2` by simp[runtime_consistent_def] >>
        `target_runtime_typed env cx st2 (BaseTarget bt)
           (ArrayT (expr_type e) (Dynamic n)) (BaseTargetV loc sbs)` by (
          irule target_runtime_typed_rebuild >> simp[] >> goal_assum drule) >>
        `assign_operation_runtime_typed env (ArrayT (expr_type e) (Dynamic n)) (AppendOp v)` by
          metis_tac[stmt_assign_operation_runtime_typed_Append_from_value_has_type] >>
        `assign_operation_matches_target_shape (BaseTargetV loc sbs) (AppendOp v)` by
          simp[stmt_assign_operation_matches_target_shape_Append_BaseTargetV] >>
        `assign_target_assignable_context cx (BaseTargetV loc sbs) st2` by
          metis_tac[target_runtime_typed_imp_assignable_context, runtime_consistent_def] >>
        rpt strip_tac >> gvs[] >>
        `assignable_type env.type_defs (ArrayT (expr_type e) (Dynamic n))` by (
          simp[assignable_type_def, well_formed_type_def] >>
          drule_at(Pat`target_runtime_typed`) target_runtime_typed_place_leaf_typed >>
          simp[] >> strip_tac >>
          drule place_leaf_typed_evaluate_type >>
          simp[optionTheory.IS_SOME_EXISTS]) >>
        drule_at(Pat`assign_target`) assign_target_preserves_runtime_consistent_result >>
        disch_then $ drule_at(Pat`target_runtime_typed`) >> simp[] >>
        strip_tac >> gvs[runtime_consistent_def, no_type_error_result_def] >>
        qspecl_then [`cx`, `BaseTargetV loc sbs`, `st2`,
          `INR (Error (TypeError msg))`, `st'`, `env`, `BaseTarget bt`,
          `expr_type e`, `elem_tv`, `n`, `v`] mp_tac
          assign_target_append_no_type_error >>
        simp[no_type_error_result_def, runtime_consistent_def] >>
        strip_tac >> drule (cj 1 assign_target_no_control) >>
        rw[no_control_exc_return_exception_typed]) >>
      strip_tac >> gvs[] >>
      qpat_x_assum `do _ od _ = _` mp_tac >>
      simp[bind_apply, bind_def, return_def, ignore_bind_apply] >>
      strip_tac >> gvs[] >>
      drule materialise_state >> strip_tac >> gvs[] >>
      conj_tac
      >- (rpt strip_tac >> gvs[] >>
          gvs[expr_result_typed_def, expr_runtime_typed_def] >>
          drule_at_then Any drule
            materialise_typed_non_none_no_type_error >>
          simp[] >>
          `expr_type e ≠ NoneT` by metis_tac[assignable_type_not_NoneT] >>
          metis_tac[evaluate_type_not_NoneT_imp_not_NoneTV]) >>
      drule materialise_no_control >>
      rw[no_control_exc_return_exception_typed]) >>
    strip_tac >> gvs[] >>
    qpat_x_assum `do _ od _ = _` mp_tac >>
    simp[bind_apply, bind_def, return_def, ignore_bind_apply] >>
    strip_tac >> gvs[] >>
    drule eval_expr_exception_return_typed >> rw[]) >>
  strip_tac >>
  qpat_x_assum `case (INR _,_) of _ => _ | _ => _` mp_tac >>
  pure_rewrite_tac[pairTheory.pair_case_def] >> BETA_TAC >>
  pure_rewrite_tac[sumTheory.sum_case_def] >> BETA_TAC >> strip_tac >>
  qpat_x_assum `(INR y,st1) = (res,st')` mp_tac >>
  pure_rewrite_tac[pairTheory.PAIR_EQ] >> strip_tac >>
  qpat_x_assum `INR y = res` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `st1 = st'` (SUBST_ALL_TAC o SYM) >>
  conj_tac >- qpat_assum `state_well_typed st1` ACCEPT_TAC >>
  conj_tac >- qpat_assum `accounts_well_typed st1.accounts` ACCEPT_TAC >>
  conj_tac >- (qpat_x_assum `!s'' loc sbs t'. _` kall_tac >>
                qpat_x_assum `case INR _ of _ => _ | _ => _` kall_tac >>
                fs[no_type_error_result_def]) >>
  drule (cj 3 eval_target_no_control) >>
  rw[no_control_exc_return_exception_typed]
QED

Resume eval_all_type_sound_mutual[Assign]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_target cx tgt st` >>
  rename1 `eval_target cx tgt st = (target_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `target_res`
  >- (
    rename1 `eval_target cx tgt st = (INL gv, st1)` >>
    qpat_x_assum `case INL _ of _ => _ | _ => _` mp_tac >> rewrite_tac[] >> strip_tac >>
    Cases_on `eval_expr cx e st1` >>
    rename1 `eval_expr cx e st1 = (expr_res, st2)` >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `expr_res` >> gvs[no_type_error_result_def]
    >- (
      rename1 `eval_expr cx e st1 = (INL tvl, st2)` >>
      Cases_on `materialise cx tvl st2` >>
      rename1 `materialise cx tvl st2 = (mat_res, st3)` >>
      Cases_on `mat_res` >> gvs[no_type_error_result_def]
      >- (
        rename1 `materialise cx tvl st2 = (INL v, st3)` >>
        Cases_on `assign_target cx gv (Replace v) st3` >>
        rename1 `assign_target cx gv (Replace v) st3 = (assign_res, st4)` >>
        Cases_on `assign_res` >> gvs[return_def, bind_apply, no_type_error_result_def]
        >- (
          imp_res_tac materialise_state >> gvs[] >>
          simp[bind_apply, ignore_bind_apply, return_def] >>
          strip_tac >> gvs[] >>
          drule_at(Pat`assign_target`)
            assign_target_preserves_state_well_typed_no_ctx >>
          simp[runtime_consistent_def, assign_operation_runtime_typed_def] >>
          disch_then drule >>
          simp[value_runtime_typed_def, expr_runtime_typed_def, PULL_EXISTS] >>
          drule_at(Pat`materialise`) materialise_preserves_value_type >>
          gvs[expr_result_typed_def, expr_runtime_typed_def] >>
          drule evaluate_type_well_formed_type_value >>
          strip_tac >>
          disch_then drule_all >> strip_tac >>
          disch_then $ drule_at Any >>
          disch_then $ drule_at Any >>
          strip_tac >>
          `target_runtime_typed env cx st2 tgt (expr_type e) gv` by (
            irule target_runtime_typed_rebuild >>
            simp[runtime_consistent_def] >>
            goal_assum drule) >>
          first_x_assum drule >> strip_tac >>
          conj_tac >- simp[] >>
          conj_tac >- simp[] >>
          drule_at(Pat`assign_target`) assign_target_preserves_runtime_consistent_no_ctx >>
          simp[runtime_consistent_def, assign_operation_runtime_typed_def] >>
          disch_then drule >>
          simp[value_runtime_typed_def, expr_runtime_typed_def] >>
          strip_tac >> first_x_assum irule >> simp[] >>
          qexists_tac `tgt` >> qexists_tac `expr_type e` >> simp[] >>
          qexists_tac `tv` >> simp[]) >>
        qpat_x_assum `do _ od _ = _` mp_tac >> simp[bind_apply, return_def] >>
        Cases_on `res` >> gvs[ignore_bind_apply] >>
        strip_tac >> gvs[] >>
        strip_tac >> gvs[] >>
        imp_res_tac materialise_state >> gvs[] >>
        `?tv. evaluate_type env.type_defs (expr_type e) = SOME tv` by (
          gvs[expr_result_typed_def, expr_runtime_typed_def] >>
          drule evaluate_type_well_formed_type_value >> simp[]) >>
        `well_formed_type_value tv` by (
          drule evaluate_type_well_formed_type_value >> simp[]) >>
        `toplevel_value_typed tvl tv` by (
          gvs[expr_result_typed_def, expr_runtime_typed_def]) >>
        `value_has_type tv v` by metis_tac[materialise_preserves_type] >>
        `target_runtime_typed env cx st2 tgt (expr_type e) gv` by (
          irule target_runtime_typed_rebuild >>
          simp[runtime_consistent_def] >> goal_assum drule) >>
        drule_at(Pat`assign_target`)
          assign_target_preserves_state_well_typed_no_ctx >>
        simp[assign_operation_runtime_typed_def, value_runtime_typed_def] >>
        simp[runtime_consistent_def] >>
        strip_tac >>
        drule_all eval_expr_preserves_ec >> strip_tac >>
        conj_asm1_tac
        >- (rpt strip_tac >> gvs[] >>
            first_x_assum (qspecl_then [`env`,`tgt`,`expr_type e`] mp_tac) >>
            simp[]) >>
        drule_at(Pat`assign_target`)
          assign_target_preserves_runtime_consistent_no_ctx >>
        simp[runtime_consistent_def, assign_operation_runtime_typed_def] >>
        simp[value_runtime_typed_def, PULL_EXISTS] >>
        disch_then(drule_at(Pat`target_runtime_typed`)) >> simp[] >>
        strip_tac >>
        Cases_on `y` >> rw[return_exception_typed_def]
        >- (
          (* Error case: need e' ≠ TypeError msg *)
          `runtime_consistent env cx st2` by (
            simp[runtime_consistent_def] >> goal_assum drule >> simp[]) >>
          `value_runtime_typed env (expr_type e) v` by (
            simp[value_runtime_typed_def] >>
            qexists `tv` >> simp[]) >>
          `assign_operation_runtime_typed env (expr_type e) (Replace v)` by
            simp[assign_operation_runtime_typed_def] >>
          `assign_operation_matches_target_shape gv (Replace v)` by
            metis_tac[assign_operation_matches_target_shape_Replace_from_typed] >>
          `assign_target_assignable_context cx gv st2` by
            metis_tac[target_runtime_typed_imp_assignable_context] >>
          drule assign_target_no_type_error >>
          simp[no_type_error_result_def] >> metis_tac[])
        >- (
          (* ReturnException case: assign_target never returns ReturnException *)
          drule (cj 1 assign_target_no_return) >> simp[])) >>
      strip_tac >> gvs[] >>
      drule materialise_state >> strip_tac >> gvs[] >>
      conj_tac
      >- (rpt strip_tac >> gvs[] >>
          (* materialise TypeError sub-case: contradiction from typed non-None expr *)
          gvs[expr_result_typed_def, expr_runtime_typed_def] >>
          drule_at_then Any drule
            materialise_typed_non_none_no_type_error >>
          simp[] >>
          `expr_type e ≠ NoneT` by metis_tac[assignable_type_not_NoneT] >>
          metis_tac[evaluate_type_not_NoneT_imp_not_NoneTV]) >>
      drule materialise_no_control >> rw[no_control_exc_return_exception_typed]) >>
    rw[] >> drule eval_expr_exception_return_typed >> rw[]) >>
  strip_tac >>
  qpat_x_assum `case (INR _,_) of _ => _ | _ => _` mp_tac >>
  pure_rewrite_tac[pairTheory.pair_case_def] >> BETA_TAC >>
  pure_rewrite_tac[sumTheory.sum_case_def] >> BETA_TAC >> strip_tac >>
  qpat_x_assum `(INR y,st1) = (res,st')` mp_tac >>
  pure_rewrite_tac[pairTheory.PAIR_EQ] >> strip_tac >>
  qpat_x_assum `INR y = res` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `st1 = st'` (SUBST_ALL_TAC o SYM) >>
  conj_tac >- qpat_assum `state_well_typed st1` ACCEPT_TAC >>
  conj_tac >- qpat_assum `accounts_well_typed st1.accounts` ACCEPT_TAC >>
  conj_tac >- (qpat_x_assum `!s'' gv t. _` kall_tac >>
                qpat_x_assum `case INR _ of _ => _ | _ => _` kall_tac >>
                fs[no_type_error_result_def]) >>
  drule (cj 1 eval_target_no_control) >>
  rw[no_control_exc_return_exception_typed]
QED

Resume eval_all_type_sound_mutual[AugAssign]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_base_target cx bt st` >>
  rename1 `eval_base_target cx bt st = (target_res, st1)` >>
  (* Apply base-target IH *)
  `type_place_target env bt = SOME (Type ty)` by fs[well_typed_target_def] >>
  qpat_x_assum `!env vt st res st'. _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ eval_base_target _ _ _ = _ ==> _`
    (qspecl_then [`env`, `Type ty`, `st`, `target_res`, `st1`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  Cases_on `target_res`
  >- (
    (* INL: base target evaluation succeeded *)
    PairCases_on `x` >>
    qpat_x_assum `case INL _ of _ => _ | _ => _` mp_tac >> rewrite_tac[] >> strip_tac >>
    pure_rewrite_tac[pairTheory.pair_case_def] >> BETA_TAC >>
    pure_rewrite_tac[sumTheory.sum_case_def] >> BETA_TAC >>
    rename1 `eval_base_target cx bt st = (INL (loc,sbs), st1)` >>
    suspend "AugAssign_base_inl")
  >- (
    (* INR: base target evaluation returned exception *)
    fs[no_type_error_result_def] >>
    strip_tac >>
    qpat_x_assum `INR y = res` (SUBST_ALL_TAC o SYM) >>
    qpat_x_assum `st1 = st'` (SUBST_ALL_TAC o SYM) >>
    conj_tac >- qpat_assum `state_well_typed st1` ACCEPT_TAC >>
    conj_tac >- qpat_assum `accounts_well_typed st1.accounts` ACCEPT_TAC >>
    conj_tac >- (rpt strip_tac >>
                  qpat_x_assum `!msg. y <> Error (TypeError msg)`
                    (qspec_then `msg` mp_tac) >>
                  qpat_x_assum `INR y = INR (Error (TypeError msg))` mp_tac >>
                  simp[]) >>
    pure_rewrite_tac[sumTheory.sum_case_def] >> BETA_TAC >>
    conj_tac >- qpat_assum `env_consistent env cx st1` ACCEPT_TAC >>
    drule (cj 3 eval_target_no_control) >>
    rw[no_control_exc_return_exception_typed])
QED

Resume eval_all_type_sound_mutual[AugAssign_base_inl]:
  Cases_on `eval_expr cx e st1` >>
  rename1 `eval_expr cx e st1 = (expr_res, st2)` >>
  (* Apply expr IH *)
  first_x_assum (qspecl_then [`st`, `loc`, `sbs`, `st1`] mp_tac) >> simp[] >>
  disch_then (qspecl_then [`env`, `st1`, `expr_res`, `st2`] mp_tac) >> simp[] >>
  `state_well_typed st1 /\ env_consistent env cx st1 /\ accounts_well_typed st1.accounts` by
    simp[] >>
  simp[] >> strip_tac >>
  Cases_on `expr_res` >> gvs[no_type_error_result_def]
  >- (
    (* INL: expression evaluation succeeded *)
    rename1 `eval_expr cx e st1 = (INL tvl, st2)` >>
    suspend "AugAssign_expr_inl")
  >- (
    (* INR: expression evaluation returned exception *)
    qpat_x_assum `do _ od _ = _` mp_tac >>
    simp[bind_apply, bind_def] >>
    strip_tac >> gvs[] >>
    drule eval_expr_exception_return_typed >> strip_tac >>
    strip_tac >> gvs[])
QED

Resume eval_all_type_sound_mutual[AugAssign_expr_inl]:
  Cases_on `get_Value tvl st2` >>
  rename1 `get_Value tvl st2 = (val_res, st3)` >>
  Cases_on `val_res` >> gvs[no_type_error_result_def]
  >- (
    (* INL get_Value: got a plain value *)
    rename1 `get_Value tvl st2 = (INL v, st3)` >>
    suspend "AugAssign_get_value_inl")
  >- (
    (* INR get_Value: get_Value failed *)
    qpat_x_assum `do _ od _ = _` mp_tac >>
    simp[bind_apply, bind_def] >>
    strip_tac >> gvs[] >>
    imp_res_tac get_Value_state >> gvs[] >>
    drule get_Value_no_control >> strip_tac >>
    `!msg. y <> Error (TypeError msg)` by (
      gvs[expr_result_typed_def, expr_runtime_typed_def] >>
      drule_all well_typed_binop_not_In_second_type >> strip_tac >>
      drule_all evaluate_type_not_ArrayT_imp_not_ArrayTV >> strip_tac >>
      drule_all evaluate_type_not_NoneT_imp_not_NoneTV >> strip_tac >>
      drule_all get_Value_no_type_error >>
      simp[no_type_error_result_def]) >>
    drule no_control_exc_return_exception_typed >> strip_tac >>
    strip_tac >> gvs[no_type_error_result_def])
QED

Resume eval_all_type_sound_mutual[AugAssign_get_value_inl]:
  imp_res_tac get_Value_state >> gvs[] >>
  `tvl = Value v` by (
    qpat_x_assum `get_Value _ _ = _` mp_tac >>
    Cases_on `tvl` >> simp[get_Value_def, return_def, raise_def]) >>
  `target_runtime_typed env cx st1 (BaseTarget bt) ty (BaseTargetV loc sbs)` by (
    simp[target_runtime_typed_def, well_typed_atarget_def,
         target_value_shape_def] >>
    qexists `loc_vt` >> simp[]) >>
  `target_runtime_typed env cx st2 (BaseTarget bt) ty (BaseTargetV loc sbs)` by
    metis_tac[target_runtime_typed_rebuild, runtime_consistent_def] >>
  `assign_operation_runtime_typed env ty (Update ty bop v)` by (
    simp[assign_operation_runtime_typed_def] >>
    qexists_tac `expr_type e` >>
    gvs[expr_result_typed_def, expr_runtime_typed_def, value_runtime_typed_def,
        toplevel_value_typed_def]) >>
  `assign_operation_matches_target_shape (BaseTargetV loc sbs) (Update ty bop v)` by
    simp[assign_operation_matches_target_shape_def] >>
  `assign_target_assignable_context cx (BaseTargetV loc sbs) st2` by
    metis_tac[target_runtime_typed_imp_assignable_context] >>
  simp[bind_apply, return_def] >>
  Cases_on `assign_target cx (BaseTargetV loc sbs) (Update ty bop v) st2` >>
  rename1 `assign_target _ _ _ _ = (assign_res, st4)` >>
  Cases_on `assign_res` >> simp[return_def, ignore_bind_def, no_type_error_result_def]
  >- suspend "AugAssign_assign_inl"
  >- suspend "AugAssign_assign_inr"
QED

Resume eval_all_type_sound_mutual[AugAssign_assign_inl]:
  (* INL assign_target: update succeeded *)
  strip_tac >> gvs[] >>
  drule_at(Pat`assign_target`)
    assign_target_preserves_runtime_consistent >>
  disch_then $ drule_at(Pat`target_runtime_typed`) >>
  simp[] >>
  impl_keep_tac >- simp[runtime_consistent_def] >>
  strip_tac >> gvs[runtime_consistent_def, bind_def, return_def]
QED

Resume eval_all_type_sound_mutual[AugAssign_assign_inr]:
  (* INR assign_target: update returned exception *)
  strip_tac >> gvs[] >>
  drule_at(Pat`assign_target`)
    assign_target_preserves_runtime_consistent_result >>
  disch_then $ drule_at(Pat`target_runtime_typed`) >>
  simp[] >>
  impl_keep_tac >- simp[runtime_consistent_def] >>
  strip_tac >> gvs[runtime_consistent_def] >>
  `res = INR y /\ st' = st4` by (
    qpat_x_assum `do _ od _ = _` mp_tac >>
    simp[bind_def, return_def]) >>
  gvs[] >>
  Cases_on `y` >> rw[return_exception_typed_def]
  >- (
    (* Error sub-case: derive no-TypeError from updated bridges *)
    `runtime_consistent env cx st2` by (
      simp[runtime_consistent_def] >> goal_assum drule >> simp[]) >>
    `well_typed_binop ty bop ty (expr_type e)` by (
      gvs[expr_result_typed_def, expr_runtime_typed_def,
          value_runtime_typed_def, toplevel_value_typed_def]) >>
    `value_runtime_typed env (expr_type e) v` by (
      gvs[expr_result_typed_def, expr_runtime_typed_def,
          value_runtime_typed_def, toplevel_value_typed_def]) >>
    drule assign_target_update_no_type_error >>
    simp[no_type_error_result_def, assign_operation_matches_target_shape_def] >>
    disch_then drule >> disch_then drule >>
    simp[] >> metis_tac[])
  >- (
    (* ReturnException sub-case: assign_target never returns ReturnException *)
    drule (cj 1 assign_target_no_return) >> simp[] >>
    disch_then drule >> simp[])
QED

Resume eval_all_type_sound_mutual[If]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  first_x_assum drule_all >> strip_tac >>
  simp_tac (srw_ss()) [] >>
  rename1 `eval_expr cx e st = (cond_res, st1)` >>
  reverse(Cases_on `cond_res`)
  >- (
    strip_tac >>
    gvs[no_type_error_result_def] >>
    drule_all eval_expr_exception_return_typed >> simp[]
  ) >>
  simp_tac(srw_ss())[ignore_bind_def, bind_def] >>
  CASE_TAC >>
  reverse CASE_TAC >- (
    strip_tac >> gvs[] >>
    pop_assum mp_tac >>
    simp_tac(srw_ss())[push_scope_def,return_def]
  ) >>
  rename1 `eval_expr cx e st = (INL tv, st1)` >>
  gvs[expr_result_typed_def, expr_runtime_typed_def, evaluate_type_def] >>
  drule toplevel_value_typed_BoolTV >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  strip_tac >>
  qpat_x_assum `IS_SOME (type_stmts env ret_ty ss)` mp_tac >>
  qpat_x_assum `IS_SOME (type_stmts env ret_ty ss')` mp_tac >>
  simp[optionTheory.IS_SOME_EXISTS] >> ntac 2 strip_tac >>
  irule scope_bracket_post >>
  conj_asm1_tac >- (
    irule env_consistent_env_maps_wf >> simp[] >>
    goal_assum drule >> simp[]
  ) >>
  qmatch_asmsub_abbrev_tac`finally body_fun pop_scope sf` >>
  qexistsl_tac[`body_fun`,`st1`] >>
  simp[bind_def, ignore_bind_def] >>
  first_x_assum (drule_then drule) >> strip_tac >>
  last_x_assum (drule_then drule) >> strip_tac >>
  gvs[push_scope_def, return_def, finally_def] >>
  qmatch_goalsub_abbrev_tac`body_fun st2` >>
  Cases_on`body_fun st2` >> gvs[] >>
  qmatch_assum_rename_tac`body_fun st2 = (rf,sf)` >>
  qho_match_abbrev_tac`P rf sf` >>
  irule switch_BoolV_post >>
  qunabbrev_tac`body_fun` >>
  goal_assum $ drule_at(Pat`switch_BoolV`) >>
  simp[] >>
  `accounts_well_typed st2.accounts` by simp[Abbr`st2`] >>
  `env_consistent env cx st2` by (simp[Abbr`st2`] >> irule push_scope_env_consistent >> simp[]) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Abbr`P`] >>
    `state_well_typed st2` by gvs[Abbr`st2`, state_well_typed_def, scope_well_typed_def] >>
    first_x_assum drule_all >> strip_tac >>
    simp[] >>
    `st2 = st1 with scopes := FEMPTY::st1.scopes`
      by simp[evaluation_state_component_equality, Abbr`st2`] >>
    conj_tac >- (
      strip_tac >> gvs[] >>
      drule eval_stmts_preserves_scopes_len >> simp[]) >>
    Cases_on `res1` >> gvs[]
    >- (
      Cases_on `st1'.scopes` >> gvs[]
      >- (drule eval_stmts_preserves_scopes_len >> simp[]) >>
      irule type_stmts_env_consistent_after_pop >> simp[] >>
      conj_tac >- (
        drule eval_stmts_preserves_scopes_len >> simp[] >>
        strip_tac >>
        `st1.scopes <> []` by fs[env_consistent_def, env_scopes_consistent_def] >>
        Cases_on `st1.scopes` >> gvs[] >>
        Cases_on `t` >> gvs[]) >>
      conj_tac >- (
        rpt strip_tac >> fs[] >>
        drule_at(Pat`eval_stmts`)lookup_scopes_not_in_new_head >>
        simp[] >> disch_then irule >>
        qpat_x_assum`env_consistent _ _ st1`mp_tac >>
        simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
      conj_tac >- (
        qexists_tac `x` >>
        qexists_tac `ret_ty` >>
        qexists_tac `ss'` >> simp[] >>
        rpt strip_tac >> fs[] >>
        drule eval_stmts_preserves_scopes_dom >> simp[preserves_scopes_dom_def] >>
        strip_tac >> gvs[FDOM_FEMPTY] >>
        drule lookup_scopes_is_some_same_fdoms >> simp[] >>
        disch_then (qspec_then `id` mp_tac) >> simp[optionTheory.IS_SOME_EXISTS] >>
        qpat_x_assum `env_consistent env cx st1` mp_tac >>
        simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS] >>
        strip_tac >> strip_tac >>
        Cases_on `lookup_scopes id t` >> gvs[] >>
        qpat_x_assum `!id entry. lookup_scopes id st1.scopes = SOME entry ==> _`
          (qspec_then `id` mp_tac) >> simp[] >> metis_tac[]) >>
      qexists_tac `st1` >> simp[] >>
      qspecl_then [`cx`, `ss'`, `FEMPTY`, `st1`, `INL ()`, `st1'`]
        mp_tac (GEN_ALL eval_stmts_scope_bracket_gen_preserves_tv) >>
      simp[] >>
      disch_then irule >>
      qmatch_goalsub_abbrev_tac `preserves_tv cx stp st1'` >>
      `stp = st1 with scopes updated_by CONS FEMPTY` by simp[Abbr`stp`] >>
      pop_assum SUBST1_TAC >>
      irule(CONJUNCT1(CONJUNCT2 eval_preserves_tv)) >>
      qexists_tac `INL ()` >> qexists_tac `ss'` >> simp[] >>
      gvs[Abbr`stp`]) >>
    Cases_on `st1'.scopes` >> gvs[]
    >- (drule eval_stmts_preserves_scopes_len >> simp[]) >>
    conj_tac >- (
      irule env_extends_env_consistent_after_pop >> simp[] >>
      conj_tac >- (
        drule eval_stmts_preserves_scopes_len >> simp[] >>
        strip_tac >>
        `st1.scopes <> []` by fs[env_consistent_def, env_scopes_consistent_def] >>
        Cases_on `st1.scopes` >> gvs[] >>
        Cases_on `t` >> gvs[]) >>


      conj_tac >- (
        conj_tac >- (
          rpt strip_tac >> fs[] >>
          `?entry. lookup_scopes id st1.scopes = SOME entry` by (
            qpat_x_assum`env_consistent _ _ st1`mp_tac >>
            simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
          `FLOOKUP h id = NONE` suffices_by simp[] >>
          drule lookup_scopes_not_in_new_head >>
          disch_then(qspecl_then [`id`, `entry`] mp_tac) >>
          simp[] >>
          disch_then irule >> simp[]) >>
        rpt strip_tac >> fs[] >>
        `?entry. lookup_scopes id st1.scopes = SOME entry` by (
          qpat_x_assum`env_consistent _ _ st1`mp_tac >>
          simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
        `FLOOKUP h id = NONE` suffices_by simp[] >>
        drule lookup_scopes_not_in_new_head >>
        disch_then(qspecl_then [`id`, `entry`] mp_tac) >>
        simp[] >>
        disch_then irule >> simp[]) >>
      conj_tac >- (
        qexists_tac `env_exn` >> simp[] >>
        rpt strip_tac >> fs[] >>
        `lookup_scopes id st1.scopes = NONE` by (
          qpat_x_assum`env_consistent env cx st1`mp_tac >>
          simp[env_consistent_def, env_scopes_consistent_def] >> strip_tac >>
          Cases_on `lookup_scopes id st1.scopes` >> gvs[] >>
          metis_tac[optionTheory.IS_SOME_DEF]) >>
        qspecl_then [`cx`, `ss'`, `st1`, `FEMPTY`, `st1.scopes`, `INR y`, `st1'`, `id`, `h`, `t`]
          mp_tac eval_stmts_preserves_tail_lookup_none >>
        simp[]) >>
      qexists_tac `st1` >> simp[] >>
      qspecl_then [`cx`, `ss'`, `FEMPTY`, `st1`, `INR y`, `st1'`]
        mp_tac (GEN_ALL eval_stmts_scope_bracket_gen_preserves_tv) >>
      simp[] >> disch_then irule >>
      qmatch_goalsub_abbrev_tac `preserves_tv cx stp st1'` >>
      `stp = st1 with scopes updated_by CONS FEMPTY` by simp[Abbr`stp`] >>
      pop_assum SUBST1_TAC >>
      irule(CONJUNCT1(CONJUNCT2 eval_preserves_tv)) >>
      qexists_tac `INR y` >> qexists_tac `ss'` >> simp[] >>
      gvs[Abbr`stp`]) >>
    irule env_extends_return_exception_typed >>
    qexists_tac `env_exn` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  simp[Abbr`P`] >>
  `state_well_typed st2` by gvs[Abbr`st2`, state_well_typed_def, scope_well_typed_def] >>
  first_x_assum drule_all >> strip_tac >>
  simp[] >>
  `st2 = st1 with scopes := FEMPTY::st1.scopes`
    by simp[evaluation_state_component_equality, Abbr`st2`] >>
  conj_tac >- (
    strip_tac >> gvs[] >>
    drule eval_stmts_preserves_scopes_len >> simp[]) >>
  Cases_on `res1` >> gvs[]
  >- (
    Cases_on `st1'.scopes` >> gvs[]
    >- (drule eval_stmts_preserves_scopes_len >> simp[]) >>
    irule type_stmts_env_consistent_after_pop >> simp[] >>
    conj_tac >- (
      drule eval_stmts_preserves_scopes_len >> simp[] >>
      strip_tac >>
      `st1.scopes <> []` by fs[env_consistent_def, env_scopes_consistent_def] >>
      Cases_on `st1.scopes` >> gvs[] >>
      Cases_on `t` >> gvs[]) >>
    conj_tac >- (
      rpt strip_tac >> fs[] >>
      drule_at(Pat`eval_stmts`)lookup_scopes_not_in_new_head >>
      simp[] >> disch_then irule >>
      qpat_x_assum`env_consistent _ _ st1`mp_tac >>
      simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
    conj_tac >- (
      qexists_tac `x'` >>
      qexists_tac `ret_ty` >>
      qexists_tac `ss` >> simp[] >>
      rpt strip_tac >> fs[] >>
      drule eval_stmts_preserves_scopes_dom >> simp[preserves_scopes_dom_def] >>
      strip_tac >> gvs[FDOM_FEMPTY] >>
      drule lookup_scopes_is_some_same_fdoms >> simp[] >>
      disch_then (qspec_then `id` mp_tac) >> simp[optionTheory.IS_SOME_EXISTS] >>
      qpat_x_assum `env_consistent env cx st1` mp_tac >>
      simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS] >>
      strip_tac >> strip_tac >>
      Cases_on `lookup_scopes id t` >> gvs[] >>
      qpat_x_assum `!id entry. lookup_scopes id st1.scopes = SOME entry ==> _`
        (qspec_then `id` mp_tac) >> simp[] >> metis_tac[]) >>
    qexists_tac `st1` >> simp[] >>
    qspecl_then [`cx`, `ss`, `FEMPTY`, `st1`, `INL x''`, `st1'`]
      mp_tac (GEN_ALL eval_stmts_scope_bracket_gen_preserves_tv) >>
    simp[] >>
    disch_then irule >>
    qmatch_goalsub_abbrev_tac `preserves_tv cx stp st1'` >>
    `stp = st1 with scopes updated_by CONS FEMPTY` by simp[Abbr`stp`] >>
    pop_assum SUBST1_TAC >>
    irule(CONJUNCT1(CONJUNCT2 eval_preserves_tv)) >>
    qexists_tac `INL x''` >> qexists_tac `ss` >> simp[] >>
    gvs[Abbr`stp`]) >>
  Cases_on `st1'.scopes` >> gvs[]
  >- (drule eval_stmts_preserves_scopes_len >> simp[]) >>
  conj_tac >- (
    irule env_extends_env_consistent_after_pop >> simp[] >>
    conj_tac >- (
      drule eval_stmts_preserves_scopes_len >> simp[] >>
      strip_tac >>
      `st1.scopes <> []` by fs[env_consistent_def, env_scopes_consistent_def] >>
      Cases_on `st1.scopes` >> gvs[] >>
      Cases_on `t` >> gvs[]) >>
    conj_tac >- (
      conj_tac >- (
        rpt strip_tac >> fs[] >>
        `?entry. lookup_scopes id st1.scopes = SOME entry` by (
          qpat_x_assum`env_consistent _ _ st1`mp_tac >>
          simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
        `FLOOKUP h id = NONE` suffices_by simp[] >>
        drule lookup_scopes_not_in_new_head >>
        disch_then(qspecl_then [`id`, `entry`] mp_tac) >>
        simp[] >> disch_then irule >> simp[]) >>
      rpt strip_tac >> fs[] >>
      `?entry. lookup_scopes id st1.scopes = SOME entry` by (
        qpat_x_assum`env_consistent _ _ st1`mp_tac >>
        simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
      `FLOOKUP h id = NONE` suffices_by simp[] >>
      drule lookup_scopes_not_in_new_head >>
      disch_then(qspecl_then [`id`, `entry`] mp_tac) >>
      simp[] >> disch_then irule >> simp[]) >>
    conj_tac >- (
      qexists_tac `env_exn` >> simp[] >>
      rpt strip_tac >> fs[] >>
      `lookup_scopes id st1.scopes = NONE` by (
        qpat_x_assum`env_consistent env cx st1`mp_tac >>
        simp[env_consistent_def, env_scopes_consistent_def] >> strip_tac >>
        Cases_on `lookup_scopes id st1.scopes` >> gvs[] >>
        metis_tac[optionTheory.IS_SOME_DEF]) >>
      qspecl_then [`cx`, `ss`, `st1`, `FEMPTY`, `st1.scopes`, `INR y`, `st1'`, `id`, `h`, `t`]
        mp_tac eval_stmts_preserves_tail_lookup_none >>
      simp[]) >>
    qexists_tac `st1` >> simp[] >>
    qspecl_then [`cx`, `ss`, `FEMPTY`, `st1`, `INR y`, `st1'`]
      mp_tac (GEN_ALL eval_stmts_scope_bracket_gen_preserves_tv) >>
    simp[] >> disch_then irule >>
    qmatch_goalsub_abbrev_tac `preserves_tv cx stp st1'` >>
    `stp = st1 with scopes updated_by CONS FEMPTY` by simp[Abbr`stp`] >>
    pop_assum SUBST1_TAC >>
    irule(CONJUNCT1(CONJUNCT2 eval_preserves_tv)) >>
    qexists_tac `INR y` >> qexists_tac `ss` >> simp[] >>
    gvs[Abbr`stp`]) >>
  irule env_extends_return_exception_typed >>
  qexists_tac `env_exn` >> simp[]
QED

Resume eval_all_type_sound_mutual[Expr]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, type_check_def,
    assert_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `eval_expr cx e st` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `q` >> gvs[no_type_error_result_def]
  >- (
    strip_tac >> gvs[expr_result_typed_def] >>
    metis_tac[]) >>
  strip_tac >> gvs[] >>
  drule_all eval_expr_exception_return_typed >> simp[]
QED

Resume eval_all_type_sound_mutual[Stmts_nil]:
  rpt gen_tac >> strip_tac >>
  gvs[Once type_stmt_def, Once evaluate_def,
      return_def, no_type_error_result_def]
QED

Resume eval_all_type_sound_mutual[Stmts_cons]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_stmts _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, ignore_bind_apply] >>
  Cases_on `eval_stmt cx s st` >>
  rename1 `eval_stmt cx s st = (r1,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `r1` >> gvs[]
  >- (
    Cases_on `eval_stmts cx ss st1` >>
    rename1 `eval_stmts cx ss st1 = (r2,st2)` >>
    first_x_assum drule_all >> strip_tac >>
    strip_tac >> fs[bind_def] >> gvs[] >>
    Cases_on `r2` >> gvs[no_type_error_result_def]
    >- (
      qexists_tac `env_exn` >> simp[] >>
      irule env_extends_trans >>
      qexists_tac `env''` >> simp[] >>
      irule type_stmt_env_extends >> simp[] >>
      conj_tac >- (irule env_consistent_env_maps_wf >> goal_assum drule >> simp[]) >>
      qexists_tac `ret_ty` >> qexists_tac `s` >> simp[]) >>
    simp[]) >>
  strip_tac >> gvs[] >>
  qexists_tac `env` >> simp[env_extends_refl]
QED

Resume eval_all_type_sound_mutual[For]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  `env.type_defs = get_tenv cx` by (
    qpat_x_assum `env_consistent env cx st` mp_tac >>
    rewrite_tac[env_consistent_def, env_context_consistent_def] >>
    strip_tac >> simp[]) >>
  `?env_after. type_stmts (extend_local env (string_to_num id) typ F) ret_ty body' = SOME env_after` by (
    qpat_x_assum `IS_SOME (type_stmts (extend_local env (string_to_num id) typ F) ret_ty body')` mp_tac >>
    rewrite_tac[optionTheory.IS_SOME_EXISTS]) >>
  `well_formed_type env.type_defs typ` by metis_tac[assignable_type_well_formed] >>
  qpat_x_assum `well_formed_type env.type_defs typ` mp_tac >>
  qpat_assum `env.type_defs = get_tenv cx` (fn th => rewrite_tac[th]) >>
  rewrite_tac[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  strip_tac >>
  rename1 `evaluate_type (get_tenv cx) typ = SOME iter_tyv` >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, lift_option_type_def,
       check_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `eval_iterator cx it st` >>
  rename1 `eval_iterator cx it st = (iter_res, st1)` >>
  qpat_x_assum `!tenv s'' tyv t. _`
    (qspecl_then [`get_tenv cx`, `st`, `iter_tyv`, `st`] mp_tac) >>
  impl_tac >- simp[lift_option_type_def, return_def] >>
  disch_then (qspecl_then [`env`, `typ`, `st`, `iter_res`, `st1`] mp_tac) >>
  impl_tac >- metis_tac[] >>
  strip_tac >>
  Cases_on `iter_res`
  >- (
    rename1 `eval_iterator cx it st = (INL vs, st1)` >>
    qpat_x_assum `case INL vs of INL vs => _ | INR v1 => _`
      (mp_tac o SIMP_RULE (srw_ss()) []) >>
    strip_tac >>
    `tyv = iter_tyv` by (
      qpat_x_assum `evaluate_type env.type_defs typ = SOME tyv` mp_tac >>
      qpat_assum `env.type_defs = get_tenv cx` (fn th => rewrite_tac[th]) >>
      qpat_assum `evaluate_type (get_tenv cx) typ = SOME iter_tyv` (fn th => rewrite_tac[th]) >>
      simp[]) >>
    qpat_x_assum `EVERY (value_has_type tyv) vs` mp_tac >>
    qpat_x_assum `tyv = iter_tyv` (fn th => rewrite_tac[th]) >>
    strip_tac >>
    Cases_on `compatible_bound (Dynamic n) (LENGTH vs)`
    >- (
      qpat_assum `evaluate_type (get_tenv cx) typ = SOME iter_tyv` (fn th => rewrite_tac[th]) >>
      qpat_assum `eval_iterator cx it st = (INL vs, st1)` (fn th => rewrite_tac[th]) >>
      rewrite_tac[bind_def, return_def, raise_def, assert_def, check_def, lift_option_type_def] >>
      Cases_on `eval_for cx iter_tyv (string_to_num id) body' vs st1` >>
      rename1 `eval_for cx iter_tyv (string_to_num id) body' vs st1 = (for_res, st2)` >>
      qpat_x_assum `!tenv s'' tyv t s1 vs' t' s2 x t''. _`
        (qspecl_then [`get_tenv cx`, `st`, `iter_tyv`, `st`, `st`, `vs`, `st1`, `st1`, `()`, `st1`] mp_tac) >>
      impl_tac >- simp[lift_option_type_def, return_def, check_def, assert_def] >>
      disch_then (qspecl_then [`env`, `ret_ty`, `typ`, `env_after`, `st1`, `for_res`, `st2`] mp_tac) >>
      simp[bind_def, ignore_bind_def, return_def, assert_def] >> strip_tac >>
      strip_tac >> gvs[no_type_error_result_def]) >>
    strip_tac >>
    qpat_x_assum `!tenv s'' tyv t s1 vs' t' s2 x t''. _` kall_tac >>
    qpat_x_assum `(let tenv = get_tenv cx in _) st = (res,st')` mp_tac >>
    qpat_assum `evaluate_type (get_tenv cx) typ = SOME iter_tyv` (fn th => rewrite_tac[th]) >>
    qpat_assum `eval_iterator cx it st = (INL vs, st1)` (fn th => rewrite_tac[th]) >>
    simp[LET_THM, bind_def, ignore_bind_def, return_def, assert_def, raise_def,
        check_def, lift_option_type_def, no_type_error_result_def,
        return_exception_typed_def] >> strip_tac >> gvs[]) >>
  strip_tac >>
  qpat_x_assum `!tenv s'' tyv t s1 vs' t' s2 x t''. _` kall_tac >>
  qpat_x_assum `(let tenv = get_tenv cx in _) st = (res,st')` mp_tac >>
  qpat_assum `evaluate_type (get_tenv cx) typ = SOME iter_tyv` (fn th => rewrite_tac[th]) >>
  qpat_assum `eval_iterator cx it st = (INR y, st1)` (fn th => rewrite_tac[th]) >>
  simp[LET_THM, bind_def, ignore_bind_def, return_def, raise_def,
      lift_option_type_def] >>
  strip_tac >> gvs[] >>
  conj_tac >- (
    qpat_x_assum `no_type_error_result (INR y)` mp_tac >>
    simp[no_type_error_result_def]) >>
  irule no_control_exc_return_exception_typed >>
  drule eval_iterator_no_control >> simp[]
QED

Resume eval_all_type_sound_mutual[For_nil]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_for _ _ _ _ [] _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, return_def] >>
  strip_tac >> gvs[no_type_error_result_def]
QED

Theorem eval_for_cons_type_sound_core:
  evaluate_type env.type_defs ty = SOME tyv /\
  EVERY (value_has_type tyv) (v::vs) /\
  id NOTIN FDOM env.var_types /\
  type_stmts (extend_local env id ty F) ret_ty body_stmts = SOME env_after /\
  env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  (!stp res_body st_body.
    env_consistent (extend_local env id ty F) cx stp /\
    state_well_typed stp /\ accounts_well_typed stp.accounts /\
    eval_stmts cx body_stmts stp = (res_body, st_body) ==>
    state_well_typed st_body /\ accounts_well_typed st_body.accounts /\
    no_type_error_result res_body /\
    case res_body of
    | INL _ => env_consistent env_after cx st_body
    | INR exn => ?env_exn. env_extends (extend_local env id ty F) env_exn /\
                              env_consistent env_exn cx st_body /\
                              return_exception_typed env_exn ret_ty exn) /\
  (!st0 res_tail st_tail.
    env_consistent env cx st0 /\ state_well_typed st0 /\
    accounts_well_typed st0.accounts /\
    eval_for cx tyv id body_stmts vs st0 = (res_tail, st_tail) ==>
    state_well_typed st_tail /\ accounts_well_typed st_tail.accounts /\
    env_consistent env cx st_tail /\ no_type_error_result res_tail /\
    case res_tail of
    | INR exn => return_exception_typed env ret_ty exn
    | INL _ => T) /\
  eval_for cx tyv id body_stmts (v::vs) st = (res, st') ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts /\ env_consistent env cx st' /\
  no_type_error_result res /\
  case res of
  | INR exn => return_exception_typed env ret_ty exn
  | INL _ => T
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_for _ _ _ _ (_::_) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                       push_scope_with_var_def, return_def] >>
  qmatch_goalsub_abbrev_tac `finally loop_body pop_scope stp` >>
  Cases_on `finally loop_body pop_scope stp` >>
  rename1 `finally loop_body pop_scope stp = (loop_res, st_after)` >>
  strip_tac >>
  `stp =
    st with scopes updated_by
      CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>))` by
    simp[Abbr`stp`] >>
  qunabbrev_tac `loop_body` >>
  drule for_body_decompose_for_cons_pushed >>
  rewrite_tac[ignore_bind_def] >>
  disch_then drule >>
  strip_tac >>
  `env.type_defs = get_tenv cx` by gvs[env_consistent_def, env_context_consistent_def] >>
  `state_well_typed stp` by (
    `value_has_type tyv v` by fs[] >>
    `well_formed_type_value tyv` by (
      qpat_assum `evaluate_type env.type_defs ty = SOME tyv`
        (ACCEPT_TAC o MATCH_MP evaluate_type_well_formed_type_value)) >>
    qpat_x_assum `stp = _` SUBST1_TAC >>
    irule for_cons_pushed_state_well_typed >>
    simp[]) >>
  `accounts_well_typed stp.accounts` by (
    qpat_x_assum `stp = _` SUBST1_TAC >>
    simp[NoAsms, evaluation_state_component_equality] >>
    qpat_assum `accounts_well_typed st.accounts` ACCEPT_TAC) >>
  `env_consistent (extend_local env id ty F) cx stp` by (
    qunabbrev_tac `stp` >>
    metis_tac[push_scope_with_var_env_consistent]) >>
  qpat_assum `!stp res_body st_body.
       env_consistent (extend_local env id ty F) cx stp /\
       state_well_typed stp /\ accounts_well_typed stp.accounts /\
       eval_stmts cx body_stmts stp = (res_body,st_body) ==> _`
    (qspecl_then [`stp`, `res_body`, `st_body`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  Cases_on `res_body` >> simp[NoAsms]
  >- (
    `state_well_typed (st_body with scopes := TL st_body.scopes)` by (
      irule scope_bracket_preserves_swt >> simp[] >>
      qexists_tac `cx` >> qexists_tac `INL x` >>
      qexists_tac `FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)` >>
      qexists_tac `body_stmts` >> qexists_tac `st` >> simp[Abbr`stp`]) >>
    `accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts` by
      simp[evaluation_state_component_equality] >>
    `env_consistent env cx (st_body with scopes := TL st_body.scopes)` by (
      `env_consistent env_after cx st_body` by (
        qpat_x_assum `case (INL x : unit + vyperState$exception) of INL u => _ | INR exn => _` mp_tac >>
        simp[NoAsms]) >>
      qpat_x_assum `stp = _` SUBST_ALL_TAC >>
      metis_tac[for_body_env_consistent_after_pop, env_consistent_env_maps_wf]) >>
    `loop_res = INL F` by (
      qpat_x_assum `(∃x'. INL x = INL x') ==> _` irule >>
      simp[]) >>
    qpat_x_assum `loop_res = INL F` SUBST_ALL_TAC >>
    qpat_x_assum `st_after = _` SUBST_ALL_TAC >>
    `eval_for cx tyv id body_stmts vs (st_body with scopes := TL st_body.scopes) = (res,st')` by (
      qpat_x_assum `(case (INL F,_) of _ => _ | _ => _) = (res,st')` mp_tac >>
      simp[return_def]) >>
    qpat_x_assum `!st0 res_tail st_tail. _`
      (qspecl_then [`st_body with scopes := TL st_body.scopes`, `res`, `st'`] mp_tac) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    simp[]) >>
  `state_well_typed (st_body with scopes := TL st_body.scopes)` by (
    irule scope_bracket_preserves_swt >> simp[] >>
    qexists_tac `cx` >> qexists_tac `INR y` >>
    qexists_tac `FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)` >>
    qexists_tac `body_stmts` >> qexists_tac `st` >> simp[Abbr`stp`]) >>
  `accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts` by
    simp[evaluation_state_component_equality] >>
  SUBGOAL_THEN ``env_consistent env cx (st_body with scopes := TL st_body.scopes)`` assume_tac >- (
    irule for_cons_popped_env_consistent_from_stmt_case >>
    qexists_tac `body_stmts` >> qexists_tac `y` >> qexists_tac `id` >>
    qexists_tac `\u. env_consistent env_after cx st_body` >>
    qexists_tac `ret_ty` >> qexists_tac `st` >> qexists_tac `ty` >>
    qexists_tac `tyv` >> qexists_tac `v` >>
    conj_tac >- simp[] >>
    conj_tac >- simp[Abbr`stp`] >>
    conj_tac >- simp[] >>
    asm_rewrite_tac[]) >>
  Cases_on `y = ContinueException`
  >- (
    qpat_x_assum `y = ContinueException` SUBST_ALL_TAC >>
    `loop_res = INL F` by (
      qpat_x_assum `INR ContinueException = INR ContinueException ==> _` irule >>
      simp[]) >>
    qpat_x_assum `loop_res = INL F` SUBST_ALL_TAC >>
    qpat_x_assum `st_after = _` SUBST_ALL_TAC >>
    `eval_for cx tyv id body_stmts vs (st_body with scopes := TL st_body.scopes) = (res,st')` by (
      qpat_x_assum `(case (INL F,_) of _ => _ | _ => _) = (res,st')` mp_tac >>
      simp[return_def]) >>
    qpat_x_assum `!st0 res_tail st_tail. _`
      (qspecl_then [`st_body with scopes := TL st_body.scopes`, `res`, `st'`] mp_tac) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    simp[]) >>
  Cases_on `y = BreakException`
  >- (
    qpat_x_assum `y = BreakException` SUBST_ALL_TAC >>
    `loop_res = INL T` by (
      qpat_x_assum `INR BreakException = INR BreakException ==> _` irule >>
      simp[]) >>
    qpat_x_assum `loop_res = INL T` SUBST_ALL_TAC >>
    qpat_x_assum `st_after = _` SUBST_ALL_TAC >>
    qpat_x_assum `(case (INL T,_) of _ => _ | _ => _) = (res,st')` mp_tac >>
    simp[NoAsms, return_def] >>
    strip_tac >>
    qpat_x_assum `_ = st'` (SUBST_ALL_TAC o SYM) >>
    simp[no_type_error_result_def]) >>
  `loop_res = INR y` by (
    qpat_x_assum `!e. INR y = INR e /\ e <> ContinueException /\ e <> BreakException ==> _`
      (qspec_then `y` irule) >>
    simp[]) >>
  qpat_x_assum `loop_res = INR y` SUBST_ALL_TAC >>
  qpat_x_assum `st_after = _` SUBST_ALL_TAC >>
  qpat_x_assum `(case (INR y,_) of _ => _ | _ => _) = (res,st')` mp_tac >>
  simp[NoAsms] >>
  strip_tac >>
  qpat_x_assum `_ = st'` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `INR y = res` (SUBST_ALL_TAC o SYM) >>
  simp[sum_case_def] >>
  irule for_cons_ordinary_exception_return_typed_from_body_ih >>
  qexists_tac `body_stmts` >> qexists_tac `cx` >>
  qexists_tac `env_after` >> qexists_tac `id` >>
  qexists_tac `st_body` >> qexists_tac `stp` >>
  qexists_tac `ty` >>
  simp[] >>
  rpt gen_tac >> strip_tac >>
  last_x_assum drule >>
  disch_then $ funpow 2 drule_then drule >>
  simp[]
QED

Resume eval_all_type_sound_mutual[For_cons]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_for _ _ _ _ (_::_) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                       push_scope_with_var_def, return_def] >>
  qmatch_goalsub_abbrev_tac `finally loop_body pop_scope stp` >>
  Cases_on `finally loop_body pop_scope stp` >>
  rename1 `finally loop_body pop_scope stp = (loop_res, st_after)` >>
  strip_tac >>
  `stp =
    st with scopes updated_by
      CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>))` by
    simp[Abbr`stp`] >>
  qunabbrev_tac `loop_body` >>
  drule for_body_decompose_for_cons_pushed >>
  rewrite_tac[ignore_bind_def] >>
  disch_then drule >>
  strip_tac >>
  `env.type_defs = get_tenv cx` by fs[env_consistent_def, env_context_consistent_def] >>
  `state_well_typed stp` by (
    `value_has_type tyv v` by fs[] >>
    `well_formed_type_value tyv` by (
      qpat_assum `evaluate_type env.type_defs ty = SOME tyv`
        (ACCEPT_TAC o MATCH_MP evaluate_type_well_formed_type_value)) >>
    qpat_x_assum `stp = _` SUBST1_TAC >>
    irule for_cons_pushed_state_well_typed >>
    simp[]) >>
  `accounts_well_typed stp.accounts` by (
    qpat_x_assum `stp = _` SUBST1_TAC >>
    simp[NoAsms, evaluation_state_component_equality] >>
    qpat_assum `accounts_well_typed st.accounts` ACCEPT_TAC) >>
  `env_consistent (extend_local env id ty F) cx stp` by (
    qunabbrev_tac `stp` >>
    metis_tac[push_scope_with_var_env_consistent]) >>
  qpat_x_assum `!s'' x t. push_scope_with_var id tyv v s'' = (INL x,t) ==> _`
    (qspecl_then [`st`, `()`, `stp`] mp_tac) >>
  impl_tac >- simp[push_scope_with_var_def, return_def, Abbr`stp`] >>
  disch_then (qspecl_then [`extend_local env id ty F`, `ret_ty`, `env_after`,
                           `stp`, `res_body`, `st_body`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  Cases_on `res_body` >> simp[NoAsms]
  >- (
    `state_well_typed (st_body with scopes := TL st_body.scopes)` by (
      irule scope_bracket_preserves_swt >> simp[] >>
      qexists_tac `cx` >> qexists_tac `INL x` >>
      qexists_tac `FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)` >>
      qexists_tac `body'` >> qexists_tac `st` >> simp[Abbr`stp`]) >>
    `accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts` by
      simp[evaluation_state_component_equality] >>
    `env_consistent env cx (st_body with scopes := TL st_body.scopes)` by (
      `env_consistent env_after cx st_body` by (
        qpat_x_assum `case (INL x : unit + vyperState$exception) of INL u => _ | INR exn => _` mp_tac >>
        simp[NoAsms]) >>
      qpat_x_assum `stp = _` SUBST_ALL_TAC >>
      metis_tac[for_body_env_consistent_after_pop, env_consistent_env_maps_wf]) >>
    qpat_x_assum `!s'' x' t s''' broke t'. _`
      (qspecl_then [`st`, `()`, `stp`, `stp`, `F`,
                    `st_body with scopes := TL st_body.scopes`] mp_tac) >>
    impl_tac >- (
      conj_tac >- simp[push_scope_with_var_def, return_def, Abbr`stp`] >>
      conj_tac >- (
        `loop_res = INL F` by (
          qpat_x_assum `(∃x'. INL x = INL x') ==> _` irule >>
          simp[]) >>
        qpat_x_assum `loop_res = INL F` SUBST_ALL_TAC >>
        qpat_x_assum `st_after = _` SUBST_ALL_TAC >>
        qpat_x_assum `stp = _` SUBST_ALL_TAC >>
        qpat_x_assum `finally _ _ _ = (INL F, _)` mp_tac >>
        strip_tac >>
        pop_assum mp_tac >>
        simp[NoAsms, bind_def, ignore_bind_def]) >>
      simp[]) >>
    `loop_res = INL F` by (
      qpat_x_assum `(∃x'. INL x = INL x') ==> _` irule >>
      simp[]) >>
    qpat_x_assum `loop_res = INL F` SUBST_ALL_TAC >>
    qpat_x_assum `st_after = _` SUBST_ALL_TAC >>
    `eval_for cx tyv id body' vs (st_body with scopes := TL st_body.scopes) = (res,st')` by (
      qpat_x_assum `(case (INL F,_) of _ => _ | _ => _) = (res,st')` mp_tac >>
      simp[return_def]) >>
    disch_then (qspecl_then [`env`, `ret_ty`, `ty`, `env_after`,
                             `st_body with scopes := TL st_body.scopes`, `res`, `st'`] mp_tac) >>
    (impl_tac >- fs[]) >>
    simp[]) >>
  `state_well_typed (st_body with scopes := TL st_body.scopes)` by (
    irule scope_bracket_preserves_swt >> simp[] >>
    qexists_tac `cx` >> qexists_tac `INR y` >>
    qexists_tac `FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)` >>
    qexists_tac `body'` >> qexists_tac `st` >> simp[Abbr`stp`]) >>
  `accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts` by
    simp[evaluation_state_component_equality] >>
  SUBGOAL_THEN ``env_consistent env cx (st_body with scopes := TL st_body.scopes)`` assume_tac >- (
    irule for_cons_popped_env_consistent_from_stmt_case >>
    qexists_tac `body'` >> qexists_tac `y` >> qexists_tac `id` >>
    qexists_tac `\u. env_consistent env_after cx st_body` >>
    qexists_tac `ret_ty` >> qexists_tac `st` >> qexists_tac `ty` >>
    qexists_tac `tyv` >> qexists_tac `v` >>
    conj_tac >- simp[] >>
    conj_tac >- simp[Abbr`stp`] >>
    conj_tac >- simp[] >>
    asm_rewrite_tac[]) >>
  Cases_on `y = ContinueException`
  >- (
    qpat_x_assum `y = ContinueException` SUBST_ALL_TAC >>
    qpat_x_assum `!s'' x t s'³' broke t'. _`
      (qspecl_then [`st`, `()`, `stp`, `stp`, `F`,
                    `st_body with scopes := TL st_body.scopes`] mp_tac) >>
    impl_tac >- (
      conj_tac >- simp[push_scope_with_var_def, return_def, Abbr`stp`] >>
      conj_tac >- (
        `loop_res = INL F` by (
          qpat_x_assum `INR ContinueException = INR ContinueException ==> _` irule >>
          simp[]) >>
        qpat_x_assum `loop_res = INL F` SUBST_ALL_TAC >>
        qpat_x_assum `st_after = _` SUBST_ALL_TAC >>
        qpat_x_assum `stp = _` SUBST_ALL_TAC >>
        qpat_x_assum `finally _ pop_scope _ = (INL F, _)` mp_tac >>
        strip_tac >>
        pop_assum mp_tac >>
        simp[NoAsms, bind_def, ignore_bind_def]) >>
      simp[]) >>
    `loop_res = INL F` by (
      qpat_x_assum `INR ContinueException = INR ContinueException ==> _` irule >>
      simp[]) >>
    qpat_x_assum `loop_res = INL F` SUBST_ALL_TAC >>
    qpat_x_assum `st_after = _` SUBST_ALL_TAC >>
    `eval_for cx tyv id body' vs (st_body with scopes := TL st_body.scopes) = (res,st')` by (
      qpat_x_assum `(case (INL F,_) of _ => _ | _ => _) = (res,st')` mp_tac >>
      simp[return_def]) >>
    disch_then (qspecl_then [`env`, `ret_ty`, `ty`, `env_after`,
                             `st_body with scopes := TL st_body.scopes`, `res`, `st'`] mp_tac) >>
    (impl_tac >- fs[]) >>
    simp[]) >>
  Cases_on `y = BreakException`
  >- (
    qpat_x_assum `y = BreakException` SUBST_ALL_TAC >>
    `loop_res = INL T` by (
      qpat_x_assum `INR BreakException = INR BreakException ==> _` irule >>
      simp[]) >>
    qpat_x_assum `loop_res = INL T` SUBST_ALL_TAC >>
    qpat_x_assum `st_after = _` SUBST_ALL_TAC >>
    qpat_x_assum `(case (INL T,_) of _ => _ | _ => _) = (res,st')` mp_tac >>
    simp[NoAsms, return_def] >>
    strip_tac >>
    qpat_x_assum `_ = st'` (SUBST_ALL_TAC o SYM) >>
    simp[no_type_error_result_def]) >>
  `loop_res = INR y` by (
    qpat_x_assum `!e. INR y = INR e /\ e <> ContinueException /\ e <> BreakException ==> _`
      (qspec_then `y` irule) >>
    simp[]) >>
  qpat_x_assum `loop_res = INR y` SUBST_ALL_TAC >>
  qpat_x_assum `st_after = _` SUBST_ALL_TAC >>
  qpat_x_assum `(case (INR y,_) of _ => _ | _ => _) = (res,st')` mp_tac >>
  simp[NoAsms] >>
  strip_tac >>
  qpat_x_assum `_ = st'` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `INR y = res` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `!s'' x t s'³' broke t'. _` kall_tac >>
  qmatch_goalsub_abbrev_tac `state_well_typed stfinal` >>
  qunabbrev_tac `stfinal` >>
  irule for_cons_non_loop_exception_suffix_projected >>
  simp[] >>
  conj_tac >- (
    simp[no_type_error_result_def] >> strip_tac >>
    qpat_x_assum `no_type_error_result (INR y)` mp_tac >>
    simp[no_type_error_result_def] >>
    disch_then (qspec_then `msg` mp_tac) >> simp[]) >>
  fs[] >>
  qexists_tac `id` >> qexists_tac `ty` >>
  qexists_tac `env_exn` >> simp[]
QED

Resume eval_all_type_sound_mutual[Iterator_Array]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `well_typed_iterator _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [well_typed_iterator_def]) >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `expr_res` >> gvs[no_type_error_result_def]
  >- (
    rename1 `eval_expr cx e st = (INL tvl, st1)` >>
    Cases_on `materialise cx tvl st1` >>
    rename1 `materialise cx tvl st1 = (mat_res, st2)` >>
    Cases_on `mat_res` >> gvs[no_type_error_result_def]
    >- (
      rename1 `materialise cx tvl st1 = (INL v, st2)` >>
      drule materialise_state >> strip_tac >> gvs[] >>
      gvs[expr_result_typed_def, expr_runtime_typed_def] >>
      `env.type_defs = get_tenv cx` by gvs[env_consistent_def, env_context_consistent_def] >>
      gvs[] >>
      drule evaluate_type_ArrayT_cases >> strip_tac >> gvs[] >>
      `value_has_type (ArrayTV elem_tv bd) v` by
        metis_tac[materialise_preserves_value_type,
                  evaluate_type_well_formed_type_value] >>
      Cases_on `lift_option_type (extract_elements (ArrayTV elem_tv bd) v) "For not ArrayV" st2` >>
      rename1 `lift_option_type _ _ st2 = (lift_res, st3)` >>
      drule lift_option_type_state >> strip_tac >> gvs[] >>
      Cases_on `lift_res` >> gvs[return_def, no_type_error_result_def]
      >- (
        rename1 `lift_option_type (extract_elements (ArrayTV elem_tv bd) v) _ st2 = (INL vs, st2)` >>
        strip_tac >> gvs[lift_option_type_def] >>
        Cases_on `extract_elements (ArrayTV elem_tv bd) v` >>
        gvs[raise_def, return_def] >>
        Cases_on `v` >> gvs[extract_elements_def] >>
        rename1 `ArrayV av` >>
        irule extract_elements_well_typed >>
        qexists_tac `av` >> qexists_tac `bd` >> simp[] >>
        conj_tac >- metis_tac[evaluate_type_well_formed_type_value] >>
        simp[extract_elements_def]) >>
      Cases_on `extract_elements (ArrayTV elem_tv bd) v` >>
      gvs[lift_option_type_def, raise_def, return_def] >>
      Cases_on `v` >> gvs[extract_elements_def, value_has_type_def]) >>
    drule materialise_state >> strip_tac >> gvs[] >>
    strip_tac >> gvs[] >>
    gvs[expr_result_typed_def, expr_runtime_typed_def] >>
    `env.type_defs = get_tenv cx` by gvs[env_consistent_def, env_context_consistent_def] >>
    gvs[] >>
    drule evaluate_type_ArrayT_cases >> strip_tac >> gvs[] >>
    irule materialise_typed_non_none_no_type_error >>
    qexists_tac `cx` >> qexists_tac `st'` >> qexists_tac `st'` >>
    qexists_tac `tvl` >> qexists_tac `ArrayTV elem_tv bd` >> simp[]) >>
  strip_tac >> gvs[]
QED

Resume eval_all_type_sound_mutual[Iterator_Range]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `well_typed_iterator _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [well_typed_iterator_def]) >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr1_res, st1)` >>
  last_x_assum drule_all >> strip_tac >>
  Cases_on `expr1_res`
  >- (
    qpat_x_assum `case INL _ of _ => _ | _ => _` mp_tac >> rewrite_tac[] >> strip_tac >>
    rename1 `eval_expr cx e st = (INL tv1, st1)` >>
    Cases_on `get_Value tv1 st1` >>
    rename1 `get_Value tv1 st1 = (val1_res, st2)` >>
    Cases_on `val1_res`
    >- (
      rename1 `get_Value tv1 st1 = (INL v1, st2)` >>
      drule get_Value_state >> strip_tac >>
      qpat_x_assum `st2 = st1` SUBST_ALL_TAC >>
      qpat_x_assum `!s'' tv1 t s''' s t'. _`
        (qspecl_then [`st`, `tv1`, `st1`, `st1`, `v1`, `st1`] mp_tac) >>
      simp[] >> strip_tac >>
      Cases_on `eval_expr cx e' st1` >>
      rename1 `eval_expr cx e' st1 = (expr2_res, st3)` >>
      qpat_x_assum `!env' st' res st''. _`
        (qspecl_then [`env`, `st1`, `expr2_res`, `st3`] mp_tac) >>
      impl_tac >- simp[] >> strip_tac >>
      qpat_x_assum `well_typed_expr env e' ==> _` mp_tac >>
      impl_tac >- simp[] >> strip_tac >>
      Cases_on `expr2_res`
      >- (
        qpat_x_assum `case INL _ of _ => _ | _ => _` mp_tac >> rewrite_tac[] >> strip_tac >>
        rename1 `eval_expr cx e' st1 = (INL tv2, st3)` >>
        Cases_on `get_Value tv2 st3` >>
        rename1 `get_Value tv2 st3 = (val2_res, st4)` >>
        Cases_on `val2_res`
        >- (
          qpat_x_assum `case INL _ of _ => _ | _ => _` mp_tac >> rewrite_tac[] >> strip_tac >>
          rename1 `get_Value tv2 st3 = (INL v2, st4)` >>
          drule get_Value_state >> strip_tac >>
          qpat_x_assum `st4 = st3` SUBST_ALL_TAC >>
          `tv1 = Value v1` by (
            qpat_x_assum `get_Value tv1 _ = _` mp_tac >>
            Cases_on `tv1` >> simp[get_Value_def, return_def, raise_def]) >>
          `tv2 = Value v2` by (
            qpat_x_assum `get_Value tv2 _ = _` mp_tac >>
            Cases_on `tv2` >> simp[get_Value_def, return_def, raise_def]) >>
          gvs[expr_result_typed_def, expr_runtime_typed_def, toplevel_value_typed_def] >>
          `?i1. v1 = IntV i1` by metis_tac[int_typed_value_is_IntV] >>
          `?i2. v2 = IntV i2` by metis_tac[int_typed_value_is_IntV] >>
          gvs[] >>
          Cases_on `lift_sum (get_range_limits (IntV i1) (IntV i2)) st3` >>
          rename1 `lift_sum (get_range_limits (IntV i1) (IntV i2)) st3 = (range_res, st5)` >>
          strip_tac >>
          qspecl_then [`env.type_defs`, `expr_type e`, `tv`, `i1`, `i2`,
                       `range_res`, `st3`, `st5`, `res`, `st'`]
            mp_tac iterator_range_tail_eval_sound >>
          impl_tac >- (
            simp[] >>
            qpat_x_assum `case (range_res,st5) of _ => _ | _ => _` mp_tac >>
            Cases_on `range_res` >> simp[return_def, raise_def]) >>
          strip_tac >> gvs[]) >>
        imp_res_tac get_Value_state >> gvs[] >>
        strip_tac >> gvs[] >>
        gvs[expr_result_typed_def, expr_runtime_typed_def] >>
        qspecl_then [`env.type_defs`, `expr_type e`, `tv`] mp_tac
          is_int_type_evaluate_type_not_None_Array >>
        impl_tac >- simp[] >> strip_tac >>
        simp[no_type_error_result_def] >>
        irule get_Value_INR_no_type_error >>
        qexistsl_tac [`st'`, `st'`, `tv2`, `tv`] >> simp[]) >>
      strip_tac >> gvs[return_def, no_type_error_result_def] >> metis_tac[]) >>
    drule get_Value_state >> strip_tac >>
    qpat_x_assum `st2 = st1` SUBST_ALL_TAC >>
    strip_tac >>
    drule_all iterator_range_first_get_value_error_eq >> strip_tac >>
    qpat_x_assum `res = INR y` SUBST_ALL_TAC >>
    qpat_x_assum `st' = st1` SUBST_ALL_TAC >>
    qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
    impl_tac >- simp[] >> strip_tac >>
    qpat_x_assum `case INL tv1 of _ => _ | _ => _` mp_tac >>
    rewrite_tac[] >> strip_tac >>
    rpt conj_tac >> simp[] >>
    irule int_expr_get_Value_INR_no_type_error >>
    qexistsl_tac [`e`, `env`, `st1`, `st1`, `tv1`, `ty`] >>
    simp[] >>
    qpat_x_assum `case INL tv1 of _ => _ | _ => _` mp_tac >>
    simp[sum_case_def]) >>
  strip_tac >>
  drule_all iterator_range_expr_error_eq >> strip_tac >>
  qpat_x_assum `res = INR y` SUBST_ALL_TAC >>
  qpat_x_assum `st' = st1` SUBST_ALL_TAC >>
  qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
  impl_tac >- simp[] >> strip_tac >>
  qpat_x_assum `case INR y of _ => _ | _ => _` mp_tac >>
  simp[sum_case_def] >>
  qpat_x_assum `(case (INR y,st1) of _ => _ | _ => _) = (INR y,st1)` kall_tac >>
  fs[no_type_error_result_def]
QED

Resume eval_all_type_sound_mutual[Target_Base]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_target _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  gvs[well_typed_atarget_def, well_typed_target_def] >>
  Cases_on `eval_base_target cx bt st` >>
  rename1 `eval_base_target cx bt st = (bt_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `bt_res` >> gvs[no_type_error_result_def]
  >- (Cases_on `x` >> gvs[return_def] >> strip_tac >> gvs[] >>
      simp[target_runtime_typed_def, target_value_shape_def,
           well_typed_atarget_def, well_typed_target_def] >> metis_tac[]) >>
  simp[return_def] >> strip_tac >> gvs[]
QED

Resume eval_all_type_sound_mutual[Target_Tuple]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_target _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  gvs[well_typed_atarget_def] >>
  Cases_on `eval_targets cx tgts st` >>
  rename1 `eval_targets cx tgts st = (tgts_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `tgts_res` >> gvs[no_type_error_result_def, return_def]
  >- (strip_tac >> gvs[target_runtime_typed_def] >>
      conj_tac >- gvs[well_typed_atarget_def] >>
      simp[target_value_shape_def] >>
      conj_tac
      >- metis_tac[target_values_runtime_typed_imp_shape,
                   target_values_runtime_typed_LIST_REL3] >>
      simp[target_values_runtime_typed_LIST_REL3]) >>
  strip_tac >> gvs[]
QED

Resume eval_all_type_sound_mutual[Targets_nil]:
  rpt gen_tac >> strip_tac >>
  gvs[Once evaluate_def, return_def, no_type_error_result_def, LIST_REL3_def]
QED

Resume eval_all_type_sound_mutual[Targets_cons]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_targets _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `tys` >- fs[] >>
  qpat_x_assum `LIST_REL _ (tgt::tgts) (h::t)` mp_tac >>
  simp_tac(srw_ss())[listTheory.LIST_REL_CONS1] >> strip_tac >>
  Cases_on `eval_target cx tgt st` >>
  rename1 `eval_target cx tgt st = (target_res, st1)` >>
  qpat_x_assum `!env ty st res st'. well_typed_atarget env tgt ty /\ _ ==> _` drule_all >> strip_tac >>
  Cases_on `target_res` >> gvs[no_type_error_result_def]
  >- (Cases_on `eval_targets cx tgts st1` >>
      rename1 `eval_targets cx tgts st1 = (targets_res, st2)` >>
      first_x_assum (qspecl_then [`st`, `x`, `st1`] mp_tac) >>
      simp[] >>
      disch_then (qspecl_then [`env`, `t`, `st1`, `targets_res`, `st2`] mp_tac) >>
      simp[] >> strip_tac >>
      Cases_on `targets_res` >> gvs[no_type_error_result_def, return_def]
      >- (strip_tac >> gvs[LIST_REL3_def] >>
          metis_tac[target_runtime_typed_rebuild, runtime_consistent_def]) >>
      strip_tac >> gvs[]) >>
  simp[return_def] >> strip_tac >> gvs[]
QED

Resume eval_all_type_sound_mutual[BaseTarget_Name]:
  rpt gen_tac >>
  `∃ty. vt = Type ty` by gvs[well_typed_expr_def,AllCaseEqs()] >>
  gvs[] >>
  drule_all NameTarget_sound >>
  strip_tac >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, assert_def, ignore_bind_def,
    get_scopes_def, type_check_def, assert_def] >>
  strip_tac >> gvs[] >>
  simp[no_type_error_result_def, base_target_value_shape_def] >>
  qexists_tac `Type ty` >> simp[location_runtime_typed_def] >>
  conj_tac >- (
    gvs[well_typed_expr_def, AllCaseEqs(), LET_THM,
        env_consistent_def, env_scopes_consistent_def,
        env_context_consistent_def] >>
    first_x_assum (qspecl_then [`string_to_num id`, `ty`, `entry`] mp_tac) >>
    simp[]) >>
  simp[target_path_type_refl]
QED

Resume eval_all_type_sound_mutual[BaseTarget_BareGlobal]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_place_target _ (BareGlobalNameTarget _) = _` mp_tac >>
  simp[type_place_target_BareGlobalNameTarget] >> strip_tac >> gvs[] >>
  drule_all env_consistent_bare_global_ready >> strip_tac >>
  drule eval_base_target_BareGlobalNameTarget_preserves_state >> strip_tac >> gvs[] >>
  `!msg. res <> INR (Error (TypeError msg))` by
    metis_tac[eval_base_target_BareGlobalNameTarget_no_type_error] >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_immutables_def,
       get_address_immutables_def, lift_option_def, lift_option_type_def,
       type_check_def, assert_def, check_def, ignore_bind_def,
       return_def, raise_def, LET_THM] >>
  rpt strip_tac >>
  gvs[no_type_error_result_def, base_target_value_shape_def,
      location_runtime_typed_def, target_path_type_refl,
      get_source_immutables_def, AllCaseEqs()] >>
  gvs[IS_SOME_EXISTS, get_immutables_def, get_address_immutables_def,
      lift_option_def, return_def] >>
  Cases_on `ALOOKUP s''.immutables cx.txn.target` >> gvs[return_def, raise_def] >>
  PairCases_on `x` >> gvs[] >>
  qexists_tac `Type ty` >> simp[target_path_type_refl] >>
  qexists_tac `imms'` >> qexists_tac `x1` >> qexists_tac `x0` >>
  gvs[env_consistent_def, env_context_consistent_def, env_immutables_consistent_def,
      get_immutables_def, get_address_immutables_def, lift_option_def,
      bind_def, return_def, get_source_immutables_def] >>
  qpat_x_assum `!src id ty' tv v.
      FLOOKUP env.bare_globals (src,id) = SOME ty' /\
      FLOOKUP (case ALOOKUP imms src of NONE => FEMPTY | SOME imm => imm) id = SOME (tv,v) ==>
      evaluate_type (get_tenv cx) ty' = SOME tv`
    (qspecl_then [`current_module cx`, `string_to_num id`, `ty`, `x0`, `x1`] mp_tac) >>
  simp[]
QED

Resume eval_all_type_sound_mutual[BaseTarget_TopLevel]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, return_def] >>
  strip_tac >> gvs[] >>
  simp[no_type_error_result_def, base_target_value_shape_def] >>
  simp[location_runtime_typed_def] >>
  gvs[well_typed_expr_def, place_leaf_typed_def, leaf_type_def] >>
  rw[] >> gvs[env_consistent_def] >>
  gvs[env_context_consistent_def] >>
  first_x_assum drule >>
  rw[well_formed_vtype_def, well_formed_type_def] >>
  gvs[IS_SOME_EXISTS, target_path_type_refl]
QED

Resume eval_all_type_sound_mutual[BaseTarget_Subscript]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_place_target _ (SubscriptTarget _ _) = _` mp_tac >>
  rewrite_tac[type_place_target_SubscriptTarget] >> strip_tac >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_base_target cx bt st` >>
  rename1 `eval_base_target cx bt st = (bt_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `bt_res`
  >- (PairCases_on `x` >> rewrite_tac[bind_def, return_def] >>
      qpat_x_assum `!s'' loc sbs t'. _`
        (qspecl_then [`st`, `x0`, `x1`, `st1`] mp_tac) >> simp[] >>
      strip_tac >>
      Cases_on `eval_expr cx e st1` >>
      rename1 `eval_expr cx e st1 = (expr_res, st2)` >>
      first_x_assum drule_all >> strip_tac >>
      Cases_on `expr_res` >> gvs[no_type_error_result_def, bind_def, return_def]
      >- (Cases_on `get_Value x st2` >>
          rename1 `get_Value tv st2 = (value_res, st3)` >>
          `no_type_error_result value_res` by
            metis_tac[subscript_vtype_index_get_Value_no_type_error] >>
          Cases_on `value_res` >> gvs[no_type_error_result_def, return_def] >>
          Cases_on `tv` >> gvs[get_Value_def, return_def, raise_def] >>
          strip_tac >> gvs[base_target_value_shape_def] >> simp[] >>
          qexists_tac `loc_vt` >> simp[] >>
          conj_tac >- (
            irule location_runtime_typed_rebuild >>
            simp[runtime_consistent_def] >>
            qexists_tac `st1` >> simp[]) >>
          irule subscript_vtype_value_step_type >>
          qexistsl_tac [`vt'`, `e`, `expr_type e`, `st'`, `st'`, `Value v`] >>
          simp[get_Value_def, return_def]) >>
      strip_tac >> gvs[]) >>
  strip_tac >> pop_assum mp_tac >> simp[return_def] >> strip_tac >>
  qpat_x_assum `INR y = res` (fn th => SUBST_ALL_TAC (SYM th)) >>
  qpat_x_assum `st1 = st'` (fn th => SUBST_ALL_TAC (SYM th)) >>
  simp[no_type_error_result_def]
QED

Resume eval_all_type_sound_mutual[BaseTarget_Attribute]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_place_target _ (AttributeTarget _ _) = _` mp_tac >>
  CONV_TAC(LAND_CONV(LAND_CONV(ONCE_REWRITE_CONV[well_typed_expr_def]))) >>
  simp[AllCaseEqs(), PULL_EXISTS] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_base_target cx bt st` >>
  rename1 `eval_base_target cx bt st = (bt_res, st1)` >>
  simp[AllCaseEqs(),return_def,EXISTS_PROD] >>
  ntac 3 strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  gvs[no_type_error_result_def, base_target_value_shape_def] >>
  goal_assum drule >>
  Cases_on`tgt_ty` >> gvs[attribute_type_def, AllCaseEqs()] >>
  simp[target_path_type_def] >>
  goal_assum drule >>
  simp[target_path_step_type_def] >>
  simp[attribute_type_def]
QED

Resume eval_all_type_sound_mutual[Expr_Name]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, get_scopes_def,
      lift_option_type_def, return_def, raise_def, no_type_error_result_def,
      AllCaseEqs()] >>
  strip_tac >> gvs[]
  >- (strip_tac >>
      drule_all well_typed_Name_lookup >> strip_tac >>
      `lookup_scopes_val (string_to_num id) st.scopes = SOME entry.value` by
        simp[lookup_scopes_val_SOME] >>
      gvs[bind_def, return_def, expr_result_typed_def, expr_runtime_typed_def,
          well_typed_expr_def, expr_type_def, toplevel_value_typed_Value]) >>
  rpt strip_tac >> gvs[well_typed_expr_def]
QED

Resume eval_all_type_sound_mutual[Expr_BareGlobalName]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, get_immutables_def, get_address_immutables_def,
      lift_option_def, bind_def, lift_option_type_def,
      return_def, raise_def, no_type_error_result_def] >>
  strip_tac >> gvs[]
  >- (strip_tac >>
      drule_all bare_global_lookup_sound >> strip_tac >>
      `env.current_src = current_module cx` by
        gvs[env_consistent_def, env_context_consistent_def] >>
      `?imms. ALOOKUP st.immutables cx.txn.target = SOME imms` by (
        Cases_on `ALOOKUP st.immutables cx.txn.target` >>
        gvs[get_source_immutables_def]) >>
      `FLOOKUP (get_source_immutables (current_module cx) imms) (string_to_num id) = SOME (tv,v)` by
        gvs[] >>
      qpat_x_assum `(case _ of _ => _ | _ => _) = (res,st')` mp_tac >>
      simp[return_def, raise_def] >> strip_tac >>
      gvs[env_consistent_def, env_context_consistent_def, expr_result_typed_def,
          expr_runtime_typed_def, expr_type_def, toplevel_value_typed_Value] >>
      metis_tac[]) >>
  rpt strip_tac >> gvs[well_typed_expr_def]
QED

Resume eval_all_type_sound_mutual[Expr_TopLevelName]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >> gvs[]
  >- (strip_tac >>
      imp_res_tac lookup_global_state >> gvs[] >>
      drule_all lookup_global_TopLevelName_sound >>
      strip_tac >> gvs[]) >>
  rpt strip_tac >>
  imp_res_tac lookup_global_state >> gvs[] >>
  drule_all lookup_global_TopLevelName_place_sound >>
  strip_tac >> gvs[]
QED

Resume eval_all_type_sound_mutual[Expr_FlagMember]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >> gvs[]
  >- (strip_tac >>
      drule_all flag_member_sound >> strip_tac >>
      imp_res_tac lookup_flag_mem_state >> gvs[] >>
      PairCases_on `nsid` >>
      gvs[env_consistent_def, env_context_consistent_def] >>
      qpat_x_assum `!src fid ls. FLOOKUP env.flag_members (src,fid) = SOME ls ==> _`
        (drule_then strip_assume_tac) >>
      `LENGTH members <= 256` by
        gvs[well_typed_expr_def, well_formed_type_def, evaluate_type_def] >>
      qpat_x_assum `lookup_flag_mem _ _ _ _ = _` mp_tac >>
      simp[lookup_flag_mem_def, return_def, raise_def] >>
      Cases_on `INDEX_OF mid members` >> strip_tac >>
      gvs[return_def, no_type_error_result_def, expr_result_typed_def,
          expr_runtime_typed_def, expr_type_def, toplevel_value_typed_Value,
          evaluate_type_def, value_has_type_def, INDEX_OF_eq_NONE,
          INDEX_OF_eq_SOME] >>
      irule bitTheory.TWOEXP_MONO >> simp[]) >>
  rpt strip_tac >> gvs[well_typed_expr_def]
QED

Theorem evaluate_type_BaseT_BoolT[local]:
  evaluate_type tenv (BaseT BoolT) = SOME (BaseTV BoolT)
Proof
  simp[evaluate_type_def]
QED

Theorem expr_result_typed_BaseT_BoolT_value[local]:
  expr_result_typed env e tv /\ expr_type e = BaseT BoolT ==>
  toplevel_value_typed tv (BaseTV BoolT)
Proof
  rw[expr_result_typed_def, expr_runtime_typed_def] >>
  gvs[evaluate_type_BaseT_BoolT]
QED

Theorem expr_result_typed_IfExp_branch[local]:
  well_typed_expr env branch /\ expr_type branch = ty /\
  expr_result_typed env branch tv ==>
  expr_result_typed env (IfExp ty cond e1 e2) tv
Proof
  rw[expr_result_typed_def, expr_runtime_typed_def, expr_type_def,
      well_typed_expr_def] >>
  metis_tac[well_typed_expr_not_hashmap_place]
QED

Theorem ifexp_branch_from_cond_ih[local]:
  (!s0 tv0 t0.
     eval_expr cx cond s0 = (INL tv0,t0) ==>
     !env0 st0 res0 st0'.
       env_consistent env0 cx st0 /\ state_well_typed st0 /\
       context_well_typed cx /\ accounts_well_typed st0.accounts /\
       functions_well_typed cx /\ eval_expr cx branch st0 = (res0,st0') ==>
       (well_typed_expr env0 branch ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => expr_result_typed env0 branch tv | INR exn => T) /\
       !vt. type_place_expr env0 branch = SOME vt ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => place_expr_result_typed env0 tv vt | INR exn => T) /\
  eval_expr cx cond cond_st = (INL cond_tv,branch_st) /\
  well_typed_expr env branch /\ expr_type branch = ty /\
  env_consistent env cx branch_st /\ state_well_typed branch_st /\
  context_well_typed cx /\ accounts_well_typed branch_st.accounts /\
  functions_well_typed cx /\ eval_expr cx branch branch_st = (res,st') ==>
  state_well_typed st' /\ env_consistent env cx st' /\
  accounts_well_typed st'.accounts /\ no_type_error_result res /\
  case res of
    INL tv => expr_result_typed env (IfExp ty cond e_true e_false) tv
  | INR exn => T
Proof
  strip_tac >>
  qpat_x_assum `!s0 tv0 t0. eval_expr cx cond s0 = (INL tv0,t0) ==> _`
    (qspecl_then [`cond_st`,`cond_tv`,`branch_st`] mp_tac) >>
  simp[] >>
  disch_then (qspecl_then [`env`,`branch_st`,`res`,`st'`] mp_tac) >>
  (impl_tac >- simp[]) >>
  strip_tac >>
  Cases_on `res` >> gvs[] >>
  irule expr_result_typed_IfExp_branch >> simp[] >>
  qexists `branch` >> simp[]
QED

Theorem ifexp_switch_from_branch_ihs[local]:
  toplevel_value_typed cond_tv (BaseTV BoolT) /\
  eval_expr cx cond cond_st = (INL cond_tv,branch_st) /\
  switch_BoolV cond_tv (eval_expr cx e_true) (eval_expr cx e_false) branch_st = (res,st') /\
  (!s0 tv0 t0.
     eval_expr cx cond s0 = (INL tv0,t0) ==>
     !env0 st0 res0 st0'.
       env_consistent env0 cx st0 /\ state_well_typed st0 /\
       context_well_typed cx /\ accounts_well_typed st0.accounts /\
       functions_well_typed cx /\ eval_expr cx e_true st0 = (res0,st0') ==>
       (well_typed_expr env0 e_true ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => expr_result_typed env0 e_true tv | INR exn => T) /\
       !vt. type_place_expr env0 e_true = SOME vt ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => place_expr_result_typed env0 tv vt | INR exn => T) /\
  (!s0 tv0 t0.
     eval_expr cx cond s0 = (INL tv0,t0) ==>
     !env0 st0 res0 st0'.
       env_consistent env0 cx st0 /\ state_well_typed st0 /\
       context_well_typed cx /\ accounts_well_typed st0.accounts /\
       functions_well_typed cx /\ eval_expr cx e_false st0 = (res0,st0') ==>
       (well_typed_expr env0 e_false ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => expr_result_typed env0 e_false tv | INR exn => T) /\
       !vt. type_place_expr env0 e_false = SOME vt ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => place_expr_result_typed env0 tv vt | INR exn => T) /\
  well_typed_expr env e_true /\ expr_type e_true = ty /\
  well_typed_expr env e_false /\ expr_type e_false = ty /\
  env_consistent env cx branch_st /\ state_well_typed branch_st /\
  context_well_typed cx /\ accounts_well_typed branch_st.accounts /\
  functions_well_typed cx ==>
  state_well_typed st' /\ env_consistent env cx st' /\
  accounts_well_typed st'.accounts /\ no_type_error_result res /\
  case res of
    INL tv => expr_result_typed env (IfExp ty cond e_true e_false) tv
  | INR exn => T
Proof
  strip_tac >>
  qho_match_abbrev_tac `P res st'` >>
  irule switch_BoolV_post >>
  goal_assum $ drule_at (Pat `switch_BoolV`) >>
  simp[] >>
  rpt strip_tac
  >- (qunabbrev_tac `P` >> BETA_TAC >>
      irule ifexp_branch_from_cond_ih >>
      conj_tac >- simp[] >>
      conj_tac >- simp[] >>
      qexistsl [`e_false`,`branch_st`,`cond_st`,`cond_tv`] >>
      conj_tac >- (
        qpat_assum `!s0 tv0 t0. eval_expr cx cond s0 = (INL tv0,t0) ==> !env0 st0 res0 st0'. _`
          ACCEPT_TAC) >>
      asm_rewrite_tac[])
  >- (qunabbrev_tac `P` >> BETA_TAC >>
      irule ifexp_branch_from_cond_ih >>
      conj_tac >- simp[] >>
      conj_tac >- simp[] >>
      qexistsl [`e_true`,`branch_st`,`cond_st`,`cond_tv`] >>
      conj_tac >- (
        qpat_assum `!s0 tv0 t0. eval_expr cx cond s0 = (INL tv0,t0) ==> !env0 st0 res0 st0'. _`
          ACCEPT_TAC) >>
      asm_rewrite_tac[])
QED

Theorem type_place_expr_IfExp_NONE[local]:
  !env ty cond e_true e_false.
    type_place_expr env (IfExp ty cond e_true e_false) = NONE
Proof
  simp[Once well_typed_expr_def]
QED

Resume eval_all_type_sound_mutual[Expr_IfExp]:
  rpt gen_tac >> strip_tac >>
  reverse conj_tac >- (
    rpt strip_tac >>
    qpat_x_assum `type_place_expr _ (IfExp _ _ _ _) = SOME _` mp_tac >>
    simp[type_place_expr_IfExp_NONE]) >>
  disch_then mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
      qpat_x_assum `eval_expr _ (IfExp _ _ _ _) _ = _` mp_tac >>
      simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
      Cases_on `eval_expr cx e st` >>
      rename1 `eval_expr cx e st = (cond_res, st1)` >>
      qpat_x_assum `!env st res st'. env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\ eval_expr cx e st = (res,st') ==> _`
        (qspecl_then [`env`,`st`,`cond_res`,`st1`] mp_tac) >>
      impl_tac >- simp[] >>
      strip_tac >>
      qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
      impl_tac >- simp[] >>
      strip_tac >>
      Cases_on `cond_res`
      >- (
        simp_tac bool_ss [] >>
        qpat_x_assum `case INL x of INL tv => expr_result_typed env e tv | INR v1 => T`
          (assume_tac o SIMP_RULE (srw_ss()) []) >>
        `toplevel_value_typed x (BaseTV BoolT)` by
          metis_tac[expr_result_typed_BaseT_BoolT_value] >>
        qpat_x_assum `(case (INL _,_) of _ => _ | _ => _) = _` mp_tac >>
        simp_tac bool_ss [] >> strip_tac >>
        strip_tac >>
        `switch_BoolV x (eval_expr cx e') (eval_expr cx e'') st1 = (res,st')` by (
          qpat_x_assum `(case (INL x,st1) of
                           (INL tv,s'') => switch_BoolV tv (eval_expr cx e') (eval_expr cx e'') s''
                         | (INR exn,s'') => (INR exn,s'')) = (res,st')` mp_tac >>
          simp_tac(srw_ss())[]) >>
        irule ifexp_switch_from_branch_ihs >>
        conj_tac >- (
          rpt strip_tac >>
          qpat_x_assum `!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> !env st res st'. env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\ eval_expr cx e'' st = (res,st') ==> _`
            (qspecl_then [`s0`,`tv0`,`t0`] mp_tac) >>
          (impl_tac >- asm_rewrite_tac[]) >>
          strip_tac >>
          qpat_x_assum `!env st res st'. _`
            (qspecl_then [`env0`,`st0`,`res0`,`st0'`] mp_tac) >>
          (impl_tac >- simp[]) >>
          strip_tac >>
          metis_tac[]) >>
        conj_tac >- (
          rpt strip_tac >>
          qpat_x_assum `!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> !env st res st'. env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\ eval_expr cx e' st = (res,st') ==> _`
            (qspecl_then [`s0`,`tv0`,`t0`] mp_tac) >>
          (impl_tac >- asm_rewrite_tac[]) >>
          strip_tac >>
          qpat_x_assum `!env st res st'. _`
            (qspecl_then [`env0`,`st0`,`res0`,`st0'`] mp_tac) >>
          (impl_tac >- simp[]) >>
          strip_tac >>
          metis_tac[]) >>
        asm_rewrite_tac[] >>
        qexistsl [`st1`,`st`,`x`] >>
        asm_rewrite_tac[])
      >- (
        simp_tac bool_ss [] >>
        strip_tac >>
        qpat_x_assum `(case (INR y,st1) of
                         (INL tv,s'') => switch_BoolV tv (eval_expr cx e') (eval_expr cx e'') s''
                       | (INR exn,s'') => (INR exn,s'')) = (res,st')` mp_tac >>
        simp_tac(srw_ss())[] >>
        strip_tac >>
        qpat_x_assum `INR y = res` (assume_tac o GSYM) >>
        qpat_x_assum `st1 = st'` (assume_tac o GSYM) >>
        qpat_x_assum `no_type_error_result (INR y)` mp_tac >>
        strip_tac >>
        asm_rewrite_tac[] >>
        simp_tac(srw_ss())[])
QED

Resume eval_all_type_sound_mutual[Expr_Literal]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, return_def] >>
  strip_tac >>
  gvs[no_type_error_result_def, well_typed_expr_def, well_formed_type_def,
      expr_type_def, optionTheory.IS_SOME_EXISTS] >>
  rw[expr_result_typed_def, expr_runtime_typed_def, expr_type_def] >>
  metis_tac[literal_toplevel_value_typed]
QED

Theorem well_typed_named_exprs_MAP_SND_stmt[local]:
  !env kes. well_typed_named_exprs env kes ==> well_typed_exprs env (MAP SND kes)
Proof
  gen_tac >> Induct >> simp[well_typed_expr_def] >>
  Cases >> simp[well_typed_expr_def]
QED

Theorem struct_has_type_zip_same_names_stmt[local]:
  !names tvs vs.
    LENGTH names = LENGTH tvs /\ LENGTH tvs = LENGTH vs /\
    LIST_REL value_has_type tvs vs ==>
    struct_has_type (ZIP (names,tvs)) (ZIP (names,vs))
Proof
  Induct >> simp[Once value_has_type_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `tvs` >> Cases_on `vs` >> gvs[Once value_has_type_def]
QED


Theorem OPT_MMAP_from_LIST_REL_evaluate_type_stmt[local]:
  !tys tvs tenv.
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs ==>
    OPT_MMAP (evaluate_type tenv) tys = SOME tvs
Proof
  Induct >> Cases_on `tvs` >> simp[OPT_MMAP_def]
QED

Theorem OPT_MMAP_evaluate_type_mono_stmt[local]:
  !types tenv nid tvs.
    OPT_MMAP (evaluate_type (tenv \\ nid)) types = SOME tvs ==>
    OPT_MMAP (evaluate_type tenv) types = SOME tvs
Proof
  Induct >> simp[OPT_MMAP_def] >>
  rpt gen_tac >>
  Cases_on `evaluate_type (tenv \\ nid) h` >> simp[] >>
  Cases_on `OPT_MMAP (evaluate_type (tenv \\ nid)) types` >> simp[] >>
  strip_tac >> gvs[] >>
  imp_res_tac evaluate_type_mono >> simp[] >>
  first_x_assum (qspecl_then [`tenv`, `nid`] mp_tac) >> simp[]
QED
Theorem struct_lit_expr_result_typed[local]:
  well_formed_type env.type_defs (StructT id) /\
  FLOOKUP env.type_defs (string_to_num id) = SOME (StructArgs args) /\
  MAP FST kes = MAP FST args /\
  MAP (expr_type o SND) kes = MAP SND args /\
  exprs_runtime_typed env (MAP SND kes) vs ==>
  expr_result_typed env (StructLit (StructT id) (src_id_opt,id) kes)
    (Value (StructV (ZIP (MAP FST args,vs))))
Proof
  rw[exprs_runtime_typed_def, expr_result_typed_def, expr_runtime_typed_def,
     expr_type_def, toplevel_value_typed_def] >>
  qexists_tac `StructTV (ZIP (MAP FST args,tvs))` >>
  gvs[well_formed_type_def, IS_SOME_EXISTS] >>
  qpat_x_assum `evaluate_type _ (StructT _) = SOME _` mp_tac >>
  simp[Once evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP] >>
  strip_tac >> gvs[value_has_type_def] >>
  qpat_x_assum `MAP (expr_type o SND) kes = MAP SND args` (assume_tac o GSYM) >>
  gvs[] >>
  `OPT_MMAP (evaluate_type env.type_defs) (MAP (expr_type o SND) kes) = SOME tvs` by
    (irule OPT_MMAP_from_LIST_REL_evaluate_type_stmt >>
     gvs[LIST_REL_EL_EQN, EL_MAP]) >>
  `OPT_MMAP (evaluate_type env.type_defs) (MAP (expr_type o SND) kes) = SOME tvs'` by
    metis_tac[OPT_MMAP_evaluate_type_mono_stmt] >>
  gvs[] >>
  irule struct_has_type_zip_same_names_stmt >>
  imp_res_tac LIST_REL_LENGTH >> gvs[LENGTH_MAP] >>
  metis_tac[LENGTH_MAP]
QED

Theorem type_place_expr_StructLit_NONE_stmt[local]:
  !env ty sid kes.
    type_place_expr env (StructLit ty sid kes) = NONE
Proof
  simp[Once well_typed_expr_def]
QED

Resume eval_all_type_sound_mutual[Expr_StructLit]:
  rpt gen_tac >> strip_tac >>
  reverse conj_tac >- (
    rpt strip_tac >>
    qpat_x_assum `type_place_expr _ (StructLit _ _ _) = SOME _` mp_tac >>
    simp[type_place_expr_StructLit_NONE_stmt]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr _ (StructLit _ _ _)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ (StructLit _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_exprs cx (MAP SND kes) st` >>
  rename1 `eval_exprs cx (MAP SND kes) st = (exprs_res,st1)` >>
  qpat_x_assum `!ks. ks = MAP FST kes ==> _` (qspec_then `MAP FST kes` mp_tac) >>
  simp_tac bool_ss [] >>
  `well_typed_exprs env (MAP SND kes)` by
    (irule well_typed_named_exprs_MAP_SND_stmt >> first_assum ACCEPT_TAC) >>
  disch_then drule_all >> strip_tac >>
  Cases_on `exprs_res` >> simp_tac(srw_ss())[]
  >- (
    strip_tac >>
    qpat_x_assum `(let ks = MAP FST kes in do vs <- eval_exprs cx (MAP SND kes); return (Value (StructV (ZIP (ks,vs)))) od) st = (res,st')` mp_tac >>
    asm_simp_tac(srw_ss())[bind_def, return_def, LET_THM] >>
    strip_tac >> gvs[no_type_error_result_def] >>
    irule struct_lit_expr_result_typed >>
    asm_rewrite_tac[])
  >- (
    strip_tac >>
    qpat_x_assum `eval_exprs cx (MAP SND kes) st = (INR y,st1)` (fn ev_th =>
      qpat_x_assum `(let ks = MAP FST kes in do vs <- eval_exprs cx (MAP SND kes); return (Value (StructV (ZIP (ks,vs)))) od) st = (res,st')` mp_tac >>
      asm_simp_tac(srw_ss())[Once bind_def, return_def, LET_THM, ev_th]) >>
    strip_tac >>
    gvs[] >>
    qpat_x_assum `no_type_error_result (INR y)` mp_tac >>
    simp[no_type_error_result_def])
QED


Theorem subscript_type_ok_evaluate_stmt[local]:
  !ct it rt tenv atv.
    subscript_type_ok ct it rt /\
    evaluate_type tenv ct = SOME atv ==>
    ?rtv. evaluate_type tenv rt = SOME rtv
Proof
  Cases >> simp[subscript_type_ok_def] >>
  rpt strip_tac >> gvs[Once evaluate_type_def, AllCaseEqs()] >>
  gvs[evaluate_types_OPT_MMAP, OPT_MMAP_SOME_IFF] >>
  Cases_on `l` >> gvs[IS_SOME_EXISTS]
QED

Theorem evaluate_subscript_success_not_HashMapRef_stmt[local]:
  !tenv tv_ty tv idx res.
    evaluate_subscript tenv tv_ty tv idx = INL (INL res) /\ ~is_HashMapRef tv ==>
    ~is_HashMapRef res
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `tv` >> gvs[is_HashMapRef_def]
  >- (Cases_on `v` >> Cases_on `idx` >>
      gvs[evaluate_subscript_def, AllCaseEqs(), is_HashMapRef_def])
  >- (Cases_on `idx` >>
      gvs[evaluate_subscript_def, AllCaseEqs(), is_HashMapRef_def])
QED

Theorem values_have_types_LIST_REL_stmt[local]:
  !tys tvs. values_have_types tys tvs = LIST_REL value_has_type tys tvs
Proof
  Induct >> rw[value_has_type_def] >>
  Cases_on `tvs` >> gvs[value_has_type_def]
QED

Theorem evaluate_subscript_value_well_typed_stmt[local]:
  !tenv arr_tv av idx v ct it ty rtv.
    subscript_type_ok ct it ty /\
    evaluate_type tenv ct = SOME arr_tv /\
    evaluate_type tenv ty = SOME rtv /\
    value_has_type arr_tv (ArrayV av) /\
    array_index arr_tv av idx = SOME v ==>
    value_has_type rtv v
Proof
  rpt gen_tac >>
  Cases_on `ct` >> simp[subscript_type_ok_def] >>
  rpt strip_tac >> gvs[]
  >- (gvs[Once evaluate_type_def, AllCaseEqs()] >>
      gvs[evaluate_types_OPT_MMAP, OPT_MMAP_SOME_IFF] >>
      Cases_on `av` >> gvs[value_has_type_inv] >>
      gvs[array_index_def, AllCaseEqs()] >>
      gvs[oEL_EQ_EL] >>
      gvs[values_have_types_LIST_REL_stmt, LIST_REL_EL_EQN] >>
      first_x_assum (qspec_then `Num idx` mp_tac) >> simp[EL_MAP] >>
      `EL (Num idx) l = ty` by (gvs[EVERY_EL] >> res_tac) >>
      gvs[])
  >> (gvs[Once evaluate_type_def, AllCaseEqs()] >>
      imp_res_tac (cj 1 evaluate_type_well_formed) >>
      metis_tac[array_index_has_type])
QED

Theorem evaluate_subscript_typed_stmt[local]:
  !tenv arr_tv x idx x' ct it result_ty.
    evaluate_subscript tenv arr_tv x idx = INL x' /\
    toplevel_value_typed x arr_tv /\
    ~is_HashMapRef x /\
    subscript_type_ok ct it result_ty /\
    evaluate_type tenv ct = SOME arr_tv ==>
    ?rtv. evaluate_type tenv result_ty = SOME rtv /\
          (case x' of
           | INL tv => toplevel_value_typed tv rtv
           | INR (is_trans, slot, tv) => tv = rtv)
Proof
  rpt gen_tac >> Cases_on `x` >>
  simp[toplevel_value_typed_def, is_HashMapRef_def]
  >- (Cases_on `v` >> Cases_on `idx` >>
      simp[evaluate_subscript_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      imp_res_tac subscript_type_ok_evaluate_stmt >>
      Cases_on `evaluate_type tenv result_ty` >> gvs[toplevel_value_typed_def] >>
      irule evaluate_subscript_value_well_typed_stmt >>
      qexistsl [`arr_tv`,`a`,`ct`,`i`,`it`,`tenv`,`result_ty`] >>
      asm_rewrite_tac[])
  >> (Cases_on `idx` >>
      simp[evaluate_subscript_def, AllCaseEqs(), LET_THM] >>
      rpt strip_tac >> gvs[] >>
      Cases_on `ct` >> gvs[subscript_type_ok_def] >>
      gvs[Once evaluate_type_def, AllCaseEqs()] >>
      simp[toplevel_value_typed_def])
QED

Theorem value_has_type_BaseTV_ArrayV_F_stmt[local]:
  !bt av. value_has_type (BaseTV bt) (ArrayV av) ==> F
Proof
  Cases >> Cases_on `av` >> simp[value_has_type_inv]
QED

Theorem value_has_type_TupleTV_dest_stmt[local]:
  !tvs v. value_has_type (TupleTV tvs) v ==>
          ?vs. v = ArrayV (TupleV vs) /\ values_have_types tvs vs
Proof
  Cases_on `v` >> gvs[value_has_type_inv] >>
  Cases_on `a` >> gvs[value_has_type_inv]
QED

Theorem value_has_type_ArrayTV_dest_stmt[local]:
  !tv bd v. value_has_type (ArrayTV tv bd) v ==> ?av. v = ArrayV av
Proof
  Cases_on `v` >> gvs[value_has_type_inv] >>
  Cases_on `a` >> gvs[value_has_type_inv]
QED

Theorem check_array_bounds_error_not_TypeError_stmt[local]:
  !cx tv v st y st'.
    check_array_bounds cx tv v st = (INR y, st') ==>
    !msg. y <> Error (TypeError msg)
Proof
  rw[oneline check_array_bounds_def, bind_def, return_def, raise_def,
     check_def, assert_def, AllCaseEqs(), toplevel_value_CASE_rator,
     value_CASE_rator, bound_CASE_rator] >>
  gvs[get_storage_backend_no_error]
QED

Theorem evaluate_subscript_error_not_TypeError_stmt[local]:
  !tenv arr_tv x idx err ct it result_ty idx_tv.
    evaluate_subscript tenv arr_tv x idx = INR err /\
    toplevel_value_typed x arr_tv /\
    ~is_HashMapRef x /\
    subscript_type_ok ct it result_ty /\
    evaluate_type tenv ct = SOME arr_tv /\
    evaluate_type tenv it = SOME idx_tv /\
    value_has_type idx_tv idx ==>
    !msg. err <> TypeError msg
Proof
  rpt gen_tac >> Cases_on `ct` >> simp[subscript_type_ok_def] >>
  rpt strip_tac >> gvs[Once evaluate_type_def, AllCaseEqs()] >>
  Cases_on `it` >> gvs[is_int_type_def, Once evaluate_type_def, AllCaseEqs()] >>
  TRY (Cases_on `b` >> gvs[is_int_type_def, Once evaluate_type_def]) >>
  Cases_on `x` >> gvs[toplevel_value_typed_def, is_HashMapRef_def] >>
  TRY (drule value_has_type_TupleTV_dest_stmt >> strip_tac >> gvs[]) >>
  TRY (drule value_has_type_ArrayTV_dest_stmt >> strip_tac >> gvs[]) >>
  Cases_on `idx` >>
  gvs[value_has_type_inv, evaluate_subscript_def, array_index_def,
      AllCaseEqs(), LET_THM, value_has_type_def]
QED

Theorem expr_subscript_storage_tail_sound_stmt[local]:
  !cx env e e' v9 x x'' y rtv bounds_st res st'.
    state_well_typed bounds_st /\
    env_consistent env cx bounds_st /\
    accounts_well_typed bounds_st.accounts /\
    evaluate_type (get_tenv cx) v9 = SOME rtv /\
    (case y of (is_trans,slot,tv') => tv' = rtv) /\
    well_formed_type_value rtv /\
    check_array_bounds cx x x'' bounds_st = (INL (),bounds_st) /\
    (do
       check_array_bounds cx x x'';
       res <- return (INR y);
       case res of
         INL v => return v
       | INR (is_transient,slot,tv) =>
         do v <- read_storage_slot cx is_transient slot tv; return (Value v) od
     od bounds_st = (res,st')) ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\
    (!msg. res <> INR (Error (TypeError msg))) /\
    (case res of
     | INL tv =>
         (?tv'. evaluate_type (get_tenv cx) (expr_type (Subscript v9 e e')) = SOME tv' /\
                toplevel_value_typed tv tv') /\
         (is_HashMapRef tv ==> ?kt vt. type_place_expr env (Subscript v9 e e') = SOME (HashMapT kt vt))
     | INR v1 => T)
Proof
  rpt gen_tac >> PairCases_on `y` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `do check_array_bounds cx x x''; _ od bounds_st = (res,st')` mp_tac >>
  simp[bind_def, ignore_bind_def, return_def] >> strip_tac >>
  Cases_on `read_storage_slot cx y0 y1 rtv bounds_st` >>
  rename1 `read_storage_slot cx y0 y1 rtv bounds_st = (read_res,read_st)` >>
  `read_st = bounds_st` by metis_tac[read_storage_slot_state] >> gvs[] >>
  Cases_on `read_res` >> gvs[return_def, raise_def]
  >- (drule read_storage_slot_error >> strip_tac >> gvs[])
  >- (`value_has_type rtv x'` by metis_tac[read_storage_slot_success_type] >>
      qexists_tac `rtv` >>
      simp[expr_result_typed_def, expr_runtime_typed_def, expr_type_def,
           toplevel_value_typed_def, is_HashMapRef_def]) >>
  simp[toplevel_value_typed_def, is_HashMapRef_def]
QED
Theorem vtype_annotation_ok_well_formed_type_stmt[local]:
  !tenv vt ty.
    well_formed_vtype tenv vt /\ vtype_annotation_ok vt ty ==>
    well_formed_type tenv ty
Proof
  Cases_on `vt` >> simp[vtype_annotation_ok_def, well_formed_vtype_def] >>
  strip_tac >> simp[well_formed_type_def, evaluate_type_def]
QED

Theorem subscript_vtype_well_formed_stmt[local]:
  !tenv base_vt idx_ty result_vt.
    well_formed_vtype tenv base_vt /\
    subscript_vtype base_vt idx_ty = SOME result_vt ==>
    well_formed_vtype tenv result_vt
Proof
  Cases_on `base_vt` >>
  simp[subscript_vtype_def, well_formed_vtype_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
  >- (Cases_on `t` >>
      gvs[subscript_vtype_def, well_formed_vtype_def,
          well_formed_type_def, evaluate_type_def, AllCaseEqs()] >>
      Cases_on `evaluate_type tenv t'` >> gvs[]) >>
  gvs[]
QED

Theorem type_place_expr_well_formed_vtype_stmt[local]:
  !env cx st e vt.
    env_consistent env cx st /\ type_place_expr env e = SOME vt ==>
    well_formed_vtype env.type_defs vt
Proof
  measureInduct_on `expr_size e` >>
  rpt strip_tac >>
  Cases_on `e` >>
  gvs[Once well_typed_expr_def, AllCaseEqs()]
  >- (PairCases_on `p` >>
      qpat_x_assum `type_place_expr _ _ = SOME _` mp_tac >>
      simp[well_typed_expr_def, AllCaseEqs()] >> strip_tac >>
      gvs[env_consistent_def, env_context_consistent_def] >>
      first_x_assum drule >> simp[]) >>
  qpat_x_assum `!y. expr_size y < _ ==> _` (qspec_then `e'` mp_tac) >>
  (impl_tac >- simp[expr_size_def]) >>
  disch_then (qspecl_then [`env`,`cx`,`st`,`vt'`] mp_tac) >>
  simp[] >> strip_tac >>
  metis_tac[subscript_vtype_well_formed_stmt]
QED

Theorem type_place_expr_annotation_ok_stmt[local]:
  !env e vt. type_place_expr env e = SOME vt ==> vtype_annotation_ok vt (expr_type e)
Proof
  Cases_on `e` >> simp[expr_type_def] >> rpt strip_tac >>
  TRY (PairCases_on `p`) >>
  qpat_x_assum `type_place_expr _ _ = SOME _` mp_tac >>
  simp[Once well_typed_expr_def, vtype_annotation_ok_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem place_expr_result_typed_expr_result_typed_stmt[local]:
  !env e tv vt.
    type_place_expr env e = SOME vt /\
    place_expr_result_typed env tv vt ==>
    expr_result_typed env e tv
Proof
  rw[place_expr_result_typed_def, expr_result_typed_def,
     expr_runtime_typed_def] >>
  `vtype_annotation_ok vt (expr_type e)` by
    metis_tac[type_place_expr_annotation_ok_stmt] >>
  Cases_on `vt` >>
  gvs[vtype_annotation_ok_def, evaluate_type_def,
      toplevel_value_typed_def, is_HashMapRef_def] >>
  metis_tac[]
QED

Theorem check_array_bounds_hashmap_stmt[local]:
  !cx is_t slot kt vt kv st.
    check_array_bounds cx (HashMapRef is_t slot kt vt) kv st = (INL (), st)
Proof
  Cases_on `kv` >> rw[check_array_bounds_def, return_def]
QED

Theorem expr_subscript_place_tail_sound_stmt[local]:
  !cx env e e' v9 vt x idx_tv idx st res st'.
    state_well_typed st /\
    env_consistent env cx st /\
    accounts_well_typed st.accounts /\
    well_formed_type env.type_defs v9 /\
    type_place_expr env e = SOME vt /\
    subscript_vtype vt (expr_type e') = SOME (Type v9) /\
    place_expr_result_typed env x vt /\
    expr_result_typed env e' idx_tv /\
    get_Value idx_tv st = (INL idx,st) /\
    (do
       arr_tv <- lift_option_type (evaluate_type (get_tenv cx) (expr_type e))
                   "Subscript array type";
       check_array_bounds cx x idx;
       res <- lift_sum (evaluate_subscript (get_tenv cx) arr_tv x idx);
       case res of
         INL v => return v
       | INR (is_transient,slot,tv) =>
           do v <- read_storage_slot cx is_transient slot tv; return (Value v) od
     od st = (res,st')) ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    (case res of INL tv => expr_result_typed env (Subscript v9 e e') tv | INR v1 => T)
Proof
  rpt gen_tac >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  Cases_on `vt`
  >- (
    `vtype_annotation_ok (Type t) (expr_type e)` by
      metis_tac[type_place_expr_annotation_ok_stmt] >>
    gvs[vtype_annotation_ok_def, place_expr_result_typed_def] >>
    Cases_on `expr_type e` >> gvs[subscript_vtype_def, subscript_type_ok_def] >>
    qpat_x_assum `do arr_tv <- lift_option_type _ _; _ od st = (res,st')` mp_tac >>
    simp[bind_def, lift_option_type_def, return_def, lift_sum_def] >>
    Cases_on `check_array_bounds cx x idx st` >>
    rename1 `check_array_bounds cx x idx st = (bounds_res,bounds_st)` >>
    `bounds_st = st` by metis_tac[check_array_bounds_state] >> gvs[] >>
    Cases_on `bounds_res` >> gvs[return_def, raise_def]
    >- (
      Cases_on `evaluate_subscript (get_tenv cx) tyv x idx` >> gvs[return_def, raise_def]
      >- (
        rename1 `evaluate_subscript (get_tenv cx) tyv x idx = INL sub_res` >>
        `subscript_type_ok (ArrayT t b) (expr_type e') t` by
          simp[subscript_type_ok_def] >>
        drule_all evaluate_subscript_typed_stmt >> strip_tac >>
        Cases_on `sub_res` >> gvs[return_def, bind_def]
        >- (
          `~is_HashMapRef x'` by
            (drule_all evaluate_subscript_success_not_HashMapRef_stmt >> simp[]) >>
          strip_tac >>
          qpat_x_assum `do check_array_bounds cx x idx; _ od bounds_st = (res,st')` mp_tac >>
          simp[bind_def, ignore_bind_def, return_def] >> strip_tac >>
          gvs[no_type_error_result_def, expr_result_typed_def, expr_runtime_typed_def, expr_type_def]) >>
        strip_tac >>
        simp[no_type_error_result_def, expr_result_typed_def, expr_runtime_typed_def] >>
        irule expr_subscript_storage_tail_sound_stmt >>
        qexistsl [`bounds_st`,`rtv`,`x`,`idx`,`y`] >>
        simp[] >>
        `well_formed_type_value rtv` by metis_tac[evaluate_type_well_formed_type_value] >>
        simp[]) >>
      strip_tac >>
      qpat_x_assum `do check_array_bounds cx x idx; _ od bounds_st = (res,st')` mp_tac >>
      simp[bind_def, ignore_bind_def, return_def, raise_def] >> strip_tac >> gvs[] >>
      `?idx_tyv. evaluate_type (get_tenv cx) (expr_type e') = SOME idx_tyv /\
                 value_has_type idx_tyv idx` by (
        qpat_x_assum `expr_result_typed env e' idx_tv` mp_tac >>
        simp[expr_result_typed_def, expr_runtime_typed_def] >> strip_tac >>
        Cases_on `idx_tv` >>
        gvs[get_Value_def, return_def, raise_def, toplevel_value_typed_def]) >>
      `subscript_type_ok (ArrayT t b) (expr_type e') t` by
        simp[subscript_type_ok_def] >>
      drule_all evaluate_subscript_error_not_TypeError_stmt >>
      strip_tac >> simp[no_type_error_result_def]) >>
    strip_tac >>
    qpat_x_assum `do check_array_bounds cx x idx; _ od bounds_st = (res,st')` mp_tac >>
    simp[bind_def, ignore_bind_def, return_def, raise_def] >> strip_tac >> gvs[] >>
    drule_all check_array_bounds_error_not_TypeError_stmt >>
    strip_tac >> simp[no_type_error_result_def])
  >- (
    `vtype_annotation_ok (HashMapT t v) (expr_type e)` by
      metis_tac[type_place_expr_annotation_ok_stmt] >>
    gvs[vtype_annotation_ok_def, place_expr_result_typed_def, subscript_vtype_def] >>
    `?rtv. evaluate_type (get_tenv cx) v9 = SOME rtv` by
      gvs[well_formed_type_def, IS_SOME_EXISTS] >>
    qpat_x_assum `do arr_tv <- lift_option_type _ _; _ od st = (res,st')` mp_tac >>
    simp[bind_def, lift_option_type_def, return_def, lift_sum_def,
         evaluate_type_def, check_array_bounds_hashmap_stmt, evaluate_subscript_def] >>
    strip_tac >>
    Cases_on `read_storage_slot cx is_t (hashmap_slot slot (encode_hashmap_key (expr_type e') idx)) rtv st` >>
    rename1 `read_storage_slot cx is_t (hashmap_slot slot (encode_hashmap_key t idx)) rtv st = (read_res,read_st)` >>
    `read_st = st` by metis_tac[read_storage_slot_state] >> gvs[] >>
    Cases_on `read_res` >> gvs[return_def, raise_def]
    >- (rename1 `read_storage_slot cx is_t _ rtv _ = (INL read_v,_)` >>
        qpat_x_assum `do check_array_bounds cx (HashMapRef is_t slot t (Type v9)) idx; _ od read_st = (res,st')` mp_tac >>
        simp[bind_def, ignore_bind_def, return_def, check_array_bounds_hashmap_stmt] >>
        strip_tac >> gvs[] >>
        `well_formed_type_value rtv` by metis_tac[evaluate_type_well_formed_type_value] >>
        `value_has_type rtv read_v` by metis_tac[read_storage_slot_success_type] >>
        gvs[no_type_error_result_def, expr_result_typed_def, expr_runtime_typed_def,
            expr_type_def, toplevel_value_typed_def, is_HashMapRef_def]) >>
    qpat_x_assum `do check_array_bounds cx (HashMapRef is_t slot t (Type v9)) idx; _ od read_st = (res,st')` mp_tac >>
    simp[bind_def, ignore_bind_def, return_def, check_array_bounds_hashmap_stmt, raise_def] >>
    strip_tac >> gvs[no_type_error_result_def] >>
    drule read_storage_slot_error >> strip_tac >> simp[])
QED

Theorem expr_subscript_place_projection_tail_sound_stmt[local]:
  !cx env e e' v9 base_vt result_vt base_tv idx_tv idx st res st'.
    state_well_typed st /\
    env_consistent env cx st /\
    accounts_well_typed st.accounts /\
    well_formed_type env.type_defs v9 /\
    type_place_expr env e = SOME base_vt /\
    subscript_vtype base_vt (expr_type e') = SOME result_vt /\
    vtype_annotation_ok result_vt v9 /\
    place_expr_result_typed env base_tv base_vt /\
    expr_result_typed env e' idx_tv /\
    get_Value idx_tv st = (INL idx,st) /\
    (do
       arr_tv <- lift_option_type (evaluate_type (get_tenv cx) (expr_type e))
                   "Subscript array type";
       check_array_bounds cx base_tv idx;
       res <- lift_sum (evaluate_subscript (get_tenv cx) arr_tv base_tv idx);
       case res of
         INL v => return v
       | INR (is_transient,slot,tv) =>
           do v <- read_storage_slot cx is_transient slot tv; return (Value v) od
     od st = (res,st')) ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    (case res of INL tv => place_expr_result_typed env tv result_vt | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  Cases_on `base_vt`
  >- (
    `vtype_annotation_ok (Type t) (expr_type e)` by
      metis_tac[type_place_expr_annotation_ok_stmt] >>
    gvs[vtype_annotation_ok_def, place_expr_result_typed_def] >>
    Cases_on `expr_type e` >> gvs[subscript_vtype_def, subscript_type_ok_def] >>
    qpat_x_assum `do arr_tv <- lift_option_type _ _; _ od st = (res,st')` mp_tac >>
    simp[bind_def, lift_option_type_def, return_def, lift_sum_def] >>
    Cases_on `check_array_bounds cx base_tv idx st` >>
    rename1 `check_array_bounds cx base_tv idx st = (bounds_res,bounds_st)` >>
    `bounds_st = st` by metis_tac[check_array_bounds_state] >> gvs[] >>
    Cases_on `bounds_res` >> gvs[return_def, raise_def]
    >- (
      Cases_on `evaluate_subscript (get_tenv cx) tyv base_tv idx` >> gvs[return_def, raise_def]
      >- (
        rename1 `evaluate_subscript (get_tenv cx) tyv base_tv idx = INL sub_res` >>
        `subscript_type_ok (ArrayT t b) (expr_type e') t` by
          simp[subscript_type_ok_def] >>
        drule_all evaluate_subscript_typed_stmt >> strip_tac >>
        Cases_on `sub_res` >> gvs[return_def, bind_def]
        >- (
          `~is_HashMapRef x` by
            (drule_all evaluate_subscript_success_not_HashMapRef_stmt >> simp[]) >>
          strip_tac >>
          qpat_x_assum `do check_array_bounds cx base_tv idx; _ od bounds_st = (res,st')` mp_tac >>
          simp[bind_def, ignore_bind_def, return_def] >> strip_tac >>
          gvs[no_type_error_result_def, place_expr_result_typed_def]) >>
        strip_tac >> PairCases_on `y` >> gvs[] >>
        qpat_x_assum `do check_array_bounds cx base_tv idx; _ od bounds_st = (res,st')` mp_tac >>
        simp[bind_def, ignore_bind_def, return_def] >> strip_tac >> gvs[] >>
        Cases_on `read_storage_slot cx y0 y1 rtv bounds_st` >>
        rename1 `read_storage_slot cx y0 y1 rtv bounds_st = (read_res,read_st)` >>
        `read_st = bounds_st` by metis_tac[read_storage_slot_state] >> gvs[] >>
        Cases_on `read_res` >> gvs[return_def, raise_def, no_type_error_result_def]
        >- (`well_formed_type_value rtv` by metis_tac[evaluate_type_well_formed_type_value] >>
            `value_has_type rtv x` by metis_tac[read_storage_slot_success_type] >>
            gvs[place_expr_result_typed_def, toplevel_value_typed_def, is_HashMapRef_def]) >>
        drule read_storage_slot_error >> strip_tac >> simp[]) >>
      strip_tac >>
      qpat_x_assum `do check_array_bounds cx base_tv idx; _ od bounds_st = (res,st')` mp_tac >>
      simp[bind_def, ignore_bind_def, return_def, raise_def] >> strip_tac >> gvs[] >>
      `?idx_tyv. evaluate_type (get_tenv cx) (expr_type e') = SOME idx_tyv /\
                 value_has_type idx_tyv idx` by (
        qpat_x_assum `expr_result_typed env e' idx_tv` mp_tac >>
        simp[expr_result_typed_def, expr_runtime_typed_def] >> strip_tac >>
        Cases_on `idx_tv` >>
        gvs[get_Value_def, return_def, raise_def, toplevel_value_typed_def]) >>
      `subscript_type_ok (ArrayT t b) (expr_type e') t` by
        simp[subscript_type_ok_def] >>
      drule_all evaluate_subscript_error_not_TypeError_stmt >>
      strip_tac >> simp[no_type_error_result_def]) >>
    strip_tac >>
    qpat_x_assum `do check_array_bounds cx base_tv idx; _ od bounds_st = (res,st')` mp_tac >>
    simp[bind_def, ignore_bind_def, return_def, raise_def] >> strip_tac >> gvs[] >>
    drule_all check_array_bounds_error_not_TypeError_stmt >>
    strip_tac >> simp[no_type_error_result_def])
  >- (
    `vtype_annotation_ok (HashMapT t v) (expr_type e)` by
      metis_tac[type_place_expr_annotation_ok_stmt] >>
    Cases_on `result_vt` >>
    gvs[vtype_annotation_ok_def, place_expr_result_typed_def, subscript_vtype_def]
    >- (
      `?rtv. evaluate_type (get_tenv cx) t' = SOME rtv` by
        gvs[well_formed_type_def, IS_SOME_EXISTS] >>
      qpat_x_assum `do arr_tv <- lift_option_type _ _; _ od st = (res,st')` mp_tac >>
      simp[bind_def, lift_option_type_def, return_def, lift_sum_def,
           evaluate_type_def, check_array_bounds_hashmap_stmt, evaluate_subscript_def] >>
      strip_tac >>
      Cases_on `read_storage_slot cx is_t (hashmap_slot slot (encode_hashmap_key (expr_type e') idx)) rtv st` >>
      rename1 `read_storage_slot cx is_t (hashmap_slot slot (encode_hashmap_key kt idx)) rtv st = (read_res,read_st)` >>
      `read_st = st` by metis_tac[read_storage_slot_state] >> gvs[] >>
      Cases_on `read_res` >> gvs[return_def, raise_def, no_type_error_result_def]
      >- (gvs[bind_def, ignore_bind_def, return_def, check_array_bounds_hashmap_stmt] >>
          `well_formed_type_value rtv` by metis_tac[evaluate_type_well_formed_type_value] >>
          `value_has_type rtv x` by metis_tac[read_storage_slot_success_type] >>
          gvs[place_expr_result_typed_def, toplevel_value_typed_def, is_HashMapRef_def]) >>
      gvs[bind_def, ignore_bind_def, return_def, check_array_bounds_hashmap_stmt] >>
      drule read_storage_slot_error >> strip_tac >> simp[]) >>
    qpat_x_assum `do arr_tv <- lift_option_type _ _; _ od st = (res,st')` mp_tac >>
    simp[bind_def, ignore_bind_def, lift_option_type_def, return_def, lift_sum_def,
         evaluate_type_def, check_array_bounds_hashmap_stmt, evaluate_subscript_def] >>
    strip_tac >> gvs[return_def, no_type_error_result_def, place_expr_result_typed_def])
QED

Theorem expr_subscript_place_projection_branch_sound_stmt[local]:
  !cx env e e' v9 base_vt result_vt base_tv st1 res st'.
    state_well_typed st1 /\
    env_consistent env cx st1 /\
    context_well_typed cx /\
    accounts_well_typed st1.accounts /\
    functions_well_typed cx /\
    well_formed_type env.type_defs v9 /\
    well_typed_expr env e' /\
    type_place_expr env e = SOME base_vt /\
    subscript_vtype base_vt (expr_type e') = SOME result_vt /\
    vtype_annotation_ok result_vt v9 /\
    place_expr_result_typed env base_tv base_vt /\
    (!env0 st0 res0 st0'.
      env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
      accounts_well_typed st0.accounts /\ functions_well_typed cx /\
      eval_expr cx e' st0 = (res0,st0') ==>
      (well_typed_expr env0 e' ==>
       state_well_typed st0' /\ env_consistent env0 cx st0' /\
       accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
       case res0 of INL tv => expr_result_typed env0 e' tv | INR v1 => T) /\
      !vt.
        type_place_expr env0 e' = SOME vt ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => place_expr_result_typed env0 tv vt | INR v1 => T) ==>
    (case (INL base_tv,st1) of
       (INL tv1,s'') =>
         (case eval_expr cx e' s'' of
            (INL tv2,s'') =>
              (case get_Value tv2 s'' of
                 (INL v2,s'') =>
                   (let
                      tenv = get_tenv cx
                    in
                      do
                        arr_tv <- lift_option_type (evaluate_type tenv (expr_type e))
                          "Subscript array type";
                        check_array_bounds cx tv1 v2;
                        res <- lift_sum (evaluate_subscript tenv arr_tv tv1 v2);
                        case res of
                          INL v => return v
                        | INR (is_transient,slot,tv) =>
                          do v <- read_storage_slot cx is_transient slot tv; return (Value v) od
                      od) s''
               | (INR e,s'') => (INR e,s''))
          | (INR e,s'') => (INR e,s''))
     | (INR e,s'') => (INR e,s'')) = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    (case res of INL tv => place_expr_result_typed env tv result_vt | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `eval_expr cx e'' st1` >>
  rename1 `eval_expr cx e'' st1 = (idx_res,st2)` >>
  qpat_x_assum `!env0 st0 res0 st0'. _ ==> _`
    (qspecl_then [`env`,`st1`,`idx_res`,`st2`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `well_typed_expr env e'' ==> _` mp_tac >>
  (impl_tac >- simp[]) >> strip_tac >>
  simp_tac(srw_ss())[] >>
  Cases_on `idx_res` >> gvs[]
  >- (
    Cases_on `get_Value x st2` >>
    rename1 `get_Value x st2 = (val_res,st3)` >>
    Cases_on `val_res` >> gvs[]
    >- (
      strip_tac >>
      drule get_Value_state >> strip_tac >> gvs[] >>
      qspecl_then [`cx`,`env`,`e'`,`e''`,`v9`,`base_vt`,`result_vt`,`base_tv`,`x`,`x'`,`st2`,`res`,`st'`]
        mp_tac expr_subscript_place_projection_tail_sound_stmt >>
      (impl_tac >- simp[]) >>
      simp[]) >>
    strip_tac >>
    drule get_Value_state >> strip_tac >> gvs[] >>
    qspecl_then [`base_vt`,`expr_type e''`,`result_vt`,`env`,`e''`,`x`,`st'`,`INR y`,`st'`]
      mp_tac subscript_vtype_index_get_Value_no_type_error >>
    simp[] >> strip_tac >> gvs[no_type_error_result_def]) >>
  strip_tac >> gvs[]
QED

Theorem expr_subscript_ordinary_tail_sound_stmt[local]:
  !cx env e e' v9 base_tv idx_tv idx st res st'.
    state_well_typed st /\
    env_consistent env cx st /\
    accounts_well_typed st.accounts /\
    well_formed_type env.type_defs v9 /\
    subscript_type_ok (expr_type e) (expr_type e') v9 /\
    expr_result_typed env e base_tv /\
    expr_result_typed env e' idx_tv /\
    get_Value idx_tv st = (INL idx,st) /\
    (do
       arr_tv <- lift_option_type (evaluate_type (get_tenv cx) (expr_type e))
                   "Subscript array type";
       check_array_bounds cx base_tv idx;
       sub_res <- lift_sum (evaluate_subscript (get_tenv cx) arr_tv base_tv idx);
       case sub_res of
         INL v => return v
       | INR (is_transient,slot,tv) =>
           do v <- read_storage_slot cx is_transient slot tv; return (Value v) od
     od st = (res,st')) ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    (case res of INL tv => expr_result_typed env (Subscript v9 e e') tv | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  qpat_x_assum `expr_result_typed env e base_tv` mp_tac >>
  simp[expr_result_typed_def, expr_runtime_typed_def] >> strip_tac >>
  qpat_x_assum `expr_result_typed env e' idx_tv` mp_tac >>
  simp[expr_result_typed_def, expr_runtime_typed_def] >> strip_tac >>
  `~is_HashMapRef base_tv` by (
    Cases_on `base_tv` >>
    gvs[is_HashMapRef_def, toplevel_value_typed_def] >>
    Cases_on `expr_type e` >>
    gvs[subscript_type_ok_def, Once evaluate_type_def, AllCaseEqs()]) >>
  `value_has_type tv' idx` by (
    qpat_x_assum `get_Value idx_tv st = (INL idx,st)` mp_tac >>
    Cases_on `idx_tv` >>
    gvs[get_Value_def, return_def, raise_def, toplevel_value_typed_def] >>
    metis_tac[]) >>
  qpat_x_assum `do arr_tv <- lift_option_type _ _; _ od st = (res,st')` mp_tac >>
  simp[bind_def, lift_option_type_def, return_def, lift_sum_def] >>
  Cases_on `check_array_bounds cx base_tv idx st` >>
  rename1 `check_array_bounds cx base_tv idx st = (bounds_res,bounds_st)` >>
  `bounds_st = st` by metis_tac[check_array_bounds_state] >> gvs[] >>
  Cases_on `bounds_res` >> gvs[return_def, raise_def]
  >- (
    Cases_on `evaluate_subscript (get_tenv cx) tv base_tv idx` >> gvs[return_def, raise_def]
    >- (
      rename1 `evaluate_subscript (get_tenv cx) tv base_tv idx = INL sub_res` >>
      drule_all evaluate_subscript_typed_stmt >> strip_tac >>
      Cases_on `sub_res` >> gvs[return_def, bind_def]
      >- (
        `~is_HashMapRef x` by
          (drule_all evaluate_subscript_success_not_HashMapRef_stmt >> simp[]) >>
        strip_tac >>
        qpat_x_assum `do check_array_bounds cx base_tv idx; _ od bounds_st = (res,st')` mp_tac >>
        simp[bind_def, ignore_bind_def, return_def] >> strip_tac >>
        gvs[no_type_error_result_def, expr_result_typed_def, expr_runtime_typed_def, expr_type_def]) >>
      strip_tac >>
      simp[no_type_error_result_def, expr_result_typed_def, expr_runtime_typed_def] >>
      irule expr_subscript_storage_tail_sound_stmt >>
      qexistsl [`bounds_st`,`rtv`,`base_tv`,`idx`,`y`] >>
      simp[] >>
      `well_formed_type_value rtv` by metis_tac[evaluate_type_well_formed_type_value] >>
      simp[]) >>
    strip_tac >>
    qpat_x_assum `do check_array_bounds cx base_tv idx; _ od bounds_st = (res,st')` mp_tac >>
    simp[bind_def, ignore_bind_def, return_def, raise_def] >> strip_tac >> gvs[] >>
    drule_all evaluate_subscript_error_not_TypeError_stmt >>
    strip_tac >> simp[no_type_error_result_def]) >>
  strip_tac >>
  qpat_x_assum `do check_array_bounds cx base_tv idx; _ od bounds_st = (res,st')` mp_tac >>
  simp[bind_def, ignore_bind_def, return_def, raise_def] >> strip_tac >> gvs[] >>
  drule_all check_array_bounds_error_not_TypeError_stmt >>
  strip_tac >> simp[no_type_error_result_def]
QED

Theorem subscript_type_ok_index_is_int_stmt[local]:
  !base_ty idx_ty result_ty.
    subscript_type_ok base_ty idx_ty result_ty ==> is_int_type idx_ty
Proof
  Cases >> simp[subscript_type_ok_def]
QED

Theorem expr_subscript_index_get_Value_INR_no_type_error_stmt[local]:
  !env e e' v9 tv st y st'.
    expr_result_typed env e' tv /\
    subscript_type_ok (expr_type e) (expr_type e') v9 /\
    get_Value tv st = (INR y, st') ==>
    no_type_error_result (INR y)
Proof
  rpt strip_tac >>
  qspecl_then [`env`,`e'`,`tv`,`expr_type e'`,`st`,`y`,`st'`]
    mp_tac int_expr_get_Value_INR_no_type_error >>
  (impl_tac >- (
    simp[] >>
    drule subscript_type_ok_index_is_int_stmt >> simp[])) >>
  simp[]
QED

Theorem expr_subscript_ordinary_base_success_sound_stmt[local]:
  !cx env e e' v9 base_tv st st1 res st'.
    env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
    accounts_well_typed st.accounts /\ functions_well_typed cx /\
    well_typed_expr env e' /\
    well_formed_type env.type_defs v9 /\
    subscript_type_ok (expr_type e) (expr_type e') v9 /\
    eval_expr cx e st = (INL base_tv,st1) /\
    state_well_typed st1 /\ env_consistent env cx st1 /\
    accounts_well_typed st1.accounts /\
    expr_result_typed env e base_tv /\
    (!env0 st0 res0 st0'.
      env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
      accounts_well_typed st0.accounts /\ functions_well_typed cx /\
      eval_expr cx e' st0 = (res0,st0') ==>
      (well_typed_expr env0 e' ==>
       state_well_typed st0' /\ env_consistent env0 cx st0' /\
       accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
       case res0 of INL tv => expr_result_typed env0 e' tv | INR v1 => T) /\
      !vt.
        type_place_expr env0 e' = SOME vt ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => place_expr_result_typed env0 tv vt | INR v1 => T) /\
    eval_expr cx (Subscript v9 e e') st = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of INL tv => expr_result_typed env (Subscript v9 e e') tv | INR v1 => T
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr cx (Subscript v9 e e') st = (res,st')` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  qpat_x_assum `eval_expr cx e st = (INL base_tv,st1)`
    (fn th => simp_tac(srw_ss())[th]) >>
  Cases_on `eval_expr cx e' st1` >>
  rename1 `eval_expr cx e' st1 = (idx_res,st2)` >>
  qpat_x_assum `!env0 st0 res0 st0'.
    env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
    accounts_well_typed st0.accounts /\ functions_well_typed cx /\
    eval_expr cx e' st0 = (res0,st0') ==> _`
    (qspecl_then [`env`,`st1`,`idx_res`,`st2`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  Cases_on `idx_res`
  >- (
    simp_tac(srw_ss())[] >> strip_tac >>
    qpat_x_assum `well_typed_expr env e' ==> _` mp_tac >>
    (impl_tac >- simp[]) >> strip_tac >>
    qpat_x_assum `case INL x of INL tv => expr_result_typed env e' tv | INR v1 => T` mp_tac >>
    simp_tac(srw_ss())[] >> strip_tac >>
    qpat_x_assum `(case get_Value x st2 of _ => _) = (res,st')` mp_tac >>
    Cases_on `get_Value x st2` >>
    rename1 `get_Value x st2 = (val_res,st3)` >>
    Cases_on `val_res`
    >- (
      simp_tac(srw_ss())[] >> strip_tac >> gvs[] >>
      rename1 `get_Value x st2 = (INL idx,st3)` >>
      drule get_Value_state >> strip_tac >> gvs[] >>
      qspecl_then [`cx`,`env`,`e`,`e'`,`v9`,`base_tv`,`x`,`idx`,`st2`,`res`,`st'`]
        mp_tac expr_subscript_ordinary_tail_sound_stmt >>
      (impl_tac >- simp[]) >>
      simp[]) >>
    simp_tac(srw_ss())[] >> strip_tac >> gvs[] >>
    rename1 `get_Value x st2 = (INR val_err,st3)` >>
    drule get_Value_state >> strip_tac >> gvs[] >>
    irule expr_subscript_index_get_Value_INR_no_type_error_stmt >>
    qexistsl [`e`,`e'`,`env`,`st2`,`st2`,`x`,`v9`] >>
    simp[])
  >- (
    simp_tac(srw_ss())[] >> strip_tac >>
    qpat_x_assum `well_typed_expr env e' ==> _` mp_tac >>
    (impl_tac >- simp[]) >> strip_tac >>
    gvs[])
QED

Theorem expr_subscript_ordinary_static_branch_sound_stmt[local]:
  !cx env e e' v9 st res st'.
    env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
    accounts_well_typed st.accounts /\ functions_well_typed cx /\
    well_typed_expr env e /\ well_typed_expr env e' /\
    well_formed_type env.type_defs v9 /\
    subscript_type_ok (expr_type e) (expr_type e') v9 /\
    eval_expr cx (Subscript v9 e e') st = (res,st') /\
    (!env0 st0 res0 st0'.
      env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
      accounts_well_typed st0.accounts /\ functions_well_typed cx /\
      eval_expr cx e st0 = (res0,st0') ==>
      (well_typed_expr env0 e ==>
       state_well_typed st0' /\ env_consistent env0 cx st0' /\
       accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
       case res0 of INL tv => expr_result_typed env0 e tv | INR v1 => T) /\
      !vt.
        type_place_expr env0 e = SOME vt ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => place_expr_result_typed env0 tv vt | INR v1 => T) /\
    (!s'' tv1 t.
      eval_expr cx e s'' = (INL tv1,t) ==>
      !env0 st0 res0 st0'.
        env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
        accounts_well_typed st0.accounts /\ functions_well_typed cx /\
        eval_expr cx e' st0 = (res0,st0') ==>
        (well_typed_expr env0 e' ==>
         state_well_typed st0' /\ env_consistent env0 cx st0' /\
         accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
         case res0 of INL tv => expr_result_typed env0 e' tv | INR v1 => T) /\
        !vt.
          type_place_expr env0 e' = SOME vt ==>
          state_well_typed st0' /\ env_consistent env0 cx st0' /\
          accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
          case res0 of INL tv => place_expr_result_typed env0 tv vt | INR v1 => T) ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of INL tv => expr_result_typed env (Subscript v9 e e') tv | INR v1 => T
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (base_res,st1)` >>
  qpat_x_assum `!env0 st0 res0 st0'.
    env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
    accounts_well_typed st0.accounts /\ functions_well_typed cx /\
    eval_expr cx e st0 = (res0,st0') ==> _`
    (qspecl_then [`env`,`st`,`base_res`,`st1`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  Cases_on `base_res`
  >- (
    rename1 `eval_expr cx e st = (INL base_tv,st1)` >>
    qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
    (impl_tac >- simp[]) >> strip_tac >>
    qpat_x_assum `!s'' tv1 t. eval_expr cx e s'' = (INL tv1,t) ==> _`
      (qspecl_then [`st`,`base_tv`,`st1`] mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    qpat_x_assum `case INL base_tv of INL tv => expr_result_typed env e tv | INR v1 => T` mp_tac >>
    simp_tac(srw_ss())[] >> strip_tac >>
    qspecl_then [`cx`,`env`,`e`,`e'`,`v9`,`base_tv`,`st`,`st1`,`res`,`st'`]
      mp_tac expr_subscript_ordinary_base_success_sound_stmt >>
    disch_then irule >>
    rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (
    qpat_x_assum `eval_expr cx (Subscript v9 e e') st = (res,st')` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
    qpat_x_assum `eval_expr cx e st = (INR y,st1)`
      (fn th => simp_tac(srw_ss())[th]) >>
    strip_tac >>
    qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
    (impl_tac >- simp[]) >> strip_tac >>
    qpat_x_assum `INR y = res` (fn th => rewrite_tac[GSYM th]) >>
    qpat_x_assum `st1 = st'` (fn th => rewrite_tac[GSYM th]) >>
    rewrite_tac[] >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    simp_tac(srw_ss())[])
QED

Theorem expr_subscript_place_as_ordinary_branch_sound_stmt[local]:
  !cx env e e' v9 base_vt st res st'.
    env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
    accounts_well_typed st.accounts /\ functions_well_typed cx /\
    well_typed_expr env e' /\
    type_place_expr env e = SOME base_vt /\
    subscript_vtype base_vt (expr_type e') = SOME (Type v9) /\
    eval_expr cx (Subscript v9 e e') st = (res,st') /\
    (!env0 st0 res0 st0'.
      env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
      accounts_well_typed st0.accounts /\ functions_well_typed cx /\
      eval_expr cx e st0 = (res0,st0') ==>
      (well_typed_expr env0 e ==>
       state_well_typed st0' /\ env_consistent env0 cx st0' /\
       accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
       case res0 of INL tv => expr_result_typed env0 e tv | INR v1 => T) /\
      !vt.
        type_place_expr env0 e = SOME vt ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => place_expr_result_typed env0 tv vt | INR v1 => T) /\
    (!s'' tv1 t.
      eval_expr cx e s'' = (INL tv1,t) ==>
      !env0 st0 res0 st0'.
        env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
        accounts_well_typed st0.accounts /\ functions_well_typed cx /\
        eval_expr cx e' st0 = (res0,st0') ==>
        (well_typed_expr env0 e' ==>
         state_well_typed st0' /\ env_consistent env0 cx st0' /\
         accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
         case res0 of INL tv => expr_result_typed env0 e' tv | INR v1 => T) /\
        !vt.
          type_place_expr env0 e' = SOME vt ==>
          state_well_typed st0' /\ env_consistent env0 cx st0' /\
          accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
          case res0 of INL tv => place_expr_result_typed env0 tv vt | INR v1 => T) ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of INL tv => expr_result_typed env (Subscript v9 e e') tv | INR v1 => T
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (base_res,st1)` >>
  qpat_x_assum `!env0 st0 res0 st0'.
    env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
    accounts_well_typed st0.accounts /\ functions_well_typed cx /\
    eval_expr cx e st0 = (res0,st0') ==> _`
    (qspecl_then [`env`,`st`,`base_res`,`st1`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  Cases_on `base_res`
  >- (
    rename1 `eval_expr cx e st = (INL base_tv,st1)` >>
    qpat_x_assum `!vt. type_place_expr env e = SOME vt ==> state_well_typed st1 /\ _`
      (qspec_then `base_vt` mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    qpat_x_assum `case INL base_tv of INL tv => place_expr_result_typed env tv base_vt | INR v1 => T`
      mp_tac >> simp_tac(srw_ss())[] >> strip_tac >>
    `well_formed_type env.type_defs v9` by (
      `well_formed_vtype env.type_defs base_vt` by
        metis_tac[type_place_expr_well_formed_vtype_stmt] >>
      `well_formed_vtype env.type_defs (Type v9)` by
        metis_tac[subscript_vtype_well_formed_stmt] >>
      `vtype_annotation_ok (Type v9) v9` by simp[vtype_annotation_ok_def] >>
      metis_tac[vtype_annotation_ok_well_formed_type_stmt]) >>
    qpat_x_assum `!s'' tv1 t. eval_expr cx e s'' = (INL tv1,t) ==> _`
      (qspecl_then [`st`,`base_tv`,`st1`] mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    qspecl_then [`cx`,`env`,`e`,`e'`,`v9`,`base_vt`,`Type v9`,`base_tv`,`st1`,`res`,`st'`]
      mp_tac expr_subscript_place_projection_branch_sound_stmt >>
    (impl_tac >- (
      rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- simp[vtype_annotation_ok_def]
      >- first_assum ACCEPT_TAC
      >> first_assum ACCEPT_TAC)) >>
    strip_tac >>
    `state_well_typed st' /\ env_consistent env cx st' /\
     accounts_well_typed st'.accounts /\ no_type_error_result res /\
     (case res of INL tv => place_expr_result_typed env tv (Type v9) | INR v1 => T)` by (
      first_x_assum irule >>
      qpat_x_assum `eval_expr cx (Subscript v9 e e') st = (res,st')` mp_tac >>
      simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
      qpat_x_assum `eval_expr cx e st = (INL base_tv,st1)`
        (fn th => simp_tac(srw_ss())[th])) >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    Cases_on `res` >> simp[] >>
    qpat_x_assum `case INL x of INL tv => place_expr_result_typed env tv (Type v9) | INR v1 => T`
      mp_tac >> simp_tac(srw_ss())[] >> strip_tac >>
    irule place_expr_result_typed_expr_result_typed_stmt >>
    qexists `Type v9` >> simp[Once well_typed_expr_def, vtype_annotation_ok_def])
  >- (
    qpat_x_assum `eval_expr cx (Subscript v9 e e') st = (res,st')` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
    qpat_x_assum `eval_expr cx e st = (INR y,st1)`
      (fn th => simp_tac(srw_ss())[th]) >>
    strip_tac >>
    qpat_x_assum `!vt. type_place_expr env e = SOME vt ==> state_well_typed st1 /\ _`
      (qspec_then `base_vt` mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    qpat_x_assum `INR y = res` (fn th => rewrite_tac[GSYM th]) >>
    qpat_x_assum `st1 = st'` (fn th => rewrite_tac[GSYM th]) >>
    rewrite_tac[] >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    simp_tac(srw_ss())[])
QED

Resume eval_all_type_sound_mutual[Expr_Subscript]:
  (* C2.1.1.13.4 splits the ordinary Subscript static alternatives at this
     boundary and discharges them through the two proved local adapters above. *)
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    qpat_x_assum `well_typed_expr env (Subscript v9 e e')` mp_tac >>
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [well_typed_expr_def])) >>
    strip_tac
    >- (qspecl_then [`cx`,`env`,`e`,`e'`,`v9`,`st`,`res`,`st'`]
          match_mp_tac expr_subscript_ordinary_static_branch_sound_stmt >>
        asm_rewrite_tac[])
    >- (qmatch_asmsub_rename_tac `type_place_expr env e = SOME base_vt` >>
        qspecl_then [`cx`,`env`,`e`,`e'`,`v9`,`base_vt`,`st`,`res`,`st'`]
          match_mp_tac expr_subscript_place_as_ordinary_branch_sound_stmt >>
        asm_rewrite_tac[]))
  >> gen_tac >> strip_tac >>
  qpat_x_assum `type_place_expr env (Subscript v9 e e') = SOME vt` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def, AllCaseEqs()] >>
  strip_tac >>
  qpat_x_assum `eval_expr cx (Subscript v9 e e') st = (res,st')` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (base_res,st1)` >>
  qpat_x_assum `!env0 st0 res0 st0'.
    env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
    accounts_well_typed st0.accounts /\ functions_well_typed cx /\
    eval_expr cx e st0 = (res0,st0') ==> _`
    (qspecl_then [`env`,`st`,`base_res`,`st1`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  Cases_on `base_res`
  >- (
    qpat_x_assum `!vt. type_place_expr env e = SOME vt ==> state_well_typed st1 /\ _`
      (qspec_then `vt'` mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    strip_tac >>
    qpat_x_assum `case INL x of INL tv => place_expr_result_typed env tv vt' | INR v1 => T` mp_tac >>
    simp_tac(srw_ss())[] >> strip_tac >>
    `well_formed_type env.type_defs v9` by (
      `well_formed_vtype env.type_defs vt'` by
        metis_tac[type_place_expr_well_formed_vtype_stmt] >>
      `well_formed_vtype env.type_defs vt` by
        metis_tac[subscript_vtype_well_formed_stmt] >>
      metis_tac[vtype_annotation_ok_well_formed_type_stmt]) >>
    qpat_x_assum `!s'' tv1 t. eval_expr cx e s'' = (INL tv1,t) ==> _`
      (qspecl_then [`st`,`x`,`st1`] mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    qspecl_then [`cx`,`env`,`e`,`e'`,`v9`,`vt'`,`vt`,`x`,`st1`,`res`,`st'`]
      mp_tac expr_subscript_place_projection_branch_sound_stmt >>
    (impl_tac >- (
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC))) >>
    (disch_then irule >> first_assum ACCEPT_TAC))
  >- (
    qpat_x_assum `!vt. type_place_expr env e = SOME vt ==> state_well_typed st1 /\ _`
      (qspec_then `vt'` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
    strip_tac >>
    qpat_x_assum `(case (INR y,st1) of _ => _) = (res,st')` mp_tac >>
    simp_tac(srw_ss())[] >> strip_tac >>
    pop_assum (fn th => rewrite_tac[GSYM th]) >>
    pop_assum (fn th => rewrite_tac[GSYM th]) >>
    rpt conj_tac >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >> simp[])
QED

Theorem struct_has_type_lookup_type_stmt[local]:
  !ftypes fields id field_tv.
    struct_has_type ftypes fields /\ ALOOKUP ftypes id = SOME field_tv ==>
    ?field_v. ALOOKUP fields id = SOME field_v /\ value_has_type field_tv field_v
Proof
  Induct >> Cases_on `fields` >> simp[Once value_has_type_def] >>
  Cases >> Cases_on `h` >> simp[Once value_has_type_def] >>
  rw[] >> gvs[] >> Cases_on `id = q` >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem evaluate_attribute_value_has_type[local]:
  !sv id ftypes field_tv.
    value_has_type (StructTV ftypes) sv /\
    ALOOKUP ftypes id = SOME field_tv ==>
    ?field_v. evaluate_attribute sv id = INL field_v /\
              value_has_type field_tv field_v
Proof
  Cases >> simp[evaluate_attribute_def, value_has_type_def] >>
  rpt strip_tac >>
  drule_all struct_has_type_lookup_type_stmt >> strip_tac >>
  qexists_tac `field_v` >> simp[]
QED

Theorem expr_attribute_success_tail_sound_stmt[local]:
  !cx env e id ty base_tv st st1 res st'.
    state_well_typed st1 /\ env_consistent env cx st1 /\
    accounts_well_typed st1.accounts /\
    expr_result_typed env e base_tv /\
    attribute_type env.type_defs (expr_type e) id = SOME ty /\
    eval_expr cx e st = (INL base_tv,st1) /\
    eval_expr cx (Attribute ty e id) st = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    (case res of
     | INL tv => expr_result_typed env (Attribute ty e id) tv
     | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr cx (Attribute ty e id) st = (res,st')` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  asm_rewrite_tac[] >>
  qhdtm_x_assum `expr_result_typed` mp_tac >>
  simp[expr_result_typed_def, expr_runtime_typed_def] >>
  strip_tac >>
  Cases_on `expr_type e` >> gvs[attribute_type_def, evaluate_type_def, AllCaseEqs()] >>
  strip_tac >>
  `?sv. base_tv = Value sv /\
        value_has_type (StructTV (ZIP (MAP FST fields,tvs))) sv` by
    (Cases_on `base_tv` >> gvs[toplevel_value_typed_def]) >>
  gvs[get_Value_def, return_def, bind_def] >>
  `?field_tv. evaluate_type env.type_defs ty = SOME field_tv /\
              ALOOKUP (ZIP (MAP FST fields,tvs)) id = SOME field_tv` by (
    qspecl_then [`env.type_defs`,`StructT s`,`id`,`ty`,
                 `ZIP (MAP FST fields,tvs)`] mp_tac attribute_type_evaluates >>
    simp[attribute_type_def, evaluate_type_def]) >>
  drule_all evaluate_attribute_value_has_type >> strip_tac >>
  gvs[lift_sum_def, return_def, no_type_error_result_def,
      expr_result_typed_def, expr_runtime_typed_def, expr_type_def,
      toplevel_value_typed_def]
QED

Resume eval_all_type_sound_mutual[Expr_Attribute]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    rename1 `well_typed_expr env (Attribute ty e id)` >>
    qpat_x_assum `well_typed_expr env (Attribute ty e id)` mp_tac >>
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [well_typed_expr_def])) >>
    strip_tac >>
    Cases_on `eval_expr cx e st` >>
    rename1 `eval_expr cx e st = (base_res,st1)` >>
    qpat_x_assum `!env0 st0 res0 st0'.
      env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
      accounts_well_typed st0.accounts /\ functions_well_typed cx /\
      eval_expr cx e st0 = (res0,st0') ==> _`
      (qspecl_then [`env`,`st`,`base_res`,`st1`] mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    Cases_on `base_res`
    >- (
      rename1 `eval_expr cx e st = (INL base_tv,st1)` >>
      qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
      (impl_tac >- simp[]) >> strip_tac >>
      qpat_x_assum `case INL base_tv of INL tv => expr_result_typed env e tv | INR v1 => T`
        mp_tac >> simp_tac(srw_ss())[] >> strip_tac >>
      qspecl_then [`cx`,`env`,`e`,`id`,`ty`,`base_tv`,`st`,`st1`,`res`,`st'`]
        match_mp_tac expr_attribute_success_tail_sound_stmt >>
      qpat_x_assum `attribute_type_ok env.type_defs (expr_type e) id ty` mp_tac >>
      simp[attribute_type_ok_def])
    >- (
      qpat_x_assum `eval_expr cx (Attribute ty e id) st = (res,st')` mp_tac >>
      simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
      qpat_x_assum `eval_expr cx e st = (INR y,st1)`
        (fn th => simp_tac(srw_ss())[th]) >>
      strip_tac >>
      qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
      (impl_tac >- simp[]) >> strip_tac >>
      qpat_x_assum `INR y = res` (assume_tac o GSYM) >>
      qpat_x_assum `st1 = st'` (assume_tac o GSYM) >>
      simp[])) >>
  gen_tac >> strip_tac >>
  gvs[Once well_typed_expr_def]
QED


Resume eval_all_type_sound_mutual[Expr_Builtin]:
  rpt gen_tac >> strip_tac >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (Builtin _ _ _) = SOME _` mp_tac >>
      simp_tac(srw_ss())[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr env (Builtin ty bt es)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  `env.type_defs = get_tenv cx` by metis_tac[env_consistent_def, env_context_consistent_def] >>
  `builtin_args_length_ok bt (LENGTH es)` by
    (drule well_typed_builtin_app_length >> simp[]) >>
  qpat_x_assum `eval_expr cx (Builtin ty bt es) st = (res,st')` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def,
                       type_check_def, assert_def] >>
  Cases_on `bt = Len`
  >- (qpat_assum `builtin_args_length_ok bt (LENGTH es)` (fn th => rewrite_tac[th]) >>
      qpat_assum `bt = Len` (fn th => rewrite_tac[th]) >>
      simp_tac(srw_ss())[bind_def, ignore_bind_def, return_def, raise_def,
                         type_check_def, assert_def] >>
      Cases_on `eval_expr cx (HD es) st` >>
      rename1 `eval_expr cx (HD es) st = (arg_res,arg_st)` >>
      qpat_x_assum `!s'' x t. _ /\ bt = Len ==> _`
        (qspecl_then [`st`,`()`,`st`] mp_tac) >>
      (impl_tac >- simp[type_check_def, assert_def]) >> strip_tac >>
      qpat_x_assum `!env st res st'. _`
        (qspecl_then [`env`,`st`,`arg_res`,`arg_st`] mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      Cases_on `arg_res`
      >- (rename1 `eval_expr cx (HD es) st = (INL arg_tv,arg_st)` >>
          qpat_x_assum `well_typed_expr env (HD es) ==> _` mp_tac >>
          (impl_tac >- (qpat_x_assum `well_typed_builtin_app ty bt (MAP expr_type es)` mp_tac >>
                        Cases_on `es` >> simp[well_typed_builtin_app_def] >>
                        Cases_on `t` >> gvs[well_typed_expr_def])) >>
          simp_tac(srw_ss())[] >> strip_tac >>
          Cases_on `toplevel_array_length cx arg_tv arg_st` >>
          rename1 `toplevel_array_length cx arg_tv arg_st = (len_res,len_st)` >>
          Cases_on `len_res`
          >- (rename1 `toplevel_array_length cx arg_tv arg_st = (INL len,len_st)` >>
              drule toplevel_array_length_state >> strip_tac >> gvs[] >>
              strip_tac >> gvs[expr_result_typed_def, expr_runtime_typed_def,
                               expr_type_def, toplevel_value_typed_Value] >>
              conj_tac >- simp[no_type_error_result_def] >>
              qexists_tac `BaseTV (UintT 256)` >>
              conj_tac
              >- (qpat_x_assum `well_typed_builtin_app ty Len (MAP expr_type es)` mp_tac >>
                  Cases_on `es` >> simp[well_typed_builtin_app_def, evaluate_type_def] >>
                  Cases_on `t` >> gvs[]) >>
              irule Len_builtin_sound >>
              qexistsl_tac [`tv`,`arg_tv`,`expr_type (HD es)`,`cx`,`arg_st`,`arg_st`,`get_tenv cx`,`ty`] >>
              simp[] >>
              qpat_x_assum `well_typed_builtin_app ty Len (MAP expr_type es)` mp_tac >>
              Cases_on `es` >> simp[well_typed_builtin_app_def, evaluate_type_def] >>
              Cases_on `t` >> gvs[]) >>
          rename1 `toplevel_array_length cx arg_tv arg_st = (INR len_exn,len_st)` >>
          drule toplevel_array_length_state >> strip_tac >> gvs[] >>
          strip_tac >> gvs[no_type_error_result_def,
                           expr_result_typed_def, expr_runtime_typed_def] >>
          strip_tac >> spose_not_then assume_tac >> gvs[] >>
          `well_formed_type_value tv` by metis_tac[evaluate_type_well_formed_type_value] >>
          `well_typed_builtin_app ty Len [expr_type (HD es)]` by
            (qpat_x_assum `well_typed_builtin_app ty Len (MAP expr_type es)` mp_tac >>
             Cases_on `es` >> simp[well_typed_builtin_app_def] >>
             Cases_on `t` >> gvs[]) >>
          drule_all Len_toplevel_array_length_no_type_error >> simp[]) >>
      qpat_x_assum `well_typed_expr env (HD es) ==> _` mp_tac >>
      (impl_tac >- (qpat_x_assum `well_typed_builtin_app ty bt (MAP expr_type es)` mp_tac >>
                    Cases_on `es` >> simp[well_typed_builtin_app_def] >>
                    Cases_on `t` >> gvs[well_typed_expr_def])) >>
      strip_tac >> strip_tac >> gvs[]) >>
  qpat_x_assum `bt <> Len` (fn th => rewrite_tac[th]) >>
  qpat_x_assum `builtin_args_length_ok bt (LENGTH es)` (fn th => rewrite_tac[th]) >>
  simp_tac(srw_ss())[bind_def, ignore_bind_def, return_def, raise_def,
                     type_check_def, assert_def, get_accounts_def, lift_sum_def] >>
  FAIL_TAC "Expr_Builtin non-Len branch"
QED

Resume eval_all_type_sound_mutual[Expr_TypeBuiltin]:
  cheat
QED

Theorem assign_subscripts_fixed_array_pop_type_error_probe[local]:
  !elem_tv n sparse.
    assign_subscripts (ArrayTV elem_tv (Fixed n)) (ArrayV (SArrayV sparse)) [] PopOp =
    INR (TypeError "pop_element")
Proof
  simp[Once assign_subscripts_def, pop_element_def]
QED

Resume eval_all_type_sound_mutual[Expr_Pop]:
  rpt gen_tac >> strip_tac >>
  (reverse conj_tac
   >- (gen_tac >> strip_tac >>
       gvs[Once well_typed_expr_def]) >>
   strip_tac >>
   drule well_typed_expr_Pop_dynamic_target_assignable >> strip_tac >>
      qpat_x_assum `eval_expr cx (Pop v11 bt) st = (res,st')` mp_tac >>
      simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
      Cases_on `eval_base_target cx bt st` >>
      rename1 `eval_base_target cx bt st = (bt_res, st1)` >>
      first_x_assum drule_all >> strip_tac >>
      Cases_on `bt_res`
      >- (gvs[no_type_error_result_def] >>
          PairCases_on `x` >>
          gvs[] >>
          strip_tac >>
          qpat_x_assum `do _ od st1 = (res,st')` mp_tac >>
          simp[bind_apply, bind_def, return_def, ignore_bind_apply] >>
          Cases_on `assign_target cx (BaseTargetV x0 x1) PopOp st1` >>
          rename1 `assign_target cx (BaseTargetV loc sbs) PopOp st1 = (assign_res, st2)` >>
          `runtime_consistent env cx st1` by simp[runtime_consistent_def] >>
          `target_runtime_typed env cx st1 (BaseTarget bt)
             (ArrayT v11 (Dynamic n)) (BaseTargetV loc sbs)` by (
            simp[target_runtime_typed_def, target_value_shape_def,
                 well_typed_atarget_def, well_typed_target_def] >>
            qexists_tac `loc_vt` >> simp[]) >>
          `?elem_tv. evaluate_type env.type_defs v11 = SOME elem_tv` by (
            `?vt final_tv.
               location_runtime_typed env cx st1 loc vt /\
               target_path_type env vt sbs (Type (ArrayT v11 (Dynamic n))) /\
               place_leaf_typed env vt sbs (ArrayT v11 (Dynamic n)) final_tv` by
              metis_tac[target_runtime_typed_place_leaf_typed] >>
            `evaluate_type env.type_defs (ArrayT v11 (Dynamic n)) = SOME final_tv` by
              metis_tac[place_leaf_typed_evaluate_type] >>
            Cases_on `evaluate_type env.type_defs v11` >> gvs[evaluate_type_def]) >>
          `assign_operation_runtime_typed env (ArrayT v11 (Dynamic n)) PopOp` by
            metis_tac[stmt_assign_operation_runtime_typed_Pop_from_dynamic_array] >>
          `assign_operation_matches_target_shape (BaseTargetV loc sbs) PopOp` by
            simp[assign_operation_matches_target_shape_def] >>
          `assign_target_assignable_context cx (BaseTargetV loc sbs) st1` by
            metis_tac[target_runtime_typed_imp_assignable_context] >>
          Cases_on `assign_res` >> simp[return_def, raise_def, lift_option_type_def]
          >- suspend "Expr_Pop_assign_inl" >>
          suspend "Expr_Pop_assign_inr") >>
      strip_tac >> gvs[no_type_error_result_def])
QED

Resume eval_all_type_sound_mutual[Expr_Pop_assign_inl]:
  `runtime_consistent env cx st2` by (
    drule_at(Pat`assign_target`) assign_target_preserves_runtime_consistent >>
    disch_then $ drule_at(Pat`target_runtime_typed`) >>
    simp[]) >>
  `?v. x = SOME v /\ value_has_type elem_tv v` by
    metis_tac[assign_target_pop_success_some_typed] >>
  strip_tac >> gvs[return_def, expr_result_typed_def, expr_runtime_typed_def,
                   toplevel_value_typed_def, runtime_consistent_def, expr_type_def]
QED

Resume eval_all_type_sound_mutual[Expr_Pop_assign_inr]:
  strip_tac >> gvs[] >>
  `runtime_consistent env cx st'` by
    metis_tac[assign_target_preserves_runtime_consistent_result] >>
  gvs[runtime_consistent_def] >>
  qspecl_then [`cx`, `BaseTargetV loc sbs`, `PopOp`, `st1`,
               `INR y`, `st'`, `env`, `BaseTarget bt`,
               `ArrayT v11 (Dynamic n)`] mp_tac assign_target_no_type_error >>
  simp[no_type_error_result_def] >>
  impl_tac >- simp[runtime_consistent_def] >>
  simp[]
QED

Resume eval_all_type_sound_mutual[Expr_Call_IntCall]:
  cheat
QED

Resume eval_all_type_sound_mutual[Expr_Call_ExtCall]:
  cheat
QED

Resume eval_all_type_sound_mutual[Expr_Call_Send]:
  cheat
QED

Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]:
  cheat
QED

Resume eval_all_type_sound_mutual[Expr_Call_RawLog]:
  cheat
QED

Resume eval_all_type_sound_mutual[Expr_Call_RawRevert]:
  cheat
QED

Resume eval_all_type_sound_mutual[Expr_Call_SelfDestructTarget]:
  cheat
QED

Resume eval_all_type_sound_mutual[Expr_Call_CreateTarget]:
  cheat
QED

Resume eval_all_type_sound_mutual[Exprs_nil]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_exprs _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, return_def] >>
  strip_tac >>
  gvs[no_type_error_result_def, exprs_runtime_typed_def]
QED

Resume eval_all_type_sound_mutual[Exprs_cons]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `well_typed_exprs env (e::es)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_exprs _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (r1,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `r1` >> gvs[no_type_error_result_def]
  >- (
    Cases_on `materialise cx x st1` >>
    rename1 `materialise cx x st1 = (mr,stm)` >>
    Cases_on `mr` >> gvs[no_type_error_result_def]
    >- (
      `stm = st1` by metis_tac[materialise_state] >> gvs[] >>
      Cases_on `eval_exprs cx es st1` >>
      rename1 `eval_exprs cx es st1 = (r2,st2)` >>
      first_x_assum drule_all >> strip_tac >>
      Cases_on `r2` >> gvs[no_type_error_result_def]
      >- (
        strip_tac >> gvs[exprs_runtime_typed_def, expr_result_typed_def,
          expr_runtime_typed_def] >>
        drule_at(Pat`materialise`) materialise_preserves_value_type >>
        simp[] >> strip_tac >>
        qexists_tac `tv::tvs` >> simp[] >>
        metis_tac[evaluate_type_well_formed_type_value]) >>
      strip_tac >> gvs[]) >>
    strip_tac >> gvs[] >>
    `st' = st1` by metis_tac[materialise_state] >> gvs[] >>
    metis_tac[expr_result_typed_materialise_no_type_error]) >>
  strip_tac >> gvs[]
QED

Finalise eval_all_type_sound_mutual

Theorem eval_stmt_no_type_error:
  type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx ==>
  no_type_error_eval (eval_stmt cx s st)
Proof
  strip_tac >>
  Cases_on `eval_stmt cx s st` >>
  simp[no_type_error_eval_def] >>
  drule_all (cj 1 eval_all_type_sound_mutual) >> rw[]
QED

Theorem eval_stmt_type_preservation_success:
  type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_stmt cx s st = (INL u, st') ==>
  state_well_typed st' /\ env_consistent env' cx st' /\ accounts_well_typed st'.accounts
Proof
  strip_tac >>
  drule_all (cj 1 eval_all_type_sound_mutual) >>
  simp[]
QED

Theorem eval_stmt_type_preservation_exception:
  type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_stmt cx s st = (INR exn, st') ==>
  state_well_typed st' /\ stmt_error_ok env ret_ty (INR exn) /\ accounts_well_typed st'.accounts
Proof
  rpt strip_tac >>
  drule_all (cj 1 eval_all_type_sound_mutual) >>
  simp[stmt_error_ok_def] >>
  simp[no_type_error_result_def]
QED

Theorem eval_stmt_type_preservation_exception_state:
  type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_stmt cx s st = (INR exn, st') ==>
  state_well_typed st'
Proof
  metis_tac[eval_stmt_type_preservation_exception]
QED

Theorem eval_stmt_type_preservation_exception_ok:
  type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_stmt cx s st = (INR exn, st') ==>
  stmt_error_ok env ret_ty (INR exn)
Proof
  metis_tac[eval_stmt_type_preservation_exception]
QED

Theorem stmt_error_ok_type_defs_eq:
  env1.type_defs = env2.type_defs ==>
  (stmt_error_ok env1 ret_ty r <=> stmt_error_ok env2 ret_ty r)
Proof
  Cases_on `r` >> simp[stmt_error_ok_def, return_exception_typed_def] >>
  Cases_on `y` >> simp[value_runtime_typed_def]
QED

Theorem type_stmt_preserves_stmt_error_ok:
  type_stmt env ret_ty s = SOME env1 /\ stmt_error_ok env1 ret_ty r ==>
  stmt_error_ok env ret_ty r
Proof
  strip_tac >>
  drule type_stmt_env_preserved_static >> strip_tac >>
  fs[stmt_error_ok_def, return_exception_typed_def, value_runtime_typed_def]
QED

Theorem eval_stmt_type_preservation_exception_state_pair:
  type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_stmt cx s st = (INR exn, st') ==>
  state_well_typed st' /\ stmt_error_ok env ret_ty (INR exn)
Proof
  metis_tac[eval_stmt_type_preservation_exception]
QED

Theorem eval_stmts_no_type_error:
  type_stmts env ret_ty ss = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx ==>
  no_type_error_eval (eval_stmts cx ss st)
Proof
  MAP_EVERY qid_spec_tac [`env'`, `st`, `env`, `ss`] >>
  Induct >>
  rw[Once evaluate_def, no_type_error_eval_def, no_type_error_result_def, return_def] >>
  (* cons case *)
  gvs[type_stmt_def, AllCaseEqs(), Once evaluate_def, bind_def, ignore_bind_def] >>
  Cases_on `eval_stmt cx h st` >> gvs[no_type_error_eval_def, no_type_error_result_def] >>
  Cases_on `q` >> gvs[no_type_error_eval_def, no_type_error_result_def]
  >- (
    drule_all eval_stmt_type_preservation_success >> strip_tac >>
    first_x_assum drule_all >> rw[no_type_error_eval_def, no_type_error_result_def]) >>
  drule_all eval_stmt_no_type_error >>
  gvs[no_type_error_eval_def, no_type_error_result_def]
QED

Theorem eval_stmts_type_preservation_success:
  type_stmts env ret_ty ss = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_stmts cx ss st = (INL u, st') ==>
  state_well_typed st' /\ env_consistent env' cx st' /\ accounts_well_typed st'.accounts
Proof
  MAP_EVERY qid_spec_tac [`env'`, `st'`, `u`, `st`, `env`, `ss`] >>
  Induct
  >- simp[Once evaluate_def, return_def, type_stmt_def] >>
  rpt gen_tac >> strip_tac >>
  (* cons case *)
  gvs[type_stmt_def, AllCaseEqs(), Once evaluate_def, bind_def, ignore_bind_def] >>
  Cases_on `eval_stmt cx h st` >> gvs[] >>
  drule_all eval_stmt_type_preservation_success >> strip_tac >>
  first_x_assum drule_all >> rw[]
QED

Theorem eval_stmts_type_preservation_exception:
  type_stmts env ret_ty ss = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
  eval_stmts cx ss st = (INR exn, st') ==>
  state_well_typed st' /\ stmt_error_ok env ret_ty (INR exn)
Proof
  MAP_EVERY qid_spec_tac [`env'`, `st'`, `exn`, `st`, `env`, `ss`] >>
  Induct >> simp[Once evaluate_def, return_def] >>
  simp[type_stmt_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >>
  reverse(gvs[bind_def, ignore_bind_def, AllCaseEqs()]) >- (
    drule_all eval_stmt_type_preservation_exception >> rw[] ) >>
  drule_all eval_stmt_type_preservation_success >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  gvs[] >>
  drule_all type_stmt_preserves_stmt_error_ok >>
  rw[]
QED

(* ===== Top-level theorem shape ===== *)

Theorem function_body_type_sound:
  functions_well_typed cx /\ context_well_typed cx /\ accounts_well_typed st.accounts /\
  state_well_typed st /\ env_consistent env cx st /\
  type_stmts env ret_ty body_stmts = SOME env_after ==>
  no_type_error_eval (eval_stmts cx body_stmts st)
Proof
  metis_tac[eval_stmts_no_type_error]
QED

