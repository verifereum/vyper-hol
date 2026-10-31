(* Source-derived ABI lookup validity; delayed locations require live tokens,
   not a premise asserting that a future decode succeeds. *)
Theory vyperTypeAbiLookupSoundness
Ancestors
  list option pair finite_map vyperAST vyperState vyperAbiOperand
  vyperTypeSystem vyperTypeInvariants vyperTypeEnv vyperTypeValues
  vyperTypeGlobalLookupSoundness vyperAbiExprTyping vyperAbiReadTyping
  vyperAbiStateTyping vyperPlaceTyping vyperStatePreservation vyperTypeExprSoundness

Theorem lookup_abi_immutable_expr_sound:
  well_typed_expr env (TopLevelName ty (src,id)) /\
  env_consistent env cx st /\ state_well_typed st /\
  functions_well_typed cx /\ get_module_code cx src = SOME code /\
  find_var_decl_by_name id code = NONE /\
  lookup_abi_immutable cx src id st = (res,rt) ==>
  state_well_typed rt /\ env_consistent env cx rt /\
  rt.accounts = st.accounts /\ no_type_error_result res /\
  case res of INL arg => abi_expr_result_valid env rt (TopLevelName ty (src,id)) arg
            | INR _ => T
Proof
  strip_tac >> drule_all TopLevelName_toplevel_vtypes_Type >> strip_tac >>
  qpat_x_assum `lookup_abi_immutable _ _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[lookup_abi_immutable_def, bind_def] >>
  Cases_on `get_immutables cx src st` >>
  rename1 `get_immutables cx src st = (imm_res,imm_st)` >>
  drule get_immutables_state >> strip_tac >> gvs[] >> Cases_on `imm_res`
  >- (rename1 `get_immutables cx src st = (INL imms,st)` >>
      Cases_on `FLOOKUP imms id`
      >- (`lookup_global cx src id st =
             (INR (Error (TypeError "lookup_global: var not found")),st)` by
            simp[lookup_global_def, bind_def, lift_option_type_def, raise_def, return_def] >>
          drule_all lookup_global_TopLevelName_find_NONE_no_type_error >>
          simp[no_type_error_result_def]) >>
      PairCases_on `x` >>
      `evaluate_type env.type_defs ty = SOME x0` by
        (drule get_immutables_success >> strip_tac >> gvs[] >>
         qpat_x_assum `env_consistent env cx st` mp_tac >>
         simp[env_consistent_def, env_immutables_consistent_def] >> strip_tac >>
         qpat_x_assum `!src' id ty' ts. _`
           (qspecl_then [`src`, `id`, `ty`, `code`] mp_tac) >>
         simp[] >> strip_tac >> gvs[env_context_consistent_def]) >>
      drule_all get_immutables_success_typed >> strip_tac >>
      drule_all lookup_abi_immutable_valid >> strip_tac >>
      qpat_x_assum `lookup_abi_immutable cx src id st = _`
        (assume_tac o SIMP_RULE (srw_ss()) [lookup_abi_immutable_def, bind_def]) >>
      simp[] >> strip_tac >>
      gvs[no_type_error_result_def, abi_expr_result_valid_def, expr_type_def]) >>
  rename1 `get_immutables cx src st = (INR exn,st)` >>
  `lookup_global cx src id st = (INR exn,st)` by
    simp[lookup_global_def, bind_def, lift_option_type_def, return_def] >>
  drule_all lookup_global_TopLevelName_find_NONE_no_type_error >>
  strip_tac >> rw[] >> gvs[no_type_error_result_def]
QED

Theorem lookup_abi_global_expr_sound:
  well_typed_expr env (TopLevelName ty (src,id)) /\
  env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\
  functions_well_typed cx /\ lookup_abi_global cx src id st = (res,rt) ==>
  state_well_typed rt /\ env_consistent env cx rt /\
  rt.accounts = st.accounts /\ no_type_error_result res /\
  case res of INL arg => abi_expr_result_valid env rt (TopLevelName ty (src,id)) arg
            | INR _ => T
Proof
  strip_tac >>
  `FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty)` by
    metis_tac[TopLevelName_toplevel_vtypes_Type] >>
  `?code. get_module_code cx src = SOME code` by
    (Cases_on `FLOOKUP env.bare_globals (src,id)` >>
     metis_tac[env_consistent_toplevel_storage_static, env_consistent_def,
               env_context_consistent_def]) >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  Cases_on `find_var_decl_by_name id code`
  >- (gvs[lookup_abi_global_def, bind_def, lift_option_type_def, return_def] >>
      drule_all lookup_abi_immutable_expr_sound >> simp[]) >>
  PairCases_on `x` >> Cases_on `x0` >> gvs[]
  >- (Cases_on `FLOOKUP env.bare_globals (src,id)`
      >- (drule_all TopLevelName_nonbare_storage_decl_context >> strip_tac >>
          gvs[IS_SOME_EXISTS, lookup_abi_global_def, bind_def,
              lift_option_type_def, return_def, no_type_error_result_def,
              abi_expr_result_valid_def, abi_operand_valid_def, expr_type_def] >>
          metis_tac[evaluate_type_well_formed_type_value]) >>
      metis_tac[TopLevelName_bare_storage_decl_impossible]) >>
  metis_tac[TopLevelName_Type_HashMapVarDecl_impossible]
QED

Theorem lookup_abi_global_place_sound:
  type_place_expr env (TopLevelName ann (src,id)) = SOME vt /\
  env_consistent env cx st /\ state_well_typed st /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\
  functions_well_typed cx /\ lookup_abi_global cx src id st = (res,rt) ==>
  state_well_typed rt /\ env_consistent env cx rt /\
  rt.accounts = st.accounts /\ no_type_error_result res /\
  case res of INL arg => abi_place_result_valid env rt arg vt | INR _ => T
Proof
  strip_tac >> qpat_x_assum `type_place_expr _ _ = SOME _` mp_tac >>
  simp[Once well_typed_expr_def, vtype_annotation_ok_def] >>
  Cases_on `vt` >> simp[] >> strip_tac >> gvs[AllCaseEqs()]
  >- (rename1 `FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type t)` >>
      Cases_on `FLOOKUP env.bare_globals (src,id)`
      >- (drule_all env_consistent_toplevel_storage_static >> strip_tac >>
          gvs[IS_SOME_EXISTS, lookup_abi_global_def, bind_def,
              lift_option_type_def, return_def, no_type_error_result_def,
              abi_place_result_valid_def, abi_operand_valid_def] >>
          `env.type_defs = get_tenv cx` by
            gvs[env_consistent_def, env_context_consistent_def] >>
          metis_tac[evaluate_type_well_formed_type_value]) >>
      `well_formed_type env.type_defs t` by
        metis_tac[env_consistent_def, env_context_consistent_def,
                  well_formed_vtype_def] >>
      `t <> NoneT` by
        (drule_all env_consistent_bare_global_find_NONE >> strip_tac >> gvs[]) >>
      `well_typed_expr env (TopLevelName t (src,id))` by
        simp[Once well_typed_expr_def] >>
      drule_all lookup_abi_global_expr_sound >>
      Cases_on `res` >> simp[abi_expr_result_valid_def,
        abi_place_result_valid_def, expr_type_def]) >>
  drule_all env_consistent_toplevel_hashmap_static >> strip_tac >>
  gvs[IS_SOME_EXISTS, lookup_abi_global_def, bind_def,
      lift_option_type_def, return_def, no_type_error_result_def,
      abi_place_result_valid_def] >> metis_tac[]
QED
