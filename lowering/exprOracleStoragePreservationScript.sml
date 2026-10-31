(* Restricted expression projection of evaluator storage preservation. *)
Theory exprOracleStoragePreservation
Ancestors
  exprOracleStorageInterfaces vyperOracleCallStorage
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph
  vyperTypeExprSoundness vyperTypeCallStackSoundness vyperTypeStoragePreservation
  vyperTypeEvalStoragePreservation vyperStorageLayoutSafety
  vyperEvalOutcomeSuffix vyperCallOutcomeStorage supportedExprTraverse
  vyperPlaceStoragePreservation vyperStoragePlaceProvenance vyperPlaceTyping
  vyperPlaceFrames vyperStatePreservation
  vyperTypeExprResult vyperValue vyperTypeEnv
  vyperTypeInvariants vyperTypeAssignContext vyperTypeBuiltins
  vyperTypeEvalSoundness vyperTypeValues
Libs monadsyntax

Theorem eval_expr_oracle_storage_mutual:
  (!cx s. eval_stmt cx s = eval_stmt cx s) /\
  (!cx ss. eval_stmts cx ss = eval_stmts cx ss) /\
  (!cx it. eval_iterator cx it = eval_iterator cx it) /\
  (!cx tyv id body vs. eval_for cx tyv id body vs = eval_for cx tyv id body vs) /\
  (!cx e. !env st res st'.
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\ int_calls_expr e = [] /\
    ~supported_expr_exists expr_evm_run_root e /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_expr cx e st = (res,st') ==>
    (well_typed_expr env e ==> contract_storage_well_formed cx st') /\
    (!vt. type_place_expr env e = SOME vt ==> contract_storage_well_formed cx st')) /\
  (!cx es. !env st res st'.
    well_typed_exprs env es /\ runtime_storage_consistent env cx st /\
    functions_well_typed cx /\ call_evaluation_safe cx (int_calls_exprs es) /\
    int_calls_exprs es = [] /\ ~supported_exprs_exists expr_evm_run_root es /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_exprs cx es st = (res,st') ==> contract_storage_well_formed cx st') /\
  (!cx bt. !env vt st res st'.
    type_place_target env bt = SOME vt /\ runtime_storage_consistent env cx st /\
    functions_well_typed cx /\ call_evaluation_safe cx (int_calls_target bt) /\
    int_calls_target bt = [] /\ ~supported_target_exists expr_evm_run_root bt /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_base_place cx bt st = (res,st') ==> contract_storage_well_formed cx st') /\
  (!cx tgt. !env ty st res st'.
    well_typed_target env tgt ty /\ runtime_storage_consistent env cx st /\
    functions_well_typed cx /\ call_evaluation_safe cx (int_calls_target tgt) /\
    int_calls_target tgt = [] /\ ~supported_target_exists expr_evm_run_root tgt /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_target_place cx tgt st = (res,st') ==> contract_storage_well_formed cx st') /\
  (!cx tgt v. assign_tuple_targets cx tgt v = assign_tuple_targets cx tgt v) /\
  (!cx tgts vs. assign_tuple_target_list cx tgts vs = assign_tuple_target_list cx tgts vs) /\
  (!cx es. !env st res st'.
    well_typed_exprs env es /\ runtime_storage_consistent env cx st /\
    functions_well_typed cx /\ call_evaluation_safe cx (int_calls_exprs es) /\
    int_calls_exprs es = [] /\ ~supported_exprs_exists expr_evm_run_root es /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_expr_results cx es st = (res,st') ==> contract_storage_well_formed cx st')
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> simp[] >>
  rpt gen_tac >> strip_tac >>
  (fn g as (asms,w) =>
    let
      fun head t = #Name (dest_thy_const (fst (strip_comb t)))
      val body = snd (strip_forall w)
      val premises = if is_imp body then strip_conj (fst (dest_imp body)) else asms
      fun evaluator t = is_eq t andalso
        List.exists (fn n => head (lhs t) = n)
          ["eval_expr", "eval_exprs", "eval_expr_results",
           "eval_base_place", "eval_target_place"]
      val call = lhs (valOf (List.find evaluator premises))
      val (h,args) = strip_comb call
      val arg = List.nth (args,1)
      val name = head h
      val label =
        if name = "eval_expr" then
          if head arg = "Call" then
            "Expr_Call_" ^ head (List.nth (snd (strip_comb arg),1))
          else "Expr_" ^ head arg
        else if name = "eval_base_place" then "Base_" ^ head arg
        else if name = "eval_target_place" then "Target"
        else (if name = "eval_exprs" then "Exprs_" else "Results_") ^
          (if listSyntax.is_nil arg then "nil" else "cons")
    in suspend label g end)
QED

Resume eval_expr_oracle_storage_mutual[Target]:
  rpt strip_tac >>
  gvs[well_typed_target_def, int_calls_expr_def, supported_expr_exists_def] >>
  qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  imp_res_tac get_place_state >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Resume eval_expr_oracle_storage_mutual[Expr_Call_IntCall]:
  rpt strip_tac >> gvs[int_calls_expr_def]
QED

Resume eval_expr_oracle_storage_mutual[Expr_Call_RawCallTarget]:
  rpt strip_tac >> gvs[supported_expr_exists_def, expr_evm_run_root_def]
QED

Resume eval_expr_oracle_storage_mutual[Expr_Call_RawCallCalldataTarget]:
  rpt strip_tac >> gvs[supported_expr_exists_def, expr_evm_run_root_def]
QED

Resume eval_expr_oracle_storage_mutual[Expr_Call_CreateTarget]:
  rpt strip_tac >> gvs[supported_expr_exists_def, expr_evm_run_root_def]
QED

Resume eval_expr_oracle_storage_mutual[Exprs_nil]:
  gvs[Once evaluate_def, return_def, runtime_storage_consistent_def]
QED

Resume eval_expr_oracle_storage_mutual[Results_nil]:
  gvs[Once evaluate_def, return_def, runtime_storage_consistent_def]
QED

Resume eval_expr_oracle_storage_mutual[Base_NameTarget]:
  rpt gen_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, type_check_def,
       assert_def, ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[runtime_storage_consistent_def]
QED

Resume eval_expr_oracle_storage_mutual[Base_TopLevelNameTarget]:
  rpt gen_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  pure_once_rewrite_tac [evaluate_def] >> strip_tac >>
  imp_res_tac lookup_global_state >> gvs[runtime_storage_consistent_def]
QED

Resume eval_expr_oracle_storage_mutual[Base_AttributeTarget]:
  rpt gen_tac >> strip_tac >>
  gvs[int_calls_expr_def, supported_expr_exists_def] >>
  qpat_x_assum `type_place_target _ (AttributeTarget _ _) = _` mp_tac >>
  simp[type_place_target_AttributeTarget] >> strip_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  imp_res_tac extend_place_state >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Resume eval_expr_oracle_storage_mutual[Base_SubscriptTarget]:
  rpt gen_tac >> strip_tac >>
  gvs[int_calls_expr_def, supported_expr_exists_def] >>
  qpat_x_assum `type_place_target _ (SubscriptTarget _ _) = _` mp_tac >>
  rewrite_tac[type_place_target_SubscriptTarget] >> strip_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_base_place cx bt st` >>
  rename1 `eval_base_place cx bt st = (bt_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  `runtime_consistent env cx st` by
    metis_tac[runtime_storage_consistent_runtime] >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_base_place_preserves_runtime_consistent] >>
  `runtime_storage_consistent env cx st1` by
    metis_tac[runtime_storage_consistent_intro, runtime_storage_consistent_layout] >>
  `IS_SOME st1.outcomes /\ oracle_storage_ok cx st1` by
    (irule oracle_storage_entry_suffix >> qexists_tac `st` >> simp[] >>
     drule (cj 7 eval_outcome_suffix_mutual) >> simp[]) >>
  Cases_on `bt_res` >> gvs[return_def]
  >- (gvs[bind_def, return_def] >>
      Cases_on `eval_expr cx e st1` >>
      rename1 `eval_expr cx e st1 = (expr_res,st2)` >>
      first_x_assum drule_all >> strip_tac >>
      `contract_storage_well_formed cx st2` by metis_tac[] >>
      Cases_on `expr_res` >> gvs[bind_def, return_def]
      >- (qmatch_assum_rename_tac `eval_expr cx e st1 = (INL idx_value,st2)` >>
          Cases_on `read_result cx idx_value st2` >>
          rename1 `read_result cx idx_value st2 = (value_res,value_st)` >>
          imp_res_tac read_result_state >> gvs[] >>
          Cases_on `value_res` >> gvs[return_def, raise_def] >>
          rpt strip_tac >> imp_res_tac extend_place_state >> gvs[]) >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Resume eval_expr_oracle_storage_mutual[Expr_Pop]:
  rpt gen_tac >> strip_tac >>
  gvs[int_calls_expr_def, supported_expr_exists_def, expr_evm_run_root_def] >>
  rename1 `eval_expr cx (Pop ty bt) st = (res,st')` >>
  conj_tac
  >- (strip_tac >>
      drule well_typed_expr_Pop_dynamic_target >> strip_tac >>
      `well_typed_target env bt (ArrayT ty (Dynamic n))` by
        simp[well_typed_target_def] >>
      `runtime_consistent env cx st` by
        metis_tac[runtime_storage_consistent_runtime] >>
      qpat_x_assum `eval_expr cx (Pop _ bt) st = _` mp_tac >>
      simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
      Cases_on `eval_target_place cx bt st` >>
      rename1 `eval_target_place cx bt st = (target_res,st1)` >>
      first_x_assum drule_all >> strip_tac >>
      Cases_on `target_res` >> gvs[bind_def] >> strip_tac >> gvs[] >>
      `call_evaluation_safe cx (int_calls_target bt)` by simp[] >>
      drule_all eval_target_place_success_storage_type >> strip_tac >>
      drule eval_target_place_region >> strip_tac >>
      gvs[eval_result_typed_def, evaluate_type_def, AllCaseEqs()] >>
      `storage_layout_safe cx` by
        metis_tac[runtime_storage_consistent_layout] >>
      drule_all pop_place_preserves_contract_storage >> simp[]) >>
  rpt gen_tac >> strip_tac >> gvs[Once well_typed_expr_def]
QED

Resume eval_expr_oracle_storage_mutual[Results_cons]:
  rpt gen_tac >> strip_tac >>
  gvs[int_calls_expr_def, supported_expr_exists_def] >>
  qpat_x_assum `well_typed_exprs env (e::es)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr_results _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (head_res,head_st)` >>
  first_x_assum drule_all >> strip_tac >>
  `contract_storage_well_formed cx head_st` by metis_tac[] >>
  `call_evaluation_safe cx (int_calls_expr e)` by simp[] >>
  `runtime_consistent env cx head_st` by
    metis_tac[eval_expr_preserves_runtime_consistent, runtime_storage_consistent_runtime] >>
  `runtime_storage_consistent env cx head_st` by
    metis_tac[runtime_storage_consistent_intro, runtime_storage_consistent_layout] >>
  `IS_SOME head_st.outcomes /\ oracle_storage_ok cx head_st` by
    (irule oracle_storage_entry_suffix >> qexists_tac `st` >> simp[] >>
     drule (cj 5 eval_outcome_suffix_mutual) >> simp[]) >>
  Cases_on `head_res` >> gvs[] >> rpt strip_tac >> gvs[] >>
  Cases_on `eval_expr_results cx es head_st` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `q` >> gvs[bind_def] >> rpt strip_tac >> gvs[]
QED

Resume eval_expr_oracle_storage_mutual[Exprs_cons]:
  rpt gen_tac >> strip_tac >>
  gvs[int_calls_expr_def, supported_expr_exists_def] >>
  qpat_x_assum `well_typed_exprs env (e::es)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_exprs _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (head_res,head_st)` >>
  first_x_assum drule_all >> strip_tac >>
  `contract_storage_well_formed cx head_st` by metis_tac[] >>
  `call_evaluation_safe cx (int_calls_expr e)` by simp[] >>
  `runtime_consistent env cx head_st` by
    metis_tac[eval_expr_preserves_runtime_consistent, runtime_storage_consistent_runtime] >>
  `runtime_storage_consistent env cx head_st` by
    metis_tac[runtime_storage_consistent_intro, runtime_storage_consistent_layout] >>
  `IS_SOME head_st.outcomes /\ oracle_storage_ok cx head_st` by
    (irule oracle_storage_entry_suffix >> qexists_tac `st` >> simp[] >>
     drule (cj 5 eval_outcome_suffix_mutual) >> simp[]) >>
  Cases_on `head_res` >> gvs[]
  >- (Cases_on `read_result cx x head_st` >>
      rename1 `read_result cx x head_st = (read_res,read_st)` >>
      `read_st = head_st` by metis_tac[read_result_state] >> gvs[] >>
      Cases_on `read_res` >> gvs[]
      >- (Cases_on `eval_exprs cx es head_st` >>
          first_x_assum drule_all >> strip_tac >>
          Cases_on `q` >> gvs[bind_def] >> rpt strip_tac >> gvs[]) >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Resume eval_expr_oracle_storage_mutual[Expr_Name]:
  rpt gen_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, get_scopes_def, type_check_def, assert_def, ignore_bind_def,
       bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[runtime_storage_consistent_def]
QED

Resume eval_expr_oracle_storage_mutual[Expr_TopLevelName]:
  rpt gen_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >>
  imp_res_tac lookup_global_state >> gvs[runtime_storage_consistent_def]
QED

Resume eval_expr_oracle_storage_mutual[Expr_FlagMember]:
  rpt gen_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >>
  imp_res_tac lookup_flag_mem_state >>
  gvs[runtime_storage_consistent_def] >> rpt strip_tac >> gvs[]
QED

Resume eval_expr_oracle_storage_mutual[Expr_Literal]:
  rpt gen_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, return_def] >>
  strip_tac >> gvs[runtime_storage_consistent_def]
QED

Resume eval_expr_oracle_storage_mutual[Expr_Attribute]:
  rpt gen_tac >> strip_tac >>
  gvs[int_calls_expr_def, supported_expr_exists_def, expr_evm_run_root_def] >>
  qpat_x_assum `eval_expr _ (Attribute _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (base_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `base_res` >> gvs[bind_def, return_def, raise_def] >>
  rpt strip_tac >>
  imp_res_tac select_result_state >> gvs[] >>
  gvs[Once well_typed_expr_def, AllCaseEqs()] >> metis_tac[]
QED

Resume eval_expr_oracle_storage_mutual[Expr_Builtin]:
  rpt gen_tac >> strip_tac >>
  gvs[int_calls_expr_def, supported_expr_exists_def, expr_evm_run_root_def] >>
  reverse conj_tac
  >- (rpt strip_tac >> gvs[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr env (Builtin ty bt es)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  `builtin_args_length_ok bt (LENGTH es)` by
    (drule well_typed_builtin_app_length >> simp[]) >>
  qpat_x_assum `eval_expr cx (Builtin ty bt es) st = (res,st')` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def,
    type_check_def, assert_def] >>
  Cases_on `bt = Len`
  >- (
    `es <> []` by (
      Cases_on `es` >> simp[] >>
      qpat_x_assum `well_typed_builtin_app ty bt (MAP expr_type [])` mp_tac >>
      gvs[well_typed_builtin_app_def]) >>
    `well_typed_expr env (HD es)` by
      (Cases_on `es` >> gvs[well_typed_expr_def]) >>
    `int_calls_expr (HD es) = [] /\
     ~supported_expr_exists expr_evm_run_root (HD es)` by
      (Cases_on `es` >> gvs[int_calls_expr_def, supported_expr_exists_def]) >>
    qpat_assum `builtin_args_length_ok bt (LENGTH es)` (fn th => rewrite_tac[th]) >>
    qpat_assum `bt = Len` (fn th => rewrite_tac[th]) >>
    simp_tac(srw_ss())[bind_def, ignore_bind_def, return_def, raise_def,
      type_check_def, assert_def] >>
    Cases_on `eval_expr cx (HD es) st` >>
    rename1 `eval_expr cx (HD es) st = (arg_res,arg_st)` >>
    qpat_x_assum `!s'' t. _ /\ bt = Len ==> _`
      (qspecl_then [`st`, `st`] mp_tac) >>
    simp[type_check_def, assert_def] >> strip_tac >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `arg_res` >> gvs[bind_def, return_def, raise_def]
    >- (Cases_on `result_array_length cx x arg_st` >>
        imp_res_tac result_array_length_state >> gvs[] >>
        Cases_on `q` >> gvs[return_def, raise_def] >>
        rpt strip_tac >> gvs[]) >>
    rpt strip_tac >> gvs[]) >>
  qpat_assum `bt <> Len` (fn th => rewrite_tac[th]) >>
  qpat_assum `builtin_args_length_ok bt (LENGTH es)` (fn th => rewrite_tac[th]) >>
  simp_tac(srw_ss())[bind_def, ignore_bind_def, return_def, raise_def,
    type_check_def, assert_def, get_accounts_def, lift_sum_def] >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (args_res,args_st)` >>
  qpat_x_assum `!s'' t. _ /\ bt <> Len ==> _`
    (qspecl_then [`st`, `st`] mp_tac) >>
  (impl_tac >- (simp[type_check_def, assert_def] >> metis_tac[])) >>
  strip_tac >> first_x_assum drule_all >> strip_tac >>
  Cases_on `args_res` >> gvs[bind_def, return_def, raise_def,
    get_accounts_def, lift_sum_def]
  >- (Cases_on `evaluate_builtin cx args_st.accounts ty bt (MAP expr_type es) x` >>
      gvs[return_def, raise_def] >> rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Resume eval_expr_oracle_storage_mutual[Expr_Call_RawLog]:
  rpt gen_tac >> strip_tac >>
  gvs[int_calls_expr_def, supported_expr_exists_def, expr_evm_run_root_def] >>
  conj_tac
  >- (strip_tac >>
      qpat_x_assum `well_typed_expr env (Call ty RawLog es extra)` mp_tac >>
      rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
        type_check_def, assert_def, return_def, raise_def, push_log_def] >>
      Cases_on `eval_exprs cx es st` >>
      rename1 `eval_exprs cx es st = (args_res,args_st)` >>
      first_x_assum drule_all >> strip_tac >>
      Cases_on `args_res` >> gvs[bind_def, ignore_bind_def, type_check_def,
        assert_def, return_def, raise_def, push_log_def]
      >- (strip_tac >> gvs[AllCaseEqs()] >>
          imp_res_tac lift_option_type_state >> gvs[] >>
          metis_tac[contract_storage_well_formed_logs]) >>
      rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >> gvs[Once well_typed_expr_def]
QED

Resume eval_expr_oracle_storage_mutual[Expr_Call_RawRevert]:
  rpt gen_tac >> strip_tac >>
  gvs[int_calls_expr_def, supported_expr_exists_def, expr_evm_run_root_def] >>
  conj_tac
  >- (strip_tac >>
      qpat_x_assum `well_typed_expr env (Call ty RawRevert es extra)` mp_tac >>
      rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
        type_check_def, assert_def, return_def, raise_def] >>
      Cases_on `eval_exprs cx es st` >>
      rename1 `eval_exprs cx es st = (args_res,args_st)` >>
      first_x_assum drule_all >> strip_tac >>
      Cases_on `args_res` >> gvs[bind_def, ignore_bind_def, type_check_def,
        assert_def, return_def, raise_def]
      >- (Cases_on `LENGTH x = 1` >> gvs[] >> rpt strip_tac >> gvs[]) >>
      rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >> gvs[Once well_typed_expr_def]
QED

Resume eval_expr_oracle_storage_mutual[Expr_Call_SelfDestructTarget]:
  rpt gen_tac >> strip_tac >>
  gvs[int_calls_expr_def, supported_expr_exists_def, expr_evm_run_root_def] >>
  conj_tac
  >- (strip_tac >>
      qpat_x_assum `well_typed_expr env (Call _ SelfDestructTarget _ _)` mp_tac >>
      rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
        type_check_def, assert_def, return_def, raise_def,
        lift_option_type_def, get_accounts_def] >> simp[] >>
      Cases_on `eval_exprs cx es st` >>
      rename1 `eval_exprs cx es st = (args_res,args_st)` >>
      first_x_assum drule_all >> strip_tac >>
      Cases_on `args_res` >> gvs[]
      >- (Cases_on `LENGTH x = 1` >>
          gvs[type_check_def, assert_def, return_def, raise_def]
          >- (Cases_on `dest_AddressV (HD x)` >> gvs[return_def, raise_def]
              >- (rpt strip_tac >> gvs[]) >>
              Cases_on `transfer_value cx.txn.target x'
                (lookup_account cx.txn.target args_st.accounts).balance args_st` >>
              rename1 `transfer_value _ _ _ args_st = (transfer_res,transfer_st)` >>
              drule_all transfer_value_preserves_contract_storage_well_formed >>
              Cases_on `transfer_res` >>
              gvs[bind_apply, ignore_bind_apply, return_def, raise_def] >>
              rpt strip_tac >> gvs[]) >>
          rpt strip_tac >> gvs[]) >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[Once well_typed_expr_def]
QED

Resume eval_expr_oracle_storage_mutual[Expr_Subscript]:
  rpt gen_tac >> strip_tac >>
  gvs[int_calls_expr_def, supported_expr_exists_def, expr_evm_run_root_def] >>
  conj_tac >> rpt strip_tac >> (
  `well_typed_expr env e' /\
   (well_typed_expr env e \/ ?base_vt. type_place_expr env e = SOME base_vt)` by
    (gvs[Once well_typed_expr_def, AllCaseEqs()] >> metis_tac[]) >> (
  qpat_x_assum `eval_expr cx (Subscript _ e e') st = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (base_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  `contract_storage_well_formed cx st1` by metis_tac[] >>
  `runtime_consistent env cx st` by
    metis_tac[runtime_storage_consistent_runtime] >>
  `call_evaluation_safe cx (int_calls_expr e)` by simp[] >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_expr_preserves_runtime_consistent,
              eval_expr_place_preserves_runtime_consistent] >>
  `runtime_storage_consistent env cx st1` by
    metis_tac[runtime_storage_consistent_intro, runtime_storage_consistent_layout] >>
  `IS_SOME st1.outcomes /\ oracle_storage_ok cx st1` by
    (irule oracle_storage_entry_suffix >> qexists_tac `st` >> simp[] >>
     drule (cj 5 eval_outcome_suffix_mutual) >> simp[]) >>
  Cases_on `base_res` >> gvs[return_def, raise_def]
  >- (Cases_on `eval_expr cx e' st1` >>
      rename1 `eval_expr cx e' st1 = (index_res,st2)` >>
      first_x_assum drule_all >> strip_tac >>
      `contract_storage_well_formed cx st2` by metis_tac[] >>
      Cases_on `index_res` >> gvs[return_def, raise_def]
      >- (rename1 `eval_expr cx e' st1 = (INL index_tv,st2)` >>
          Cases_on `read_result cx index_tv st2` >>
          rename1 `read_result cx index_tv st2 = (value_res,st3)` >>
          `st3 = st2` by metis_tac[read_result_state] >> gvs[] >>
          Cases_on `value_res` >> gvs[return_def, raise_def] >>
          rpt strip_tac >> imp_res_tac select_result_state >> gvs[]) >>
      strip_tac >> gvs[]) >>
  strip_tac >> gvs[]))
QED

Resume eval_expr_oracle_storage_mutual[Expr_Call_Send]:
  rpt gen_tac >> strip_tac >>
  gvs[int_calls_expr_def, supported_expr_exists_def, expr_evm_run_root_def] >>
  conj_tac
  >- (strip_tac >>
      qpat_x_assum `well_typed_expr env (Call _ (Send _) _ _)` mp_tac >>
      rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
      `LENGTH es = if has_gas then 3 else 2` by
        (qpat_x_assum `MAP expr_type es = _` (mp_tac o Q.AP_TERM `LENGTH`) >> rw[]) >>
      qpat_x_assum `!s'' t. type_check _ _ s'' = (INL (),t) ==> _`
        (qspecl_then [`st`, `st`] mp_tac) >>
      (impl_tac >- simp[type_check_def, assert_def]) >> strip_tac >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
           assert_def, return_def] >>
      Cases_on `eval_exprs cx es st` >>
      rename1 `eval_exprs cx es st = (args_res,args_st)` >>
      first_x_assum drule_all >> strip_tac >>
      `IS_SOME args_st.outcomes /\ oracle_storage_ok cx args_st` by
        (irule oracle_storage_entry_suffix >> qexists_tac `st` >> simp[] >>
         drule (cj 6 eval_outcome_suffix_mutual) >> simp[]) >>
      Cases_on `args_res` >> gvs[]
      >- metis_tac[eval_send_oracle_storage_preserved] >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[Once well_typed_expr_def]
QED

Resume eval_expr_oracle_storage_mutual[Expr_IfExp]:
  rpt gen_tac >> strip_tac >>
  gvs[int_calls_expr_def, supported_expr_exists_def, expr_evm_run_root_def] >>
  reverse conj_tac
  >- (rpt strip_tac >> gvs[Once well_typed_expr_def]) >>
  disch_then mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ (IfExp _ _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (cond_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by simp[] >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_expr_preserves_runtime_consistent, runtime_storage_consistent_runtime] >>
  `runtime_storage_consistent env cx st1` by
    metis_tac[runtime_storage_consistent_intro, runtime_storage_consistent_layout] >>
  `IS_SOME st1.outcomes /\ oracle_storage_ok cx st1` by
    (irule oracle_storage_entry_suffix >> qexists_tac `st` >> simp[] >>
     drule (cj 5 eval_outcome_suffix_mutual) >> simp[]) >>
  Cases_on `cond_res`
  >- (rename1 `eval_expr cx e st = (INL tv,st1)` >>
      `runtime_consistent env cx st` by metis_tac[runtime_storage_consistent_runtime] >>
      drule_all eval_expr_success_storage_facts >> strip_tac >>
      Cases_on `read_result cx tv st1` >>
      rename1 `read_result cx tv st1 = (rr,rs)` >>
      imp_res_tac read_result_state >> gvs[] >>
      reverse (Cases_on `rr`)
      >- (simp[switch_BoolV_def, bind_def, raise_def] >> strip_tac >> gvs[]) >>
      rename1 `read_result cx tv st1 = (INL cv,st1)` >>
      `value_runtime_typed env (expr_type e) cv` by
        (fs[runtime_consistent_def] >> drule_all read_live_result_success_type >> simp[]) >>
      gvs[value_runtime_typed_def, evaluate_type_def] >>
      drule value_has_type_BoolTV >> strip_tac >> gvs[] >>
      Cases_on `b` >> simp[switch_BoolV_def, bind_def] >> (
      first_x_assum drule >> strip_tac >>
      rename1 `eval_expr cx selected st1` >>
      Cases_on `eval_expr cx selected st1` >>
      rename1 `eval_expr cx selected st1 = (selected_res,st2)` >>
      first_x_assum drule_all >> strip_tac >>
      Cases_on `selected_res` >> gvs[bind_def, return_def, raise_def] >>
      rpt strip_tac >> imp_res_tac conditional_result_state >> gvs[])) >>
  rpt strip_tac >> gvs[]
QED

Resume eval_expr_oracle_storage_mutual[Expr_StructLit]:
  rpt gen_tac >> strip_tac >>
  gvs[int_calls_expr_def, supported_expr_exists_def, expr_evm_run_root_def] >>
  `int_calls_exprs (MAP SND kes) = [] /\
   ~supported_exprs_exists expr_evm_run_root (MAP SND kes)` by
    gvs[int_calls_exprs_empty_every, int_calls_named_exprs_empty_every,
        supported_exprs_exists_not_every, supported_fields_exists_not_every] >>
  reverse conj_tac
  >- (rpt strip_tac >> gvs[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr _ (StructLit _ _ _)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  `well_typed_exprs env (MAP SND kes)` by
    (irule well_typed_named_exprs_MAP_SND_stmt >> simp[]) >>
  qpat_x_assum `eval_expr _ (StructLit _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_exprs cx (MAP SND kes) st` >>
  rename1 `eval_exprs cx (MAP SND kes) st = (exprs_res,st1)` >>
  `call_evaluation_safe cx (int_calls_exprs (MAP SND kes))` by simp[] >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `exprs_res` >> gvs[LET_THM, bind_def, return_def] >>
  rpt strip_tac >> gvs[]
QED

Resume eval_expr_oracle_storage_mutual[Expr_TypeBuiltin]:
  rpt gen_tac >> strip_tac >>
  gvs[int_calls_expr_def, supported_expr_exists_def, expr_evm_run_root_def] >>
  reverse conj_tac
  >- (rpt strip_tac >> gvs[Once well_typed_expr_def]) >>
  strip_tac >>
  `well_typed_exprs env es` by
    (qpat_assum `well_typed_expr env (TypeBuiltin _ _ _ es)` mp_tac >>
     simp_tac(srw_ss())[Once well_typed_expr_def]) >>
  `type_builtin_args_length_ok tb (LENGTH es)` by
    (qpat_assum `well_typed_expr env (TypeBuiltin _ tb _ es)` mp_tac >>
     CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [well_typed_expr_def])) >>
     strip_tac >> drule well_typed_type_builtin_args_length >> simp[]) >>
  qpat_x_assum `eval_expr _ (TypeBuiltin _ _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
    return_def, raise_def, type_check_def, assert_def] >>
  qpat_assum `type_builtin_args_length_ok tb (LENGTH es)` (fn th => rewrite_tac[th]) >>
  simp_tac(srw_ss())[bind_def, ignore_bind_def, return_def, raise_def,
    type_check_def, assert_def] >>
  qpat_x_assum `!s'' t. type_check _ _ _ = _ ==> _`
    (qspecl_then [`st`, `st`] mp_tac) >>
  (impl_tac >- simp[type_check_def, assert_def, return_def]) >> strip_tac >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (exprs_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `exprs_res` >> gvs[bind_def, return_def, raise_def]
  >- (Cases_on `lift_sum (evaluate_type_builtin cx tb typ (MAP expr_type es) x) st1` >>
      imp_res_tac lift_sum_state >> gvs[] >>
      Cases_on `q` >> gvs[return_def, raise_def] >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Resume eval_expr_oracle_storage_mutual[Expr_Call_ExtCall]:
  rpt gen_tac >> strip_tac >>
  gvs[int_calls_expr_def, supported_expr_exists_def, expr_evm_run_root_def] >>
  reverse conj_tac
  >- (rpt strip_tac >> gvs[Once well_typed_expr_def]) >>
  strip_tac >>
  `well_typed_exprs env es` by metis_tac[ext_call_args_typed] >>
  PairCases_on `sig` >>
  `well_typed_exprs env (TAKE 1 es) /\
   well_typed_exprs env (TAKE (LENGTH sig1) (DROP 1 es)) /\
   well_typed_exprs env (DROP (1 + LENGTH sig1) es)` by
    metis_tac[well_typed_exprs_TAKE, well_typed_exprs_DROP] >>
  `int_calls_exprs (TAKE 1 es) = [] /\
   int_calls_exprs (TAKE (LENGTH sig1) (DROP 1 es)) = [] /\
   int_calls_exprs (DROP (1 + LENGTH sig1) es) = [] /\
   ~supported_exprs_exists expr_evm_run_root (TAKE 1 es) /\
   ~supported_exprs_exists expr_evm_run_root (TAKE (LENGTH sig1) (DROP 1 es)) /\
   ~supported_exprs_exists expr_evm_run_root (DROP (1 + LENGTH sig1) es)` by
    (gvs[int_calls_exprs_empty_every, supported_exprs_exists_not_every] >>
     metis_tac[rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP]) >>
  `call_evaluation_safe cx (int_calls_exprs (TAKE 1 es)) /\
   call_evaluation_safe cx (int_calls_exprs (TAKE (LENGTH sig1) (DROP 1 es))) /\
   call_evaluation_safe cx (int_calls_exprs (DROP (1 + LENGTH sig1) es))` by simp[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_apply] >>
  Cases_on `eval_exprs cx (TAKE 1 es) st` >>
  rename1 `eval_exprs cx (TAKE 1 es) st = (target_res,target_st)` >>
  qpat_x_assum `!env0 st0 res0 st0'. well_typed_exprs env0 (TAKE 1 es) /\ _ ==> _`
    drule_all >> strip_tac >>
  `runtime_consistent env cx target_st` by
    metis_tac[eval_exprs_preserves_runtime_consistent, runtime_storage_consistent_runtime] >>
  `runtime_storage_consistent env cx target_st` by
    metis_tac[runtime_storage_consistent_intro, runtime_storage_consistent_layout] >>
  `IS_SOME target_st.outcomes /\ oracle_storage_ok cx target_st` by
    (irule oracle_storage_entry_suffix >> qexists_tac `st` >> simp[] >>
     drule (cj 6 eval_outcome_suffix_mutual) >> simp[]) >>
  Cases_on `target_res`
  >- (qpat_assum `eval_exprs cx (TAKE 1 es) st = _`
        (fn th => simp_tac(srw_ss())[th, LET_THM, bind_apply]) >>
      qpat_x_assum `!s target t. eval_exprs cx (TAKE 1 es) s = (INL target,t) ==> _`
        (drule o SIMP_RULE (srw_ss()) []) >> strip_tac >>
      Cases_on `eval_expr_results cx (TAKE (LENGTH sig1) (DROP 1 es)) target_st` >>
      rename1 `eval_expr_results _ _ target_st = (capture_res,capture_st)` >>
      qpat_x_assum `!env0 st0 res0 st0'. well_typed_exprs env0 (TAKE _ (DROP _ es)) /\ _ ==> _`
        drule_all >> strip_tac >>
      Cases_on `capture_res`
      >- (qpat_x_assum `!s target t s1 rs t1. _ ==> _`
            (drule o SIMP_RULE (srw_ss()) []) >> disch_then drule >> strip_tac >>
          `runtime_consistent env cx capture_st` by
            (qpat_x_assum `runtime_consistent env cx target_st` mp_tac >>
             simp[runtime_consistent_def] >> strip_tac >>
             drule_all (cj 1 (SPEC_ALL (cj 11 eval_scc_type_sound_results_mutual))) >>
             simp[runtime_consistent_def]) >>
          `runtime_storage_consistent env cx capture_st` by
            metis_tac[runtime_storage_consistent_intro, runtime_storage_consistent_layout] >>
          `IS_SOME capture_st.outcomes /\ oracle_storage_ok cx capture_st` by
            (irule oracle_storage_entry_suffix >> qexists_tac `target_st` >> simp[] >>
             drule eval_expr_results_outcome_suffix >> simp[]) >>
          qpat_assum `eval_expr_results _ _ target_st = _`
            (fn th => simp_tac(srw_ss())[th, LET_THM, bind_apply]) >>
          Cases_on `eval_exprs cx (DROP (1 + LENGTH sig1) es) capture_st` >>
          rename1 `eval_exprs _ _ capture_st = (kw_res,kw_st)` >>
          fs[arithmeticTheory.ADD_COMM] >> first_x_assum drule_all >> strip_tac >>
          `IS_SOME kw_st.outcomes /\ oracle_storage_ok cx kw_st` by
            (irule oracle_storage_entry_suffix >> qexists_tac `capture_st` >> simp[] >>
             drule (cj 6 eval_outcome_suffix_mutual) >> simp[]) >>
          rpt (qpat_x_assum `!a b c d. _` kall_tac) >>
          Cases_on `kw_res` >> gvs[]
          >- (Cases_on `read_results cx x' kw_st` >>
              drule read_results_state >> strip_tac >> gvs[] >>
              rename1 `read_results cx _ kw_st = (read_res,kw_st)` >>
              Cases_on `read_res` >> gvs[]
              >- metis_tac[eval_ext_call_oracle_storage_preserved] >>
              strip_tac >> gvs[]) >>
          strip_tac >> gvs[]) >>
      rpt (qpat_x_assum `!a b c d. _` kall_tac) >>
      gvs[LET_THM, bind_apply] >> strip_tac >> gvs[]) >>
  rpt (qpat_x_assum `!a b c d. _` kall_tac) >>
  gvs[] >> strip_tac >> gvs[]
QED

Finalise eval_expr_oracle_storage_mutual
