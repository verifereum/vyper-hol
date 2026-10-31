(* Postulate-free storage preservation for statement evaluation.
   Expressions are handled through the internal-call boundary of
   exprOracleStoragePreservation; statement writes use the semantic typed
   write interface. *)
Theory stmtOracleStoragePreservation
Ancestors
  list pair exprOracleStoragePreservation exprOracleStorageInterfaces supportedStmtTraverse supportedStmts
  supportedExprTraverse vyperAST vyperInterpreter vyperState vyperTypeSystem
  vyperTypeCallGraph vyperTypeExprSoundness vyperTypeCallStackSoundness
  vyperTypeStoragePreservation vyperTypeEvalStoragePreservation
  vyperStorageLayoutSafety vyperEvalOutcomeSuffix vyperCallOutcomeStorage
  vyperTypeInvariants vyperTypeEnv vyperTypeValues vyperTypeStmtSoundness vyperTypeArgFits
  vyperTypeEvalSoundness vyperTypeExprResult vyperTypeAssignContext
  vyperPlaceStoragePreservation vyperPlaceFrames vyperPlaceTyping
  vyperPlaceResultTyping vyperStoragePlaceProvenance vyperStatePreservation
  vyperScopePreservation vyperValue vyperTypeEnvPreservation
  vyperImmutableMetadataFrame vyperTargetPlaceWrite vyperAugAssignWriteSoundness
Libs markerLib

Theorem oracle_expr_storage:
  well_typed_expr env e /\ runtime_storage_consistent env cx st /\
  functions_well_typed cx /\ call_evaluation_safe cx (int_calls_expr e) /\
  EVERY (oracle_internal_call_storage cx) (int_calls_expr e) /\
  ~supported_expr_exists expr_evm_run_root e /\
  IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
  eval_expr cx e st = (res,rt) ==>
  runtime_storage_consistent env cx rt /\
  IS_SOME rt.outcomes /\ oracle_storage_ok cx rt
Proof
  rpt strip_tac >>
  `contract_storage_well_formed cx rt` by
    (drule_all (cj 5 eval_expr_oracle_storage_results_mutual) >> simp[]) >>
  `runtime_consistent env cx rt` by
    metis_tac[eval_expr_preserves_runtime_consistent, runtime_storage_consistent_runtime] >>
  `runtime_storage_consistent env cx rt` by
    metis_tac[runtime_storage_consistent_intro,runtime_storage_consistent_layout] >>
  drule (cj 5 eval_outcome_suffix_mutual) >>
  metis_tac[oracle_storage_entry_suffix]
QED

Theorem oracle_target_storage:
  well_typed_target env bt ty /\ runtime_storage_consistent env cx st /\
  functions_well_typed cx /\ call_evaluation_safe cx (int_calls_target bt) /\
  EVERY (oracle_internal_call_storage cx) (int_calls_target bt) /\
  ~supported_target_exists expr_evm_run_root bt /\
  IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
  eval_target_place cx bt st = (res,rt) ==>
  runtime_storage_consistent env cx rt /\
  IS_SOME rt.outcomes /\ oracle_storage_ok cx rt
Proof
  rpt strip_tac >>
  `contract_storage_well_formed cx rt` by
    (drule_all (cj 8 eval_expr_oracle_storage_results_mutual) >> simp[]) >>
  `runtime_consistent env cx rt` by
    metis_tac[eval_target_place_preserves_runtime_consistent, runtime_storage_consistent_runtime] >>
  `runtime_storage_consistent env cx rt` by
    metis_tac[runtime_storage_consistent_intro,runtime_storage_consistent_layout] >>
  drule (cj 8 eval_outcome_suffix_mutual) >>
  metis_tac[oracle_storage_entry_suffix]
QED

Theorem assign_tuple_targets_preserves_runtime_consistent[local]:
  well_typed_atarget env tgt ty /\ value_runtime_typed env ty v /\
  runtime_consistent env cx st /\ functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_atarget tgt) /\
  assign_tuple_targets cx tgt v st = (res,rt) ==>
  runtime_consistent env cx rt
Proof
  simp[runtime_consistent_def] >> metis_tac[cj 9 eval_scc_type_sound_mutual]
QED

Theorem oracle_switch_storage:
  contract_storage_well_formed cx st /\
  (!r s. yes st = (r,s) ==> contract_storage_well_formed cx s) /\
  (!r s. no st = (r,s) ==> contract_storage_well_formed cx s) /\
  switch_BoolV cx v yes no st = (res,rt) ==>
  contract_storage_well_formed cx rt
Proof
  rw[switch_BoolV_def,bind_def,AllCaseEqs()] >>
  imp_res_tac read_result_state >> gvs[raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[raise_def]) >> metis_tac[]
QED

Theorem oracle_finally_storage:
  (!r s. action st = (r,s) ==> contract_storage_well_formed cx s) /\
  (!s r t. contract_storage_well_formed cx s /\ cleanup s = (r,t) ==>
           contract_storage_well_formed cx t) /\
  finally action cleanup st = (res,rt) ==>
  contract_storage_well_formed cx rt
Proof
  rpt strip_tac >> Cases_on `action st` >> rename1 `action st = (ar,ast)` >>
  Cases_on `ar` >> Cases_on `cleanup ast` >> rename1 `cleanup ast = (cr,cst)` >>
  Cases_on `cr` >> gvs[finally_def,ignore_bind_apply,return_def,raise_def] >> metis_tac[]
QED

fun ENTRY_TAC g = (
  rpt gen_tac >> TRY strip_tac >>
  gvs[int_calls_stmt_def,int_calls_expr_def,int_calls_iterator_def,int_calls_atarget_def,
      int_calls_assert_reason_def,int_calls_raise_reason_def,
      supported_stmt_expr_exists_def,supported_expr_exists_def,
      supported_raise_exists_def,supported_assert_exists_def,
      supported_iterator_exists_def,supported_assignment_exists_def] >>
  NTAC 3 (imp_res_tac call_evaluation_safe_append_left >>
          imp_res_tac call_evaluation_safe_append_right)) g;

Theorem eval_stmts_oracle_storage_mutual:
  (!cx s. !tops bindings env ret_ty env' st res rt.
    supported_stmt tops bindings s /\ type_stmt env ret_ty s = SOME env' /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmt s) /\
    EVERY (oracle_internal_call_storage cx) (int_calls_stmt s) /\
    ~supported_stmt_expr_exists expr_evm_run_root s /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_stmt cx s st = (res,rt) ==> contract_storage_well_formed cx rt) /\
  (!cx ss. !tops bindings env ret_ty env' st res rt.
    supported_stmts tops bindings ss /\ type_stmts env ret_ty ss = SOME env' /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    EVERY (oracle_internal_call_storage cx) (int_calls_stmts ss) /\
    ~supported_stmts_expr_exists expr_evm_run_root ss /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_stmts cx ss st = (res,rt) ==> contract_storage_well_formed cx rt) /\
  (!cx it. !env ty st res rt.
    well_typed_iterator env ty it /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_iterator it) /\
    EVERY (oracle_internal_call_storage cx) (int_calls_iterator it) /\
    ~supported_iterator_exists expr_evm_run_root it /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_iterator cx it st = (res,rt) ==> contract_storage_well_formed cx rt) /\
  (!cx tyv id body vs. !tops bindings env ret_ty ty env_after st res rt.
    supported_stmts tops bindings body /\ evaluate_type env.type_defs ty = SOME tyv /\ EVERY (value_has_type tyv) vs /\
    id NOTIN FDOM env.var_types /\
    type_stmts (extend_local env id ty F) ret_ty body = SOME env_after /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmts body) /\
    EVERY (oracle_internal_call_storage cx) (int_calls_stmts body) /\
    ~supported_stmts_expr_exists expr_evm_run_root body /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_for cx tyv id body vs st = (res,rt) ==> contract_storage_well_formed cx rt) /\
  (!cx e. eval_expr cx e = eval_expr cx e) /\
  (!cx es. eval_exprs cx es = eval_exprs cx es) /\
  (!cx bt. eval_base_place cx bt = eval_base_place cx bt) /\
  (!cx bt. eval_target_place cx bt = eval_target_place cx bt) /\
  (!cx tgt v. !env ty st res rt.
    well_typed_atarget env tgt ty /\ value_runtime_typed env ty v /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atarget tgt) /\
    EVERY (oracle_internal_call_storage cx) (int_calls_atarget tgt) /\
    ~supported_assignment_exists expr_evm_run_root tgt /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    assign_tuple_targets cx tgt v st = (res,rt) ==> contract_storage_well_formed cx rt) /\
  (!cx tgts vs. !env tys st res rt.
    LIST_REL (\t ty. well_typed_atarget env t ty) tgts tys /\
    LIST_REL (value_runtime_typed env) tys vs /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atargets tgts) /\
    EVERY (oracle_internal_call_storage cx) (int_calls_atargets tgts) /\
    ~supported_assignments_exists expr_evm_run_root tgts /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    assign_tuple_target_list cx tgts vs st = (res,rt) ==> contract_storage_well_formed cx rt) /\
  (!cx es. eval_expr_results cx es = eval_expr_results cx es) /\
  (!cx e. eval_abi_expr cx e = eval_abi_expr cx e) /\
  (!cx es. eval_abi_exprs cx es = eval_abi_exprs cx es)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> simp[] >>
  rpt gen_tac >> strip_tac >>
  (fn g as (asms,w) => let
    fun head t = #Name(dest_thy_const(fst(strip_comb t)))
    val body = snd(strip_forall w)
    val ps = if is_imp body then strip_conj(fst(dest_imp body)) else asms
    val eq = valOf(List.find (fn t => is_eq t andalso
      List.exists (fn n => head(lhs t) = n)
        ["eval_stmt","eval_stmts","eval_iterator","eval_for",
         "assign_tuple_targets","assign_tuple_target_list"]) ps)
    val (h,args) = strip_comb(lhs eq)
    val n = head h
    val arg = el 2 args
    val (a,xs) = strip_comb arg
    fun shape t = if listSyntax.is_nil t then "nil" else "cons"
    val label = if n = "assign_tuple_targets" then "Tuple_" ^ head arg
      else if n = "assign_tuple_target_list" then "TupleList_" ^ shape arg ^ "_" ^ shape(el 3 args)
      else if n = "eval_stmts" then "Stmts_" ^ shape arg
      else if n = "eval_iterator" then "Iterator_" ^ head arg
      else if n = "eval_for" then "For_" ^ shape(el 5 args)
      else if head arg = "Return" then "Return_" ^ head(hd xs)
      else if head arg = "Raise" then head(hd xs)
      else if head arg = "Assert" then head(el 2 xs)
      else if head arg = "Assign" then "Assign_" ^ head(hd xs)
      else head arg
  in suspend label g end)
QED

Resume eval_stmts_oracle_storage_mutual[Pass]:
  gvs[Once evaluate_def,return_def,runtime_storage_consistent_def]
QED
Resume eval_stmts_oracle_storage_mutual[Break]:
  gvs[Once evaluate_def,raise_def,runtime_storage_consistent_def]
QED
Resume eval_stmts_oracle_storage_mutual[Continue]:
  gvs[Once evaluate_def,raise_def,runtime_storage_consistent_def]
QED
Resume eval_stmts_oracle_storage_mutual[Return_NONE]:
  gvs[Once evaluate_def,raise_def,runtime_storage_consistent_def]
QED
Resume eval_stmts_oracle_storage_mutual[RaiseBare]:
  gvs[Once evaluate_def,raise_def,runtime_storage_consistent_def]
QED
Resume eval_stmts_oracle_storage_mutual[RaiseUnreachable]:
  gvs[Once evaluate_def,raise_def,runtime_storage_consistent_def]
QED
Resume eval_stmts_oracle_storage_mutual[Stmts_nil]:
  gvs[Once evaluate_def,return_def,runtime_storage_consistent_def]
QED
Resume eval_stmts_oracle_storage_mutual[For_nil]:
  gvs[Once evaluate_def,return_def,runtime_storage_consistent_def]
QED
Resume eval_stmts_oracle_storage_mutual[StorageRawCreate]:
  gvs[supported_stmt_expr_exists_def]
QED

Resume eval_stmts_oracle_storage_mutual[RaiseCustomError]:
  gvs[supported_stmt_def,supported_raise_reason_def]
QED
Resume eval_stmts_oracle_storage_mutual[AssertCustomError]:
  gvs[supported_stmt_def,supported_assert_reason_def]
QED

Resume eval_stmts_oracle_storage_mutual[Expr]:
  ENTRY_TAC >> gvs[Once type_stmt_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def,bind_def,type_check_def,assert_def,return_def,raise_def] >>
  Cases_on `eval_expr cx e st` >>
  drule_all oracle_expr_storage >> strip_tac >>
  Cases_on `q` >> gvs[runtime_storage_consistent_def] >> rpt strip_tac >> gvs[]
QED

Resume eval_stmts_oracle_storage_mutual[Return_SOME]:
  ENTRY_TAC >> gvs[Once type_stmt_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def,bind_def] >>
  Cases_on `eval_expr cx e st` >>
  drule_all oracle_expr_storage >> strip_tac >>
  Cases_on `q` >> gvs[runtime_storage_consistent_def] >>
  Cases_on `read_result cx x r` >> imp_res_tac read_result_state >> gvs[] >>
  Cases_on `q` >> gvs[raise_def] >> rpt strip_tac >> gvs[]
QED

Resume eval_stmts_oracle_storage_mutual[Stmts_cons]:
  ENTRY_TAC >> gvs[supported_stmt_def] >>
  qpat_x_assum `type_stmts _ _ _ = _` mp_tac >>
  simp[Once type_stmt_def,AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >>
  simp[Once evaluate_def,ignore_bind_apply] >>
  Cases_on `eval_stmt cx s st` >>
  rename1 `eval_stmt cx s st = (r1,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `r1` >> gvs[]
  >- (qpat_x_assum `runtime_storage_consistent env cx st` mp_tac >>
      simp[runtime_storage_consistent_def,runtime_consistent_def] >> strip_tac >>
      drule_all eval_stmt_type_preservation_success >> strip_tac >>
      `runtime_storage_consistent env'' cx st1` by
        simp[runtime_storage_consistent_def,runtime_consistent_def] >>
      `IS_SOME st1.outcomes /\ oracle_storage_ok cx st1` by
        (drule (cj 1 eval_outcome_suffix_mutual) >>
         metis_tac[oracle_storage_entry_suffix]) >>
      Cases_on `eval_stmts cx ss st1` >>
      first_x_assum drule_all >> strip_tac >>
      gvs[bind_def] >> rpt strip_tac >> gvs[]) >>
  gvs[bind_def] >> rpt strip_tac >> gvs[]
QED

Resume eval_stmts_oracle_storage_mutual[RaiseReason]:
  ENTRY_TAC >> gvs[Once type_stmt_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def,bind_def,return_def,raise_def] >>
  Cases_on `eval_expr cx e st` >> drule_all oracle_expr_storage >> strip_tac >>
  Cases_on `q` >> gvs[runtime_storage_consistent_def] >>
  Cases_on `read_result cx x r` >> imp_res_tac read_result_state >> gvs[] >>
  Cases_on `q` >> gvs[bind_def,return_def,raise_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(),raise_def] >>
  imp_res_tac lift_option_type_state >> gvs[]
QED

fun ASSERT_ORACLE_TAC g = (
  ENTRY_TAC >> gvs[Once type_stmt_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def,bind_def,return_def,raise_def] >>
  Cases_on `eval_expr cx e st` >> drule_all oracle_expr_storage >> strip_tac >>
  Cases_on `q` >> gvs[runtime_storage_consistent_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  `rt = r` by
    (drule_at (Pat `switch_BoolV _ _ _ _ _ = _`) switch_BoolV_state >>
     simp[return_def,raise_def]) >> gvs[]) g;

Resume eval_stmts_oracle_storage_mutual[AssertBare]:
  ASSERT_ORACLE_TAC
QED
Resume eval_stmts_oracle_storage_mutual[AssertUnreachable]:
  ASSERT_ORACLE_TAC
QED

Resume eval_stmts_oracle_storage_mutual[Log]:
  ENTRY_TAC >> gvs[Once type_stmt_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def,bind_def,return_def] >>
  Cases_on `eval_exprs cx es st` >>
  drule_all (cj 6 eval_expr_oracle_storage_results_mutual) >> strip_tac >>
  Cases_on `q` >> gvs[bind_def,return_def,push_log_def] >>
  Cases_on `encode_source_event (get_tenv cx) cx.sources cx.txn.target id x` >>
  gvs[lift_option_def,raise_def,return_def,push_log_def] >>
  rpt strip_tac >> pop_assum (SUBST1_TAC o SYM) >>
  metis_tac[contract_storage_well_formed_logs]
QED

Resume eval_stmts_oracle_storage_mutual[Iterator_Array]:
  ENTRY_TAC >> gvs[well_typed_iterator_def] >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp[Once evaluate_def,bind_def,return_def] >>
  Cases_on `eval_expr cx e st` >> drule_all oracle_expr_storage >> strip_tac >>
  Cases_on `q` >> gvs[runtime_storage_consistent_def] >>
  Cases_on `read_result cx x r` >> imp_res_tac read_result_state >> gvs[] >>
  Cases_on `q` >> gvs[bind_def,return_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(),return_def,raise_def] >>
  imp_res_tac lift_option_type_state >> gvs[]
QED

Resume eval_stmts_oracle_storage_mutual[AnnAssign]:
  ENTRY_TAC >> gvs[Once type_stmt_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def,bind_def] >>
  Cases_on `lift_option_type (evaluate_type (get_tenv cx) typ) "AnnAssign evaluate_type" st` >>
  imp_res_tac lift_option_type_state >> gvs[] >>
  rename1 `runtime_storage_consistent env cx st` >>
  Cases_on `q` >> gvs[]
  >- (Cases_on `eval_expr cx e st` >> drule_all oracle_expr_storage >> strip_tac >>
      Cases_on `q` >> gvs[runtime_storage_consistent_def] >>
      Cases_on `read_result cx x' r` >> imp_res_tac read_result_state >> gvs[] >>
      Cases_on `q` >> gvs[return_def,raise_def] >>
      metis_tac[new_variable_preserves_contract_storage_well_formed]) >>
  rw[] >> gvs[runtime_storage_consistent_def]
QED

Resume eval_stmts_oracle_storage_mutual[TupleList_nil_nil]:
  gvs[Once evaluate_def,return_def,runtime_storage_consistent_def]
QED
Resume eval_stmts_oracle_storage_mutual[TupleList_cons_nil]:
  gvs[Once evaluate_def,raise_def,runtime_storage_consistent_def]
QED
Resume eval_stmts_oracle_storage_mutual[TupleList_nil_cons]:
  gvs[Once evaluate_def,raise_def,runtime_storage_consistent_def]
QED

Resume eval_stmts_oracle_storage_mutual[Tuple_BaseTarget]:
  ENTRY_TAC >> gvs[well_typed_atarget_def] >>
  qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
  simp[Once evaluate_def,bind_def] >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (answer,middle)` >>
  drule_all oracle_target_storage >> strip_tac >>
  reverse (Cases_on `answer`)
  >- (simp[] >> strip_tac >> gvs[runtime_storage_consistent_def]) >>
  simp[] >> strip_tac >> gvs[] >>
  `runtime_consistent env cx st` by metis_tac[runtime_storage_consistent_runtime] >>
  drule_all eval_target_place_success_storage_type >> strip_tac >>
  drule eval_target_place_region >> strip_tac >>
  `storage_layout_safe cx` by metis_tac[runtime_storage_consistent_layout] >>
  `contract_storage_well_formed cx middle` by metis_tac[runtime_storage_consistent_storage] >>
  drule_all typed_write_place_preserves_storage >> simp[]
QED

Resume eval_stmts_oracle_storage_mutual[Tuple_TupleTarget]:
  ENTRY_TAC >> gvs[well_typed_atarget_def] >>
  drule value_runtime_typed_tuple_components >> strip_tac >> gvs[] >>
  qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >> first_x_assum drule_all >> simp[]
QED

Resume eval_stmts_oracle_storage_mutual[TupleList_cons_cons]:
  ENTRY_TAC >>
  rename1 `assign_tuple_target_list cx (g::gs) (v::vs) st = (res,rt)` >>
  qpat_x_assum `assign_tuple_target_list _ _ _ _ = _` mp_tac >>
  simp[Once evaluate_def,bind_def,ignore_bind_def] >>
  Cases_on `assign_tuple_targets cx g v st` >>
  rename1 `assign_tuple_targets cx g v st = (answer,middle)` >>
  first_x_assum drule_all >> strip_tac >>
  `runtime_consistent env cx st` by metis_tac[runtime_storage_consistent_runtime] >>
  `runtime_consistent env cx middle` by
    (drule_all assign_tuple_targets_preserves_runtime_consistent >> simp[]) >>
  `runtime_storage_consistent env cx middle` by
    metis_tac[runtime_storage_consistent_intro,runtime_storage_consistent_layout] >>
  `IS_SOME middle.outcomes /\ oracle_storage_ok cx middle` by
    (drule (cj 9 eval_outcome_suffix_mutual) >> metis_tac[oracle_storage_entry_suffix]) >>
  Cases_on `answer` >> gvs[] >> strip_tac >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Resume eval_stmts_oracle_storage_mutual[Assign_BaseTarget]:
  ENTRY_TAC >> gvs[Once type_stmt_def] >>
  `?tty. well_typed_atarget env (BaseTarget bt) tty /\
         type_widens_to env.type_defs (expr_type e) tty /\
         assignable_type env.type_defs tty` by
    metis_tac[atarget_accepts_well_typed_atarget] >>
  gvs[well_typed_atarget_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def,bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (rhs_res,rhs_st)` >>
  drule_all oracle_expr_storage >> strip_tac >>
  reverse (Cases_on `rhs_res`)
  >- (simp[] >> strip_tac >> gvs[runtime_storage_consistent_def]) >>
  `runtime_consistent env cx st` by metis_tac[runtime_storage_consistent_runtime] >>
  drule_all eval_expr_success_storage_facts >> strip_tac >> simp[] >>
  Cases_on `eval_target_place cx bt rhs_st` >>
  rename1 `eval_target_place cx bt rhs_st = (target_res,target_st)` >>
  drule_all oracle_target_storage >> strip_tac >>
  reverse (Cases_on `target_res`)
  >- (simp[] >> strip_tac >> gvs[runtime_storage_consistent_def]) >>
  simp[] >> strip_tac >>
  qmatch_assum_rename_tac `eval_expr cx e st = (INL pv,rhs_st)` >>
  qmatch_assum_rename_tac `eval_target_place cx bt rhs_st = (INL p,target_st)` >>
  `runtime_consistent env cx rhs_st` by metis_tac[runtime_storage_consistent_runtime] >>
  drule_all eval_target_place_success_storage_type >> strip_tac >>
  drule_all eval_target_place_storage_trace >> strip_tac >>
  `immutable_metadata_frame rhs_st target_st` by
    (drule (cj 8 eval_metadata_frame_mutual) >> simp[]) >>
  `eval_result_typed (env,cx,target_st) pv (Type (expr_type e))` by
    (Cases_on `pv` >> gvs[eval_result_typed_def] >> metis_tac[runtime_place_typed_transport]) >>
  `live_memory_result target_st pv` by
    (irule live_result_transport >> qexists_tac `rhs_st` >> simp[]) >>
  `state_well_typed target_st` by
    metis_tac[runtime_storage_consistent_runtime,runtime_consistent_def] >>
  Cases_on `read_result cx pv target_st` >>
  rename1 `read_result cx pv target_st = (read_res,read_st)` >>
  imp_res_tac read_result_state >> gvs[] >> reverse (Cases_on `read_res`) >> gvs[]
  >- metis_tac[runtime_storage_consistent_storage] >>
  rename1 `read_result cx pv target_st = (INL v,target_st)` >>
  `value_runtime_typed env (expr_type e) v` by
    (drule_all read_live_result_success_type >> simp[]) >>
  `value_runtime_typed env tty v` by
    (fs[value_runtime_typed_def] >> drule_all type_widens_to_value_has_type >> strip_tac >> gvs[]) >>
  drule eval_target_place_region >> strip_tac >>
  `storage_layout_safe cx /\ contract_storage_well_formed cx target_st` by
    metis_tac[runtime_storage_consistent_layout,runtime_storage_consistent_storage] >>
  `eval_result_typed (env,cx,target_st) (PlaceR p) (Type tty)` by simp[eval_result_typed_def] >>
  drule_all typed_write_place_preserves_storage >> simp[]
QED

Resume eval_stmts_oracle_storage_mutual[Assign_TupleTarget]:
  ENTRY_TAC >> gvs[Once type_stmt_def,atarget_accepts_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def,bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (er,s1)` >>
  drule_all oracle_expr_storage >> strip_tac >>
  reverse (Cases_on `er`)
  >- (simp[] >> strip_tac >> gvs[runtime_storage_consistent_def]) >>
  `runtime_consistent env cx st` by metis_tac[runtime_storage_consistent_runtime] >>
  drule_all eval_expr_success_storage_facts >> strip_tac >>
  Cases_on `read_result cx x s1` >>
  imp_res_tac read_result_state >> gvs[] >> reverse (Cases_on `q`)
  >- (simp[] >> strip_tac >> gvs[runtime_storage_consistent_def]) >>
  `value_runtime_typed env (expr_type e) x'` by
    (fs[runtime_storage_consistent_def,runtime_consistent_def] >>
     drule_all read_live_result_success_type >> simp[]) >>
  simp[] >> strip_tac >> first_x_assum drule_all >> simp[]
QED

Resume eval_stmts_oracle_storage_mutual[Append]:
  ENTRY_TAC >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp[Once type_stmt_def,AllCaseEqs()] >> strip_tac >> gvs[] >>
  `well_typed_target env bt (ArrayT elem_ty (Dynamic n))` by simp[well_typed_target_def] >>
  `runtime_consistent env cx st` by metis_tac[runtime_storage_consistent_runtime] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >> simp[Once evaluate_def,bind_def] >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (target_res,st1)` >>
  drule_all oracle_target_storage >> strip_tac >>
  reverse (Cases_on `target_res`)
  >- (simp[] >> strip_tac >> gvs[runtime_storage_consistent_def]) >>
  rename1 `eval_target_place cx bt st = (INL p,st1)` >>
  drule_all eval_target_place_success_storage_type >> strip_tac >>
  drule eval_target_place_region >> strip_tac >> simp[] >>
  Cases_on `eval_expr cx e st1` >> rename1 `eval_expr cx e st1 = (expr_res,st2)` >>
  drule_all oracle_expr_storage >> strip_tac >>
  reverse (Cases_on `expr_res`)
  >- (simp[] >> strip_tac >> gvs[runtime_storage_consistent_def]) >>
  rename1 `eval_expr cx e st1 = (INL pv,st2)` >>
  `runtime_consistent env cx st1` by metis_tac[runtime_storage_consistent_runtime] >>
  drule_all eval_expr_success_storage_facts >> strip_tac >>
  drule_all eval_expr_storage_trace >> strip_tac >>
  `immutable_metadata_frame st1 st2` by (drule (cj 5 eval_metadata_frame_mutual) >> simp[]) >>
  `?elem_tv. evaluate_type env.type_defs elem_ty = SOME elem_tv /\
     runtime_place_typed cx st1 p (ArrayTV elem_tv (Dynamic n))` by
    gvs[eval_result_typed_def,evaluate_type_def,AllCaseEqs()] >>
  `runtime_place_typed cx st2 p (ArrayTV elem_tv (Dynamic n))` by
    (irule runtime_place_typed_transport >> qexists_tac `st1` >> simp[]) >>
  Cases_on `read_result cx pv st2` >>
  rename1 `read_result cx pv st2 = (read_res,read_st)` >>
  imp_res_tac read_result_state >> gvs[] >> reverse (Cases_on `read_res`)
  >- (simp[] >> strip_tac >> gvs[runtime_storage_consistent_def]) >>
  rename1 `read_result cx pv read_st = (INL v,read_st)` >>
  `value_runtime_typed env (expr_type e) v` by
    (fs[runtime_storage_consistent_def,runtime_consistent_def] >>
     drule_all read_live_result_success_type >> simp[]) >>
  `value_runtime_typed env elem_ty v` by
    (gvs[value_runtime_typed_def] >> drule_all type_widens_to_value_has_type >> strip_tac >> gvs[]) >>
  `value_has_type elem_tv v` by gvs[value_runtime_typed_def] >>
  strip_tac >> gvs[] >>
  `storage_layout_safe cx /\ contract_storage_well_formed cx read_st` by
    metis_tac[runtime_storage_consistent_layout,runtime_storage_consistent_storage] >>
  drule_all append_place_preserves_contract_storage >> simp[]
QED

Resume eval_stmts_oracle_storage_mutual[AugAssign]:
  ENTRY_TAC >> gvs[Once type_stmt_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >> simp[Once evaluate_def,bind_def] >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (target_res,target_st)` >>
  drule_all oracle_target_storage >> strip_tac >>
  `runtime_consistent env cx st` by metis_tac[runtime_storage_consistent_runtime] >>
  reverse (Cases_on `target_res`)
  >- (simp[] >> strip_tac >> gvs[runtime_storage_consistent_def]) >>
  drule_all eval_target_place_success_storage_facts >> strip_tac >>
  gvs[eval_result_typed_def] >>
  qmatch_assum_rename_tac `runtime_place_typed cx target_st p ptv` >>
  `place_type_value cx p target_st = (INL ptv,target_st)` by
    gvs[runtime_place_typed_def] >>
  `state_well_typed target_st` by
    metis_tac[runtime_storage_consistent_runtime,runtime_consistent_def] >>
  simp[] >> Cases_on `read_place cx p target_st` >>
  rename1 `read_place cx p target_st = (read_res,read_st)` >>
  drule_all live_place_read_sound >> strip_tac >> gvs[] >>
  reverse (Cases_on `read_res`)
  >- (simp[] >> strip_tac >> gvs[runtime_storage_consistent_def]) >>
  simp[] >> Cases_on `eval_expr cx e read_st` >>
  rename1 `eval_expr cx e read_st = (rhs_res,rhs_st)` >>
  drule_all oracle_expr_storage >> strip_tac >>
  reverse (Cases_on `rhs_res`)
  >- (simp[] >> strip_tac >> gvs[runtime_storage_consistent_def]) >>
  rename1 `eval_expr cx e read_st = (INL rhs,rhs_st)` >>
  `runtime_consistent env cx read_st` by metis_tac[runtime_storage_consistent_runtime] >>
  drule_all eval_expr_success_storage_facts >> strip_tac >>
  drule_all eval_expr_storage_trace >> strip_tac >>
  `immutable_metadata_frame read_st rhs_st` by (drule (cj 5 eval_metadata_frame_mutual) >> simp[]) >>
  `runtime_place_typed cx rhs_st p ptv` by
    (irule runtime_place_typed_transport >> qexists_tac `read_st` >> simp[]) >>
  drule eval_target_place_region >> strip_tac >>
  `storage_layout_safe cx /\ contract_storage_well_formed cx rhs_st /\ state_well_typed rhs_st` by
    metis_tac[runtime_storage_consistent_layout,runtime_storage_consistent_storage,
              runtime_storage_consistent_runtime,runtime_consistent_def] >>
  simp[] >> strip_tac >> gvs[] >>
  drule_all (SIMP_RULE (srw_ss()) [bind_def] update_place_tail_preserves_storage) >> simp[]
QED

Resume eval_stmts_oracle_storage_mutual[AssertReason]:
  ENTRY_TAC >> gvs[Once type_stmt_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >> simp[Once evaluate_def,bind_apply] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (er,s1)` >>
  drule_all oracle_expr_storage >> strip_tac >>
  reverse (Cases_on `er`)
  >- (simp[] >> strip_tac >> gvs[runtime_storage_consistent_def]) >>
  simp[] >> strip_tac >>
  `contract_storage_well_formed cx s1` by metis_tac[runtime_storage_consistent_storage] >>
  drule_at (Pat `switch_BoolV _ _ _ _ _ = _`) oracle_switch_storage >>
  disch_then irule >> simp[return_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `do _ od _ = _` mp_tac >> simp[bind_def] >>
  Cases_on `eval_expr cx e' s1` >> drule_all oracle_expr_storage >> strip_tac >>
  Cases_on `q` >> gvs[runtime_storage_consistent_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(),raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac lift_option_type_state >> gvs[]
QED

Resume eval_stmts_oracle_storage_mutual[Iterator_Range]:
  ENTRY_TAC >> gvs[well_typed_iterator_def] >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp[Once evaluate_def,bind_def,return_def,raise_def] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (er,s1)` >>
  drule_all oracle_expr_storage >> strip_tac >>
  reverse (Cases_on `er`)
  >- (simp[] >> strip_tac >> gvs[runtime_storage_consistent_def]) >>
  Cases_on `read_result cx x s1` >> imp_res_tac read_result_state >> gvs[] >>
  reverse (Cases_on `q`)
  >- (simp[] >> strip_tac >> gvs[runtime_storage_consistent_def]) >>
  simp[] >> Cases_on `eval_expr cx e' r` >>
  rename1 `eval_expr cx e' r = (er2,s2)` >>
  drule_all oracle_expr_storage >> strip_tac >>
  Cases_on `er2` >> gvs[runtime_storage_consistent_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  imp_res_tac read_result_state >> imp_res_tac lift_sum_state >> gvs[]
QED

Resume eval_stmts_oracle_storage_mutual[If]:
  ENTRY_TAC >> gvs[Once type_stmt_def,supported_stmt_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def,bind_apply,push_scope_def,return_def] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (er,s1)` >>
  drule_all oracle_expr_storage >> strip_tac >>
  reverse (Cases_on `er`)
  >- (simp[] >> strip_tac >> gvs[runtime_storage_consistent_def]) >>
  simp[ignore_bind_apply,push_scope_def,return_def] >> strip_tac >>
  `push_scope s1 = (INL (),s1 with scopes updated_by CONS FEMPTY)` by
    simp[push_scope_def,return_def] >>
  NTAC 2 (
    qpat_x_assum `!s'' tv t s''' t'. eval_expr cx e s'' = (INL tv,t) /\ push_scope s''' = (INL (),t') ==> _`
      (qspecl_then [`st`,`x`,`s1`,`s1`,`s1 with scopes updated_by CONS FEMPTY`] mp_tac) >>
    simp[] >> strip_tac) >>
  drule_at (Pat `finally _ _ _ = _`) oracle_finally_storage >> disch_then irule >>
  conj_tac >- metis_tac[pop_scope_preserves_contract_storage_well_formed] >>
  rpt gen_tac >> strip_tac >>
      drule_at (Pat `switch_BoolV _ _ _ _ _ = _`) oracle_switch_storage >> disch_then irule >>
      `runtime_storage_consistent env cx (s1 with scopes updated_by CONS FEMPTY)` by
        (irule push_scope_preserves_runtime_storage_consistent >>
         qexistsl_tac [`INL ()`,`s1`] >> simp[push_scope_def,return_def]) >>
      `IS_SOME (s1 with scopes updated_by CONS FEMPTY).outcomes /\
       oracle_storage_ok cx (s1 with scopes updated_by CONS FEMPTY)` by
        (`oracle_storage_ok cx (s1 with scopes updated_by CONS FEMPTY) <=> oracle_storage_ok cx s1` by
           (irule oracle_storage_ok_outcomes >> simp[]) >> simp[]) >>
      rpt conj_tac >> TRY (metis_tac[runtime_storage_consistent_storage]) >>
      rpt gen_tac >> strip_tac >>
      rpt (qpat_x_assum `IS_SOME (type_stmts _ _ _)`
        (strip_assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS])) >>
      first_x_assum drule_all >> simp[]
QED

Resume eval_stmts_oracle_storage_mutual[For]:
  ENTRY_TAC >>
  rename1 `eval_stmt cx (For id typ it n loop_stmts) st = (res,rt)` >>
  gvs[Once type_stmt_def,supported_stmt_def] >>
  `env.type_defs = get_tenv cx` by
    fs[runtime_storage_consistent_def,runtime_consistent_def,env_consistent_def,env_context_consistent_def] >>
  qpat_x_assum `IS_SOME (type_stmts _ _ _)`
    (strip_assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def,bind_def,lift_option_type_def,check_def,return_def,raise_def] >>
  Cases_on `evaluate_type (get_tenv cx) typ` >> gvs[bind_apply,return_def,raise_def]
  >- (rw[] >> gvs[runtime_storage_consistent_def]) >>
  rename1 `evaluate_type (get_tenv cx) typ = SOME tyv` >>
  rename1 `type_stmts (extend_local env id typ F) ret_ty loop_stmts = SOME env_after` >>
  Cases_on `eval_iterator cx it st` >> rename1 `eval_iterator cx it st = (ir,s1)` >>
  first_x_assum drule_all >> strip_tac >>
  `runtime_consistent env cx st` by metis_tac[runtime_storage_consistent_runtime] >>
  `runtime_consistent env cx s1` by metis_tac[eval_iterator_preserves_runtime_consistent] >>
  `runtime_storage_consistent env cx s1` by
    metis_tac[runtime_storage_consistent_intro,runtime_storage_consistent_layout] >>
  `IS_SOME s1.outcomes /\ oracle_storage_ok cx s1` by
    (drule (cj 3 eval_outcome_suffix_mutual) >> metis_tac[oracle_storage_entry_suffix]) >>
  reverse (Cases_on `ir`)
  >- (simp[] >> strip_tac >> gvs[]) >>
  drule_all eval_iterator_success_values_typed >> strip_tac >> gvs[] >>
  rename1 `eval_iterator cx it st = (INL vals,s1)` >>
  Cases_on `compatible_bound (Dynamic n) (LENGTH vals)` >>
  simp[bind_apply,ignore_bind_apply,check_def,assert_def,return_def,raise_def]
  >- (strip_tac >>
      qpat_x_assum `!s'' vs t s''' t'. _`
        (qspecl_then [`st`,`vals`,`s1`,`s1`,`s1`] mp_tac) >>
      simp[check_def,assert_def,return_def] >> strip_tac >>
      qpat_x_assum `!tops bindings env ret_ty ty env_after st res rt. _`
        (qspecl_then [`tops`,`bindings`,`env`,`ret_ty`,`typ`,`env_after`,`s1`,`res`,`rt`] mp_tac) >>
      simp[]) >>
  rw[] >> gvs[]
QED

Resume eval_stmts_oracle_storage_mutual[For_cons]:
  ENTRY_TAC >>
  rename1 `eval_for cx tyv id loop_stmts (v::vs) st = (res,rt)` >>
  qpat_x_assum `eval_for _ _ _ _ _ _ = _` mp_tac >>
  simp[Once evaluate_def,bind_def,ignore_bind_def,push_scope_with_var_def,return_def] >>
  qmatch_goalsub_abbrev_tac `finally loop_body pop_scope stp` >>
  Cases_on `finally loop_body pop_scope stp` >>
  rename1 `finally loop_body pop_scope stp = (lr,after)` >> strip_tac >>
  `stp.scopes <> []` by simp[Abbr`stp`] >>
  qunabbrev_tac `loop_body` >>
  drule for_body_decompose_storage >>
  disch_then (qspecl_then [`after`,`lr`,`cx`,`loop_stmts`] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  `push_scope_with_var id tyv v st = (INL (),stp)` by
    simp[push_scope_with_var_def,return_def,Abbr`stp`] >>
  `well_formed_type_value tyv` by metis_tac[evaluate_type_well_formed_type_value] >>
  `runtime_storage_consistent (extend_local env id ty F) cx stp` by
    (irule push_scope_with_var_preserves_runtime_storage_consistent >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`st`,`tyv`,`v`] >> simp[]) >>
  `IS_SOME stp.outcomes /\ oracle_storage_ok cx stp` by
    (`oracle_storage_ok cx stp <=> oracle_storage_ok cx st` by
       (irule oracle_storage_ok_outcomes >> simp[Abbr`stp`]) >> simp[Abbr`stp`]) >>
  qpat_x_assum `!s'' t. push_scope_with_var _ _ _ _ = _ ==> _`
    (qspecl_then [`st`,`stp`] mp_tac) >> simp[] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  `contract_storage_well_formed cx after` by
    metis_tac[contract_storage_well_formed_scopes] >>
  `eval_for cx tyv id loop_stmts [v] st =
     ((case lr of INL broke => INL () | INR e => INR e),after)` by
    (simp[Once evaluate_def,bind_def,ignore_bind_def,push_scope_with_var_def,return_def,Abbr`stp`] >>
     qpat_assum `finally _ _ stp = (lr,after)` (fn th => rewrite_tac[th]) >>
     Cases_on `lr` >> simp[Once evaluate_def,return_def]) >>
  `runtime_consistent env cx st` by metis_tac[runtime_storage_consistent_runtime] >>
  `EVERY (value_has_type tyv) [v]` by simp[] >>
  `runtime_consistent env cx after` by (drule_all eval_for_preserves_runtime_consistent >> simp[]) >>
  `runtime_storage_consistent env cx after` by
    metis_tac[runtime_storage_consistent_intro,runtime_storage_consistent_layout] >>
  `IS_SOME after.outcomes /\ oracle_storage_ok cx after` by
    (drule (cj 4 eval_outcome_suffix_mutual) >> metis_tac[oracle_storage_entry_suffix]) >>
  qpat_x_assum `after = _` kall_tac >>
  Cases_on `lr` >> gvs[] >> Cases_on `x` >> gvs[return_def]
  >- (rename1 `eval_for cx tyv id loop_stmts vs after = (res,rt)` >>
      qpat_x_assum `!s'' t s''' t'. _`
        (qspecl_then [`st`,`stp`,`stp`,`after`] mp_tac) >>
      simp[ignore_bind_def] >> strip_tac >>
      qpat_x_assum `!tops bindings env ret_ty ty env_after st res rt. _`
        (qspecl_then [`tops`,`bindings`,`env`,`ret_ty`,`ty`,`env_after`,`after`,`res`,`rt`] mp_tac) >>
      simp[])
QED

Finalise eval_stmts_oracle_storage_mutual
