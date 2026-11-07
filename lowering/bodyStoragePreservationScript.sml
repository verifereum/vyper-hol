(*
 * Storage well-formedness across an expression of a function body
 *
 * exprStoragePreservation keeps contract_storage_well_formed across an
 * expression with no internal calls.  A body's expression may make
 * internal calls, and the callee's statements then run too.  In a
 * supported program no function body has raw_call or create
 * (supported_expr_no_evm_run) and every internal call is to the main
 * module, whose code is the program, so in oracle mode (IS_SOME
 * st.outcomes) nothing the callee runs needs a postulate about EVM code
 * either: external calls and send take the oracle's outcomes, which keep
 * storage well formed by oracle_storage_ok, and storage writes keep it by
 * the source semantics.
 *
 * TOP-LEVEL:
 *   eval_expr_body_oracle_storage — across an expression
 *   eval_stmts_body_oracle_storage — across a supported statement, or a
 *     list of them (supported_stmt gives the same syntactic facts)
 *)

Theory bodyStoragePreservation
Ancestors
  vyperCall
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph
  vyperTypeExprSoundness vyperTypeCallStackSoundness vyperTypeInvariants
  vyperStorageLayoutSafety vyperTypeStoragePreservation
  vyperTypeEvalStoragePreservation vyperEvalOutcomeSuffix
  supportedExprTraverse supportedProgram vyperPlaceFrames
  vyperStatePreservation vyperTypeAssignContext vyperStoragePlaceProvenance
  vyperPlaceStoragePreservation vyperValue vyperMachineFrame
  vyperTypeContractStaticMaps supportedDecls supportedStmts supportedExprs
  supportedTargets supportedStmtTraverse bodyStorageCases
  bodyStorageIntcallDefaults list

(* Proved by one mutual induction over evaluate_ind; each clause is
   discharged by its case lemma from bodyStorageCases. *)
Theorem body_oracle_storage_mutual:
  (!cx s. !tops env ret_ty env' st res st'.
    type_stmt env ret_ty s = SOME env' /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_stmt_expr_exists expr_evm_run_root s /\
    EVERY (\c. FST c = NONE) (int_calls_stmt s) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmt s) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_stmt cx s st = (res,st') ==> contract_storage_well_formed cx st') /\
  (!cx ss. !tops env ret_ty env' st res st'.
    type_stmts env ret_ty ss = SOME env' /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_stmts_expr_exists expr_evm_run_root ss /\
    EVERY (\c. FST c = NONE) (int_calls_stmts ss) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_stmts cx ss st = (res,st') ==> contract_storage_well_formed cx st') /\
  (!cx it. !tops env ty st res st'.
    well_typed_iterator env ty it /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_iterator_exists expr_evm_run_root it /\
    EVERY (\c. FST c = NONE) (int_calls_iterator it) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_iterator it) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_iterator cx it st = (res,st') ==> contract_storage_well_formed cx st') /\
  (!cx tyv id body vs. !tops env ret_ty ty env_after st res st'.
    evaluate_type env.type_defs ty = SOME tyv /\
    EVERY (value_has_type tyv) vs /\ id NOTIN FDOM env.var_types /\
    type_stmts (extend_local env id ty F) ret_ty body = SOME env_after /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_stmts_expr_exists expr_evm_run_root body /\
    EVERY (\c. FST c = NONE) (int_calls_stmts body) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmts body) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_for cx tyv id body vs st = (res,st') ==> contract_storage_well_formed cx st') /\
  (!cx e. !tops env st res st'.
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~expr_has_evm_run e /\ EVERY (\c. FST c = NONE) (int_calls_expr e) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_expr cx e st = (res,st') ==>
    (well_typed_expr env e ==> contract_storage_well_formed cx st') /\
    (!vt. type_place_expr env e = SOME vt ==> contract_storage_well_formed cx st')) /\
  (!cx es. !tops env st res st'.
    well_typed_exprs env es /\ supported_program tops /\
    get_module_code cx NONE = SOME tops /\
    ~supported_exprs_exists expr_evm_run_root es /\
    EVERY (\c. FST c = NONE) (int_calls_exprs es) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_exprs es) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_exprs cx es st = (res,st') ==> contract_storage_well_formed cx st') /\
  (!cx bt. !tops env vt st res st'.
    type_place_target env bt = SOME vt /\ supported_program tops /\
    get_module_code cx NONE = SOME tops /\
    ~supported_target_exists expr_evm_run_root bt /\
    EVERY (\c. FST c = NONE) (int_calls_target bt) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_base_place cx bt st = (res,st') ==> contract_storage_well_formed cx st') /\
  (!cx tgt. !tops env ty st res st'.
    well_typed_target env tgt ty /\ supported_program tops /\
    get_module_code cx NONE = SOME tops /\
    ~supported_target_exists expr_evm_run_root tgt /\
    EVERY (\c. FST c = NONE) (int_calls_target tgt) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target tgt) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_target_place cx tgt st = (res,st') ==> contract_storage_well_formed cx st') /\
  (!cx tgt v. !tops env ty st res st'.
    well_typed_atarget env tgt ty /\ value_runtime_typed env ty v /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_assignment_exists expr_evm_run_root tgt /\
    EVERY (\c. FST c = NONE) (int_calls_atarget tgt) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atarget tgt) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    assign_tuple_targets cx tgt v st = (res,st') ==> contract_storage_well_formed cx st') /\
  (!cx tgts vs. !tops env tys st res st'.
    LIST_REL (\t ty. well_typed_atarget env t ty) tgts tys /\
    LIST_REL (value_runtime_typed env) tys vs /\
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    ~supported_assignments_exists expr_evm_run_root tgts /\
    EVERY (\c. FST c = NONE) (int_calls_atargets tgts) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atargets tgts) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    assign_tuple_target_list cx tgts vs st = (res,st') ==> contract_storage_well_formed cx st') /\
  (!cx es. !tops env st res st'.
    well_typed_exprs env es /\ supported_program tops /\
    get_module_code cx NONE = SOME tops /\
    ~supported_exprs_exists expr_evm_run_root es /\
    EVERY (\c. FST c = NONE) (int_calls_exprs es) /\
    runtime_storage_consistent env cx st /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_exprs es) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_expr_results cx es st = (res,st') ==> contract_storage_well_formed cx st')
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> simp[] >> rpt gen_tac
  >~ [`Call ty (IntCall (src_id_opt,fn)) es kw`] >- suspend "intcall_start"
  >~ [`eval_iterator cx (Array e)`] >-
    (strip_tac >> match_mp_tac body_array_iterator_consumer >>
     first_assum ACCEPT_TAC)
  >~ [`eval_iterator cx (Range e1 e2)`] >-
    (strip_tac >> match_mp_tac body_range_iterator_consumer >>
     conj_tac >> first_assum ACCEPT_TAC)
  >~ [`eval_stmts cx (stmt::ss)`] >-
    (strip_tac >> match_mp_tac body_stmts_cons_consumer >>
     conj_tac
     >- (rpt gen_tac >> rename1 `eval_stmt _ _ _ = (INL x,_)` >>
         Cases_on `x` >> first_assum MATCH_ACCEPT_TAC) >>
     first_assum ACCEPT_TAC)
  >~ [`eval_stmts cx []`] >-
    (rpt gen_tac >> strip_tac >>
     metis_tac[body_stmts_nil_storage, runtime_storage_consistent_storage])
  >~ [`eval_stmt _ (Assign (BaseTarget _) _)`] >- suspend "assign_base"
  >~ [`eval_stmt _ (If _ _ _)`] >- suspend "if_stmt"
  >~ [`eval_stmt _ (AnnAssign _ _ _)`] >- suspend "annassign"
  >~ [`eval_stmt _ (Log _ _)`] >- suspend "log_stmt"
  >~ [`eval_stmt _ (Append _ _)`] >- suspend "append_stmt"
  >~ [`eval_stmt _ (AugAssign _ _ _ _)`] >- suspend "augassign"
  >~ [`eval_stmt _ (Assign (TupleTarget _) _)`] >- suspend "assign_tuple"
  >~ [`eval_stmt _ (Expr _)`] >- suspend "expr_stmt"
  >~ [`eval_stmt _ (Return (SOME _))`] >- suspend "return_stmt"
  >~ [`eval_stmt _ (Raise (RaiseReason _))`] >- suspend "raise_reason"
  >~ [`eval_stmt _ (Assert _ AssertBare)`] >- suspend "assert_bare"
  >~ [`eval_stmt _ (Assert _ AssertUnreachable)`] >- suspend "assert_unreachable"
  >~ [`eval_stmt _ (Raise (RaiseCustomError _))`] >- suspend "raise_custom"
  >~ [`eval_stmt _ (Assert _ (AssertCustomError _))`] >- suspend "assert_custom"
  >~ [`eval_stmt _ (Assert _ (AssertReason _))`] >- suspend "assert_reason"
  >~ [`eval_stmt _ (For _ _ _ _ _)`] >- suspend "for_entry"
  >>~- ([`eval_stmt _ _`],
    strip_tac >> metis_tac[body_terminal_stmt_storage, runtime_storage_consistent_storage]) >>
  all_tac
  >~ [`eval_for _ _ _ _ []`] >-
    (rpt strip_tac >> metis_tac[body_eval_for_nil_storage, runtime_storage_consistent_storage])
  >~ [`eval_for _ _ _ _ (_::_)`] >- suspend "for_cons"
  >~ [`assign_tuple_target_list _ (_::_) (_::_)`] >-
    (strip_tac >> match_mp_tac (SRULE [] body_tuple_list_cons_consumer) >>
     conj_tac >> first_assum ACCEPT_TAC)
  >~ [`assign_tuple_targets _ (BaseTarget _) _`] >-
    (strip_tac >> match_mp_tac body_tuple_base_consumer >> first_assum ACCEPT_TAC)
  >~ [`assign_tuple_targets _ (TupleTarget _) _`] >-
    (strip_tac >> match_mp_tac body_tuple_nested_consumer >> first_assum ACCEPT_TAC)
  >>~- ([`assign_tuple_target_list _ _ _`],
    rpt strip_tac >> gvs[Once evaluate_def, return_def, raise_def] >>
    metis_tac[runtime_storage_consistent_storage]) >>
  all_tac
  >~ [`eval_expr _ (Name _ _)`] >- suspend "name_expr"
  >~ [`eval_expr _ (TopLevelName _ _)`] >- suspend "global_expr"
  >~ [`eval_expr _ (FlagMember _ _ _)`] >- suspend "flag_expr"
  >~ [`eval_expr _ (Literal _ _)`] >- suspend "literal_expr"
  >~ [`eval_expr _ (IfExp _ _ _ _)`] >- suspend "if_expr"
  >~ [`eval_expr _ (Call _ (RawCallTarget _) _ _)`] >-
    (strip_tac >> rpt gen_tac >> strip_tac >>
     gvs[expr_has_evm_run_def, supported_expr_exists_def, expr_evm_run_root_def,
         int_calls_expr_def] >>
     reverse conj_tac
     >- (rpt strip_tac >> gvs[Once well_typed_expr_def]) >>
     strip_tac >>
     qpat_x_assum `well_typed_expr env (Call _ _ _ _)`
       (strip_assume_tac o SRULE [Once well_typed_expr_def]) >>
     irule exprOracleStorageInterfacesTheory.eval_raw_call_expr_oracle_storage >>
     rpt (goal_assum (drule_at Any)) >>
     reverse conj_tac >- metis_tac[runtime_storage_consistent_storage] >>
     rpt strip_tac
     >~ [`eval_exprs _ _ _ = _`]
     >- (first_x_assum irule >> qexists_tac `env` >>
         first_assum (irule_at Any) >> fs[]) >>
     metis_tac[runtime_storage_consistent_storage])
  >~ [`eval_expr _ (Call _ (RawCallCalldataTarget _) _ _)`] >-
    (strip_tac >> rpt gen_tac >> strip_tac >>
     gvs[expr_has_evm_run_def, supported_expr_exists_def, expr_evm_run_root_def,
         int_calls_expr_def] >>
     reverse conj_tac
     >- (rpt strip_tac >> gvs[Once well_typed_expr_def]) >>
     strip_tac >>
     qpat_x_assum `well_typed_expr env (Call _ _ _ _)`
       (strip_assume_tac o SRULE [Once well_typed_expr_def]) >>
     irule exprOracleStorageInterfacesTheory.eval_raw_call_calldata_expr_oracle_storage >>
     rpt (goal_assum (drule_at Any)) >>
     reverse conj_tac >- metis_tac[runtime_storage_consistent_storage] >>
     rpt strip_tac
     >~ [`eval_exprs _ _ _ = _`]
     >- (first_x_assum irule >> qexists_tac `env` >>
         first_assum (irule_at Any) >> fs[]) >>
     metis_tac[runtime_storage_consistent_storage])
  >~ [`eval_expr _ (Call _ (CreateTarget _ _ _ _) _ _)`] >-
    (rpt strip_tac >> gvs[expr_has_evm_run_def, supported_expr_exists_def, expr_evm_run_root_def])
  >~ [`eval_exprs _ []`] >-
    (rpt strip_tac >> gvs[Once evaluate_def, return_def, runtime_storage_consistent_def])
  >~ [`eval_expr_results _ []`] >-
    (rpt strip_tac >> gvs[Once evaluate_def, return_def, runtime_storage_consistent_def])
  >~ [`eval_base_place _ (NameTarget _)`] >- suspend "name_target"
  >~ [`eval_base_place _ (TopLevelNameTarget _)`] >- suspend "global_target"
  >~ [`eval_expr _ (StructLit _ _ _)`] >- suspend "struct_expr"
  >~ [`eval_expr _ (Attribute _ _ _)`] >- suspend "attribute_expr"
  >~ [`eval_expr _ (Pop _ _)`] >- suspend "pop_expr"
  >~ [`eval_target_place _ _`] >- suspend "target_place"
  >~ [`eval_base_place _ (AttributeTarget _ _)`] >- suspend "attribute_target" >>
  all_tac
  >~ [`eval_expr_results _ (_::_)`] >- suspend "results_cons"
  >~ [`eval_exprs _ (_::_)`] >- suspend "exprs_cons"
  >~ [`eval_base_place _ (SubscriptTarget _ _)`] >- suspend "subscript_target"
  >~ [`eval_expr _ (Call _ RawRevert _ _)`] >- suspend "raw_revert"
  >~ [`eval_expr _ (Call _ RawLog _ _)`] >- suspend "raw_log"
  >~ [`eval_expr _ (Call _ SelfDestructTarget _ _)`] >- suspend "selfdestruct"
  >~ [`eval_expr _ (TypeBuiltin _ _ _ _)`] >- suspend "type_builtin"
  >~ [`eval_expr _ (Subscript _ _ _)`] >- suspend "subscript_expr" >>
  all_tac
  >~ [`eval_expr _ (Builtin _ _ _)`] >- suspend "builtin_expr"
  >~ [`eval_expr _ (Call _ (Send _) _ _)`] >- suspend "send_expr" >>
  suspend "ext_call"
QED

Resume body_oracle_storage_mutual[ext_call]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[expr_has_evm_run_def, supported_expr_exists_def, int_calls_expr_def] >>
  reverse conj_tac
  >- (rpt strip_tac >> gvs[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_assum `well_typed_expr env (Call _ (ExtCall _ _ _ _) _ _)`
    (strip_assume_tac o SRULE [Once well_typed_expr_def]) >>
  `well_typed_exprs env es` by metis_tac[vyperTypeBuiltinsTheory.ext_call_args_typed] >>
  PairCases_on `sig` >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  `well_typed_exprs env (TAKE 1 es) /\
   well_typed_exprs env (TAKE (LENGTH sig1) (DROP 1 es)) /\
   well_typed_exprs env (DROP (1 + LENGTH sig1) es)` by
    metis_tac[vyperTypeEvalSoundnessTheory.well_typed_exprs_TAKE,
              vyperTypeEvalSoundnessTheory.well_typed_exprs_DROP] >>
  `~supported_exprs_exists expr_evm_run_root (TAKE 1 es) /\
   ~supported_exprs_exists expr_evm_run_root (TAKE (LENGTH sig1) (DROP 1 es)) /\
   ~supported_exprs_exists expr_evm_run_root (DROP (1 + LENGTH sig1) es)` by
    (gvs[exprOracleStorageInterfacesTheory.supported_exprs_exists_not_every] >>
     metis_tac[rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP]) >>
  `EVERY (\c. FST c = NONE) (int_calls_exprs (TAKE 1 es)) /\
   EVERY (\c. FST c = NONE) (int_calls_exprs (TAKE (LENGTH sig1) (DROP 1 es))) /\
   EVERY (\c. FST c = NONE) (int_calls_exprs (DROP (1 + LENGTH sig1) es))` by
    metis_tac[body_exprs_main_calls_every, rich_listTheory.EVERY_TAKE,
              rich_listTheory.EVERY_DROP] >>
  `call_evaluation_safe cx (int_calls_exprs (TAKE 1 es)) /\
   call_evaluation_safe cx (int_calls_exprs (TAKE (LENGTH sig1) (DROP 1 es))) /\
   call_evaluation_safe cx (int_calls_exprs (DROP (1 + LENGTH sig1) es))` by
    metis_tac[vyperTypeEvalSoundnessTheory.call_evaluation_safe_exprs_TAKE,
              vyperTypeEvalSoundnessTheory.call_evaluation_safe_exprs_DROP] >>
  gvs[arithmeticTheory.ADD_COMM] >>
  qpat_assum `eval_expr _ (Call _ (ExtCall _ _ _ _) _ _) _ = _`
    (mp_then (Pos last) mp_tac body_eval_ext_call_storage) >>
  disch_then irule >> simp[] >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  qexists_tac `env` >> simp[] >> rpt strip_tac >> metis_tac[]
QED

Resume body_oracle_storage_mutual[send_expr]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[expr_has_evm_run_def, supported_expr_exists_def, int_calls_expr_def] >>
  reverse conj_tac
  >- (rpt strip_tac >> gvs[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_assum `well_typed_expr env (Call _ (Send _) _ _)`
    (strip_assume_tac o SRULE [Once well_typed_expr_def]) >>
  irule body_eval_send_storage >> rpt (goal_assum (drule_at Any)) >>
  reverse conj_tac >- metis_tac[runtime_storage_consistent_storage] >>
  rpt strip_tac >>
  qpat_x_assum `!s'' t. type_check _ _ _ = _ ==> _`
    (qspecl_then [`st`,`st`] mp_tac) >>
  simp[type_check_def, assert_def, return_def] >> metis_tac[]
QED

Resume body_oracle_storage_mutual[builtin_expr]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[expr_has_evm_run_def, supported_expr_exists_def, int_calls_expr_def] >>
  reverse conj_tac
  >- (rpt strip_tac >> gvs[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_assum `well_typed_expr env (Builtin ty bt es)`
    (strip_assume_tac o SRULE [Once well_typed_expr_def]) >>
  `builtin_args_length_ok bt (LENGTH es)` by
    (drule vyperTypeBuiltinsTheory.well_typed_builtin_app_length >> simp[]) >>
  Cases_on `bt = Env MsgGas`
  >- suspend "builtin_gas" >>
  irule body_eval_builtin_storage >> rpt (goal_assum (drule_at Any)) >>
  suspend "builtin_args"
QED

Resume body_oracle_storage_mutual[builtin_gas]:
  gvs[] >>
  qpat_x_assum `eval_expr _ (Builtin _ _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, type_check_def, assert_def, bind_def,
       ignore_bind_def, return_def] >>
  Cases_on `next_gas_reading st` >>
  imp_res_tac vyperStatePreservationTheory.next_gas_reading_state >>
  Cases_on `q` >> gvs[return_def, raise_def] >>
  rpt strip_tac >> gvs[] >>
  irule contract_storage_well_formed_backends_frame >>
  qexists_tac `st` >> simp[] >> metis_tac[runtime_storage_consistent_storage]
QED

Resume body_oracle_storage_mutual[builtin_args]:
  reverse conj_tac
  >- (conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `!s'' t. _ /\ bt <> Len /\ _ ==> _`
            (qspecl_then [`st`,`st`] mp_tac) >>
          simp[type_check_def, assert_def, return_def] >> metis_tac[]) >>
      metis_tac[runtime_storage_consistent_storage]) >>
  rpt strip_tac >>
  `es <> []` by
    (Cases_on `es` >> gvs[well_typed_builtin_app_def]) >>
  `well_typed_expr env (HD es) /\
   ~supported_expr_exists expr_evm_run_root (HD es) /\
   EVERY (\c. FST c = NONE) (int_calls_expr (HD es)) /\
   call_evaluation_safe cx (int_calls_expr (HD es))` by
    (Cases_on `es` >> gvs[well_typed_expr_def, supported_expr_exists_def,
       int_calls_expr_def] >> metis_tac[call_evaluation_safe_append_left]) >>
  qpat_x_assum `!s'' t. _ /\ bt = Len ==> _`
    (qspecl_then [`st`,`st`] mp_tac) >>
  simp[type_check_def, assert_def, return_def] >> metis_tac[]
QED

Resume body_oracle_storage_mutual[subscript_expr]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[expr_has_evm_run_def, supported_expr_exists_def, int_calls_expr_def] >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  conj_tac >> rpt strip_tac >> (
  `well_typed_expr env e' /\
   (well_typed_expr env e \/ ?base_vt. type_place_expr env e = SOME base_vt)` by
    (gvs[Once well_typed_expr_def, AllCaseEqs()] >> metis_tac[]) >> (
  qpat_assum `eval_expr _ (Subscript _ _ _) _ = _`
    (mp_then (Pos last) mp_tac body_eval_subscript_storage) >>
  disch_then irule >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!env' st'' res' st'3'. _`
        (qspecl_then [`env`,`st`,`r`,`s'`] mp_tac) >> simp[] >> metis_tac[]) >>
  simp[] >> qexists_tac `env` >> simp[] >> rpt strip_tac >> metis_tac[]))
QED

Resume body_oracle_storage_mutual[raw_revert]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[expr_has_evm_run_def, supported_expr_exists_def, int_calls_expr_def] >>
  reverse conj_tac
  >- (rpt strip_tac >> gvs[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_assum `well_typed_expr env (Call _ _ _ _)`
    (strip_assume_tac o SRULE [Once well_typed_expr_def]) >>
  irule body_eval_raw_revert_storage >> rpt (goal_assum (drule_at Any)) >>
  rpt strip_tac >> metis_tac[]
QED

Resume body_oracle_storage_mutual[raw_log]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[expr_has_evm_run_def, supported_expr_exists_def, int_calls_expr_def] >>
  reverse conj_tac
  >- (rpt strip_tac >> gvs[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_assum `well_typed_expr env (Call _ _ _ _)`
    (strip_assume_tac o SRULE [Once well_typed_expr_def]) >>
  irule body_eval_raw_log_storage >> rpt (goal_assum (drule_at Any)) >>
  rpt strip_tac >> metis_tac[]
QED

Resume body_oracle_storage_mutual[selfdestruct]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[expr_has_evm_run_def, supported_expr_exists_def, int_calls_expr_def] >>
  reverse conj_tac
  >- (rpt strip_tac >> gvs[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_assum `well_typed_expr env (Call _ _ _ _)`
    (strip_assume_tac o SRULE [Once well_typed_expr_def]) >>
  irule body_eval_selfdestruct_storage >> rpt (goal_assum (drule_at Any)) >>
  rpt strip_tac >> metis_tac[]
QED

Resume body_oracle_storage_mutual[type_builtin]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[expr_has_evm_run_def, supported_expr_exists_def, int_calls_expr_def] >>
  reverse conj_tac
  >- (rpt strip_tac >> gvs[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_assum `well_typed_expr env (TypeBuiltin _ _ _ _)`
    (strip_assume_tac o SRULE [Once well_typed_expr_def]) >>
  irule body_eval_type_builtin_storage >> rpt (goal_assum (drule_at Any)) >>
  reverse conj_tac >- metis_tac[runtime_storage_consistent_storage] >>
  rpt strip_tac >>
  qpat_x_assum `!s'' t. type_check _ _ _ = _ ==> _`
    (qspecl_then [`st`,`st`] mp_tac) >>
  simp[type_check_def, assert_def, return_def] >> metis_tac[]
QED

Resume body_oracle_storage_mutual[subscript_target]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[supported_expr_exists_def, int_calls_expr_def] >>
  qpat_assum `type_place_target env (SubscriptTarget _ _) = _`
    (strip_assume_tac o SRULE [vyperTypeEnvTheory.type_place_target_SubscriptTarget]) >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  irule body_eval_subscript_target_storage >>
  rpt (goal_assum (drule_at Any)) >>
  rpt strip_tac >> metis_tac[expr_has_evm_run_def]
QED

Resume body_oracle_storage_mutual[results_cons]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[supported_expr_exists_def, int_calls_expr_def, Once well_typed_expr_def] >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  irule body_eval_expr_results_cons_storage >>
  rpt (goal_assum (drule_at Any)) >>
  rpt strip_tac >> metis_tac[expr_has_evm_run_def]
QED

Resume body_oracle_storage_mutual[exprs_cons]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[supported_expr_exists_def, int_calls_expr_def, Once well_typed_expr_def] >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  irule body_eval_exprs_cons_storage >>
  rpt (goal_assum (drule_at Any)) >>
  rpt strip_tac >> metis_tac[expr_has_evm_run_def]
QED

Resume body_oracle_storage_mutual[target_place]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[well_typed_target_def] >>
  qpat_assum `eval_target_place _ _ _ = _`
    (mp_then (Pos last) mp_tac body_eval_target_place_storage) >>
  disch_then irule >> rpt strip_tac >> metis_tac[]
QED

Resume body_oracle_storage_mutual[attribute_target]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[supported_expr_exists_def, int_calls_expr_def] >>
  qpat_assum `type_place_target env (AttributeTarget _ _) = _`
    (strip_assume_tac o SRULE [vyperTypeEnvTheory.type_place_target_AttributeTarget]) >>
  qpat_assum `eval_base_place _ (AttributeTarget _ _) _ = _`
    (mp_then (Pos last) mp_tac body_eval_attribute_target_storage) >>
  disch_then irule >> rpt strip_tac >> metis_tac[]
QED

Resume body_oracle_storage_mutual[pop_expr]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[expr_has_evm_run_def] >>
  irule body_oracle_pop_case >> rpt (goal_assum (drule_at Any)) >>
  simp[] >> rpt strip_tac >> metis_tac[]
QED

Resume body_oracle_storage_mutual[struct_expr]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[expr_has_evm_run_def, supported_expr_exists_def, int_calls_expr_def] >>
  reverse conj_tac
  >- (rpt strip_tac >> gvs[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_assum `well_typed_expr env (StructLit _ _ _)`
    (strip_assume_tac o SRULE [Once well_typed_expr_def]) >>
  `well_typed_exprs env (MAP SND kes)` by
    (irule vyperTypeEvalSoundnessTheory.well_typed_named_exprs_MAP_SND_stmt >> simp[]) >>
  `~supported_exprs_exists expr_evm_run_root (MAP SND kes)` by
    gvs[exprOracleStorageInterfacesTheory.supported_exprs_exists_not_every,
        exprOracleStorageInterfacesTheory.supported_fields_exists_not_every] >>
  `int_calls_exprs (MAP SND kes) = int_calls_named_exprs kes` by
    (POP_ASSUM_LIST (K all_tac) >> Induct_on `kes` >> simp[int_calls_expr_def] >>
     gen_tac >> PairCases_on `h` >> simp[int_calls_expr_def]) >>
  qpat_assum `eval_expr _ (StructLit _ _ _) _ = _`
    (mp_then (Pos last) mp_tac body_eval_struct_storage) >>
  disch_then irule >> rpt strip_tac >>
  first_x_assum (qspecl_then [`env`,`st`,`r`,`s`] mp_tac) >> simp[]
QED

Resume body_oracle_storage_mutual[attribute_expr]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[expr_has_evm_run_def, supported_expr_exists_def, int_calls_expr_def] >>
  qpat_assum `eval_expr _ (Attribute _ _ _) _ = _`
    (mp_then (Pos last) mp_tac body_eval_attribute_storage) >>
  disch_then (fn th => conj_tac >> rpt strip_tac >> mp_tac th) >>
  (impl_tac >- (rpt strip_tac >>
    qpat_x_assum `!a b c d. _` (qspecl_then [`env`,`st`,`r`,`s`] mp_tac) >>
    gvs[Once well_typed_expr_def, AllCaseEqs()])) >> simp[]
QED

Resume body_oracle_storage_mutual[name_target]:
  rpt strip_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, type_check_def,
       assert_def, ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[runtime_storage_consistent_def]
QED

Resume body_oracle_storage_mutual[global_target]:
  rpt strip_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  pure_once_rewrite_tac [evaluate_def] >> strip_tac >>
  imp_res_tac lookup_global_state >> gvs[runtime_storage_consistent_def]
QED

Resume body_oracle_storage_mutual[if_expr]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[expr_has_evm_run_def, supported_expr_exists_def, int_calls_expr_def,
      EVERY_APPEND] >>
  reverse conj_tac
  >- (rpt strip_tac >> gvs[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_assum `well_typed_expr env (IfExp _ _ _ _)`
    (strip_assume_tac o SRULE [Once well_typed_expr_def]) >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e) /\
   call_evaluation_safe cx (int_calls_expr e') /\
   call_evaluation_safe cx (int_calls_expr e'')` by
    metis_tac[call_evaluation_safe_append_left, call_evaluation_safe_append_right] >>
  qpat_assum `eval_expr _ (IfExp _ _ _ _) _ = _`
    (mp_then (Pos last) mp_tac body_eval_if_storage) >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!a b c d. _` (qspecl_then [`env`,`st`,`r`,`s`] mp_tac) >> simp[]) >>
  qexists_tac `env` >> simp[] >> conj_tac >> rpt strip_tac >>
  first_assum (fn th =>
    drule_then (qspec_then `env` mp_tac) th >>
    disch_then (qspecl_then [`s`,`r`,`s'`] mp_tac) >> simp[] >> NO_TAC)
QED

Resume body_oracle_storage_mutual[name_expr]:
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, get_scopes_def, type_check_def, assert_def, ignore_bind_def,
       bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[runtime_storage_consistent_def]
QED

Resume body_oracle_storage_mutual[global_expr]:
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >>
  imp_res_tac lookup_global_state >> gvs[runtime_storage_consistent_def]
QED

Resume body_oracle_storage_mutual[flag_expr]:
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >>
  imp_res_tac lookup_flag_mem_state >>
  gvs[runtime_storage_consistent_def] >> rpt strip_tac >> gvs[]
QED

Resume body_oracle_storage_mutual[literal_expr]:
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, return_def] >>
  strip_tac >> gvs[runtime_storage_consistent_def]
QED

Resume body_oracle_storage_mutual[for_cons]:
  strip_tac >> match_mp_tac (SRULE [] body_for_cons_consumer) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      rename1 `push_scope_with_var _ _ _ _ = (INL x,_)` >> Cases_on `x` >>
      gvs[] >> first_assum match_mp_tac >> rpt (goal_assum (drule_at Any))) >>
  rpt gen_tac >> strip_tac >>
  rename1 `push_scope_with_var _ _ _ _ = (INL x,_)` >> Cases_on `x` >>
  first_assum drule >> simp[]
QED

Resume body_oracle_storage_mutual[assign_base]:
  strip_tac >> match_mp_tac body_assign_base_consumer >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Resume body_oracle_storage_mutual[if_stmt]:
  strip_tac >> match_mp_tac body_if_consumer >>
  conj_tac
  >- (rpt gen_tac >> rename1 `push_scope s = (INL x,t)` >>
      Cases_on `x` >> first_assum MATCH_ACCEPT_TAC) >>
  conj_tac
  >- (rpt gen_tac >> rename1 `push_scope s = (INL x,t)` >>
      Cases_on `x` >> first_assum MATCH_ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

Resume body_oracle_storage_mutual[annassign]:
  strip_tac >> match_mp_tac body_annassign_consumer >>
  rpt gen_tac >> strip_tac >> gvs[] >> first_assum drule >> simp[]
QED

Resume body_oracle_storage_mutual[log_stmt]:
  strip_tac >> match_mp_tac body_log_consumer >> first_assum ACCEPT_TAC
QED

Resume body_oracle_storage_mutual[append_stmt]:
  strip_tac >> match_mp_tac body_append_consumer >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Resume body_oracle_storage_mutual[augassign]:
  strip_tac >> match_mp_tac body_augassign_consumer >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Resume body_oracle_storage_mutual[assign_tuple]:
  strip_tac >> match_mp_tac body_assign_tuple_consumer >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Resume body_oracle_storage_mutual[expr_stmt]:
  rename1 `eval_stmt cx (Expr e)` >>
  strip_tac >> drule body_single_expr_stmt_consumer >>
  disch_then (qspec_then `Expr e` mp_tac) >> simp[]
QED

Resume body_oracle_storage_mutual[return_stmt]:
  rename1 `eval_stmt cx (Return (SOME e))` >>
  strip_tac >> drule body_single_expr_stmt_consumer >>
  disch_then (qspec_then `Return (SOME e)` mp_tac) >> simp[]
QED

Resume body_oracle_storage_mutual[raise_reason]:
  rename1 `eval_stmt cx (Raise (RaiseReason e))` >>
  strip_tac >> drule body_single_expr_stmt_consumer >>
  disch_then (qspec_then `Raise (RaiseReason e)` mp_tac) >> simp[]
QED

Resume body_oracle_storage_mutual[assert_bare]:
  rename1 `eval_stmt cx (Assert e AssertBare)` >>
  strip_tac >> drule body_single_expr_stmt_consumer >>
  disch_then (qspec_then `Assert e AssertBare` mp_tac) >> simp[]
QED

Resume body_oracle_storage_mutual[assert_unreachable]:
  rename1 `eval_stmt cx (Assert e AssertUnreachable)` >>
  strip_tac >> drule body_single_expr_stmt_consumer >>
  disch_then (qspec_then `Assert e AssertUnreachable` mp_tac) >> simp[]
QED

Resume body_oracle_storage_mutual[raise_custom]:
  strip_tac >> match_mp_tac body_raise_custom_consumer >> first_assum ACCEPT_TAC
QED

Resume body_oracle_storage_mutual[assert_custom]:
  strip_tac >> match_mp_tac body_assert_custom_consumer >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Resume body_oracle_storage_mutual[assert_reason]:
  strip_tac >> match_mp_tac body_assert_reason_consumer >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Resume body_oracle_storage_mutual[for_entry]:
  strip_tac >> match_mp_tac body_for_entry_consumer >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      rename1 `check _ _ _ = (INL x,_)` >> Cases_on `x` >>
      gvs[] >> first_assum match_mp_tac >>
      rpt (goal_assum (drule_at Any))) >>
  rpt gen_tac >> strip_tac >> gvs[] >> first_assum match_mp_tac >>
  rpt (goal_assum (drule_at Any))
QED

Resume body_oracle_storage_mutual[intcall_start]:
  strip_tac >>
  qpat_x_assum `!a b c d e f g h i j k l m n p q r s. _ ==> _`
    (mk_asm "default_ih") >>
  qpat_x_assum `!a. _` (mk_asm "intcall_ih1") >>
  qpat_x_assum `!a. _` (mk_asm "intcall_ih2") >>
  rpt gen_tac >> strip_tac >> reverse conj_tac
  >- (rpt strip_tac >> gvs[Once well_typed_expr_def]) >>
  strip_tac >>
  gvs[int_calls_expr_def, EVERY_APPEND, expr_has_evm_run_def,
      supported_expr_exists_def] >>
  Cases_on `MEM (NONE,fn) cx.stk`
  >- (asm_x "intcall_ih1" kall_tac >> asm_x "intcall_ih2" kall_tac >>
      asm_x "default_ih" kall_tac >>
      gvs[Once evaluate_def, type_check_def, assert_def, raise_def,
          ignore_bind_apply] >>
      drule runtime_storage_consistent_storage >> simp[]) >>
  Cases_on `lookup_callable_function cx.in_deploy fn tops`
  >- (asm_x "intcall_ih1" kall_tac >> asm_x "intcall_ih2" kall_tac >>
      asm_x "default_ih" kall_tac >>
      gvs[Once evaluate_def, type_check_def, assert_def, lift_option_type_def,
          return_def, raise_def, ignore_bind_apply, bind_apply] >>
      drule runtime_storage_consistent_storage >> simp[]) >>
  rename1 `lookup_callable_function cx.in_deploy fn tops = SOME tup` >>
  PairCases_on `tup` >>
  rename1 `lookup_callable_function cx.in_deploy fn tops =
             SOME (mut,nr,args,dflts,ret,ss)` >>
  drule_all supported_callable_storage_syntax >> strip_tac >> gvs[] >>
  Cases_on `LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts`
  >- (pop_assum strip_assume_tac >> suspend "intcall_live") >>
  asm_x "intcall_ih1" kall_tac >> asm_x "intcall_ih2" kall_tac >>
  asm_x "default_ih" kall_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, type_check_def, assert_def, lift_option_type_def,
       return_def, raise_def, ignore_bind_apply, bind_apply] >>
  strip_tac >> gvs[] >> metis_tac[runtime_storage_consistent_storage]
QED

Resume body_oracle_storage_mutual[intcall_live]:
  asm_x "intcall_ih1" mp_tac >> simp[] >> disch_then assume_tac >>
  asm_x "intcall_ih2" mp_tac >> simp[] >> disch_then assume_tac >>
  asm_x "default_ih" mp_tac >> simp[] >> disch_then (mk_asm "default_ih") >>
  rule_assum_tac (SRULE [type_check_def, assert_def, return_def,
                        get_scopes_def]) >>
  Cases_on `eval_expr_results cx es st` >>
  rename1 `eval_expr_results cx es st = (args_res,args_st)` >>
  drule_all eval_expr_intcall_defaults_step >>
  disch_then (fn th => qpat_x_assum `eval_expr _ _ _ = _` (mp_tac o REWRITE_RULE [th])) >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `(NONE,fn)::int_calls_exprs es` >> simp[]) >>
  qpat_x_assum `well_typed_expr _ (Call _ (IntCall _) _ _)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  `contract_storage_well_formed cx args_st` by
    (qpat_x_assum `!env st res st'. well_typed_exprs _ _ /\ _ ==> _` drule_all >>
     simp[]) >>
  Cases_on `args_res` >> pure_rewrite_tac [sumTheory.sum_case_def] >> BETA_TAC
  >- suspend "intcall_args_success" >>
  strip_tac >> gvs[]
QED

Resume body_oracle_storage_mutual[intcall_args_success]:
  rename1 `eval_expr_results cx es st = (INL actual_results,args_st)` >>
  `runtime_consistent env cx st` by
    metis_tac[runtime_storage_consistent_runtime] >>
  `runtime_consistent env cx args_st` by
    (fs[runtime_consistent_def] >>
     drule_all (cj 1 (SPEC_ALL (cj 11 vyperTypeEvalSoundnessTheory.eval_scc_type_sound_results_mutual))) >> simp[]) >>
  `expr_results_typed (env,cx,args_st) es actual_results` by
    (qpat_assum `runtime_consistent env cx st`
       (strip_assume_tac o SRULE [runtime_consistent_def]) >>
     drule_all (cj 1 (SPEC_ALL (cj 11 vyperTypeEvalSoundnessTheory.eval_scc_type_sound_results_mutual))) >> simp[]) >>
  `runtime_storage_consistent env cx args_st /\
   IS_SOME args_st.outcomes /\ oracle_storage_ok cx args_st` by
    (irule body_oracle_storage_entry_transfer >> simp[] >>
     qexists_tac `st` >> simp[] >>
     drule eval_expr_results_outcome_suffix >> simp[]) >>
  qpat_x_assum `!env0 s0 r0 s1. well_typed_exprs _ _ /\ _ ==> _` kall_tac >>
  Cases_on `finally (do set_scopes [FEMPTY];
                       eval_exprs (cx with stk updated_by CONS (NONE,fn))
                         (DROP (LENGTH dflts + LENGTH es - LENGTH args) dflts) od)
              (set_scopes args_st.scopes) args_st` >>
  rename1 `_ = (dflt_res,d_st)` >>
  `d_st.scopes = args_st.scopes /\ runtime_storage_consistent env cx d_st /\
   IS_SOME d_st.outcomes /\ oracle_storage_ok cx d_st /\
   expr_results_typed (env,cx,d_st) es actual_results` by
    (`env_consistent env cx args_st` by fs[runtime_consistent_def] >>
     `IS_SOME (FLOOKUP env.fn_sigs (NONE,fn))` by simp[] >>
     drule_all vyperTypeEvalSoundnessTheory.callable_body_typing_from_env_consistent >>
     strip_tac >>
     `call_evaluation_safe (cx with stk updated_by CONS (NONE,fn))
        (int_calls_exprs (DROP (LENGTH dflts + LENGTH es - LENGTH args) dflts))` by
       (irule vyperTypeCallStackSoundnessTheory.call_evaluation_safe_push_needed_defaults >>
        metis_tac[]) >>
     `runtime_storage_consistent (defaults_env env_body)
        (cx with stk updated_by CONS (NONE,fn)) (args_st with scopes := [FEMPTY]) /\
      functions_well_typed (cx with stk updated_by CONS (NONE,fn))` by
       (irule vyperTypeEvalStoragePreservationTheory.intcall_defaults_runtime_storage_consistent >>
        simp[] >> qexists_tac `env` >> simp[]) >>
     `!r1 s1. eval_exprs (cx with stk updated_by CONS (NONE,fn))
         (DROP (LENGTH dflts + LENGTH es - LENGTH args) dflts)
         (args_st with scopes := [FEMPTY]) = (r1,s1) ==>
       contract_storage_well_formed cx s1` by
       (rpt strip_tac >>
        qsuff_tac `contract_storage_well_formed
          (cx with stk updated_by CONS (NONE,fn)) s1`
        >- simp[vyperTypeEvalStoragePreservationTheory.contract_storage_well_formed_stk] >>
        mp_tac (Q.INST [`st` |-> `args_st`, `f` |-> `CONS (NONE,fn)`,
                        `scopes` |-> `[FEMPTY]`] body_oracle_storage_frame_entry) >>
        impl_tac >- simp[] >> strip_tac >>
        `oracle_storage_ok cx (args_st with scopes := [FEMPTY])` by
          fs[oracle_storage_ok_payload] >>
        asm_x "default_ih" irule >>
        simp[supported_exprs_exists_DROP, int_calls_exprs_DROP_EVERY,
             get_scopes_def, set_scopes_def, type_check_def, assert_def,
             return_def] >>
        conj_tac
        >- (qexists_tac `tops` >> fs[vyperContextTheory.get_module_code_def]) >>
        conj_tac >- (goal_assum (drule_at Any)) >>
        qexistsl_tac [`defaults_env env_body`, `r1`,
                      `args_st with scopes := [FEMPTY]`] >>
        simp[vyperTypeEvalSoundnessTheory.well_typed_exprs_DROP]) >>
     irule bodyStorageIntcallDefaultsTheory.intcall_defaults_oracle_storage >>
     simp[] >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `runtime_consistent env cx d_st` by
    metis_tac[runtime_storage_consistent_runtime] >>
  `contract_storage_well_formed cx d_st` by
    metis_tac[runtime_storage_consistent_storage] >>
  reverse (Cases_on `dflt_res`) >- (simp[] >> strip_tac >> gvs[]) >>
  simp[Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "lift_option_type_def",
       Excl "is_view_mut_def"] >>
  rename1 `_ = (INL dflt_vs,d_st)` >>
  simp_tac bool_ss [bind_def, ignore_bind_def] >>
  Cases_on `read_results cx actual_results d_st` >>
  rename1 `read_results cx actual_results d_st = (read_res,read_st)` >>
  drule read_results_state >> strip_tac >>
  gvs[Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "lift_option_type_def"] >>
  Cases_on `read_res` >>
  gvs[Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "lift_option_type_def"]
  >- suspend "intcall_read_success" >>
  rpt strip_tac >> gvs[]
QED

Resume body_oracle_storage_mutual[intcall_read_success]:
  rename1 `read_results cx actual_results d_st = (INL vs,d_st)` >>
  Cases_on `bind_arguments (get_tenv cx) args (vs ++ dflt_vs)`
  >- (simp[lift_option_type_def, raise_def] >> rpt strip_tac >> gvs[]) >>
  rename1 `bind_arguments (get_tenv cx) args (vs ++ dflt_vs) = SOME call_env` >>
  `env_consistent env cx d_st` by fs[runtime_consistent_def] >>
  `IS_SOME (FLOOKUP env.fn_sigs (NONE,fn))` by simp[] >>
  drule_all vyperTypeEvalSoundnessTheory.callable_body_typing_from_env_consistent >>
  strip_tac >>
  (`scope_well_typed call_env` by
    metis_tac[vyperTypeBindArgumentsTheory.bind_arguments_scope_well_typed_from_success] >>
  `env_scopes_consistent env_body cx (d_st with scopes := [call_env])` by
    (drule vyperTypeBindArgumentsTheory.bind_arguments_env_scopes_consistent >>
     disch_then irule >> simp[] >> metis_tac[]) >>
  asm_simp_tac std_ss [Once lift_option_type_def, return_def] >>
  asm_simp_tac std_ss [Once lift_option_type_def, return_def] >>
  simp[Excl "lock_if_nr_def", Excl "unlock_if_nr_def",
       Excl "lift_option_type_def", Excl "is_view_mut_def"] >>
  Cases_on `lock_if_nr cx nr (is_view_mut mut) d_st` >>
  rename1 `lock_if_nr cx nr (is_view_mut mut) d_st = (lock_res,lock_st)` >>
  `storage_layout_safe cx` by metis_tac[runtime_storage_consistent_layout] >>
  drule_all body_intcall_lock_oracle_entry >> strip_tac >>
  rewrite_tac[GSYM is_view_mut_def] >> Cases_on `lock_res` >>
  asm_simp_tac (srw_ss()) [Excl "lock_if_nr_def", Excl "unlock_if_nr_def",
       Excl "lift_option_type_def", Excl "is_view_mut_def"]
  >- suspend "intcall_lock_success" >>
  rpt strip_tac >> gvs[ignore_bind_def])
QED

Resume body_oracle_storage_mutual[intcall_lock_success]:
  markerLib.RESUME_TAC >> Cases_on `x` >>
  (`push_function (NONE,fn) call_env cx lock_st =
      (INL (cx with stk updated_by CONS (NONE,fn)), lock_st with scopes := [call_env])` by
      simp[push_function_def, return_def] >>
   qpat_x_assum `!s0 results t0 prev s1 dflt_vs t1 s2 vs t2 s3 ce t3 s4 rtv t4 s5 t5 s6 cxf t6. _`
      (assume_tac o SIMP_RULE bool_ss [GSYM is_view_mut_def, GSYM lock_if_nr_def]) >>
   drule body_intcall_guard_apply >> disch_then (mk_asm "intcall_guard") >>
   drule_all body_intcall_runtime_frame >> strip_tac >>
   `call_evaluation_safe (cx with stk updated_by CONS (NONE,fn)) (int_calls_stmts ss)` by
     (drule call_evaluation_safe_push_body >> simp[] >>
      disch_then drule >> disch_then drule >> simp[]) >>
   `functions_well_typed (cx with stk updated_by CONS (NONE,fn))` by
     (fs[runtime_consistent_def] >>
      drule_all vyperTypeEvalSoundnessTheory.intcall_default_env_side_conditions >>
      disch_then (qspec_then `fn` mp_tac) >> simp[]) >>
   `!r s. eval_stmts (cx with stk updated_by CONS (NONE,fn)) ss
       (lock_st with scopes := [call_env]) = (r,s) ==>
       contract_storage_well_formed (cx with stk updated_by CONS (NONE,fn)) s` by
     (rpt strip_tac >>
      qpat_x_assum `!fn. runtime_storage_consistent _ _ _ /\ _` (qspec_then `fn` strip_assume_tac) >>
      `get_module_code (cx with stk updated_by CONS (NONE,fn)) NONE = SOME tops` by
        (qpat_x_assum `get_module_code cx NONE = _` mp_tac >>
         simp[vyperContextTheory.get_module_code_def]) >>
      gvs[Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "lift_option_type_def"] >>
      asm_x "intcall_guard" irule >>
      simp[Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
      conj_tac
      >- (rpt (goal_assum (drule_at Any)) >>
          simp[Excl "lock_if_nr_def", is_view_mut_def]) >>
      rpt (goal_assum (drule_at Any)) >> simp[]) >>
   suspend "intcall_return")
QED

Resume body_oracle_storage_mutual[intcall_return]:
  markerLib.RESUME_TAC >>
  `!r s. eval_stmts (cx with stk updated_by CONS (NONE,fn)) ss
       (lock_st with scopes := [call_env]) = (r,s) ==>
       contract_storage_well_formed cx s` by
     (`!b s. get_storage (cx with stk updated_by CONS (NONE,fn)) s b = get_storage cx s b` by
        (rpt gen_tac >> Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def]) >>
      rpt strip_tac >> first_x_assum drule >>
      simp[contract_storage_well_formed_def,
        vyperLookupStorageTheory.well_formed_storage_def,
        vyperLookupStorageTheory.storage_var_in_range_def,
        vyperStorageBackendTheory.get_storage_backend_eq,
        vyperStorageBackendTheory.get_storage_def]) >>
   simp_tac (srw_ss()) [Once push_function_def, return_def,
     Excl "unlock_if_nr_def", Excl "lock_if_nr_def", Excl "lift_option_type_def"] >> strip_tac >>
   irule (SIMP_RULE bool_ss [bind_def, return_def] body_intcall_return_storage) >>
   goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
   simp_tac bool_ss [GSYM ignore_bind_def] >>
   qpat_x_assum `(case _ of _ => _ | _ => _) = (res,st')`
     (assume_tac o REWRITE_RULE [GSYM ignore_bind_def]) >>
   goal_assum (drule_at Any)
QED

Finalise body_oracle_storage_mutual

Theorem eval_expr_body_oracle_storage:
  !tops cx e env st res st'.
    supported_program tops /\ get_module_code cx NONE = SOME tops /\
    well_typed_expr env e /\
    runtime_storage_consistent env cx st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\
    ~expr_has_evm_run e /\ EVERY (\c. FST c = NONE) (int_calls_expr e) /\
    IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
    eval_expr cx e st = (res, st') ==>
    contract_storage_well_formed cx st'
Proof
  rpt strip_tac >> drule_all (cj 5 body_oracle_storage_mutual) >> simp[]
QED

Theorem eval_stmts_body_oracle_storage:
  (!tops bindings cx s env ret_ty env' st res st'.
     supported_program tops /\ get_module_code cx NONE = SOME tops /\
     supported_stmt tops bindings s /\ type_stmt env ret_ty s = SOME env' /\
     runtime_storage_consistent env cx st /\
     functions_well_typed cx /\
     call_evaluation_safe cx (int_calls_stmt s) /\
     IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
     eval_stmt cx s st = (res, st') ==>
     contract_storage_well_formed cx st') /\
  (!tops bindings cx ss env ret_ty env' st res st'.
     supported_program tops /\ get_module_code cx NONE = SOME tops /\
     supported_stmts tops bindings ss /\ type_stmts env ret_ty ss = SOME env' /\
     runtime_storage_consistent env cx st /\
     functions_well_typed cx /\
     call_evaluation_safe cx (int_calls_stmts ss) /\
     IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
     eval_stmts cx ss st = (res, st') ==>
     contract_storage_well_formed cx st')
Proof
  conj_tac >> rpt strip_tac
  >- (drule (cj 1 supported_stmts_storage_syntax) >> strip_tac >>
      drule_all (cj 1 body_oracle_storage_mutual) >> simp[]) >>
  drule (cj 2 supported_stmts_storage_syntax) >> strip_tac >>
  drule_all (cj 2 body_oracle_storage_mutual) >> simp[]
QED
