(* Conditional branches of the checked selected-prefix schema. *)
Theory guardSourceOrdinaryConditionals
Ancestors
  list guardSourceOrdinarySchema vyperInterpreter vyperState vyperStorageFootprint
  vyperTypeSystem vyperTypeCallGraph vyperEvalMisc vyperStorageTrace
  vyperTypeStmtSoundness vyperTypeExprSoundness vyperTypeCallStackSoundness
  vyperEvalOutcomeSuffix vyperTypeEvalStoragePreservation vyperStatePreservation
  vyperFiniteStoragePreservation
Libs
  guardSourceSchemaLib

Theorem finite_prefix_Expr_IfExp:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Expr_IfExp")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_expr (IfExp ty e1 e2 e3))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e1)` by
    (irule call_evaluation_safe_mono >>
     qexists `int_calls_expr e1 ++ int_calls_expr e2 ++ int_calls_expr e3` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e2)` by
    (irule call_evaluation_safe_mono >>
     qexists `int_calls_expr e1 ++ int_calls_expr e2 ++ int_calls_expr e3` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e3)` by
    (irule call_evaluation_safe_mono >>
     qexists `int_calls_expr e1 ++ int_calls_expr e2 ++ int_calls_expr e3` >> simp[]) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (IfExp _ _ _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  disch_then mp_tac >> simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ (IfExp _ _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e1 st` >> rename1 `eval_expr cx e1 st = (er,st1)` >>
  reverse (Cases_on `er`)
  >- (ntac 2 (qpat_x_assum `!s tv t. eval_expr cx e1 s = (INL tv,t) ==> _` kall_tac) >>
      simp_tac(srw_ss())[] >> strip_tac >>
      qpat_x_assum `st1 = st'` SUBST_ALL_TAC >>
      qpat_x_assum `!initial_st selected env st res st0. _`
        (qspecl_then [`initial_st`, `selected`] mp_tac) >>
      disch_then (irule o cj 1) >> metis_tac[]) >>
  ntac 2 (qpat_x_assum `!s tv t. eval_expr cx e1 s = (INL tv,t) ==> _` drule >> strip_tac) >>
  simp_tac(srw_ss())[switch_BoolV_def, bind_def] >>
  Cases_on `read_result cx x st1` >> rename1 `read_result cx x st1 = (rr,st2)` >>
  `st2 = st1` by metis_tac[read_result_state] >> pop_assum SUBST_ALL_TAC >>
  reverse (Cases_on `rr`)
  >- (simp_tac(srw_ss())[raise_def] >> strip_tac >>
      qpat_x_assum `st1 = st'` SUBST_ALL_TAC >>
      qpat_x_assum `!initial_st selected env st res st0. _ ==> (well_typed_expr env e1 ==> _) /\ _`
        (qspecl_then [`initial_st`, `selected`] mp_tac) >>
      disch_then (irule o cj 1) >> metis_tac[]) >>
  simp_tac(srw_ss())[] >>
  Cases_on `x' = BoolV T` >> pop_assum (fn th => rewrite_tac[th])
  >- (qpat_x_assum `!initial_st selected env st res st0. _ ==> (well_typed_expr env e3 ==> _) /\ _` kall_tac >>
      Cases_on `eval_expr cx e2 st1` >> rename1 `eval_expr cx e2 st1 = (er2,st3)` >>
      strip_tac >>
      `st' = st3` by
        (ntac 2 (qpat_x_assum `!initial_st selected env st res st0. _` kall_tac) >>
         Cases_on `er2` >> gvs[] >> imp_res_tac conditional_result_state >> gvs[]) >>
      qpat_x_assum `st' = st3` SUBST_ALL_TAC >>
      suspend "true_branch") >>
  Cases_on `x' = BoolV F` >> pop_assum (fn th => rewrite_tac[th])
  >- (qpat_x_assum `!initial_st selected env st res st0. _ ==> (well_typed_expr env e2 ==> _) /\ _` kall_tac >>
      Cases_on `eval_expr cx e3 st1` >> rename1 `eval_expr cx e3 st1 = (er2,st3)` >>
      strip_tac >>
      `st' = st3` by
        (ntac 2 (qpat_x_assum `!initial_st selected env st res st0. _` kall_tac) >>
         Cases_on `er2` >> gvs[] >> imp_res_tac conditional_result_state >> gvs[]) >>
      qpat_x_assum `st' = st3` SUBST_ALL_TAC >>
      suspend "false_branch") >>
  simp_tac(srw_ss())[raise_def] >> strip_tac >>
  qpat_x_assum `st1 = st'` SUBST_ALL_TAC >>
  qpat_x_assum `!initial_st selected env st res st0. _ ==> (well_typed_expr env e1 ==> _) /\ _`
    (qspecl_then [`initial_st`, `selected`] mp_tac) >>
  disch_then (irule o cj 1) >> metis_tac[]
QED

(* Both choices use the same sequencing argument; only the selected IH remains. *)
val IFEXP_FINISH =
  `?suffix. st3.storage_trace = st1.storage_trace ++ suffix` by
    metis_tac[storage_trace_frame_prefix, cj 5 evaluate_storage_trace_frame] >>
  `?tail. selected = st1.storage_trace ++ tail` by metis_tac[APPEND_ASSOC] >>
  `storage_well_formed_on cx st1 (FST H) /\
   storage_observations_ok cx H st1.storage_trace` by
    (qpat_x_assum `!initial_st selected env st res st0. _ ==> (well_typed_expr env e1 ==> _) /\ _`
       (qspecl_then [`initial_st`, `selected`] mp_tac) >>
     disch_then (irule o cj 1) >> metis_tac[]) >>
  `runtime_consistent env cx st1` by metis_tac[eval_expr_preserves_runtime_consistent] >>
  `IS_SOME st1.outcomes` by
    (qpat_assum `eval_expr cx e1 st = _` (mp_then Any mp_tac (cj 5 eval_outcome_suffix_mutual)) >>
     disch_then (mp_tac o MATCH_MP outcome_suffix_modes) >>
     Cases_on `st.outcomes` >> Cases_on `st1.outcomes` >> simp[] >> metis_tac[]) >>
  `valid_horizon cx initial_st H st1.storage_trace` by
    (qpat_x_assum `valid_horizon cx initial_st H st.storage_trace` mp_tac >>
     simp_tac(srw_ss())[valid_horizon_def] >> metis_tac[]) >>
  first_x_assum (qspecl_then [`initial_st`, `selected`] mp_tac) >>
  disch_then (irule o cj 1) >> metis_tac[];

Resume finite_prefix_Expr_IfExp[true_branch]:
  IFEXP_FINISH
QED
Resume finite_prefix_Expr_IfExp[false_branch]:
  IFEXP_FINISH
QED
Finalise finite_prefix_Expr_IfExp

Theorem finite_prefix_If:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "If")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (If e ss1 ss2))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_mono >>
     qexists `int_calls_expr e ++ int_calls_stmts ss1 ++ int_calls_stmts ss2` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_stmts ss1)` by
    (irule call_evaluation_safe_mono >>
     qexists `int_calls_expr e ++ int_calls_stmts ss1 ++ int_calls_stmts ss2` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_stmts ss2)` by
    (irule call_evaluation_safe_mono >>
     qexists `int_calls_expr e ++ int_calls_stmts ss1 ++ int_calls_stmts ss2` >> simp[]) >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (er,st1)` >>
  reverse (Cases_on `er`)
  >- (ntac 2 (qpat_x_assum `!s tv t sp u tp. eval_expr cx e s = (INL tv,t) /\ _ ==> _` kall_tac) >>
      simp_tac(srw_ss())[] >> strip_tac >>
      qpat_x_assum `st1 = st'` SUBST_ALL_TAC >>
      qpat_x_assum `!initial_st selected env st res st0. _`
        (qspecl_then [`initial_st`, `selected`] mp_tac) >>
      disch_then (irule o cj 1) >> metis_tac[]) >>
  `push_scope st1 = (INL (),st1 with scopes := FEMPTY::st1.scopes)` by
    (ntac 2 (qpat_x_assum `!s tv t sp u tp. _` kall_tac) >>
     qpat_x_assum `!initial_st selected env st res st0. _` kall_tac >>
     Cases_on `st1` >> simp[push_scope_def, return_def, evaluation_state_fn_updates]) >>
  ntac 2 (qpat_x_assum `!s tv t sp u tp. eval_expr cx e s = (INL tv,t) /\ _ ==> _`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
    disch_then (drule_at (Pat `push_scope _ = _`)) >> strip_tac) >>
  simp_tac(srw_ss())[ignore_bind_apply] >>
  qpat_assum `push_scope st1 = _` (fn th => rewrite_tac[th]) >>
  simp_tac(srw_ss())[finally_def, switch_BoolV_def, bind_def, read_result_empty_scope] >>
  Cases_on `read_result cx x st1` >> rename1 `read_result cx x st1 = (rr,st2)` >>
  `st2 = st1` by metis_tac[read_result_state] >> pop_assum SUBST_ALL_TAC >>
  reverse (Cases_on `rr`)
  >- (ntac 2 (qpat_x_assum `!initial_st selected env ret_ty env0 st res st0. _` kall_tac) >>
      simp_tac(srw_ss())[ignore_bind_apply, pop_scope_def, return_def, raise_def] >>
      strip_tac >> qpat_x_assum `st1 = st'` SUBST_ALL_TAC >>
      qpat_x_assum `!initial_st selected env st res st0. _`
        (qspecl_then [`initial_st`, `selected`] mp_tac) >>
      disch_then (irule o cj 1) >> metis_tac[]) >>
  simp_tac(srw_ss())[] >>
  Cases_on `x' = BoolV T` >> pop_assum (fn th => rewrite_tac[th])
  >- (qpat_x_assum `!initial_st selected env ret_ty env0 st res st0. type_stmts env ret_ty ss2 = _ /\ _ ==> _` kall_tac >>
      qpat_x_assum `IS_SOME (type_stmts env ret_ty ss1)` mp_tac >>
      simp_tac(srw_ss())[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
      Cases_on `eval_stmts cx ss1 (st1 with scopes := FEMPTY::st1.scopes)` >>
      rename1 `eval_stmts cx ss1 (st1 with scopes := FEMPTY::st1.scopes) = (br,stb)` >>
      strip_tac >> suspend "true_branch") >>
  Cases_on `x' = BoolV F` >> pop_assum (fn th => rewrite_tac[th])
  >- (qpat_x_assum `!initial_st selected env ret_ty env0 st res st0. type_stmts env ret_ty ss1 = _ /\ _ ==> _` kall_tac >>
      qpat_x_assum `IS_SOME (type_stmts env ret_ty ss2)` mp_tac >>
      simp_tac(srw_ss())[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
      Cases_on `eval_stmts cx ss2 (st1 with scopes := FEMPTY::st1.scopes)` >>
      rename1 `eval_stmts cx ss2 (st1 with scopes := FEMPTY::st1.scopes) = (br,stb)` >>
      strip_tac >> suspend "false_branch") >>
  ntac 2 (qpat_x_assum `!initial_st selected env ret_ty env0 st res st0. _` kall_tac) >>
  simp_tac(srw_ss())[ignore_bind_apply, pop_scope_def, return_def, raise_def] >>
  strip_tac >> qpat_x_assum `st1 = st'` SUBST_ALL_TAC >>
  qpat_x_assum `!initial_st selected env st res st0. _`
    (qspecl_then [`initial_st`, `selected`] mp_tac) >>
  disch_then (irule o cj 1) >> metis_tac[]
QED

(* Discharge each recursive premise before projecting its conclusions. *)
val IF_CONDITION_GOOD =
  qpat_x_assum `!initial_st selected env ret_ty env0 st res st0. _` kall_tac >>
  qpat_x_assum `!initial_st selected env st res st0. _`
    (qspecl_then [`initial_st`, `selected`, `env`, `st`, `INL x`, `st1`] mp_tac) >>
  (impl_tac >- (gvs[] >> metis_tac[])) >>
  strip_tac >> qpat_x_assum `well_typed_expr env e ==> _` irule >> first_assum ACCEPT_TAC;

val IF_BODY_GOOD =
  qpat_x_assum `!initial_st selected env st res st0. _ ==> (well_typed_expr env e ==> _) /\ _` kall_tac >>
  qpat_x_assum `!initial_st selected env ret_ty env0 st res st0. _`
     (qspecl_then [`initial_st`, `selected`] mp_tac) >>
  disch_then irule >> simp[] >> gvs[] >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  goal_assum (drule_at (Pat `eval_stmts _ _ _ = _`)) >> simp[] >> metis_tac[];

val IF_AFTER_CONDITION =
  `runtime_consistent env cx st1` by
    (qpat_x_assum `!initial_st selected env ret_ty env0 st res st0. _` kall_tac >>
     qpat_x_assum `!initial_st selected env st res st0. _` kall_tac >>
     metis_tac[eval_expr_preserves_runtime_consistent]) >>
  `IS_SOME st1.outcomes` by
    (qpat_assum `eval_expr cx e st = _` (mp_then Any mp_tac (cj 5 eval_outcome_suffix_mutual)) >>
     disch_then (mp_tac o MATCH_MP outcome_suffix_modes) >>
     Cases_on `st.outcomes` >> Cases_on `st1.outcomes` >> simp[] >> metis_tac[]) >>
  `valid_horizon cx initial_st H st1.storage_trace` by
    (qpat_x_assum `valid_horizon cx initial_st H st.storage_trace` mp_tac >>
     simp_tac(srw_ss())[valid_horizon_def] >> metis_tac[]) >>
  `storage_well_formed_on cx (st1 with scopes := FEMPTY::st1.scopes) (FST H)` by
    (irule (iffRL storage_well_formed_on_backends) >> qexists `st1` >> simp[]) >>
  `runtime_consistent env cx (st1 with scopes := FEMPTY::st1.scopes)` by
    (irule push_empty_scope_runtime_consistent >> first_assum ACCEPT_TAC) >>
  `storage_well_formed_on cx stb (FST H) /\ storage_observations_ok cx H stb.storage_trace` by
    IF_BODY_GOOD >>
  conj_tac >- metis_tac[storage_well_formed_on_backends] >> metis_tac[];

val IF_FINISH =
  `st'.storage_trace = stb.storage_trace /\
   st'.accounts = stb.accounts /\ st'.tStorage = stb.tStorage` by
    (qpat_x_assum `!initial_st selected env ret_ty env0 st res st0. _` kall_tac >>
     qpat_x_assum `!initial_st selected env st res st0. _` kall_tac >>
     Cases_on `br` >> gvs[ignore_bind_apply, pop_scope_def, return_def, raise_def, AllCaseEqs()]) >>
  `?suffix. stb.storage_trace = st1.storage_trace ++ suffix` by
    (qpat_x_assum `!initial_st selected env ret_ty env0 st res st0. _` kall_tac >>
     qpat_x_assum `!initial_st selected env st res st0. _` kall_tac >>
     qpat_assum `eval_stmts cx _ _ = _`
       (mp_then (Pat `f st = _`) mp_tac storage_trace_frame_prefix) >>
     simp[cj 2 evaluate_storage_trace_frame]) >>
  `?tail. selected = st1.storage_trace ++ tail` by metis_tac[APPEND_ASSOC] >>
  `storage_well_formed_on cx st1 (FST H) /\
   storage_observations_ok cx H st1.storage_trace` by IF_CONDITION_GOOD >>
  IF_AFTER_CONDITION;

Resume finite_prefix_If[true_branch]:
  IF_FINISH
QED
Resume finite_prefix_If[false_branch]:
  IF_FINISH
QED
Finalise finite_prefix_If
