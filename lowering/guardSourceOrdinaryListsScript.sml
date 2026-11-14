(* Sequencing and control flow for the checked selected-prefix schema. *)
Theory guardSourceOrdinaryLists
Ancestors
  list guardSourceOrdinarySchema vyperInterpreter vyperState vyperStorageFootprint
  guardSourceOrdinaryConditionals guardSourceOrdinaryLoops
  vyperTypeSystem vyperTypeCallGraph vyperEvalMisc vyperStorageTrace
  vyperTypeStmtSoundness vyperTypeExprSoundness vyperTypeCallStackSoundness
  vyperEvalOutcomeSuffix vyperTypeEvalStoragePreservation vyperStatePreservation
Libs
  guardSourceSchemaLib

Theorem finite_prefix_Stmts_nil:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Stmts_nil")
Proof
  rpt strip_tac >> gvs[Once evaluate_def, return_def, valid_horizon_def]
QED

Theorem finite_prefix_Exprs_nil:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Exprs_nil")
Proof
  rpt strip_tac >> gvs[Once evaluate_def, return_def, valid_horizon_def]
QED

Theorem finite_prefix_Results_nil:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Results_nil")
Proof
  rpt strip_tac >> gvs[Once evaluate_def, return_def, valid_horizon_def]
QED

Theorem finite_prefix_For_nil:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "For_nil")
Proof
  rpt strip_tac >> gvs[Once evaluate_def, return_def, valid_horizon_def]
QED

Theorem finite_prefix_Stmts_cons:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Stmts_cons")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmts (s::ss))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_stmt s)` by
    (irule call_evaluation_safe_append_left >>
     qexists `int_calls_stmts ss` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_stmts ss)` by
    (irule call_evaluation_safe_append_right >>
     qexists `int_calls_stmt s` >> simp[]) >>
  qpat_x_assum `type_stmts _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, ignore_bind_apply] >>
  Cases_on `eval_stmt cx s st` >>
  rename1 `eval_stmt cx s st = (r1,st1)` >>
  reverse (Cases_on `r1`)
  >- (simp_tac(srw_ss())[bind_def] >> strip_tac >>
      qpat_x_assum `st1 = st'` SUBST_ALL_TAC >>
      qpat_x_assum `!s0 x t. eval_stmt _ _ _ = _ ==> _` kall_tac >>
      qpat_x_assum `!initial_st selected env ret_ty env0 st res st0. _`
        (qspecl_then [`initial_st`, `selected`] mp_tac) >>
      disch_then irule >> metis_tac[]) >>
  simp_tac(srw_ss())[bind_def] >> strip_tac >>
  `?delta. st'.storage_trace = st1.storage_trace ++ delta` by
    metis_tac[storage_trace_frame_prefix, cj 2 evaluate_storage_trace_frame] >>
  `?tail. selected = st1.storage_trace ++ tail` by
    metis_tac[APPEND_ASSOC] >>
  `storage_well_formed_on cx st1 (FST H) /\
   storage_observations_ok cx H st1.storage_trace` by
    (qpat_x_assum `!initial_st selected env ret_ty env0 st res st0. _`
       (qspecl_then [`initial_st`, `selected`] mp_tac) >>
     disch_then irule >> metis_tac[]) >>
  `runtime_consistent env'' cx st1` by
    (qpat_x_assum `!s0 x t. eval_stmt _ _ _ = _ ==> _` kall_tac >>
     qpat_x_assum `!initial_st selected env ret_ty env0 st res st0. _` kall_tac >>
     gvs[runtime_consistent_def] >>
     drule_all eval_stmt_type_preservation_success >> simp[]) >>
  `IS_SOME st1.outcomes` by
    (drule (cj 1 eval_outcome_suffix_mutual) >>
     disch_then (mp_tac o MATCH_MP outcome_suffix_modes) >>
     Cases_on `st.outcomes` >> Cases_on `st1.outcomes` >> simp[] >>
     metis_tac[]) >>
  `valid_horizon cx initial_st H st1.storage_trace` by
    (qpat_x_assum `valid_horizon cx initial_st H st.storage_trace` mp_tac >>
     simp_tac(srw_ss())[valid_horizon_def] >> metis_tac[]) >>
  qpat_x_assum `!s0 x t. eval_stmt _ _ _ = _ ==> _` drule >>
  disch_then (qspecl_then [`initial_st`, `selected`] mp_tac) >>
  disch_then irule >> metis_tac[]
QED

Theorem finite_prefix_Results_cons:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Results_cons")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_exprs (e::es))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_x_assum `well_typed_exprs env (e::es)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr_results _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (er,st1)` >>
  reverse (Cases_on `er`)
  >- (qpat_x_assum `!s0 v t. eval_expr _ _ _ = _ ==> _` kall_tac >>
      simp_tac(srw_ss())[] >> strip_tac >>
      qpat_x_assum `st1 = st'` SUBST_ALL_TAC >>
      qpat_x_assum `!initial_st selected env st res st0. _`
        (qspecl_then [`initial_st`, `selected`] mp_tac) >>
      disch_then (irule o cj 1) >> metis_tac[]) >>
  simp_tac(srw_ss())[] >>
  qpat_x_assum `!s0 v t. eval_expr _ _ _ = _ ==> _` drule >> strip_tac >>
  Cases_on `eval_expr_results cx es st1` >>
  rename1 `eval_expr_results cx es st1 = (ers,st3)` >>
  Cases_on `ers` >> simp_tac(srw_ss())[bind_def, return_def, raise_def] >>
  strip_tac >> qpat_x_assum `st3 = st'` SUBST_ALL_TAC >>
  `?suffix. st'.storage_trace = st1.storage_trace ++ suffix` by
    metis_tac[storage_trace_frame_prefix, cj 11 evaluate_storage_trace_frame] >>
  `?tail. selected = st1.storage_trace ++ tail` by metis_tac[APPEND_ASSOC] >>
  `storage_well_formed_on cx st1 (FST H) /\
   storage_observations_ok cx H st1.storage_trace` by
    (qpat_x_assum `!initial_st selected env st res st0. runtime_consistent _ _ _ /\ _ ==> _`
       (qspecl_then [`initial_st`, `selected`] mp_tac) >>
     disch_then (irule o cj 1) >> metis_tac[]) >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_expr_preserves_runtime_consistent] >>
  `IS_SOME st1.outcomes` by
    (drule (cj 5 eval_outcome_suffix_mutual) >>
     disch_then (mp_tac o MATCH_MP outcome_suffix_modes) >>
     Cases_on `st.outcomes` >> Cases_on `st1.outcomes` >> simp[] >> metis_tac[]) >>
  `valid_horizon cx initial_st H st1.storage_trace` by
    (qpat_x_assum `valid_horizon cx initial_st H st.storage_trace` mp_tac >>
     simp_tac(srw_ss())[valid_horizon_def] >> metis_tac[]) >>
  qpat_x_assum `!initial_st selected env st res st0. well_typed_exprs _ _ /\ _ ==> _`
    (qspecl_then [`initial_st`, `selected`, `env`, `st1`] mp_tac) >>
  disch_then irule >> metis_tac[]
QED

Theorem finite_prefix_Exprs_cons:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Exprs_cons")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_exprs (e::es))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_x_assum `well_typed_exprs env (e::es)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_exprs _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (er,st1)` >>
  reverse (Cases_on `er`)
  >- (qpat_x_assum `!s0 tv t s1 v t1. eval_expr _ _ _ = _ /\ read_result _ _ _ = _ ==> _` kall_tac >>
      simp_tac(srw_ss())[] >> strip_tac >>
      qpat_x_assum `st1 = st'` SUBST_ALL_TAC >>
      qpat_x_assum `!initial_st selected env st res st0. _`
        (qspecl_then [`initial_st`, `selected`] mp_tac) >>
      disch_then (irule o cj 1) >> metis_tac[]) >>
  simp_tac(srw_ss())[] >>
  Cases_on `read_result cx x st1` >> rename1 `read_result cx x st1 = (rr,stm)` >>
  `stm = st1` by metis_tac[read_result_state] >> pop_assum SUBST_ALL_TAC >>
  reverse (Cases_on `rr`)
  >- (simp_tac(srw_ss())[bind_def] >> strip_tac >>
      qpat_x_assum `st1 = st'` SUBST_ALL_TAC >>
      qpat_x_assum `!s0 tv t s1 v t1. eval_expr _ _ _ = _ /\ read_result _ _ _ = _ ==> _` kall_tac >>
      qpat_x_assum `!initial_st selected env st res st0. _`
        (qspecl_then [`initial_st`, `selected`] mp_tac) >>
      disch_then (irule o cj 1) >> metis_tac[]) >>
  simp_tac(srw_ss())[bind_def] >>
  qpat_x_assum `!s0 tv t s1 v t1. eval_expr cx e s0 = (INL tv,t) /\ read_result cx tv s1 = (INL v,t1) ==> _` drule >>
  disch_then drule >> strip_tac >>
  Cases_on `eval_exprs cx es st1` >> rename1 `eval_exprs cx es st1 = (ers,st3)` >>
  Cases_on `ers` >> simp_tac(srw_ss())[bind_def, return_def] >>
  strip_tac >> qpat_x_assum `st3 = st'` SUBST_ALL_TAC >>
  `?suffix. st'.storage_trace = st1.storage_trace ++ suffix` by
    metis_tac[storage_trace_frame_prefix, cj 6 evaluate_storage_trace_frame] >>
  `?tail. selected = st1.storage_trace ++ tail` by metis_tac[APPEND_ASSOC] >>
  `storage_well_formed_on cx st1 (FST H) /\
   storage_observations_ok cx H st1.storage_trace` by
    (qpat_x_assum `!initial_st selected env st res st0. runtime_consistent _ _ _ /\ _ ==> _`
       (qspecl_then [`initial_st`, `selected`] mp_tac) >>
     disch_then (irule o cj 1) >> metis_tac[]) >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_expr_preserves_runtime_consistent] >>
  `IS_SOME st1.outcomes` by
    (drule (cj 5 eval_outcome_suffix_mutual) >>
     disch_then (mp_tac o MATCH_MP outcome_suffix_modes) >>
     Cases_on `st.outcomes` >> Cases_on `st1.outcomes` >> simp[] >> metis_tac[]) >>
  `valid_horizon cx initial_st H st1.storage_trace` by
    (qpat_x_assum `valid_horizon cx initial_st H st.storage_trace` mp_tac >>
     simp_tac(srw_ss())[valid_horizon_def] >> metis_tac[]) >>
  qpat_x_assum `!initial_st selected env st res st0. well_typed_exprs _ _ /\ _ ==> _`
    (qspecl_then [`initial_st`, `selected`, `env`, `st1`] mp_tac) >>
  disch_then irule >> metis_tac[]
QED

Theorem finite_prefix_Iterator_Array:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Iterator_Array")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_iterator (Array e))` mp_tac >>
  pure_rewrite_tac[int_calls_iterator_def] >> strip_tac >>
  qpat_x_assum `well_typed_iterator _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [well_typed_iterator_def]) >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (er,st1)` >>
  Cases_on `er` >> simp_tac(srw_ss())[] >> strip_tac >>
  `st' = st1` by metis_tac[array_iterator_results_state] >>
  pop_assum SUBST_ALL_TAC >>
  qpat_x_assum `!initial_st selected env st res st0. _`
    (qspecl_then [`initial_st`, `selected`] mp_tac) >>
  disch_then (irule o cj 1) >> metis_tac[]
QED

Theorem finite_prefix_Iterator_Range:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Iterator_Range")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `eval_iterator cx (Range e e') st = _` >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_iterator (Range e e'))` mp_tac >>
  pure_rewrite_tac[int_calls_iterator_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_x_assum `well_typed_iterator _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [well_typed_iterator_def]) >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (er,st1)` >>
  reverse (Cases_on `er`)
  >- (simp_tac(srw_ss())[] >> strip_tac >>
      qpat_x_assum `st1 = st'` SUBST_ALL_TAC >>
      qpat_x_assum `!initial_st selected env st res st0. _`
        (qspecl_then [`initial_st`, `selected`] mp_tac) >>
      disch_then (irule o cj 1) >> metis_tac[]) >>
  simp_tac(srw_ss())[] >>
  Cases_on `read_result cx x st1` >> rename1 `read_result cx x st1 = (rr,stm)` >>
  `stm = st1` by metis_tac[read_result_state] >> pop_assum SUBST_ALL_TAC >>
  reverse (Cases_on `rr`)
  >- (simp_tac(srw_ss())[bind_def] >> strip_tac >>
      qpat_x_assum `st1 = st'` SUBST_ALL_TAC >>
      qpat_x_assum `!initial_st selected env st res st0. _`
        (qspecl_then [`initial_st`, `selected`] mp_tac) >>
      disch_then (irule o cj 1) >> metis_tac[]) >>
  simp_tac(srw_ss())[bind_def] >>
  qpat_x_assum `!s0 tv t s1 v t1. eval_expr cx e s0 = (INL tv,t) /\ read_result cx tv s1 = (INL v,t1) ==> _` drule >>
  disch_then drule >> strip_tac >>
  Cases_on `eval_expr cx e' st1` >> rename1 `eval_expr cx e' st1 = (er2,st2)` >>
  Cases_on `er2` >> simp_tac(srw_ss())[] >>
  rpt (pairarg_tac >> simp_tac(srw_ss())[bind_def, return_def, raise_def]) >>
  strip_tac >>
  `st' = st2` by
    (qpat_x_assum `!initial_st selected env st res st0. runtime_consistent _ _ _ /\ _ ==> _` kall_tac >>
     qpat_x_assum `!initial_st selected env st res st0. runtime_consistent _ _ _ /\ _ ==> _` kall_tac >>
     gvs[AllCaseEqs(), return_def] >>
     imp_res_tac read_result_state >> imp_res_tac lift_sum_state >>
     gvs[return_def]) >>
  pop_assum SUBST_ALL_TAC >>
  `?suffix. st2.storage_trace = st1.storage_trace ++ suffix` by
    metis_tac[storage_trace_frame_prefix, cj 5 evaluate_storage_trace_frame] >>
  `?tail. selected = st1.storage_trace ++ tail` by metis_tac[APPEND_ASSOC] >>
  `storage_well_formed_on cx st1 (FST H) /\
   storage_observations_ok cx H st1.storage_trace` by
    (qpat_x_assum `!initial_st selected env st res st0. _ ==> ((well_typed_expr env e ==> _) /\ _)`
       (qspecl_then [`initial_st`, `selected`] mp_tac) >>
     disch_then (irule o cj 1) >> metis_tac[]) >>
  `runtime_consistent env cx st1` by metis_tac[eval_expr_preserves_runtime_consistent] >>
  `IS_SOME st1.outcomes` by
    (qpat_assum `eval_expr cx e st = _` (mp_then Any mp_tac (cj 5 eval_outcome_suffix_mutual)) >>
     disch_then (mp_tac o MATCH_MP outcome_suffix_modes) >>
     Cases_on `st.outcomes` >> Cases_on `st1.outcomes` >> simp[] >> metis_tac[]) >>
  `valid_horizon cx initial_st H st1.storage_trace` by
    (qpat_x_assum `valid_horizon cx initial_st H st.storage_trace` mp_tac >>
     simp_tac(srw_ss())[valid_horizon_def] >> metis_tac[]) >>
  qpat_x_assum `!initial_st selected env st res st0. runtime_consistent _ _ _ /\ _ ==> _`
    (qspecl_then [`initial_st`, `selected`, `env`, `st1`] mp_tac) >>
  disch_then (irule o cj 1) >> metis_tac[]
QED

(* Publication audit: every Lists-owned premise has exactly one checked export,
 * and every export has exactly the generated schema statement. *)
val lists_exports =
  [("Stmts_nil", finite_prefix_Stmts_nil),
   ("Stmts_cons", finite_prefix_Stmts_cons),
   ("Exprs_nil", finite_prefix_Exprs_nil),
   ("Exprs_cons", finite_prefix_Exprs_cons),
   ("Results_nil", finite_prefix_Results_nil),
   ("Results_cons", finite_prefix_Results_cons),
   ("Iterator_Array", finite_prefix_Iterator_Array),
   ("Iterator_Range", finite_prefix_Iterator_Range),
   ("For_nil", finite_prefix_For_nil),
   ("For", finite_prefix_For),
   ("For_cons", finite_prefix_For_cons),
   ("If", finite_prefix_If),
   ("Expr_IfExp", finite_prefix_Expr_IfExp)];
val lists_expected = List.filter
  (fn (name,_) => guardSourceSchemaLib.owner name = "lists")
  (guardSourceSchemaLib.manifest finite_prefix_evaluate_ind);
val _ = if length lists_exports = length lists_expected andalso
           length (mk_set (map #1 lists_exports)) = length lists_exports
        then () else raise Fail "Lists branch coverage/uniqueness mismatch";
val _ = List.app (fn (name,tm) =>
  case List.find (fn (n,_) => n = name) lists_exports of
    SOME (_,th) => if aconv (concl th) tm then ()
                   else raise Fail ("Lists branch statement mismatch: " ^ name)
  | NONE => raise Fail ("Missing Lists branch: " ^ name)) lists_expected;
