(* Non-IntCall branches of the checked fixed-selected-prefix schema. *)
Theory guardSourceCallConstructors
Ancestors
  guardSourceOrdinarySchema guardSourceInstrumentation vyperInterpreter
  vyperFiniteStoragePreservation vyperStorageTrace vyperStorageFootprint
  vyperState vyperTypeSystem vyperTypeCallGraph vyperEvalMisc
  vyperEvalOutcomeSuffix
Libs
  guardSourceSchemaLib

Theorem finite_prefix_Expr_Call_RawRevert:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Expr_Call_RawRevert")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_expr (Call _ _ _ _))` mp_tac >>
     pure_rewrite_tac[int_calls_expr_def] >> strip_tac) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (Call _ _ _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr env (Call _ _ _ _)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  (qpat_x_assum `eval_expr _ (Call _ _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
    type_check_def, assert_def, raise_def, return_def] >>
  Cases_on `eval_exprs cx es st` >> rename1 `eval_exprs cx es st = (er,st1)` >>
  Cases_on `er` >> simp_tac(srw_ss())[bind_def, raise_def, return_def] >>
  rpt IF_CASES_TAC >> simp_tac(srw_ss())[bind_def, raise_def, return_def] >>
  strip_tac >>
  `st' = st1` by
    (qpat_x_assum `!initial_st selected env st res st'. _` kall_tac >>
     gvs[lift_option_type_def, return_def, raise_def,
         vyperMiscTheory.option_CASE_rator, AllCaseEqs()]) >>
  qpat_x_assum `st' = st1` SUBST_ALL_TAC >>
  first_x_assum (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
  (disch_then irule >> simp[] >>
   conj_tac >- (qexists `env` >> simp[]) >>
   qexistsl [`initial_st`,`selected`] >>
   simp[listTheory.APPEND_ASSOC, listTheory.APPEND] >>
   qpat_x_assum `!pre rq co sfx. selected = _ /\ _ ==> _` mp_tac >>
   qpat_x_assum `selected = _` SUBST_ALL_TAC >> simp[]))
QED

Theorem finite_prefix_Expr_Call_RawLog:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "Expr_Call_RawLog")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_expr (Call _ _ _ _))` mp_tac >>
     pure_rewrite_tac[int_calls_expr_def] >> strip_tac) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (Call _ _ _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr env (Call _ _ _ _)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  (qpat_x_assum `eval_expr _ (Call _ _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
    type_check_def, assert_def, raise_def, return_def, push_log_def] >>
  Cases_on `eval_exprs cx es st` >> rename1 `eval_exprs cx es st = (er,st1)` >>
  disch_tac >>
  `st'.storage_trace = st1.storage_trace /\ st'.accounts = st1.accounts /\
   st'.tStorage = st1.tStorage` suffices_by
    (strip_tac >>
     `storage_well_formed_on cx st1 (FST H) /\
      storage_observations_ok cx H st1.storage_trace` by
       (first_x_assum (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
        disch_then irule >> simp[] >>
        conj_tac >- (qexists `env` >> simp[]) >>
        qexistsl [`initial_st`,`selected`] >> gvs[] >> metis_tac[]) >>
     gvs[] >> metis_tac[iffRL storage_well_formed_on_backends]) >>
  qpat_x_assum `!initial_st selected env st res st'. _` kall_tac >>
  qpat_x_assum `(case er of _ => _ | _ => _) = _` mp_tac >>
  Cases_on `er` >> simp_tac(srw_ss())[bind_def, raise_def, return_def]
  >- (simp_tac(srw_ss())[lift_option_type_def, bind_def, ignore_bind_def,
        type_check_def, assert_def, raise_def, return_def, push_log_def] >>
      Cases_on `LENGTH x = 2` >> simp_tac(srw_ss())[]
      >- (Cases_on `dest_ArrayV (HD x)` >>
          simp_tac(srw_ss())[bind_def, return_def, raise_def]
          >- (strip_tac >> gvs[]) >>
          Cases_on `dest_BytesV (EL 1 x)` >>
          simp_tac(srw_ss())[bind_def, return_def, raise_def]
          >- (strip_tac >> gvs[]) >>
          simp_tac(srw_ss())[LET_THM, bind_def, ignore_bind_def,
            assert_def, return_def, raise_def, push_log_def] >>
          rpt IF_CASES_TAC >> simp_tac(srw_ss())[bind_def, return_def, raise_def] >>
          strip_tac >> gvs[]) >> strip_tac >> gvs[]) >>
  strip_tac >> gvs[])
QED
