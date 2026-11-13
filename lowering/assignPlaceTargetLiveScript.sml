Theory assignPlaceTargetLive
Ancestors
  bodySimAugPlaceLive bodySimAugPlaceMemory bodySimAugPlaceScopes
  notMutateExprScopes stmtLowering exprLowering vyperInterpreter vyperState vyperMisc stmtSimAugAssignPlaceMemory
Libs monadsyntax

Theorem assign_place_target_induct[local]:
  !P. (!id. P (NameTarget id)) /\ (!nsid. P (TopLevelNameTarget nsid)) /\
      (!bt e. P bt ==> P (SubscriptTarget bt e)) /\
      (!bt s. P bt ==> P (AttributeTarget bt s)) ==> !bt. P bt
Proof
  rpt strip_tac >>
  `(!e:expr. T) /\ !bt. P bt` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >> simp[]
QED

Theorem assign_place_pure_base_memory_live:
  !bt cenv cx s id path ee.
    ~expr_can_mutate cenv (target_to_expr bt) /\
    eval_base_place cx bt s = (INL (PlaceR (MemoryPlace id path)),ee) ==>
    ?entry v. lookup_scopes id ee.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL v
Proof
  recInduct assign_place_target_induct >> rpt conj_tac >> rpt gen_tac
  >- (simp[Once evaluate_def, get_scopes_def, bind_def, ignore_bind_def,
           type_check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
      rpt strip_tac >> rename1 `IS_SOME (lookup_scopes name st.scopes)` >>
      Cases_on `lookup_scopes name st.scopes` >> gvs[evaluate_subscripts_def])
  >- (PairCases_on `nsid` >> simp[Once evaluate_def] >>
      metis_tac[bodySimAugPlaceScopesTheory.aug_place_lookup_global_not_memory])
  >- (rpt strip_tac >>
      qpat_x_assum `eval_base_place _ (SubscriptTarget _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      strip_tac >> gvs[target_to_expr_def, expr_can_mutate_def] >>
      drule aug_place_extend_memory_inversion >> strip_tac >> gvs[] >>
      imp_res_tac read_result_state >> gvs[] >>
      imp_res_tac not_mutate_expr_scopes >>
      first_x_assum (drule_all_then strip_assume_tac) >>
      gvs[] >> metis_tac[aug_place_extend_memory_live]) >>
  rpt strip_tac >>
  qpat_x_assum `eval_base_place _ (AttributeTarget _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  strip_tac >> gvs[target_to_expr_def, expr_can_mutate_def] >>
  drule aug_place_extend_memory_inversion >> strip_tac >> gvs[] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  metis_tac[aug_place_extend_memory_live]
QED

Theorem assign_place_pure_target_memory_live:
  !cenv bt cx s id path ee.
    ~expr_can_mutate cenv (target_to_expr bt) /\
    eval_target_place cx bt s = (INL (MemoryPlace id path),ee) ==>
    ?entry v. lookup_scopes id ee.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL v
Proof
  rpt gen_tac >> simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
  rpt strip_tac >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  drule_all assign_place_pure_base_memory_live >> simp[]
QED

Theorem assign_place_pure_memory_write_success:
  ~expr_can_mutate cenv (target_to_expr bt) /\
  eval_target_place cx bt s = (INL (MemoryPlace id path),ee) /\
  write_place cx (MemoryPlace id path) v ee = (res,ff) /\
  stmt_res_ok lctx res ==> res = INL ()
Proof
  strip_tac >> drule_all assign_place_pure_target_memory_live >> strip_tac >>
  drule_all aug_place_memory_write_success >> simp[]
QED
