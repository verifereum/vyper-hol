Theory bodySimAugPlaceLive
Ancestors
  bodySimAugPlaceMemory bodySimAugPlaceScopes supportedTargets
  vyperInterpreter vyperState vyperMisc pair sum

Theorem aug_place_target_induct[local]:
  !P. (!id. P (NameTarget id)) /\ (!nsid. P (TopLevelNameTarget nsid)) /\
      (!bt e. P bt ==> P (SubscriptTarget bt e)) /\
      (!bt s. P bt ==> P (AttributeTarget bt s)) ==> !bt. P bt
Proof
  rpt strip_tac >>
  `(!e:expr. T) /\ !bt. P bt` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >> simp[]
QED

Theorem aug_place_base_memory_live:
  !t tops bindings info cx s id path s'.
    supported_target_info tops bindings t = SOME info /\
    eval_base_place cx t s = (INL (PlaceR (MemoryPlace id path)),s') ==>
    ?entry v. lookup_scopes id s'.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL v
Proof
  recInduct aug_place_target_induct >> rpt conj_tac >> rpt gen_tac
  >- (simp[Once evaluate_def, get_scopes_def, bind_def, ignore_bind_def,
           type_check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
      rpt strip_tac >> rename1 `IS_SOME (lookup_scopes name st.scopes)` >>
      Cases_on `lookup_scopes name st.scopes` >> gvs[evaluate_subscripts_def])
  >- (PairCases_on `nsid` >> simp[Once evaluate_def] >>
      metis_tac[aug_place_lookup_global_not_memory])
  >- suspend "subscript"
  >> suspend "attribute"
QED
Resume aug_place_base_memory_live[subscript]:
  rpt strip_tac >>
  qpat_x_assum `eval_base_place _ (SubscriptTarget _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  strip_tac >> gvs[supported_target_info_def, AllCaseEqs()] >>
  drule aug_place_extend_memory_inversion >> strip_tac >> gvs[] >>
  imp_res_tac read_result_state >> gvs[] >>
  imp_res_tac aug_place_supported_expr_scopes >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  gvs[] >> metis_tac[aug_place_extend_memory_live]
QED
Resume aug_place_base_memory_live[attribute]:
  rpt strip_tac >>
  qpat_x_assum `eval_base_place _ (AttributeTarget _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  strip_tac >> gvs[supported_target_info_def, AllCaseEqs()] >>
  drule aug_place_extend_memory_inversion >> strip_tac >> gvs[] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  metis_tac[aug_place_extend_memory_live]
QED
Finalise aug_place_base_memory_live

Theorem aug_place_target_memory_live:
  !tops bindings t info cx s id path s'.
    supported_target_info tops bindings t = SOME info /\
    eval_target_place cx t s = (INL (MemoryPlace id path),s') ==>
    ?entry v. lookup_scopes id s'.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL v
Proof
  rpt gen_tac >> simp[Once evaluate_def, bind_def, AllCaseEqs()] >>
  rpt strip_tac >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  drule_all aug_place_base_memory_live >> simp[]
QED
