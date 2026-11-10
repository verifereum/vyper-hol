Theory bodyIntCallReturnLayout
Ancestors
  compileEnv loweringStateRelDefs vyperValue vyperTypeABI vyperTypeExprSoundness
  list rich_list finite_map

(* Stack-return fields remain word fields after type evaluation. *)
Theorem evaluated_word_types:
  EVERY is_word_type tys /\ evaluate_types tenv tys [] = SOME tvs ==>
  EVERY (\tv. ?ty. is_word_type ty /\ evaluate_type tenv ty = SOME tv) tvs
Proof
  strip_tac >> drule evaluate_types_LIST_REL >> strip_tac >>
  fs[EVERY_MEM, LIST_REL_EL_EQN, MEM_EL] >> rpt strip_tac >>
  qexists_tac `EL n tys` >> simp[] >>
  first_x_assum irule >> qexists_tac `n` >> simp[]
QED

Theorem stack_return_value_layout:
  sfields_tenv_consistent sf tenv /\
  evaluate_type tenv ty = SOME tv /\
  0 < returns_stack_count
    (\name. MAP (FST o SND) (get_struct_fields sf name)) ty ==>
  (?t. is_word_type t /\ evaluate_type tenv t = SOME tv) \/
  (?tvs. tv = TupleTV tvs /\
    EVERY (\etv. ?t. is_word_type t /\ evaluate_type tenv t = SOME etv) tvs) \/
  (?ftvs. tv = StructTV ftvs /\
    EVERY (\etv. ?t. is_word_type t /\ evaluate_type tenv t = SOME etv)
      (MAP SND ftvs))
Proof
  Cases_on `ty` >>
  simp[returns_stack_count_def, tuple_like_stack_count_def] >>
  rpt strip_tac >>
  qpat_x_assum `0 < _` mp_tac >> IF_CASES_TAC >> simp[] >> rpt strip_tac
  >- (disj1_tac >> goal_assum (drule_at Any) >> simp[])
  >- (gvs[Once evaluate_type_def, AllCaseEqs()] >>
      disj2_tac >> irule evaluated_word_types >> goal_assum (drule_at Any) >> simp[])
  >- (disj1_tac >> goal_assum (drule_at Any) >> simp[])
  >- (gvs[Once evaluate_type_def, AllCaseEqs()] >>
      drule (cj 2 evaluate_type_mono) >> strip_tac >>
      disj2_tac >>
      `LENGTH tvs = LENGTH args` by
        (drule evaluate_types_LIST_REL >> simp[LIST_REL_EL_EQN]) >>
      simp[MAP_ZIP] >> irule evaluated_word_types >>
      qexists_tac `MAP SND args` >> simp[] >>
      fs[sfields_tenv_consistent_def, get_struct_fields_def] >>
      res_tac >> gvs[]) >>
  disj1_tac >> goal_assum (drule_at Any) >> simp[]
QED
