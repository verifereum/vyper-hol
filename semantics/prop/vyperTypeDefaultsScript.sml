(*
 * Default-value and evaluate_type list helper lemmas for fresh Vyper typing.
 *)

Theory vyperTypeDefaults
Ancestors
  list rich_list arithmetic finite_map option pair
  vyperAST vyperValue vyperValueOperation vyperMisc vyperTyping
  vyperTypeValues
Libs
  wordsLib

Theorem values_have_types_LIST_REL:
  !tys tvs. values_have_types tys tvs =
  LIST_REL value_has_type tys tvs
Proof
  Induct \\ rw[value_has_type_def]
  \\ Cases_on`tvs` \\ gvs[value_has_type_def]
QED

Theorem evaluate_types_length:
  !tenv ts acc tvs. evaluate_types tenv ts acc = SOME tvs ==>
    LENGTH tvs = LENGTH acc + LENGTH ts
Proof
  Induct_on `ts` >>
  simp[evaluate_type_def, AllCaseEqs()] >>
  rpt strip_tac >> res_tac >> gvs[ADD1]
QED

Theorem values_have_types_default:
  !tvs. EVERY (\tv. value_has_type tv (default_value tv)) tvs ==>
        values_have_types tvs (MAP default_value tvs)
Proof
  Induct >> simp[value_has_type_def]
QED

Theorem struct_has_type_default:
  !args. EVERY (\(id,tv). value_has_type tv (default_value tv)) args ==>
         struct_has_type args (MAP (\(id,tv). (id, default_value tv)) args)
Proof
  Induct >> simp[value_has_type_def] >>
  Cases >> simp[value_has_type_def]
QED

Theorem default_value_has_type:
  (!tenv typ tv.
    evaluate_type tenv typ = SOME tv ==>
    value_has_type tv (default_value tv)) /\
  (!tenv ts acc tvs.
    evaluate_types tenv ts acc = SOME tvs ==>
    EVERY (\tv. value_has_type tv (default_value tv)) acc ==>
    EVERY (\tv. value_has_type tv (default_value tv)) tvs)
Proof
  ho_match_mp_tac evaluate_type_ind >> rpt conj_tac >> rpt gen_tac
  >- (Cases_on `bt` >>
      simp[evaluate_type_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[default_value_def, value_has_type_def,
           within_int_bound_def] >>
      TRY (Cases_on `b`) >>
      gvs[evaluate_type_def, AllCaseEqs(), default_value_def,
           value_has_type_def, within_int_bound_def])
  >- (strip_tac >> simp[evaluate_type_def, AllCaseEqs(), PULL_EXISTS] >>
      rpt strip_tac >> gvs[default_value_def, default_value_tuple_MAP,
        value_has_type_def] >>
      irule values_have_types_default >> first_x_assum irule >> simp[])
  >- (strip_tac >> simp[evaluate_type_def, AllCaseEqs(), PULL_EXISTS] >>
      rpt strip_tac >> gvs[] >>
      Cases_on `bd` >> gvs[default_value_def, value_has_type_def])
  >- (strip_tac >> rpt gen_tac >>
      simp[evaluate_type_def, AllCaseEqs(), PULL_EXISTS] >>
      rpt strip_tac >> gvs[default_value_def, default_value_struct_MAP,
        value_has_type_def] >>
      irule struct_has_type_default >>
      `LENGTH args = LENGTH tvs` by
        (imp_res_tac evaluate_types_length >> gvs[]) >>
      gvs[EVERY_MEM, FORALL_PROD, MEM_ZIP, PULL_EXISTS, MEM_EL,
          EL_ZIP, EL_MAP, LENGTH_MAP])
  >- (simp[evaluate_type_def, AllCaseEqs()] >> rpt strip_tac >>
      gvs[default_value_def, value_has_type_def])
  >- (simp[evaluate_type_def] >> rpt strip_tac >>
      gvs[default_value_def, value_has_type_def])
  >- (simp[evaluate_type_def] >> rpt strip_tac >> gvs[])
  >- (rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs()] >>
      first_x_assum drule >> disch_then irule >>
      first_x_assum drule >> simp[])
QED

Theorem default_value_has_type_thm:
  evaluate_type tenv typ = SOME tv ==> value_has_type tv (default_value tv)
Proof
  metis_tac[default_value_has_type]
QED
