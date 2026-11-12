Theory bodyPtrIfExpConditionalSource
Ancestors
  vyperState vyperStatePreservation exprSimDefs exprSimMemorySource

Theorem ifexp_conditional_read_cases[local]:
  !cx raw st res st'.
    (do r <- conditional_result cx raw; read_result cx r od) st = (res,st') ==>
    read_result cx raw st = (res,st') \/
    ?m. conditional_result cx raw st = (INR (Error (TypeError m)),st') /\
        res = INR (Error (TypeError m))
Proof
  rpt gen_tac >> Cases_on `raw` >>
  simp[conditional_result_def, read_result_def, bind_def, return_def, raise_def] >>
  rename1 `place_type_value cx p st` >>
  Cases_on `place_type_value cx p st` >> rename1 `place_type_value cx p st = (pr,pst)` >>
  drule place_type_value_state >> strip_tac >> gvs[] >>
  Cases_on `pr` >> simp[]
  >- (IF_CASES_TAC >> simp[read_result_def, bind_def, return_def] >>
      Cases_on `read_place cx p pst` >> rename1 `read_place cx p pst = (rr,ss)` >>
      Cases_on `rr` >> simp[read_result_def, return_def]) >>
  Cases_on `p` >>
  gvs[place_type_value_def, get_scopes_def, get_immutables_def,
      get_address_immutables_def, bind_def, return_def, lift_option_type_def,
      raise_def, AllCaseEqs()] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def])
QED

Theorem ifexp_conditional_read[local]:
  read_result cx raw ee = (INL v,ee) /\
  conditional_result cx raw ee = (res,ss) /\ expr_vv_res_ok res ==>
  ?tv. res = INL tv /\ ss = ee /\ read_result cx tv ee = (INL v,ee)
Proof
  rpt strip_tac >>
  Cases_on `(do r <- conditional_result cx raw; read_result cx r od) ee` >>
  drule ifexp_conditional_read_cases >> strip_tac >>
  imp_res_tac conditional_result_state >>
  gvs[expr_vv_res_ok_def, bind_def, AllCaseEqs()]
QED

Theorem ifexp_conditional_gas_obs[local]:
  conditional_result cx raw ee = (INL tv,ee) ==>
  !tail. conditional_result cx raw (ee with gas_obs := tail) =
    (INL tv,ee with gas_obs := tail)
Proof
  Cases_on `raw`
  >- simp[conditional_result_def, return_def]
  >- (simp[conditional_result_def, bind_def] >>
      Cases_on `place_type_value cx p ee` >>
      rename1 `place_type_value cx p ee = (pr,pst)` >>
      drule place_type_value_state >> strip_tac >> gvs[] >>
      `!tail. place_type_value cx p (ee with gas_obs := tail) =
         (pr,ee with gas_obs := tail)` by
        (Cases_on `p` >>
         gvs[place_type_value_def, get_scopes_def, get_immutables_def,
             get_address_immutables_def, bind_def, return_def,
             lift_option_type_def, raise_def, AllCaseEqs()] >>
         rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def])) >>
      simp[] >> Cases_on `pr` >> simp[] >>
      IF_CASES_TAC >> simp[return_def] >>
      Cases_on `read_place cx p ee` >>
      rename1 `read_place cx p ee = (rr,ss)` >>
      Cases_on `rr` >> simp[return_def] >> rpt strip_tac >>
      gvs[bind_def, return_def] >>
      rename1 `read_place cx p ee = (INL v,ee)` >>
      `read_result cx (PlaceR p) ee = (INL v,ee)` by simp[read_result_def] >>
      drule read_result_gas_obs >> simp[read_result_def]) >>
  simp[conditional_result_def, raise_def]
QED

Theorem ifexp_conditional_source_success:
  read_result cx raw es = (INL v,es) /\
  conditional_result cx raw es = (res,ss) /\ expr_vv_res_ok res ==>
  ?tv. (!tail. conditional_result cx raw (es with gas_obs := tail) =
          (INL tv,es with gas_obs := tail)) /\
       read_result cx tv es = (INL v,es)
Proof
  strip_tac >> drule_all ifexp_conditional_read >> strip_tac >> gvs[] >>
  qexists_tac `tv` >> simp[] >> irule ifexp_conditional_gas_obs >> simp[]
QED
