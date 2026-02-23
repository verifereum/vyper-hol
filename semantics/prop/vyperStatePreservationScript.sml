Theory vyperStatePreservation
Ancestors
  vyperAST vyperValue vyperState vyperInterpreter vyperLookup

(* ===== Lemmas about scopes preservation ===== *)

(* Basic monad operations preserve scopes *)
Theorem return_state:
  !x st res st'. return x st = (res, st') ==> st' = st
Proof
  rw[return_def]
QED

Theorem raise_state:
  !e st res st'. raise e st = (res, st') ==> st' = st
Proof
  rw[raise_def]
QED

Theorem check_state:
  !b s st res st'. check b s st = (res, st') ==> st' = st
Proof
  rw[check_def, type_check_def, assert_def]
QED

Theorem type_check_state:
  !b s st res st'. type_check b s st = (res, st') ==> st' = st
Proof
  rw[type_check_def, assert_def]
QED

Theorem lift_option_type_state:
  !x s st res st'. lift_option_type x s st = (res, st') ==> st' = st
Proof
  rw[lift_option_type_def] >> Cases_on `x` >> fs[return_def, raise_def]
QED

Theorem lift_option_state:
  !x s st res st'. lift_option x s st = (res, st') ==> st' = st
Proof
  rw[lift_option_def] >> Cases_on `x` >> fs[return_def, raise_def]
QED

Theorem lift_sum_state:
  !x st res st'. lift_sum x st = (res, st') ==> st' = st
Proof
  rw[lift_sum_def] >> Cases_on `x` >> fs[return_def, raise_def]
QED

Theorem get_Value_state:
  !tv st res st'. get_Value tv st = (res, st') ==> st' = st
Proof
  Cases_on `tv` >> rw[get_Value_def, return_def, raise_def]
QED

Theorem get_accounts_state:
  !st res st'. get_accounts st = (res, st') ==> st' = st
Proof
  rw[get_accounts_def, return_def]
QED

Theorem get_address_immutables_state:
  !cx st res st'. get_address_immutables cx st = (res, st') ==> st' = st
Proof
  rw[get_address_immutables_def, lift_option_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> fs[return_def, raise_def]
QED

Theorem get_transient_storage_state:
  !st res st'. get_transient_storage st = (res, st') ==> st' = st
Proof
  rw[get_transient_storage_def, return_def]
QED

Theorem get_storage_backend_state:
  !cx is_trans st res st'. get_storage_backend cx is_trans st = (res, st') ==> st' = st
Proof
  Cases_on `is_trans` >>
  rw[get_storage_backend_def, bind_def, get_transient_storage_def, get_accounts_def, return_def]
QED

Theorem read_storage_slot_state:
  !cx is_trans slot tv st res st'. read_storage_slot cx is_trans slot tv st = (res, st') ==> st' = st
Proof
  Cases_on `is_trans` >>
  rw[read_storage_slot_def, bind_def, get_storage_backend_def,
     get_transient_storage_def, get_accounts_def, return_def, lift_option_def] >>
  qpat_x_assum `_ = _` mp_tac >> CASE_TAC >> gvs[raise_def, return_def]
QED

(* ===== Lemmas about immutables preservation ===== *)

(* Storage operations preserve immutables *)
Theorem read_storage_slot_immutables:
  !cx is_trans slot tv st res st'.
    read_storage_slot cx is_trans slot tv st = (res, st') ==>
    st'.immutables = st.immutables
Proof
  Cases_on `is_trans` >>
  rw[read_storage_slot_def, bind_def, get_storage_backend_def,
     get_transient_storage_def, get_accounts_def, return_def, lift_option_def] >>
  qpat_x_assum `_ = _` mp_tac >> CASE_TAC >> gvs[raise_def, return_def]
QED

Theorem write_storage_slot_immutables:
  !cx is_trans slot tv v st res st'.
    write_storage_slot cx is_trans slot tv v st = (res, st') ==>
    st'.immutables = st.immutables
Proof
  Cases_on `is_trans` >>
  rw[write_storage_slot_def, bind_def, ignore_bind_def, lift_option_def, lift_option_type_def,
     get_storage_backend_def, set_storage_backend_def,
     get_transient_storage_def, update_transient_def,
     get_accounts_def, update_accounts_def, return_def, raise_def] >>
  gvs[AllCaseEqs()] >>
  Cases_on `encode_value tv v` >> gvs[return_def, raise_def]
QED

Theorem lookup_global_immutables:
  !cx src n st res st'.
    lookup_global cx src n st = (res, st') ==>
    st'.immutables = st.immutables
Proof
  rw[lookup_global_def, bind_def, return_def, lift_option_def, lift_option_type_def] >>
  Cases_on `get_module_code cx src` >> gvs[return_def, raise_def] >>
  Cases_on `find_var_decl_by_num n x` >> gvs[return_def, raise_def] >-
  ((* NONE case: get_immutables is read-only *)
   qpat_x_assum `_ = (res, st')` mp_tac >>
   simp[get_immutables_def, get_address_immutables_def, bind_def,
        lift_option_def, lift_option_type_def, return_def, raise_def] >>
   rpt CASE_TAC >> gvs[return_def, raise_def]) >>
  PairCases_on `x'` >> gvs[] >>
  Cases_on `x'0` >> gvs[bind_def, return_def, raise_def] >>
  qpat_x_assum `_ = (res, st')` mp_tac >>
  rpt (CASE_TAC >> gvs[return_def, raise_def, bind_def]) >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac read_storage_slot_immutables
QED

Theorem set_global_immutables:
  !cx src n v st res st'.
    set_global cx src n v st = (res, st') ==>
    st'.immutables = st.immutables
Proof
  rw[set_global_def, bind_def, return_def, lift_option_def, lift_option_type_def] >>
  Cases_on `get_module_code cx src` >> gvs[return_def, raise_def] >>
  rename1 `SOME ts` >>
  Cases_on `find_var_decl_by_num n ts` >> gvs[return_def, raise_def] >>
  rename1 `SOME decl_id` >> PairCases_on `decl_id` >> gvs[] >>
  Cases_on `decl_id0` >> gvs[return_def, raise_def, bind_def] >>
  rename1 `StorageVarDecl is_tr typ` >>
  Cases_on `lookup_var_slot_from_layout cx is_tr src decl_id1` >>
  gvs[return_def, raise_def] >>
  Cases_on `evaluate_type (get_tenv cx) typ` >> gvs[return_def, raise_def] >>
  imp_res_tac write_storage_slot_immutables >> gvs[]
QED

Theorem get_immutables_state:
  !cx src st res st'. get_immutables cx src st = (res, st') ==> st' = st
Proof
  rw[get_immutables_def, bind_def, return_def, get_address_immutables_def, lift_option_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> fs[return_def, raise_def]
QED

Theorem lookup_global_state:
  !cx src n st res st'. lookup_global cx src n st = (res, st') ==> st' = st
Proof
  rw[lookup_global_def, bind_def, return_def, lift_option_def, lift_option_type_def] >>
  Cases_on `get_module_code cx src` >> gvs[return_def, raise_def] >>
  Cases_on `find_var_decl_by_num n x` >> gvs[return_def, raise_def] >-
  (qpat_x_assum `_ = (res, st')` mp_tac >>
   simp[get_immutables_def, get_address_immutables_def, bind_def,
        lift_option_def, lift_option_type_def, return_def, raise_def] >>
   rpt CASE_TAC >> gvs[return_def, raise_def]) >>
  PairCases_on `x'` >> gvs[] >>
  Cases_on `x'0` >> gvs[bind_def, return_def, raise_def] >>
  qpat_x_assum `_ = (res, st')` mp_tac >>
  rpt (CASE_TAC >> gvs[return_def, raise_def, bind_def]) >>
  rpt strip_tac >> gvs[] >>
  drule read_storage_slot_state >> simp[]
QED

Theorem lookup_flag_mem_state:
  !cx nsid mid st res st'. lookup_flag_mem cx nsid mid st = (res, st') ==> st' = st
Proof
  rpt gen_tac >> PairCases_on `nsid` >>
  simp[lookup_flag_mem_def, return_def, raise_def] >>
  rpt CASE_TAC >> simp[return_def, raise_def]
QED

Theorem switch_BoolV_state:
  ∀v f g st res st'.
    switch_BoolV v f g st = (res, st') ∧
    (∀st1 res1 st1'. f st1 = (res1, st1') ⇒ st1' = st1) ∧
    (∀st1 res1 st1'. g st1 = (res1, st1') ⇒ st1' = st1) ⇒
    st' = st
Proof
  rw[switch_BoolV_def, raise_def]
QED

Theorem assign_result_state:
  !ao v subs st res st'. assign_result ao v subs st = (res, st') ==> st' = st
Proof
  Cases_on `ao` >> rw[assign_result_def, return_def, bind_def, lift_sum_def] >>
  qpat_x_assum `_ = (res, st')` mp_tac >>
  rpt (CASE_TAC >> gvs[return_def, raise_def])
QED

Theorem resolve_array_element_state:
  !cx b base tv subs st res st'.
    resolve_array_element cx b base tv subs st = (res, st') ==> st' = st
Proof
  ho_match_mp_tac resolve_array_element_ind >> rw[] >>
  qpat_x_assum `_ = (res, st')` mp_tac >>
  simp[Once resolve_array_element_def, bind_def, return_def, raise_def] >>
  rpt (CASE_TAC >> gvs[return_def, raise_def, bind_def, check_def, type_check_def, assert_def, AllCaseEqs()]) >>
  rpt strip_tac >> gvs[] >>
  gvs[assert_def, bind_def, ignore_bind_def, return_def, raise_def,
      AllCaseEqs()] >>
  imp_res_tac get_storage_backend_state >> gvs[] >>
  FIRST [first_x_assum (qspec_then `0` mp_tac) >> simp[] >>
         disch_then drule >> simp[],
         first_x_assum (qspec_then `1` mp_tac) >> simp[] >>
         disch_then drule >> simp[]]
QED

Theorem materialise_state:
  !cx tv st res st'. materialise cx tv st = (res, st') ==> st' = st
Proof
  Cases_on `tv` >>
  rw[materialise_def, return_def, raise_def] >>
  gvs[bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac read_storage_slot_state >> gvs[]
QED

Theorem check_array_bounds_state:
  !cx tv v st res st'. check_array_bounds cx tv v st = (res, st') ==> st' = st
Proof
  rpt gen_tac >> strip_tac >>
  gvs[oneline check_array_bounds_def, return_def, raise_def,
      bind_def, ignore_bind_def, check_def, type_check_def, assert_def,
      AllCaseEqs(), toplevel_value_CASE_rator, value_CASE_rator,
      bound_CASE_rator] >>
  imp_res_tac get_storage_backend_state >> gvs[]
QED

Theorem toplevel_array_length_state:
  !cx tv st res st'. toplevel_array_length cx tv st = (res, st') ==> st' = st
Proof
  rpt gen_tac >> strip_tac >>
  gvs[oneline toplevel_array_length_def, return_def, raise_def,
      bind_def, ignore_bind_def, check_def, type_check_def, assert_def,
      AllCaseEqs(), toplevel_value_CASE_rator, value_CASE_rator,
      bound_CASE_rator] >>
  imp_res_tac get_storage_backend_state >> gvs[]
QED
