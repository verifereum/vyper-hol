Theory vyperImmutablesPreservation
Ancestors
  vyperState vyperInterpreter

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
