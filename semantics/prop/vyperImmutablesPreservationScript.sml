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
  rpt strip_tac >>
  Cases_on `get_module_code cx src`
  >- gvs[lookup_global_def, bind_def, ignore_bind_def, record_storage_event_def, lift_option_type_def, raise_def] >>
  rename1 `SOME ts` >>
  Cases_on `find_var_decl_by_name n ts`
  >- (Cases_on `ALOOKUP st.immutables cx.txn.target`
      >- gvs[lookup_global_def, bind_def, ignore_bind_def, record_storage_event_def, lift_option_type_def,
             get_immutables_def, get_address_immutables_def,
             return_def, raise_def] >>
      rename1 `SOME imms` >>
      Cases_on `FLOOKUP (get_source_immutables src imms) n` >>
      gvs[lookup_global_def, bind_def, ignore_bind_def, record_storage_event_def, lift_option_type_def,
          get_immutables_def, get_address_immutables_def,
          return_def, raise_def]) >>
  rename1 `SOME decl_id` >> PairCases_on `decl_id` >>
  Cases_on `decl_id0`
  >- (rename1 `StorageVarDecl tr typ` >>
      Cases_on `lookup_var_slot_from_layout cx tr src decl_id1`
      >- gvs[lookup_global_def, bind_def, ignore_bind_def, record_storage_event_def, lift_option_type_def,
             return_def, raise_def] >>
      Cases_on `evaluate_type (get_tenv cx) typ` >>
      gvs[lookup_global_def, bind_def, ignore_bind_def, record_storage_event_def, lift_option_type_def,
          return_def, raise_def]) >>
  rename1 `HashMapVarDecl tr kt vt` >>
  Cases_on `lookup_var_slot_from_layout cx tr src decl_id1` >>
  gvs[lookup_global_def, bind_def, ignore_bind_def, record_storage_event_def, lift_option_type_def,
      return_def, raise_def]
QED

Theorem set_global_immutables:
  !cx src n v st res st'.
    set_global cx src n v st = (res, st') ==>
    st'.immutables = st.immutables
Proof
  rw[set_global_def, bind_def, ignore_bind_def, record_storage_event_def, return_def, lift_option_def, lift_option_type_def] >>
  Cases_on `get_module_code cx src` >> gvs[return_def, raise_def] >>
  rename1 `SOME ts` >>
  Cases_on `find_var_decl_by_name n ts` >> gvs[return_def, raise_def] >>
  rename1 `SOME decl_id` >> PairCases_on `decl_id` >> gvs[] >>
  Cases_on `decl_id0` >> gvs[return_def, raise_def, bind_def] >>
  rename1 `StorageVarDecl is_tr typ` >>
  Cases_on `lookup_var_slot_from_layout cx is_tr src decl_id1` >>
  gvs[return_def, raise_def] >>
  Cases_on `evaluate_type (get_tenv cx) typ` >>
  gvs[return_def, raise_def, record_storage_event_def] >>
  imp_res_tac write_storage_slot_immutables >> gvs[]
QED
