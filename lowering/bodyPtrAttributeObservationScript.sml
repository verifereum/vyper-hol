Theory bodyPtrAttributeObservation
Ancestors
  exprSimAttribute vyperState vyperStorageBackend vyperValue vyperAST
  gasExemptCert exprSimMemorySource

(* A functional update law, including unsuccessful field selection. *)
Theorem select_attr_gas_update:
  select_result cx ty tv (AttrSubscript fld) (ee with gas_obs := gs) =
    (FST (select_result cx ty tv (AttrSubscript fld) ee),
     (SND (select_result cx ty tv (AttrSubscript fld) ee)) with gas_obs := gs)
Proof
  Cases_on `tv`
  >~ [`Value v`]
  >- (simp[select_result_def, bind_def, lift_option_type_def, lift_sum_def,
           return_def, raise_def] >>
      rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]))
  >~ [`HashMapRef`] >- simp[select_result_def, extend_place_def, raise_def] >>
  rename1 `PlaceR pl` >> Cases_on `pl`
  >~ [`StoragePlace tr slot ptv`]
  >- (Cases_on `ptv` >>
      simp[select_result_def, extend_place_def, extend_storage_place_def,
           bind_def, lift_option_type_def, return_def, raise_def,
           pairTheory.UNCURRY] >>
      rpt (BasicProvers.FULL_CASE_TAC >>
           gvs[return_def, raise_def, pairTheory.UNCURRY])) >>
  simp[select_result_def, extend_place_def, place_type_value_def,
       read_place_def, get_scopes_def, get_immutables_def,
       get_address_immutables_def, bind_def, ignore_bind_def,
       lift_option_type_def, lift_sum_def, return_def, raise_def]
  >~ [`ALOOKUP _.immutables _`]
  >- rpt (BasicProvers.FULL_CASE_TAC >> gvs[bind_def, return_def, raise_def]) >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[bind_def, return_def, raise_def])
QED
