Theory s1PrefixSubscriptMapSelect
Ancestors
  vyperHashMapStorage vyperState extCallOracle rich_list

Theorem mapping_select_no_request_outcome:
  select_result cx ty (HashMapRef tr slot kt vt) (ValueSubscript kv)
    (st with gas_obs := gobs) = (res,ee) ==>
  EVERY (\ob. !rq oc. ob = StorageOutcome rq oc ==> computed_precompile rq)
    (DROP (LENGTH st.storage_trace) ee.storage_trace)
Proof
  Cases_on `vt`
  >- (rename1 `HashMapRef tr slot kt (Type t)` >>
      Cases_on `evaluate_type (get_tenv cx) t`
      >- (simp[select_result_def, extend_place_def, lift_option_type_def,
               bind_def, raise_def] >> strip_tac >> gvs[]) >>
      drule select_result_hashmap_leaf >> disch_then (simp o single) >>
      strip_tac >> gvs[DROP_LENGTH_APPEND]) >>
  simp[select_result_hashmap_nested] >> strip_tac >> gvs[]
QED
