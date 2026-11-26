(* Locate an ordinary outcome in the executed side of a source bind. *)
Theory s1PrefixBoolChainSourcePosition
Ancestors
  vyperStorageTrace vyperState extCallOracle rich_list list

Theorem bool_chain_bind_selected_occurrence:
  storage_trace_frame m /\
  (!v. storage_trace_frame (k v)) /\
  bind m k (ee with gas_obs := obs ++ tail) = (res,fin) /\
  fin.storage_trace = seen ++ StorageOutcome rq oc :: rest /\
  LENGTH ee.storage_trace <= LENGTH seen /\
  ~computed_precompile rq ==>
  ?a mid.
    m (ee with gas_obs := obs ++ tail) = (a,mid) /\
    isPREFIX ee.storage_trace mid.storage_trace /\
    ((LENGTH seen < LENGTH mid.storage_trace /\
      ?r1. mid.storage_trace = seen ++ StorageOutcome rq oc :: r1) \/
     (?v earlier. a = INL v /\
       k v mid = (res,fin) /\
       seen = mid.storage_trace ++ earlier))
Proof
  strip_tac >>
  Cases_on `m (ee with gas_obs := obs ++ tail)` >>
  rename1 `m _ = (a,mid)` >>
  `isPREFIX ee.storage_trace mid.storage_trace` by
    (drule_all storage_trace_frame_prefix >> simp[IS_PREFIX_APPEND]) >>
  qexistsl_tac [`a`,`mid`] >> simp[] >>
  Cases_on `a` >> fs[bind_def]
  >- (rename1 `m _ = (INL v,mid)` >>
      `?ext. fin.storage_trace = mid.storage_trace ++ ext` by
        (`storage_trace_frame (k v)` by simp[] >>
         metis_tac[storage_trace_frame_prefix]) >>
      `seen ++ [StorageOutcome rq oc] ++ rest = mid.storage_trace ++ ext` by
        (qpat_x_assum `fin.storage_trace = mid.storage_trace ++ ext` mp_tac >> simp[]) >>
      pop_assum mp_tac >> simp_tac bool_ss [APPEND_EQ_APPEND_MID] >>
      disch_then (DISJ_CASES_THEN (qx_choose_then `xs` strip_assume_tac))
      >- (disj1_tac >> simp[] >> qexists_tac `xs` >> simp[]) >>
      disj2_tac >> qexists_tac `xs` >> simp[]) >>
  disj1_tac >> fs[] >> qexists_tac `rest` >> simp[]
QED
