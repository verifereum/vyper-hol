Theory s1PrefixAssignTupleLocalsTrace
Ancestors
  s1PrefixDefs stmtSimAssignTuple tuplePlaceStep vyperInterpreter vyperState
Libs
  monadsyntax

Theorem assign_tuple_local_storage_trace[local]:
  assign_tuple_targets cx (BaseTarget (NameTarget id)) v st = (res,ee) ==>
  ee.storage_trace = st.storage_trace
Proof
  simp[Once evaluate_def] >>
  simp[Once evaluate_def, Once evaluate_def,
       bind_def, ignore_bind_def, get_scopes_def, type_check_def, assert_def,
       return_def, raise_def, get_place_def] >>
  Cases_on `lookup_scopes id st.scopes` >> simp[get_place_def, return_def] >>
  strip_tac >> drule write_place_storage_trace >> simp[]
QED

Theorem assign_tuple_target_list_locals_storage_trace[local]:
  !ids cx vs st res ee.
    assign_tuple_target_list cx (MAP (BaseTarget o NameTarget) ids) vs st =
      (res,ee) ==> ee.storage_trace = st.storage_trace
Proof
  Induct >> Cases_on `vs` >>
  simp[Once evaluate_def, return_def, raise_def, ignore_bind_def, bind_def] >>
  rpt gen_tac >>
  rename1 `assign_tuple_targets cx (BaseTarget (NameTarget id)) v st` >>
  Cases_on `assign_tuple_targets cx (BaseTarget (NameTarget id)) v st` >>
  rename1 `assign_tuple_targets _ _ _ _ = (rr,mid)` >>
  Cases_on `rr` >> simp[] >>
  metis_tac[assign_tuple_local_storage_trace]
QED

Theorem assign_tuple_locals_storage_trace:
  assign_tuple_targets cx (TupleTarget (MAP (BaseTarget o NameTarget) ids))
    v st = (res,ee) ==> ee.storage_trace = st.storage_trace
Proof
  Cases_on `v` >> simp[evaluate_def, raise_def] >>
  Cases_on `a` >> simp[raise_def] >>
  strip_tac >> drule assign_tuple_target_list_locals_storage_trace >> simp[]
QED

Theorem assign_tuple_locals_prefix_from_rhs:
  gas_prefix_full cfg cx st0 (bind (eval_expr cx e) (read_result cx))
    (es,s,G,tn) ==>
  gas_prefix_full cfg cx st0
    (eval_stmt cx (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e))
    (es,s,G,tn)
Proof
  PairCases_on `cfg` >>
  pure_rewrite_tac[gas_prefix_full_def, eval_assign_tuple_action] >>
  disch_then (qx_choose_then `marks` (CONJUNCTS_THEN ASSUME_TAC)) >>
  qexists_tac `marks` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `gs = gas_explicit marks s.vs_gas_readings ++ tail` >>
  Cases_on `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs)` >>
  rename1 `bind (eval_expr _ _) (read_result _) _ = (rhs,mid)` >>
  `ee.storage_trace = mid.storage_trace` by
    (qpat_x_assum `bind _ (assign_tuple_targets _ _) _ = _` mp_tac >>
     Cases_on `rhs` >> simp[Once bind_def] >>
     metis_tac[assign_tuple_locals_storage_trace]) >>
  qpat_assum `!tail res ee obs_pre rq outcome sfx H. _ ==> request_site _ _ _ _ _ _ _`
    (qspec_then `tail` irule) >>
  simp[] >> qexistsl [`mid`, `rhs`, `sfx`, `tail`] >> fs[Abbr `gs`]
QED
