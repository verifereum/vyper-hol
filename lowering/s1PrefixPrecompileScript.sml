(* The ECRecover and Sha256 actions emit only computed outcomes and preserve the request prefix. *)
Theory s1PrefixPrecompile
Ancestors
  s1PrefixFrame s1PrefixDefs vyperStorageTrace vyperInterpreter
  vyperCallOutcomeProps vyperCallOutcome vyperState vyperAST extCallOracle list

(* The child arguments have already been evaluated at this point. *)
Theorem precompile_call_success_only_computed_outcomes:
  (bt = ECRecover \/ bt = Sha256) /\
  precompile_call_success bt vs st = (res, st') ==>
  EVERY (\ob. !rq oc. ob = StorageOutcome rq oc ==> computed_precompile rq)
    (DROP (LENGTH st.storage_trace) st'.storage_trace)
Proof
  strip_tac >> gvs[] >>
  qpat_x_assum `precompile_call_success _ _ _ = _` mp_tac >>
  Cases_on `st.outcomes` >>
  simp[precompile_call_success_def, return_def] >>
  rename1 `st.outcomes = SOME outcomes` >>
  Cases_on `outcomes` >> simp[check_def, assert_def, raise_def] >>
  simp[bind_def, take_call_outcome_def, take_request_outcome_def, LET_THM] >>
  pairarg_tac >>
  simp[call_outcome_request_def, check_def, assert_def, AllCaseEqs(),
       return_def, raise_def] >>
  rw[] >>
  simp[DROP_APPEND1, computed_precompile_def, precompile_address_def,
       precompile_result_def]
QED

Theorem precompile_call_success_prefix:
  (bt = ECRecover \/ bt = Sha256) /\ ~s.vs_halted ==>
  gas_prefix_full P cx st0 (precompile_call_success bt vs) (es,s,G,tn)
Proof
  strip_tac >> irule gas_prefix_full_no_outcome >>
  simp[storage_trace_frame_precompile_call_success] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `precompile_call_success _ _ _ = _`
    (mp_then Any mp_tac precompile_call_success_only_computed_outcomes) >>
  simp[]
QED
