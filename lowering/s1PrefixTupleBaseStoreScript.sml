(* The store after a base-target evaluation adds no request to its trace. *)
Theory s1PrefixTupleBaseStore
Ancestors
  s1PrefixDefs bodyPtrPopTargetFragTransport tuplePlaceStep
  vyperInterpreter vyperPlaceFrames vyperState

Triviality tuple_base_store_trace:
  (SND (assign_tuple_targets cx (BaseTarget bt) vi st)).storage_trace =
  (SND (eval_base_place cx bt st)).storage_trace
Proof
  simp_tac bool_ss [Once evaluate_def, eval_target_place_as_bind, bind_assoc] >>
  Cases_on `eval_base_place cx bt st` >>
  rename1 `eval_base_place cx bt st = (res,mid)` >>
  Cases_on `res` >> simp[bind_def] >>
  rename1 `get_place pv mid` >>
  Cases_on `get_place pv mid` >>
  drule_then SUBST_ALL_TAC get_place_state >>
  rename1 `get_place pv mid = (pr,mid)` >>
  Cases_on `pr` >> simp[] >>
  rename1 `SND (write_place cx p vi mid)` >>
  Cases_on `write_place cx p vi mid` >>
  drule_then (simp o single) write_place_storage_trace
QED

Theorem tuple_base_store_prefix_from_place:
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (eval_base_place cx bt) (es,s,G,tn) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (assign_tuple_targets cx (BaseTarget bt) vi) (es,s,G,tn)
Proof
  rewrite_tac[gas_prefix_full_def] >>
  disch_then (qx_choose_then `marks` (CONJUNCTS_THEN ASSUME_TAC)) >>
  qexists_tac `marks` >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!tail res ee obs_pre rq outcome sfx H. _ ==> request_site _ _ _ _ _ _ _`
    (qspec_then `tail` irule) >>
  qpat_assum `assign_tuple_targets _ _ _ _ = (_,_)`
    (mp_tac o AP_TERM ``\r : (unit + exception) # evaluation_state.
                          (SND r).storage_trace``) >>
  simp[tuple_base_store_trace] >>
  Cases_on `eval_base_place cx bt
     (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail)` >>
  gvs[] >> metis_tac[]
QED
