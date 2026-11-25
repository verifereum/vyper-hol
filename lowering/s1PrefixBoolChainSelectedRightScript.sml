(* Lift a selected request from the continuing side of a source bind. *)
Theory s1PrefixBoolChainSelectedRight
Ancestors
  s1PrefixBoolChainSourcePosition s1PrefixCompose s1PrefixProps
  gasOutcomeFull vyperStorageTrace vyperState list rich_list

Theorem bool_chain_selected_right_site:
  storage_trace_frame A /\
  (!x. storage_trace_frame (K x)) /\
  requests_outcomes_frame A /\
  LENGTH es.requests = recorded_outcomes_count es.storage_trace /\
  (!tail. A (es with gas_obs := gas_explicit left s.vs_gas_readings ++ tail) =
    (INL v, mid with gas_obs := tail)) /\
  bind A K (es with gas_obs := gas_explicit left s.vs_gas_readings ++ tail) =
    (res,ee) /\
  ee.storage_trace = obs_pre ++ StorageOutcome rq oc :: sfx /\
  obs_pre = mid.storage_trace ++ prior /\
  valid_horizon cx st0 H obs_pre /\
  ~computed_precompile rq /\
  (!H0. valid_horizon cx st0 H0 mid.storage_trace ==>
     gas_origin_ptr_path (DF H0,lo,explicit,ctx,func,PG)
       (s,G,tn) left (OK t,G1,tn1)) /\
  (!tail res' ee' obs_pre' rq' oc' sfx' H'.
     LENGTH mid.requests = recorded_outcomes_count mid.storage_trace /\
     K v (mid with gas_obs := tail) = (res',ee') /\
     ee'.storage_trace = obs_pre' ++ StorageOutcome rq' oc' :: sfx' /\
     LENGTH mid.storage_trace <= LENGTH obs_pre' /\
     valid_horizon cx st0 H' obs_pre' /\
     ~computed_precompile rq' ==>
     request_site (DF H',lo,explicit,ctx,func,PG) cx H'
       (t,G1,tn1) (recorded_outcomes_count obs_pre') rq' oc') ==>
  request_site (DF H,lo,explicit,ctx,func,PG) cx H
    (s,G,tn) (recorded_outcomes_count obs_pre) rq oc
Proof
  strip_tac >>
  `LENGTH mid.requests = recorded_outcomes_count mid.storage_trace` by
    (qpat_assum `!tail. A _ = _`
       (qspec_then `tail` (mp_then Any mp_tac requests_outcomes_frame_result)) >>
     simp[]) >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `obs_pre = _` (fn eq =>
       qpat_assum `valid_horizon cx st0 H obs_pre` (fn vh =>
         mp_tac (REWRITE_RULE [eq] vh) >> metis_tac[valid_horizon_append]))) >>
  `K v (mid with gas_obs := tail) = (res,ee)` by
    (qpat_assum `!tail. A _ = _` (qspec_then `tail` assume_tac) >>
     gvs[bind_def]) >>
  `request_site (DF H,lo,explicit,ctx,func,PG) cx H
      (t,G1,tn1) (recorded_outcomes_count obs_pre) rq oc` by
    (qpat_assum `!tail res' ee' obs_pre' rq' oc' sfx' H'. _ ==> _`
       (qspecl_then [`tail`,`res`,`ee`,`obs_pre`,`rq`,`oc`,`sfx`,`H`] mp_tac) >>
     simp[]) >>
  irule request_site_prepend_path >>
  qexistsl_tac [`G1`,`left`,`t`,`tn1`] >>
  simp[]
QED
