(* Request-prefix companion to bodyFullUnaryValueCompose. *)
Theory s1PrefixUnaryValueCompose
Ancestors
  s1PrefixPreds bodyFullUnaryValueCompose s1PrefixDefs
  s1PrefixCompose s1PrefixProps gasOutcomeFullCompose
  vyperStorageFootprint vyperStorageTrace sum

Theorem gas_outcome_prefix_unary_value:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn) childQ childR /\
  gas_prefix_full (DF,lo,explicit,ctx,func,PG)
      cx st0 (bind (eval_expr cx e) (read_result cx))
      (es,s,G,tn) /\
  (!H res ee HG tm t. childQ H res ee HG tm t ==> ?v. res = INL v) /\
  (!H res ee gt r. childR H res ee gt r ==>
    ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  (!v. storage_trace_frame (next v)) /\
  (!marks res mid HG tm t v.
    res = INL v /\
    (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (res,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    ~t.vs_halted /\ mid.gas_obs = [] /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==> childQ H res mid HG tm t) ==>
    gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
      (next v) (mid,t,HG,tm) Q R) /\
  (!marks res mid HG tm t v.
    res = INL v /\
    (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (res,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    ~t.vs_halted /\ mid.gas_obs = [] /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==> childQ H res mid HG tm t) ==>
       gas_prefix_full (DF,lo,explicit,ctx,func,PG)
      cx st0 (next v)
      (mid,t,HG,tm)) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG)
      cx st0 (bind (bind (eval_expr cx e) (read_result cx)) next)
      (es,s,G,tn)
Proof
  strip_tac >>
  qpat_abbrev_tac `source = bind (eval_expr cx e) (read_result cx)` >>
  qabbrev_tac `post = \H res ee HG tm t.
    childQ H res ee HG tm t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  `gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
     source (es,s,G,tn) post childR` by
    (irule gas_outcome_full_post_source >>
     qpat_assum `gas_outcome_full _ _ _ _ source _ childQ childR` (irule_at Any) >>
     simp[Abbr `post`]) >>
  qpat_assum `gas_outcome_full _ _ _ _ source _ post childR`
    (mp_then Any irule gas_prefix_full_bind) >>
  simp[] >> rpt conj_tac
  >- (qx_genl_tac [`marks`,`v`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
      `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
         mid.storage_trace` by fs[storage_trace_domain_def] >>
      fs[Abbr `post`] >>
      qpat_assum `!marks mid HG tm t v. _ ==> gas_prefix_full _ _ _ _ _` irule >>
      conj_tac >- (qexists_tac `marks` >> simp[]) >> metis_tac[])
  >- metis_tac[ISR]
  >- (simp[Abbr `source`] >> irule requests_outcomes_frame_bind_all >>
      simp[evaluate_requests_outcomes_frame, requests_outcomes_frame_read_result]) >>
  simp[Abbr `source`] >> irule storage_trace_frame_bind_all >>
  simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]
QED
