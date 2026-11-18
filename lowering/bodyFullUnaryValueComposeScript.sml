Theory bodyFullUnaryValueCompose
Ancestors
  gasOutcomeFullCompose gasExemptCert
  vyperInterpreter vyperStorageTrace vyperStorageFootprint

(* Pass the child's actual evaluation and all its horizon posts to a unary suffix. *)
Theorem gas_outcome_full_unary_value:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn) childQ childR /\
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
      (next v) (mid,t,HG,tm) Q R) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (bind (eval_expr cx e) (read_result cx)) next)
    (es,s,G,tn) Q R
Proof
  strip_tac >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >- simp[]
  >~ [`storage_trace_frame (bind _ _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[cj 5 evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid`,`t`,`v`] >> gvs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[]) >>
  qexists_tac `\H res ee HG tm t. childQ H res ee HG tm t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
      simp[]) >>
  qx_genl_tac [`marks`,`res`,`mid`,`HG`,`tm`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  `?v. res = INL v` by metis_tac[] >>
  disj1_tac >> qexists_tac `v` >> simp[] >>
  qpat_assum `!marks res mid HG tm t v. _ ==> gas_outcome_full _ _ _ _ _ _ _ _`
    (qspecl_then [`marks`,`res`,`mid`,`HG`,`tm`,`t`,`v`] mp_tac) >>
  simp[] >> metis_tac[]
QED
