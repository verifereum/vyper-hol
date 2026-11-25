Theory bodyRawCallForcedFullBind
Ancestors
  exprSimFullBundleProps exprSimDefs stmtSimProps gasOutcomeFullCompose
  gasExemptCert gasExplicitSites gasSummary vyperStorageTrace vyperStorageFootprint
  fragGasOriginPtr vyperInterpreter vyperState

(* Preserve the observations and ghosts of the normal read witness. The
   exceptional branch uses the same exception at the continuation's type. *)
Theorem raw_call_forced_bind_full:
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx))
    (ei,u,Gu,tnu)
    (expr_sim_full_post (DF,lo,dframe,ctx,func) cenv cx e (ei,ca,cm,u,x,Gu,tnu))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !h. r = Halt h ==> allocas_below_fmp h)) /\
  (!H exc ee gt r. expr_exit (INR exc : value + vyperState$exception) r /\
     halt_exit H cx ee (INR exc) r ==> R H (INR exc) ee gt r) /\
  (!v. storage_trace_frame (nextv v)) /\
  (!marks v mid Gm tnm m.
    (!tail. bind (eval_expr cx e) (read_result cx)
      (ei with gas_obs := gas_explicit marks u.vs_gas_readings ++ tail) =
        (INL v, mid with gas_obs := tail)) /\
    mid.gas_obs = [] /\ ~m.vs_halted /\ storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      expr_sim_full_post (DF,lo,dframe,ctx,func) cenv cx e
        (ei,ca,cm,u,x,Gu,tnu) H (INL v : value + vyperState$exception) mid Gm tnm m /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (u,Gu,tnu) marks (OK m,Gm,tnm)) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (nextv v) (mid,m,Gm,tnm) Q R) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (bind (eval_expr cx e) (read_result cx)) nextv)
    (ei,u,Gu,tnu) Q R
Proof
  strip_tac >> irule gas_outcome_full_bind_all_path >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` (irule_at Any) >> gvs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[cj 5 evaluate_storage_trace_frame,storage_trace_frame_read_result])
  >- first_assum ACCEPT_TAC >>
  qexists_tac `\H (res : value + vyperState$exception) mid Gm tnm m.
    expr_sim_full_post (DF,lo,dframe,ctx,func) cenv cx e (ei,ca,cm,u,x,Gu,tnu)
      H res mid Gm tnm m /\ mid.gas_obs = [] /\ ~m.vs_halted` >>
  reverse conj_tac
  >- (BETA_TAC >> irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
      simp[NoAsms] >> rpt strip_tac >>
      Cases_on `res` >> gvs[expr_exit_def,halt_exit_def]) >>
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
    by fs[storage_trace_domain_def] >>
  `?v. res = INL v /\ mid.gas_obs = [] /\ ~t.vs_halted` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_sim_full_post _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     simp[NoAsms,expr_sim_full_post_def] >> metis_tac[]) >>
  gvs[] >> qpat_assum `!marks v mid Gm tnm m. _` irule >>
  simp[] >> qexists_tac `marks` >> simp[]
QED
