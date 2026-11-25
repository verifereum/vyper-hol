(* Source composition for a stored struct field followed by the other fields. *)
Theory s1PrefixStructLitFieldSource
Ancestors
  s1PrefixCompose s1PrefixOfVV s1PrefixProps exprSimWordArgs
  vyperStorageTrace vyperInterpreter vyperState

Theorem structlit_singleton_result[local]:
  eval_exprs cx [e] st =
    case bind (eval_expr cx e) (read_result cx) st of
      (INL v, mid) => (INL [v], mid)
    | (INR exc, mid) => (INR exc, mid)
Proof
  rewrite_tac[eval_exprs_cons_action] >>
  `eval_exprs cx [] = return []` by simp[Once evaluate_def] >>
  Cases_on `bind (eval_expr cx e) (read_result cx) st` >>
  rename1 `_ = (res,mid)` >> Cases_on `res` >> simp[bind_def, return_def]
QED

Theorem structlit_cons_singleton_bind:
  eval_exprs cx (e::rest) =
    bind (eval_exprs cx [e])
      (\vs. bind (eval_exprs cx rest) (\rs. return (HD vs::rs)))
Proof
  simp[FUN_EQ_THM] >> gen_tac >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [eval_exprs_cons_action])) >>
  qabbrev_tac `head = bind (eval_expr cx e) (read_result cx)` >>
  `eval_exprs cx [e] x =
     case head x of (INL v,mid) => (INL [v],mid)
                  | (INR exc,mid) => (INR exc,mid)` by
    simp[Abbr `head`, structlit_singleton_result] >>
  Cases_on `head x` >> rename1 `_ = (res,mid)` >>
  Cases_on `res` >> simp[bind_def]
QED

Theorem structlit_fields_cons_prefix_from_singleton:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (eval_exprs cx [e]) (es,s,G,tn) Q1 R1 /\
  (!H res ee gt r. R1 H res ee gt r ==> ISR res) /\
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn) /\
  (!marks v mid G1 tn1 t.
     (!tail. eval_exprs cx [e] (es with gas_obs :=
       gas_explicit marks s.vs_gas_readings ++ tail) =
       (INL [v],mid with gas_obs := tail)) /\
     (!tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs :=
       gas_explicit marks s.vs_gas_readings ++ tail) =
       (INL v,mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==> Q1 H (INL [v]) mid G1 tn1 t) ==>
     gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
       (eval_exprs cx rest) (mid,t,G1,tn1)) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (eval_exprs cx (e::rest)) (es,s,G,tn)
Proof
  strip_tac >>
  `!qe. SND (eval_exprs cx [e] qe) =
        SND (bind (eval_expr cx e) (read_result cx) qe)` by
    (qx_gen_tac `qe` >> simp[structlit_singleton_result] >>
     Cases_on `bind (eval_expr cx e) (read_result cx) qe` >>
     rename1 `_ = (res,mid)` >> Cases_on `res` >> simp[]) >>
  `gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
     (eval_exprs cx [e]) (es,s,G,tn)` by
    (drule_then (fn th => rewrite_tac[th]) gas_prefix_full_state_cong >>
     first_assum ACCEPT_TAC) >>
  once_rewrite_tac[structlit_cons_singleton_bind] >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ Q1 R1`
    (mp_then Any irule gas_prefix_full_bind) >>
  simp[evaluate_storage_trace_frame, evaluate_requests_outcomes_frame,
       storage_trace_frame_bind_all, storage_trace_frame_return] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  map_every qx_gen_tac [`marks`,`vs`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  `?v. vs = [v]` by
    (qpat_assum `!tail. eval_exprs cx [e] _ = _` (qspec_then `[]` mp_tac) >>
     simp[NoAsms, structlit_singleton_result, AllCaseEqs()] >> metis_tac[]) >>
  gvs[] >>
  `!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL v,mid with gas_obs := tail)` by
    (qx_gen_tac `tail` >>
     qpat_assum `!tail. eval_exprs cx [e] _ = _` (qspec_then `tail` mp_tac) >>
     simp[NoAsms, structlit_singleton_result, AllCaseEqs()]) >>
  `!qe. SND (bind (eval_exprs cx rest) (\rs. return (v::rs)) qe) =
        SND (eval_exprs cx rest qe)` by
    (qx_gen_tac `qe` >> Cases_on `eval_exprs cx rest qe` >>
     rename1 `_ = (res,ee)` >> Cases_on `res` >> simp[bind_def, return_def]) >>
  qpat_assum `!qe. SND (bind (eval_exprs cx rest) _ qe) = _`
    (fn eq => rewrite_tac[MATCH_MP gas_prefix_full_state_cong eq]) >>
  first_x_assum irule >> metis_tac[]
QED
