(* Preserve the full head run's path when composing the field prefixes. *)
Theory s1PrefixStructLitBind
Ancestors
  s1PrefixCompose s1PrefixProps s1PrefixOfVV gasOutcomeFull
  exprSimWordArgs s1PrefixStructLitFieldSource[qualified]
  vyperStorageTrace vyperStorageFootprint vyperState list sum

Triviality marked_normal_post:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s,G,tn) Q R ==>
  ?marks. gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s,G,tn)
    (\H res mid G1 tn1 t.
      Q H res mid G1 tn1 t /\
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (s,G,tn) marks (OK t,G1,tn1) /\
      !tail. source (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
        (res,mid with gas_obs := tail)) R
Proof
  rw[gas_outcome_full_def] >> qexists_tac `marks` >>
  metis_tac[]
QED

Theorem eval_exprs_cons_prefix_from_singleton:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (eval_exprs cx [e]) (es,s,G,tn)
    (\H res mid G1 tn1 t. ?v. res = INL [v] /\ Head H v mid G1 tn1 t) R /\
  (!H res mid gt r. R H res mid gt r ==> ISR res) /\
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (eval_exprs cx [e]) (es,s,G,tn) /\
  (!marks v mid G1 tn1 t.
    (!tail. eval_exprs cx [e]
      (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL [v],mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (s,G,tn) marks (OK t,G1,tn1) /\ Head H v mid G1 tn1 t) ==>
    gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
      (eval_exprs cx rest) (mid,t,G1,tn1)) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (eval_exprs cx (e::rest)) (es,s,G,tn)
Proof
  strip_tac >> drule marked_normal_post >>
  disch_then (qx_choose_then `head_marks` assume_tac) >>
  PURE_ONCE_REWRITE_TAC[s1PrefixStructLitFieldSourceTheory.structlit_cons_singleton_bind] >>
  pop_assum (mp_then Any irule gas_prefix_full_bind) >>
  simp[evaluate_storage_trace_frame, evaluate_requests_outcomes_frame,
       storage_trace_frame_bind_all, storage_trace_frame_return] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  map_every qx_gen_tac [`marks`, `vs`, `mid`, `G1`, `tn1`, `t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `?v. vs = [v]` by metis_tac[] >> gvs[] >>
  `!st. SND (bind (eval_exprs cx rest) (\ws. return (v::ws)) st) =
        SND (eval_exprs cx rest st)` by
    (gen_tac >> Cases_on `eval_exprs cx rest st` >>
     rename1 `_ = (res,ee)` >> Cases_on `res` >> simp[bind_def,return_def]) >>
  drule gas_prefix_full_state_cong >> disch_then (fn th => once_rewrite_tac[th]) >>
  qpat_assum `!marks v mid G1 tn1 t. _ ==> gas_prefix_full _ _ _ _ _`
    (qspec_then `head_marks` irule) >>
  simp[] >> metis_tac[]
QED
