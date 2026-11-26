(* Compose the request-bearing stages of source Append evaluation. *)
Theory s1PrefixAppendSourceChildren
Ancestors
  s1PrefixCompose s1PrefixProps vyperInterpreter vyperState vyperStorageTrace
  guardMutationTrace list sum

Theorem append_source_children_prefix:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (eval_target_place cx target) (es,s,G,tn)
    QT (\H res ee gt r. ?exc. res = INR exc /\ RT H (INR exc) ee gt r) /\
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (eval_target_place cx target) (es,s,G,tn) /\
  (!marks p mid G1 tn1 t.
     (!tail. eval_target_place cx target
        (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
        (INL p,mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==> QT H (INL p) mid G1 tn1 t) ==>
     gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
       (vyperState$bind (eval_expr cx e) (read_result cx)) (mid,t,G1,tn1)
       QV (\H res ee gt r. ?exc. res = INR exc /\ RV H (INR exc) ee gt r) /\
     gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
       (vyperState$bind (eval_expr cx e) (read_result cx)) (mid,t,G1,tn1)) /\
  (!H v ee G2 tn2 u. QV H (INL v) ee G2 tn2 u ==> ~u.vs_halted) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (eval_stmt cx (Append target e)) (es,s,G,tn)
Proof
  strip_tac >> simp[Once evaluate_def, GSYM bind_assoc] >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (mp_then Any irule gas_prefix_full_bind) >> BETA_TAC >>
  simp[evaluate_storage_trace_frame, evaluate_requests_outcomes_frame,
       storage_trace_frame_bind_all, storage_trace_frame_read_result,
       storage_trace_frame_append_place] >>
  reverse conj_tac >- (rpt strip_tac >> gvs[sumTheory.ISR]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!marks p mid G1 tn1 t. _ ==> _ /\ _`
    (qspecl_then [`marks`,`v`,`mid`,`G1`,`tn1`,`t`] mp_tac) >>
  simp[] >> strip_tac >>
  irule gas_prefix_full_bind_no_outcome >> BETA_TAC >>
  pure_rewrite_tac[ETA_THM] >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, storage_trace_frame_append_place,
       requests_outcomes_frame_bind_all, evaluate_requests_outcomes_frame,
       requests_outcomes_frame_read_result] >>
  conj_tac >- (rpt strip_tac >> drule append_place_trace_unchanged >> simp[]) >>
  qexistsl [`QV`,`\H res ee gt r. ?exc. res = INR exc /\ RV H (INR exc) ee gt r`,
            `tops`] >>
  simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> gvs[sumTheory.ISR]
QED
