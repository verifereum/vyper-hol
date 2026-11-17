Theory assignPlaceGasCompose
Ancestors
  aggregateCountedOutcome vyperInterpreter vyperState
  vyperStorageTrace gasOutcome gasSummary gasExemptCert

(* Keep the RHS replay until read_result has captured its value. *)
Theorem assign_place_result_outcome:
  gas_outcome F (cx_tops cx) (ctx,func) cx st0
    (eval_expr cx e) (es,s0) P Exit /\
  (!H res ee t. P H res ee t ==> ?pv. res = INL pv) /\
  (!H res ee r. Exit H res ee r ==>
     ?ex. res = INR ex /\ R H (INR ex) ee r) /\
  (!marks pv mid t.
     gas_marked_exec F (ctx,func) (eval_expr cx e) (es,s0)
       marks (INL pv) mid (OK t) /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
       P H (INL pv) (mid with gas_obs := []) t) ==>
     gas_outcome F (cx_tops cx) (ctx,func) cx st0
       (bind (read_result cx pv)
         (\v. bind (eval_target_place cx bt) (\p. write_place cx p v)))
       (mid with gas_obs := [],t) Q R) ==>
  gas_outcome F (cx_tops cx) (ctx,func) cx st0
    (eval_stmt cx (Assign (BaseTarget bt) e)) (es,s0) Q R
Proof
  strip_tac >> simp[Once evaluate_def] >>
  match_mp_tac counted_outcome_bind_exec >> BETA_TAC >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (rpt strip_tac >>
      pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_bind_result >>
      goal_assum (drule_at Any) >> simp[GSYM ignore_bind_def])
  >- (rpt strip_tac >>
      pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_error_result >> simp[GSYM ignore_bind_def]) >>
  gen_tac >>
  irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_read_result] >> gen_tac >>
  irule storage_trace_frame_bind_all >>
  simp[evaluate_storage_trace_frame, storage_trace_frame_write_place]
QED

Theorem assign_place_target_outcome:
  gas_outcome memory tops (ctx,func) cx st0
    (eval_target_place cx bt) (es,s0) Qa Ra /\
  (!H res ee t. Qa H res ee t ==> ?p. res = INL p) /\
  (!marks p mid t.
    gas_marked_exec memory (ctx,func) (eval_target_place cx bt)
      (es,s0) marks (INL p) mid (OK t) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      Qa H (INL p) (mid with gas_obs := []) t) ==>
    gas_outcome memory tops (ctx,func) cx st0 (write_place cx p v)
      (mid with gas_obs := [],t) Q R) /\
  (!H res ee r. Ra H res ee r ==>
    ?ex. res = INR ex /\ R H (INR ex) ee r) ==>
  gas_outcome memory tops (ctx,func) cx st0
    (bind (eval_target_place cx bt) (\p. write_place cx p v)) (es,s0) Q R
Proof
  strip_tac >>
  match_mp_tac (Q.INST [`P` |-> `Qa`, `Exit` |-> `Ra`]
    counted_outcome_bind_exec) >> BETA_TAC >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (rpt strip_tac >>
      pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_bind_place >>
      goal_assum (drule_at Any) >> simp[GSYM ignore_bind_def])
  >- (rpt strip_tac >>
      pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_error_place >> simp[GSYM ignore_bind_def]) >>
  simp[storage_trace_frame_write_place]
QED
