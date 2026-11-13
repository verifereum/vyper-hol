Theory bodyPtrSubscriptMarkedCompose
Ancestors
  gasSummaryComposePtr fragGasPathPtr gasExemptCert gasOutcome
  gasSummary gasSummaryCompose exprSimDefs vyperState list
  gasStorage vyperStorageTrace fragGasMode

(* The index run's summary, whichever way it ends, gives the composed run's:
   bad storage when no horizon is valid at its end, else a summary. *)
Theorem array_index_summary_compose_ptr[local]:
  gas_marked_exec F (ctx,func) a (es,s0) left (INL captured) mid (OK t) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
       gas_path_ptr (D H) 0 ctx func PG G0 tn0 s0 (LENGTH left) G1 tn1
         (OK t)) /\
  storage_trace_frame b /\ (!v. storage_trace_frame (k captured v)) /\
  gas_summary_ptr_at D (ctx,func) PG cx st0 marks b
    (mid with gas_obs := [],t,G1,tn1)
    (\H res ee G tn u. ?v. res = INL v /\ V H v ee G tn u)
    (\H res ee gt out. ?exc. res = INR exc /\ R H (INR exc) ee gt out) /\
  (!imarks raw v Gi tni u.
     gas_marked_exec F (ctx,func) b (mid with gas_obs := [],t) imarks
       (INL v) raw (OK u) /\
     (!H. valid_horizon cx st0 H raw.storage_trace ==>
          gas_path_ptr (D H) 0 ctx func PG G1 tn1 t (LENGTH imarks) Gi tni
            (OK u) /\
          V H v (raw with gas_obs := []) Gi tni u) ==>
     gas_summary_ptr_at D (ctx,func) PG cx st0 [] (k captured v)
       (raw with gas_obs := [],u,Gi,tni) Q R) ==>
  gas_bad_storage_at cx st0 (bind a (\r. bind b (k r))) es s0
    (left ++ marks) \/
  gas_summary_ptr_at D (ctx,func) PG cx st0 (left ++ marks)
    (bind a (\r. bind b (k r))) (es,s0,G0,tn0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ b _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_summary_ptr_at_def]) >>
  Cases_on `?H. valid_horizon cx st0 H es_end.storage_trace`
  >- suspend "live" >>
  disj1_tac >> irule gas_bad_storage_at_bind_right >>
  goal_assum (drule_at Any) >> BETA_TAC >>
  irule gas_bad_storage_at_bind_left >> simp[] >>
  irule gas_bad_storage_at_no_horizon >> fs[] >> metis_tac[]
QED

Resume array_index_summary_compose_ptr[live]:
  pop_assum strip_assume_tac >> disj2_tac >>
  `gas_path ctx func t (LENGTH marks) r` by
    (first_assum drule >> metis_tac[gas_path_ptr_erase]) >>
  `gas_marked_exec F (ctx,func) b (mid with gas_obs := [],t) marks res
     es_end r` by simp[gas_marked_exec_def, gas_marked_path_def] >>
  `storage_trace_frame (bind b (k captured))` by
    (irule storage_trace_frame_bind_all >> simp[]) >>
  `gas_summary_ptr_at D (ctx,func) PG cx st0 marks (bind b (k captured))
     (mid with gas_obs := [],t,G1,tn1) Q R` suffices_by
    (strip_tac >>
     mp_tac (Q.INST [`source` |-> `a`, `next` |-> `\r. bind b (k r)`,
                     `v` |-> `captured`, `right` |-> `marks`]
               gas_summary_ptr_at_bind_normal) >>
     simp[]) >>
  first_assum drule >> strip_tac >> gvs[]
  >- suspend "normal" >>
  mp_tac (Q.INST [`fin` |-> `es_end`, `es` |-> `mid with gas_obs := []`,
                  `s0` |-> `t`, `G0` |-> `G1`, `tn0` |-> `tn1`,
                  `source` |-> `b`, `next` |-> `k captured`]
            gas_summary_ptr_at_bind_exception) >>
  impl_tac
  >- (fs[] >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
      gvs[fragExecTheory.exit_result_def]) >>
  simp[]
QED

Resume array_index_summary_compose_ptr[normal]:
  rename1 `V H v _ G tn u` >>
  `!H. valid_horizon cx st0 H es_end.storage_trace ==>
       gas_path_ptr (D H) 0 ctx func PG G1 tn1 t (LENGTH marks) G tn
         (OK u) /\ V H v (es_end with gas_obs := []) G tn u` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >>
     gvs[fragExecTheory.exit_result_def]) >>
  mp_tac (Q.INST [`right` |-> `[]`, `left` |-> `marks`, `source` |-> `b`,
                  `next` |-> `k captured`, `mid` |-> `es_end`, `t` |-> `u`,
                  `G1` |-> `G`, `tn1` |-> `tn`,
                  `es` |-> `mid with gas_obs := []`, `s0` |-> `t`,
                  `G0` |-> `G1`, `tn0` |-> `tn1`]
            gas_summary_ptr_at_bind_normal |> REWRITE_RULE [APPEND_NIL]) >>
  impl_tac
  >- (fs[] >> first_x_assum irule >> fs[]) >>
  simp[]
QED
Finalise array_index_summary_compose_ptr

(* The callback sees the actual marked run, not an invented evaluation
   equation at an initial state whose gas observations have been erased. *)
Theorem array_index_outcome_compose_ptr:
  gas_marked_exec F (ctx,func)
    (a : evaluation_state -> eval_result evaluation_result)
    (es,s0) left (INL captured) mid (OK t) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
       gas_path_ptr (D H) 0 ctx func PG G0 tn0 s0 (LENGTH left) G1 tn1
         (OK t)) /\
  storage_trace_frame (b : evaluation_state -> value evaluation_result) /\
  (!v. storage_trace_frame (k captured v)) /\
  gas_outcome_ptr D tops (ctx,func) PG cx st0 b
    (mid with gas_obs := [],t,G1,tn1)
    (\H res ee G tn u. ?v. res = INL v /\ V H v ee G tn u)
    (\H res ee gt out. ?exc. res = INR exc /\ R H (INR exc) ee gt out) /\
  (!imarks raw v Gi tni u.
     gas_marked_exec F (ctx,func) b (mid with gas_obs := [],t) imarks
       (INL v) raw (OK u) /\
     (!H. valid_horizon cx st0 H raw.storage_trace ==>
          gas_path_ptr (D H) 0 ctx func PG G1 tn1 t (LENGTH imarks) Gi tni
            (OK u) /\
          V H v (raw with gas_obs := []) Gi tni u) ==>
     gas_summary_ptr_at D (ctx,func) PG cx st0 [] (k captured v)
       (raw with gas_obs := [],u,Gi,tni) Q R) ==>
  gas_outcome_ptr D tops (ctx,func) PG cx st0
    (bind a (\r. bind b (k r))) (es,s0,G0,tn0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ b _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_ptr_def]) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `left ++ marks`
  >- (disj1_tac >> irule gas_bad_storage_at_bind_right >>
      goal_assum (drule_at Any) >> BETA_TAC >>
      irule gas_bad_storage_at_bind_left >> simp[])
  >- (`gas_bad_storage_at cx st0 (bind a (\r. bind b (k r))) es s0
         (left ++ marks) \/
       gas_summary_ptr_at D (ctx,func) PG cx st0 (left ++ marks)
         (bind a (\r. bind b (k r))) (es,s0,G0,tn0) Q R` by
        (irule array_index_summary_compose_ptr >> metis_tac[]) >>
      simp[]) >>
  disj2_tac >> disj2_tac >> qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  pure_rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_bind_result >>
  goal_assum (drule_at Any) >> BETA_TAC >> pure_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_error_value >> first_assum ACCEPT_TAC
QED

(* Match the whole normal post before inspecting its value tag. *)
Theorem array_index_outcome_post_compose_ptr:
  gas_outcome_ptr D tops (ctx,func) PG cx st0
    (b : evaluation_state -> value evaluation_result)
    (mid with gas_obs := [],t,G1,tn1) Qidx
    (\H res ee gt out. ?exc. res = INR exc /\ R H (INR exc) ee gt out) ==>
  gas_marked_exec F (ctx,func)
    (a : evaluation_state -> eval_result evaluation_result)
    (es,s0) left (INL captured) mid (OK t) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
       gas_path_ptr (D H) 0 ctx func PG G0 tn0 s0 (LENGTH left) G1 tn1
         (OK t)) /\
  storage_trace_frame b /\ (!v. storage_trace_frame (k captured v)) /\
  (!H res ee Gi tni u. Qidx H res ee Gi tni u ==> ?v. res = INL v) /\
  (!imarks raw v Gi tni u.
     gas_marked_exec F (ctx,func) b (mid with gas_obs := [],t) imarks
       (INL v) raw (OK u) /\
     (!H. valid_horizon cx st0 H raw.storage_trace ==>
          gas_path_ptr (D H) 0 ctx func PG G1 tn1 t (LENGTH imarks) Gi tni
            (OK u) /\
          Qidx H (INL v) (raw with gas_obs := []) Gi tni u) ==>
     gas_summary_ptr_at D (ctx,func) PG cx st0 [] (k captured v)
       (raw with gas_obs := [],u,Gi,tni) Q R) ==>
  gas_outcome_ptr D tops (ctx,func) PG cx st0
    (bind a (\r. bind b (k r))) (es,s0,G0,tn0) Q R
Proof
  rpt strip_tac >>
  irule array_index_outcome_compose_ptr >>
  qexistsl_tac [`G1`, `\H v ee Gi tni u. Qidx H (INL v) ee Gi tni u`,
    `captured`, `left`, `mid`, `t`, `tn1`] >>
  simp[] >> conj_tac >- metis_tac[] >>
  irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED
