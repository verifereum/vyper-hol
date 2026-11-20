Theory requestCutVisitReachability
Ancestors
  requestCutOracleFrames requestCutOracleClip frameRawProjection
  jointRequestCut contextCodegenRel venomState list rich_list arithmetic

(* Recover the full source frame at the matched visit. The same entry
   oracle gives both programs the same unread suffix at request k. *)
Theorem request_cut_restore_visit:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  v.vs_requests = vt.vs_requests /\ v.vs_outcomes = vt.vs_outcomes /\
  clip0 = (v with vs_outcomes := TAKE (k - LENGTH v.vs_requests) v.vs_outcomes) /\
  frame_reachable clip0 C stk PG G tn fn i sc /\ sc.vs_outcomes = [] /\
  EVERY wf_function CT.ctx_functions /\
  frame_reachable vt CT stkT PT gT un fnT j t /\ LENGTH t.vs_requests = k ==>
  ?stk' s. frame_reachable v C stk' PG G tn fn i s /\
    (s with vs_outcomes := []) = sc /\
    LENGTH s.vs_requests = k /\ s.vs_outcomes = t.vs_outcomes
Proof
  strip_tac >>
  `raw_reachable vt CT fnT j t` by metis_tac[frame_reachable_raw] >>
  drule_all raw_reachable_recorded_oracle_drop >> strip_tac >>
  `LENGTH t.vs_requests + LENGTH t.vs_outcomes =
    LENGTH vt.vs_requests + LENGTH vt.vs_outcomes` by
    (qpat_assum `frame_reachable vt CT stkT PT gT un fnT j t`
       (mp_tac o MATCH_MP (SPEC_ALL frame_reachable_oracle_length)) >> simp[]) >>
  `LENGTH sc.vs_requests = k` by
    (qpat_assum `frame_reachable clip0 C stk PG G tn fn i sc`
       (mp_tac o MATCH_MP (SPEC_ALL frame_reachable_oracle_length)) >>
     simp[LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF] >> decide_tac) >>
  `(clip0 with vs_outcomes := clip0.vs_outcomes ++ t.vs_outcomes) = v` by
    fs[TAKE_DROP, venom_state_component_equality] >>
  qexistsl_tac [`MAP (\f. f with cf_state :=
      (f.cf_state with vs_outcomes := f.cf_state.vs_outcomes ++ t.vs_outcomes)) stk`,
    `sc with vs_outcomes := t.vs_outcomes`] >>
  simp[] >>
  qpat_assum `frame_reachable clip0 C stk PG G tn fn i sc`
    (mp_tac o MATCH_MP (Q.INST [`tail` |-> `t.vs_outcomes`]
      (SPEC_ALL frame_reachable_outcome_suffix))) >>
  simp[venom_state_component_equality]
QED

Theorem request_cut_clip_visit:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  frame_reachable v C stk PG G tn fn i s /\ LENGTH s.vs_requests = k ==>
  ?stk'. frame_reachable
    (v with vs_outcomes := TAKE (k - LENGTH v.vs_requests) v.vs_outcomes)
    C stk' PG G tn fn i (s with vs_outcomes := [])
Proof
  strip_tac >>
  drule frame_reachable_outcome_clip >> simp[] >>
  disch_then (qspec_then `k` mp_tac) >> simp[] >> metis_tac[]
QED
