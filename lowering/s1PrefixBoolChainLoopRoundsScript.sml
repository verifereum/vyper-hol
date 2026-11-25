(* Compose the certificates of reached loop bodies at their pushed scopes. *)
Theory s1PrefixBoolChainLoopRounds
Ancestors
  s1PrefixForRounds s1PrefixForHandlers s1PrefixInvalidTraceDomain
  s1PrefixCompose s1PrefixFrame s1PrefixProps s1PrefixDefs
  vyperStorageTrace vyperCallOutcomeFrame vyperInterpreter vyperState sum list

val _ = Parse.hide "body";

Triviality loop_round_body_prefix:
  head = bind (read_result cx a) (push_scope_with_var nm tyv) /\
  ~s.vs_halted /\
  (storage_trace_domain cx st0 es.storage_trace ==>
    gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
      head (es,s,G,tn) Q (\H res ee gt r. ?ex. res = INR ex /\ E H ex ee gt r)) /\
  (!marks eb G1 tn1 t.
    (!tail. head (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
       (INL (),eb with gas_obs := tail)) /\
    storage_trace_domain cx st0 eb.storage_trace /\
    (!H. valid_horizon cx st0 H eb.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) marks (OK t,G1,tn1) /\
       Q H (INL ()) eb G1 tn1 t) ==>
    (?Qb Rb. gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
       (eval_stmts cx body) (eb,t,G1,tn1) Qb Rb) /\
    gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
       (eval_stmts cx body) (eb,t,G1,tn1)) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (do v <- read_result cx a; push_scope_with_var nm tyv v;
        finally (try (do eval_stmts cx body; return F od)
          handle_loop_exception) pop_scope od) (es,s,G,tn)
Proof
  strip_tac >> qpat_x_assum `head = _` SUBST_ALL_TAC >>
  qabbrev_tac `head = bind (read_result cx a) (push_scope_with_var nm tyv)` >>
  qabbrev_tac `clean = finally (try (ignore_bind (eval_stmts cx body) (return F))
    handle_loop_exception) pop_scope` >>
  `bind head (\u:unit. clean) =
     bind (read_result cx a) (\v. ignore_bind (push_scope_with_var nm tyv v) clean)` by
    simp[Abbr `head`,bind_assoc,ignore_bind_def] >>
  pop_assum (SUBST1_TAC o SYM) >>
  `storage_trace_frame head` by
    (simp[Abbr `head`] >> irule storage_trace_frame_bind_all >>
     simp[storage_trace_frame_read_result,storage_trace_frame_state_updates]) >>
  `storage_trace_frame clean` by
    simp[Abbr `clean`,storage_trace_frame_finally,storage_trace_frame_try,
         storage_trace_frame_ignore_bind,storage_trace_frame_pop_scope,
         storage_trace_frame_loop_handler,storage_trace_frame_return,evaluate_storage_trace_frame] >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (irule gas_prefix_full_invalid_trace_domain >> simp[storage_trace_frame_bind_all]) >>
  qpat_assum `storage_trace_domain _ _ _ ==> gas_outcome_full _ _ _ _ _ _ _ _` drule >>
  disch_then (mp_then Any irule gas_prefix_full_bind_replay) >>
  BETA_TAC >> simp[] >>
  conj_tac >- suspend "body" >>
  conj_tac >- (rpt strip_tac >> simp[ISR]) >>
  conj_tac >-
    (simp[Abbr `head`] >> irule requests_outcomes_frame_bind_all >>
     simp[requests_outcomes_frame_read_result,requests_outcomes_frame_def,
          state_rel_frame_def,push_scope_with_var_def,return_def]) >>
  irule gas_prefix_full_no_outcome >> simp[Abbr `head`] >> rpt gen_tac >>
  Cases_on `read_result cx a (es with gas_obs := gobs)` >> rename1 `_ = (rr,er)` >>
  `er = es with gas_obs := gobs` by metis_tac[read_result_state] >>
  Cases_on `rr` >> simp[bind_def,push_scope_with_var_def,return_def] >>
  strip_tac >> gvs[DROP_LENGTH_NIL]
QED

Resume loop_round_body_prefix[body]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!marks eb G1 tn1 t. _` (drule_all_then strip_assume_tac) >>
  simp[Abbr `clean`] >> irule for_body_cleanup_prefix >>
  qpat_assum `gas_outcome_full _ _ _ _ (eval_stmts _ _) _ _ _` (irule_at Any) >>
  simp[] >>
  qpat_x_assum `!tail. head _ = (INL (),_)` (qspec_then `[]` mp_tac) >>
  simp[Abbr `head`,bind_def] >>
  qmatch_goalsub_abbrev_tac `read_result cx a start` >>
  Cases_on `read_result cx a start` >> rename1 `_ = (rr,er)` >>
  Cases_on `rr` >> simp[push_scope_with_var_def,return_def] >>
  disch_then (mp_tac o AP_TERM ``evaluation_state_scopes``) >>
  Cases_on `mid.scopes` >> simp[]
QED

Finalise loop_round_body_prefix

(* The round post carries the invariant only along a continuing round.
   The body callback is at the actual entry after the read and scope push. *)
Theorem bool_chain_loop_rounds_prefix:
  (!a rs es s G tn.
    ~s.vs_halted /\
    (!H. valid_horizon cx st0 H es.storage_trace ==> Inv H (a::rs) es G tn s) /\
    gas_admissible (eval_for cx tyv nm body (a::rs)) ok es ==>
    gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
      (do v <- read_result cx a; push_scope_with_var nm tyv v;
          finally (try (do eval_stmts cx body; return F od)
            handle_loop_exception) pop_scope od) (es,s,G,tn)
      (\H res ee G1 tn1 t. ee.gas_obs = [] /\ ~t.vs_halted /\
        ?b. res = INL b /\ (b ==> Done H ee G1 tn1 t) /\ (~b ==> Inv H rs ee G1 tn1 t))
      (\H res ee gt r. ?ex. res = INR ex /\ R H ex ee gt r)) /\
  (!a rs es s G tn.
    ~s.vs_halted /\
    (!H. valid_horizon cx st0 H es.storage_trace ==> Inv H (a::rs) es G tn s) /\
    gas_admissible (eval_for cx tyv nm body (a::rs)) ok es /\
    storage_trace_domain cx st0 es.storage_trace ==>
    gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
      (bind (read_result cx a) (push_scope_with_var nm tyv)) (es,s,G,tn)
      (Entry a rs es s G tn) (\H res ee gt r. ?ex. res = INR ex /\ E H ex ee gt r)) /\
  (!a rs es s G tn marks eb G1 tn1 t.
    ~s.vs_halted /\
    (!H. valid_horizon cx st0 H es.storage_trace ==> Inv H (a::rs) es G tn s) /\
    gas_admissible (eval_for cx tyv nm body (a::rs)) ok es /\
    (!tail. bind (read_result cx a) (push_scope_with_var nm tyv)
      (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL (),eb with gas_obs := tail)) /\
    storage_trace_domain cx st0 eb.storage_trace /\
    (!H. valid_horizon cx st0 H eb.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) marks (OK t,G1,tn1) /\
       Entry a rs es s G tn H (INL ()) eb G1 tn1 t) ==>
    (?Qb Rb. gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
       (eval_stmts cx body) (eb,t,G1,tn1) Qb Rb) /\
    gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
       (eval_stmts cx body) (eb,t,G1,tn1)) ==>
  !rs es s G tn.
    ~s.vs_halted /\
    (!H. valid_horizon cx st0 H es.storage_trace ==> Inv H rs es G tn s) /\
    gas_admissible (eval_for cx tyv nm body rs) ok es ==>
    gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
      (eval_for cx tyv nm body rs) (es,s,G,tn)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  irule eval_for_rounds_prefix >>
  conj_tac
  >- (qexists_tac `\rs b. if b then return () else eval_for cx tyv nm body rs` >> simp[]) >>
  simp[] >>
  qexistsl_tac [`Done`,`Inv`,`R`,`ok`,
    `\a. do v <- read_result cx a; push_scope_with_var nm tyv v;
         finally (try (do eval_stmts cx body; return F od)
           handle_loop_exception) pop_scope od`, `tops`] >>
  BETA_TAC >> simp[] >>
  map_every qx_gen_tac [`a`,`rest`,`er`,`z`,`J`,`tz`] >> strip_tac >>
  irule loop_round_body_prefix >> simp[] >>
  qexistsl_tac [`E`,`Entry a rest er z J tz`,`tops`] >>
  simp[] >> rpt gen_tac >> strip_tac >>
  qpat_assum `!a rs es s G tn marks eb G1 tn1 t. _`
    (drule_all_then ACCEPT_TAC)
QED
