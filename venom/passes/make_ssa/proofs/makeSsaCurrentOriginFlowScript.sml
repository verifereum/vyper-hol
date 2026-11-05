Theory makeSsaCurrentOriginFlow
Ancestors list alist pair

Datatype:
  current_flow_event =
    CurrentFlowPair 'a 'b 'c |
    CurrentFlowSource 'a 'c |
    CurrentFlowTarget 'b 'c |
    CurrentFlowCopy 'b 'b
End

Datatype:
  current_flow_request = CurrentFlowBlocked | CurrentFlowDischarged |
    CurrentFlowPending 'a 'b
End

Definition current_flow_step_def:
  (current_flow_step (CurrentFlowPair v y origin) M N M' N' <=>
    M' = (v,origin)::M /\ N' = (y,origin)::N) /\
  (current_flow_step (CurrentFlowSource v origin) M N M' N' <=>
    M' = (v,origin)::M /\ N' = N) /\
  (current_flow_step (CurrentFlowTarget y origin) M N M' N' <=>
    M' = M /\ N' = (y,origin)::N) /\
  (current_flow_step (CurrentFlowCopy x y) M N M' N' <=>
    ?origin. ALOOKUP N y = SOME origin /\ M' = M /\ N' = (x,origin)::N)
End

Definition current_origin_flow_replay_def:
  (current_origin_flow_replay [] M N M' N' <=> M'=M /\ N'=N) /\
  (current_origin_flow_replay (e::es) M N M' N' <=>
    ?Mi Ni. current_flow_step e M N Mi Ni /\
      current_origin_flow_replay es Mi Ni M' N')
End

Definition current_request_step_def:
  (current_request_step e CurrentFlowBlocked = CurrentFlowBlocked) /\
  (current_request_step e CurrentFlowDischarged = CurrentFlowDischarged) /\
  (current_request_step (CurrentFlowPair a b origin) (CurrentFlowPending v y) =
    if v=a /\ y=b then CurrentFlowDischarged
    else if v=a \/ y=b then CurrentFlowBlocked else CurrentFlowPending v y) /\
  (current_request_step (CurrentFlowSource a origin) (CurrentFlowPending v y) =
    if v=a then CurrentFlowBlocked else CurrentFlowPending v y) /\
  (current_request_step (CurrentFlowTarget b origin) (CurrentFlowPending v y) =
    if y=b then CurrentFlowBlocked else CurrentFlowPending v y) /\
  (current_request_step (CurrentFlowCopy x z) (CurrentFlowPending v y) =
    CurrentFlowPending v (if y=x then z else y))
End

Definition current_request_pullback_def:
  (current_request_pullback [] r = r) /\
  (current_request_pullback (e::es) r =
    current_request_step e (current_request_pullback es r))
End

Theorem current_origin_flow_replay_append:
  !es M N M' N' fs.
  current_origin_flow_replay (es ++ fs) M N M' N' <=>
  ?Mi Ni. current_origin_flow_replay es M N Mi Ni /\
    current_origin_flow_replay fs Mi Ni M' N'
Proof
  Induct >> simp[current_origin_flow_replay_def] >> metis_tac[]
QED

Theorem current_request_pullback_append:
  !es fs r. current_request_pullback (es ++ fs) r =
    current_request_pullback es (current_request_pullback fs r)
Proof
  Induct >> simp[current_request_pullback_def]
QED

Theorem current_request_pullback_absorbing:
  !es. current_request_pullback es CurrentFlowBlocked = CurrentFlowBlocked /\
    current_request_pullback es CurrentFlowDischarged = CurrentFlowDischarged
Proof
  Induct >> simp[current_request_pullback_def, current_request_step_def]
QED

Theorem current_request_step_pending:
  current_flow_step e M N M' N' /\
  current_request_step e (CurrentFlowPending v y) = CurrentFlowPending a b ==>
  ALOOKUP M' v = ALOOKUP M a /\ ALOOKUP N' y = ALOOKUP N b /\ a=v
Proof
  Cases_on `e` >> simp[current_flow_step_def, current_request_step_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem current_request_step_discharged:
  current_flow_step e M N M' N' /\
  current_request_step e (CurrentFlowPending v y) = CurrentFlowDischarged ==>
  ?origin. ALOOKUP M' v = SOME origin /\ ALOOKUP N' y = SOME origin
Proof
  Cases_on `e` >> simp[current_flow_step_def, current_request_step_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem current_request_pending_source:
  !es v y a b. current_request_pullback es (CurrentFlowPending v y) = CurrentFlowPending a b ==> a=v
Proof
  Induct >> simp[current_request_pullback_def] >> rpt strip_tac >>
  Cases_on `current_request_pullback es (CurrentFlowPending v y)` >>
  gvs[current_request_step_def] >> Cases_on `h` >>
  gvs[current_request_step_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem current_request_pending_transport:
  !es M0 N0 M N v y a b.
  current_origin_flow_replay es M0 N0 M N /\
  current_request_pullback es (CurrentFlowPending v y) = CurrentFlowPending a b ==>
  ALOOKUP M v = ALOOKUP M0 a /\ ALOOKUP N y = ALOOKUP N0 b
Proof
  Induct >> simp[current_origin_flow_replay_def, current_request_pullback_def] >>
  rpt strip_tac >>
  Cases_on `current_request_pullback es (CurrentFlowPending v y)` >>
  gvs[current_request_step_def] >>
  drule_all current_request_step_pending >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> metis_tac[]
QED

Theorem current_request_entry:
  current_origin_flow_replay es M0 N0 M N /\
  current_request_pullback es (CurrentFlowPending v y) = CurrentFlowPending v z /\
  ALOOKUP M0 v = ALOOKUP N0 z ==> ALOOKUP M v = ALOOKUP N y
Proof
  metis_tac[current_request_pending_transport]
QED

Theorem current_request_discharged_sound:
  !es M0 N0 M N v y.
  current_origin_flow_replay es M0 N0 M N /\
  current_request_pullback es (CurrentFlowPending v y) = CurrentFlowDischarged ==>
  ?origin. ALOOKUP M v = SOME origin /\ ALOOKUP N y = SOME origin
Proof
  Induct >> simp[current_origin_flow_replay_def, current_request_pullback_def] >>
  rpt strip_tac >>
  Cases_on `current_request_pullback es (CurrentFlowPending v y)` >>
  gvs[current_request_step_def]
  >- (first_x_assum drule_all >> metis_tac[]) >>
  drule_all current_request_step_discharged >> strip_tac >>
  drule_all current_request_pending_transport >> strip_tac >> metis_tac[]
QED

Theorem current_request_step_pair_inverse:
  current_request_step e (CurrentFlowPending v y) = CurrentFlowDischarged ==>
  ?origin. e = CurrentFlowPair v y origin
Proof
  Cases_on `e` >> simp[current_request_step_def, AllCaseEqs()]
QED

Theorem current_request_producer:
  !es M0 N0 M N v y.
  current_origin_flow_replay es M0 N0 M N /\
  current_request_pullback es (CurrentFlowPending v y) = CurrentFlowDischarged ==>
  ?pre a b origin post Mb Nb Ma Na.
    es = pre ++ CurrentFlowPair a b origin :: post /\ LENGTH pre < LENGTH es /\
    current_origin_flow_replay pre M0 N0 Mb Nb /\
    current_origin_flow_replay [CurrentFlowPair a b origin] Mb Nb Ma Na /\
    current_origin_flow_replay post Ma Na M N /\
    current_request_pullback post (CurrentFlowPending v y) = CurrentFlowPending a b /\
    ALOOKUP M v = SOME origin /\ ALOOKUP N y = SOME origin
Proof
  Induct >> simp[current_origin_flow_replay_def, current_request_pullback_def] >>
  rpt strip_tac >>
  Cases_on `current_request_pullback es (CurrentFlowPending v y)` >>
  gvs[current_request_step_def]
  >- (first_x_assum drule_all >> strip_tac >>
      qexistsl_tac [`h::pre`, `a`, `b`, `origin`, `post`, `Mb`, `Nb`, `Ma`, `Na`] >>
      fs[current_origin_flow_replay_def] >> metis_tac[]) >>
  drule current_request_step_pair_inverse >> strip_tac >> gvs[] >>
  drule_all current_request_pending_transport >> strip_tac >>
  qexistsl_tac [`[]`, `a`, `b`, `origin`, `es`, `M0`, `N0`, `Mi`, `Ni`] >>
  gvs[current_origin_flow_replay_def, current_flow_step_def]
QED

(* Trace lists the request before scanning, then after each backwards event.
   The first Pending -> Discharged transition identifies the producer index. *)
Definition current_request_trace_def:
  (current_request_trace [] r = [r]) /\
  (current_request_trace (e::es) r = current_request_trace es r ++
    [current_request_step e (current_request_pullback es r)])
End

Theorem current_request_trace_last:
  !es r. LAST (current_request_trace es r) = current_request_pullback es r
Proof
  Induct >> simp[current_request_trace_def, current_request_pullback_def]
QED

Theorem current_request_trace_length:
  !es r. LENGTH (current_request_trace es r) = SUC (LENGTH es)
Proof
  Induct >> simp[current_request_trace_def]
QED

Theorem current_origin_flow_two_visits_test:
  current_origin_flow_replay
    [CurrentFlowPair (0:num) (0:num) (11:num); CurrentFlowPair 0 0 22]
    [] [] [(0,22);(0,11)] [(0,22);(0,11)] /\
  current_request_pullback
    [CurrentFlowPair (0:num) (0:num) (11:num); CurrentFlowPair 0 0 22]
    (CurrentFlowPending 0 0) = CurrentFlowDischarged
Proof
  EVAL_TAC >> simp[]
QED

Theorem current_origin_flow_copy_old_clobber_test:
  current_origin_flow_replay
    [CurrentFlowPair (0:num) (0:num) (11:num); CurrentFlowCopy 1 0; CurrentFlowTarget 0 22]
    [] [] [(0,11)] [(0,22);(1,11);(0,11)] /\
  current_request_pullback
    [CurrentFlowPair (0:num) (0:num) (11:num); CurrentFlowCopy 1 0; CurrentFlowTarget 0 22]
    (CurrentFlowPending 0 1) = CurrentFlowDischarged
Proof
  EVAL_TAC >> simp[]
QED

Theorem current_origin_flow_current_clobber_test:
  current_origin_flow_replay
    [CurrentFlowPair (0:num) (0:num) (11:num); CurrentFlowCopy 1 0; CurrentFlowTarget 1 22]
    [] [] [(0,11)] [(1,22);(1,11);(0,11)] /\
  current_request_pullback
    [CurrentFlowPair (0:num) (0:num) (11:num); CurrentFlowCopy 1 0; CurrentFlowTarget 1 22]
    (CurrentFlowPending 0 1) = CurrentFlowBlocked
Proof
  EVAL_TAC >> simp[]
QED
