Theory ctorDeployLoweringFrameTrace
Ancestors
  callTrace

Theorem observe_no_root_call:
  obs.pending = NONE /\
  (LENGTH s.contexts = d ==> ~observable_call (FST (HD s.contexts))) ==>
  (observe d s (r,s') obs).entries = obs.entries /\
  (observe d s (r,s') obs).pending = NONE
Proof
  strip_tac >> simp[observe_def] >>
  Cases_on `ISL r` >> simp[] >>
  Cases_on `LENGTH s.contexts = d` >> simp[] >>
  Cases_on `next_opcode (FST (HD s.contexts)) = SOME Gas /\ LENGTH s'.contexts = d` >> simp[] >>
  Cases_on `d < LENGTH s.contexts /\ LENGTH s'.contexts = d` >> simp[]
QED

Theorem frame_obs_tr_no_root_call:
  !d obs s r s'.
    (!t. P t ==> P (SND (step t))) /\
    (!t. P t /\ LENGTH t.contexts = d ==>
         ~observable_call (FST (HD t.contexts))) /\
    P s /\ step s = (r,s') /\ obs.pending = NONE ==>
    (frame_obs_tr d obs s (r,s')).entries = obs.entries /\
    (frame_obs_tr d obs s (r,s')).pending = NONE
Proof
  recInduct frame_obs_tr_ind >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `~observable_call (FST (HD s.contexts)) \/ LENGTH s.contexts <> d` by metis_tac[] >>
  `(observe d s (r,s') obs).entries = obs.entries /\
   (observe d s (r,s') obs).pending = NONE` by
    (irule observe_no_root_call >> simp[] >> metis_tac[]) >>
  `P s'` by metis_tac[pairTheory.SND] >>
  simp[Ntimes frame_obs_tr_def 2] >>
  Cases_on `ISR r \/ LENGTH s'.contexts < d` >> simp[] >>
  first_x_assum (qspec_then `observe d s (r,s') obs` mp_tac) >>
  Cases_on `r` >> gvs[]
QED

Theorem call_trace_empty_step_invariant:
  (!t. P t ==> P (SND (step t))) /\
  (!t. P t /\ LENGTH t.contexts = LENGTH es.contexts ==>
       ~observable_call (FST (HD t.contexts))) /\ P es ==>
  call_trace es = []
Proof
  strip_tac >> simp[call_trace_def, frame_obs_def] >>
  mp_tac (Q.SPECL
    [`LENGTH es.contexts`, `<|entries := []; readings := []; pending := NONE|>`,
     `es`, `FST (step es)`, `SND (step es)`]
    frame_obs_tr_no_root_call) >> simp[]
QED
