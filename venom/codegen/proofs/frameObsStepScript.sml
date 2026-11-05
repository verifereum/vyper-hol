(*
 * One step of a frame's run against its call trace, GAS readings and
 * run_call.  The frame is at depth LENGTH es.contexts; a step either
 * stays at that depth, enters a child (one deeper) whose run_call comes
 * back to it, or ends the frame (an exception or a drop below it).
 *
 * TOP-LEVEL:
 *   frame_obs_plain_step, frame_obs_gas_step, frame_obs_call_same_depth,
 *   frame_obs_call_enter, frame_obs_terminal - call_trace/gas_readings
 *   run_call_same_depth_step, run_call_enter_return,
 *   run_call_terminal_step - run_call
 *)

Theory frameObsStep
Ancestors
  callTrace frameOutcome vfmExecution vfmExecutionProp vfmDecreasesGas
  vfmAccountFrame vfmContextLength

Theorem observe_prefix:
  !d s rs obs ep gp.
  observe d s rs (obs with <|entries := ep ++ obs.entries;
                            readings := gp ++ obs.readings|>) =
  (observe d s rs obs) with
    <|entries := ep ++ (observe d s rs obs).entries;
      readings := gp ++ (observe d s rs obs).readings|>
Proof
  rpt gen_tac >> PairCases_on `rs` >>
  simp[observe_def] >>
  rpt (IF_CASES_TAC >> simp[listTheory.APPEND_ASSOC]) >>
  Cases_on `obs.pending` >> simp[] >>
  rename1 `SOME x` >> PairCases_on `x` >> simp[listTheory.APPEND_ASSOC]
QED

Theorem frame_obs_tr_prefix:
  !d obs s r post ep gp.
  frame_obs_tr d
    (obs with <|entries := ep ++ obs.entries;
               readings := gp ++ obs.readings|>) s (r, post) =
  (frame_obs_tr d obs s (r, post)) with
    <|entries := ep ++ (frame_obs_tr d obs s (r, post)).entries;
      readings := gp ++ (frame_obs_tr d obs s (r, post)).readings|>
Proof
  recInduct frame_obs_tr_ind >> rpt strip_tac >>
  once_rewrite_tac[frame_obs_tr_def] >>
  simp[observe_prefix] >> IF_CASES_TAC >> simp[] >>
  first_x_assum (qspec_then `observe d s (r,s') obs` mp_tac) >>
  Cases_on `r` >> gvs[]
QED

Theorem frame_obs_tr_child:
  !h r post d pre obs t.
  h = SUC d /\ d < LENGTH pre.contexts /\
  run_call_tr h (r,post) = (INL (),t) /\ LENGTH t.contexts = d ==>
  frame_obs_tr d obs pre (r,post) =
  frame_obs_tr d (observe d pre ((INL () : unit + exception option),t) obs)
    t (step t)
Proof
  recInduct run_call_tr_ind >> rpt strip_tac >> gvs[] >>
  Cases_on `r` >- (
    Cases_on `LENGTH s.contexts < SUC (LENGTH t.contexts)` >- (
      qpat_x_assum `run_call_tr _ _ = _` mp_tac >>
      once_rewrite_tac[run_call_tr_def] >> simp[] >> strip_tac >> gvs[] >>
      once_rewrite_tac[frame_obs_tr_def] >> simp[observe_def]) >>
    qpat_x_assum `run_call_tr _ _ = _` mp_tac >>
    once_rewrite_tac[run_call_tr_def] >> simp[] >> strip_tac >>
    once_rewrite_tac[frame_obs_tr_def] >> simp[observe_def]) >>
  qpat_x_assum `run_call_tr _ _ = _` mp_tac >>
  once_rewrite_tac[run_call_tr_def] >> simp[]
QED

(* ===== call_trace and gas_readings ===== *)

Theorem frame_obs_plain_step:
  step es = (INL (), es1) /\ LENGTH es1.contexts = LENGTH es.contexts /\
  next_opcode (FST (HD es.contexts)) <> SOME Gas /\
  ~observable_call (FST (HD es.contexts)) ==>
  call_trace es = call_trace es1 /\ gas_readings es = gas_readings es1
Proof
  strip_tac >>
  simp[call_trace_def, gas_readings_def, frame_obs_def] >>
  once_rewrite_tac[frame_obs_tr_def] >> simp[observe_def]
QED

Theorem frame_obs_gas_step:
  step es = (INL (), es1) /\ LENGTH es1.contexts = LENGTH es.contexts /\
  next_opcode (FST (HD es.contexts)) = SOME Gas ==>
  call_trace es = call_trace es1 /\
  gas_readings es = HD (FST (HD es1.contexts)).stack :: gas_readings es1
Proof
  strip_tac >>
  simp[call_trace_def, gas_readings_def, frame_obs_def] >>
  once_rewrite_tac[frame_obs_tr_def] >> simp[observe_def] >>
  qspecl_then [`LENGTH es.contexts`,
    `<|entries := []; readings := []; pending := NONE|>`] mp_tac
    frame_obs_tr_prefix >>
  disch_then (qspec_then `es1` mp_tac) >>
  disch_then (qspecl_then [`FST (step es1)`, `SND (step es1)`] mp_tac) >>
  disch_then (qspecl_then [`[]`, `[HD (FST (HD es1.contexts)).stack]`] mp_tac) >>
  simp[] >> disch_then SUBST1_TAC >> simp[]

QED

Theorem frame_obs_call_same_depth:
  step es = (INL (), es1) /\ LENGTH es1.contexts = LENGTH es.contexts /\
  observable_call (FST (HD es.contexts)) ==>
  call_trace es =
    (request_of es,
     outcome_of (request_of es).cr_kind es1
       (LENGTH (FST (HD es.contexts)).logs) (LENGTH es.rollback.toDelete)) ::
    call_trace es1 /\
  gas_readings es = gas_readings es1
Proof
  strip_tac >>
  `next_opcode (FST (HD es.contexts)) <> SOME Gas` by
    (fs[observable_call_def] >> metis_tac[]) >>
  simp[call_trace_def, gas_readings_def, frame_obs_def] >>
  once_rewrite_tac[frame_obs_tr_def] >> simp[observe_def] >>
  qspecl_then [`LENGTH es.contexts`,
    `<|entries := []; readings := []; pending := NONE|>`] mp_tac
    frame_obs_tr_prefix >>
  disch_then (qspec_then `es1` mp_tac) >>
  disch_then (qspecl_then [`FST (step es1)`, `SND (step es1)`] mp_tac) >>
  disch_then (qspecl_then
    [`[(request_of es, outcome_of (request_of es).cr_kind es1
        (LENGTH (FST (HD es.contexts)).logs) (LENGTH es.rollback.toDelete))]`,
     `[]`] mp_tac) >>
  simp[] >> disch_then SUBST1_TAC >> simp[]
QED

(* The child's run_call ends at the first state back at the frame's depth. *)
Theorem frame_obs_call_enter:
  step es = (INL (), es1) /\ LENGTH es1.contexts = SUC (LENGTH es.contexts) /\
  observable_call (FST (HD es.contexts)) /\
  run_call es1 = SOME (INL (), es2) /\
  LENGTH es2.contexts = LENGTH es.contexts ==>
  call_trace es =
    (request_of es,
     outcome_of (request_of es).cr_kind es2
       (LENGTH (FST (HD es.contexts)).logs) (LENGTH es.rollback.toDelete)) ::
    call_trace es2 /\
  gas_readings es = gas_readings es2
Proof
  strip_tac >>
  `run_call_tr (SUC (LENGTH es.contexts)) (step es1) = (INL (),es2)` by
    gvs[run_call_eq_tr] >>
  Cases_on `step es1` >>
  drule_at (Pat `run_call_tr _ _ = _`) frame_obs_tr_child >>
  disch_then (qspecl_then [`LENGTH es.contexts`, `es1`] mp_tac) >>
  simp[] >> disch_tac >>
  simp[call_trace_def, gas_readings_def, frame_obs_def] >>
  once_rewrite_tac[frame_obs_tr_def] >> simp[observe_def] >>
  qspecl_then [`LENGTH es.contexts`,
    `<|entries := []; readings := []; pending := NONE|>`] mp_tac
    frame_obs_tr_prefix >>
  disch_then (qspec_then `es2` mp_tac) >>
  disch_then (qspecl_then [`FST (step es2)`, `SND (step es2)`] mp_tac) >>
  disch_then (qspecl_then
    [`[(request_of es, outcome_of (request_of es).cr_kind es2
        (LENGTH (FST (HD es.contexts)).logs) (LENGTH es.rollback.toDelete))]`,
     `[]`] mp_tac) >>
  simp[] >> disch_then SUBST1_TAC >> simp[]
QED

Theorem frame_obs_terminal:
  step es = (r, es1) /\ (ISR r \/ LENGTH es1.contexts < LENGTH es.contexts) ==>
  call_trace es = [] /\ gas_readings es = []
Proof
  strip_tac >>
  simp[call_trace_def, gas_readings_def, frame_obs_def] >>
  once_rewrite_tac[frame_obs_tr_def] >>
  Cases_on `r` >> gvs[observe_def]

QED

(* ===== run_call ===== *)

Theorem run_call_same_depth_step:
  step es = (INL (), es1) /\ LENGTH es1.contexts = LENGTH es.contexts ==>
  run_call es1 = run_call es
Proof
  strip_tac >> simp[run_call_eq_tr] >>
  once_rewrite_tac[run_call_tr_def] >> simp[]
QED

Theorem run_call_enter_return:
  step es = (INL (), es1) /\ LENGTH es1.contexts = SUC (LENGTH es.contexts) /\
  run_call es1 = SOME (INL (), es2) /\
  LENGTH es2.contexts = LENGTH es.contexts ==>
  run_call es2 = run_call es
Proof
  strip_tac >> drule run_call_step_equation >> disch_then SUBST1_TAC >>
  `LENGTH es.contexts <= LENGTH es1.contexts` by simp[] >>
  drule_all run_call_child_continuation >> disch_then SUBST1_TAC >>
  simp[run_call_def, arithmeticTheory.GREATER_EQ]
QED

Theorem run_call_terminal_step:
  step es = (r, es1) /\ (ISR r \/ LENGTH es1.contexts < LENGTH es.contexts) ==>
  run_call es = SOME (r, es1)
Proof
  strip_tac >> simp[run_call_eq_tr] >>
  once_rewrite_tac[run_call_tr_def] >> Cases_on `r` >> gvs[]
QED
