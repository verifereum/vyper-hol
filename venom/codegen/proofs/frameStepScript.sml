(* Our frame's run, one of its own steps at a time, for the sufficient-gas
 * theorems: the step from one state of the frame to the next, and the
 * gas the frame has left.
 *
 * TOP-LEVEL:
 *   frame_next          - es1 is the frame's next state after es
 *   frame_last          - es's step ends the frame
 *   frame_gas_left      - the top frame's unused gas
 *   frame_next_run_call - the frame's run from es passes through es1
 *   frame_reaches_next  - a later state of the frame comes at or after the
 *                         next one
 *   frame_reaches_last  - nothing of the frame comes after its last state
 *)
Theory frameStep
Ancestors
  frameGas frameObsStep vfmDecreasesGas vfmExecution vfmExecutionProp vfmContext list
  relation

(* es1 is the next state of es's frame: its step, or a call's step and
   the callee's run back to es's depth. *)
Definition frame_next_def:
  frame_next es es1 <=>
    ?v. step es = (INL (), v) /\
        LENGTH es1.contexts = LENGTH es.contexts /\
        (es1 = v \/
         LENGTH v.contexts = SUC (LENGTH es.contexts) /\
         run_call v = SOME (INL (), es1))
End

(* es's step ends the frame: no state of the frame follows es. *)
Definition frame_last_def:
  frame_last es <=>
    !v. step es = (INL (), v) ==> LENGTH v.contexts < LENGTH es.contexts
End

Definition frame_gas_left_def:
  frame_gas_left es =
    case es.contexts of
      (c, rb) :: rest => c.msgParams.gasLimit - c.gasUsed
    | [] => 0
End

Theorem frame_next_run_call:
  !es es1. frame_next es es1 ==> run_call es1 = run_call es
Proof
  rw[frame_next_def] >> gvs[]
  >- metis_tac[run_call_same_depth_step] >>
  metis_tac[run_call_enter_return]
QED

(* The callee's run from u back to depth below n passes through no state
   below n, so a state below n reached from u comes at or after t. *)
Theorem run_call_tr_reaches[local]:
  !n r s t z.
    run_call_tr n (r, s) = (INL (), t) /\ ISL r /\
    RTC (\a b. LENGTH a.contexts >= d /\ step a = (INL (), b)) s z /\
    LENGTH z.contexts < n ==>
    RTC (\a b. LENGTH a.contexts >= d /\ step a = (INL (), b)) t z
Proof
  recInduct run_call_tr_ind >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >> Cases_on `r` >> gvs[] >>
  qpat_x_assum `run_call_tr _ _ = _` mp_tac >>
  simp[Once run_call_tr_def] >>
  IF_CASES_TAC >- (strip_tac >> gvs[]) >>
  strip_tac >>
  qpat_x_assum `RTC _ s z`
    (strip_assume_tac o ONCE_REWRITE_RULE [RTC_CASES1]) >- gvs[] >>
  gvs[] >> first_x_assum irule >> simp[] >> metis_tac[]
QED

(* A state s of es's frame (reached by steps at its depth or deeper, as
   frame_inst_at) is es itself or comes from the frame's next state. *)
Theorem frame_reaches_next:
  !es es1 s.
    frame_next es es1 /\
    RTC (\a b. LENGTH a.contexts >= LENGTH es.contexts /\
               step a = (INL (), b)) es s /\
    LENGTH s.contexts = LENGTH es.contexts ==>
    s = es \/
    RTC (\a b. LENGTH a.contexts >= LENGTH es.contexts /\
               step a = (INL (), b)) es1 s
Proof
  rpt strip_tac >>
  qpat_x_assum `RTC _ es s`
    (strip_assume_tac o ONCE_REWRITE_RULE [RTC_CASES1])
  >- (disj1_tac >> first_assum (ACCEPT_TAC o SYM)) >>
  gvs[frame_next_def] >>
  qpat_x_assum `RTC _ _ s`
    (strip_assume_tac o ONCE_REWRITE_RULE [RTC_CASES1]) >- gvs[] >>
  gvs[run_call_eq_tr] >> disj2_tac >>
  drule run_call_tr_reaches >> simp[] >> disch_then irule >> simp[]
QED

Theorem frame_reaches_last:
  !es s.
    frame_last es /\
    RTC (\a b. LENGTH a.contexts >= LENGTH es.contexts /\
               step a = (INL (), b)) es s /\
    LENGTH s.contexts = LENGTH es.contexts ==>
    s = es
Proof
  rpt strip_tac >>
  qpat_x_assum `RTC _ _ _` mp_tac >> simp[Once RTC_CASES1] >>
  strip_tac >- simp[] >>
  gvs[frame_last_def] >>
  qpat_x_assum `RTC _ _ _` mp_tac >> simp[Once RTC_CASES1] >>
  strip_tac >> gvs[]
QED

(* add_frame_gas g gives a well-formed frame at least g gas left. *)
Theorem wf_state_frame_gas_left:
  !g es. wf_state es ==> g <= frame_gas_left (add_frame_gas g es)
Proof
  rw[wf_state_def, add_frame_gas_def] >>
  Cases_on `es.contexts` >> gvs[] >>
  PairCases_on `h` >> gvs[frame_gas_left_def, wf_context_def]
QED

Theorem run_call_tr_forward[local]:
  !n r s t d.
    run_call_tr n (r,s) = (INL (),t) /\ ISL r /\ d <= n ==>
    RTC (\a b. LENGTH a.contexts >= d /\ step a = (INL (),b)) s t
Proof
  recInduct run_call_tr_ind >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >> Cases_on `r` >> gvs[] >>
  qpat_x_assum `run_call_tr _ _ = _` mp_tac >>
  simp[Once run_call_tr_def] >>
  IF_CASES_TAC >- (strip_tac >> gvs[]) >>
  strip_tac >> Cases_on `step s` >> rename1 `(q,v)` >>
  Cases_on `q` >> gvs[]
  >- simp[RTC_RULES] >>
  gvs[Once run_call_tr_def]
QED

Theorem frame_next_reaches:
  !es es1. frame_next es es1 ==>
    RTC (\a b. LENGTH a.contexts >= LENGTH es.contexts /\
               step a = (INL (),b)) es es1
Proof
  rw[frame_next_def]
  >- simp[RTC_RULES] >>
  gvs[run_call_eq_tr] >>
  `run_call_tr (SUC (LENGTH es.contexts)) (INL (),v) = (INL (),es1)` by
    simp[Once run_call_tr_def] >>
  drule run_call_tr_forward >>
  disch_then (qspec_then `LENGTH es.contexts` mp_tac) >>
  simp[] >> strip_tac >> simp[RTC_RULES]
QED

Theorem frame_next_inst_at:
  frame_next es es1 /\ frame_inst_at es s op ==>
  s = es \/ frame_inst_at es1 s op
Proof
  strip_tac >>
  `LENGTH es1.contexts = LENGTH es.contexts` by fs[frame_next_def] >>
  drule frame_reaches_next >>
  fs[frame_inst_at_def] >> metis_tac[]
QED

Theorem frame_next_inst_at_prefix:
  frame_next es es1 /\ frame_inst_at es1 s op ==> frame_inst_at es s op
Proof
  strip_tac >> drule frame_next_reaches >> strip_tac >>
  irule frame_inst_at_prefix >> qexists_tac `es1` >> fs[frame_next_def]
QED
