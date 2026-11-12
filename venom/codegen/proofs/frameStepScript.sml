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
  frameObsStep vfmDecreasesGas vfmExecution vfmExecutionProp vfmContext list
  relation vfmSameFrame vfmRunCall callTrace

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

(* PC handling never charges gas, including an invalid jump. *)
Theorem frame_gas_left_inc_pc_or_jump:
  s.contexts <> [] /\ inc_pc_or_jump op s = (r,t) ==>
  LENGTH t.contexts = LENGTH s.contexts /\
  frame_gas_left t = frame_gas_left s
Proof
  namedCases_on `s.contexts` ["", "head tail"] >> simp[] >>
  PairCases_on `head` >>
  Cases_on `is_call op` >>
  simp[inc_pc_or_jump_def, return_def, bind_def, ignore_bind_def,
       get_current_context_def, set_current_context_def, assert_def,
       fail_def, frame_gas_left_def] >>
  Cases_on `head0.jumpDest` >> simp[] >>
  rpt strip_tac >>
  gvs[AllCaseEqs(), bind_def, assert_def, fail_def,
      set_current_context_def, return_def, frame_gas_left_def]
QED

Theorem frame_next_noncall_gas_bound:
  es.contexts = (c,rb)::rest /\ wf_context c /\
  next_opcode c = SOME op /\ ~is_call op /\
  (!r s'. step_inst op es = (r,s') /\
     LENGTH s'.contexts = LENGTH es.contexts ==>
     frame_gas_left es <= frame_gas_left s' + B) /\
  frame_next es es1 ==>
  frame_gas_left es <= frame_gas_left es1 + B
Proof
  strip_tac >>
  `preserves_same_frame (step_inst op)` by
    simp[preserves_same_frame_step_inst_not_call] >>
  `step es = handle (do step_inst op; inc_pc_or_jump op od) handle_step es` by
    (simp[step_def, handle_def, get_current_context_def, bind_def,
          return_def] >>
     Cases_on `LENGTH c.msgParams.code <= c.pc`
     >- (`FLOOKUP c.msgParams.parsed c.pc = NONE` by
           (Cases_on `FLOOKUP c.msgParams.parsed c.pc` >> simp[] >>
            gvs[wf_context_def] >>
            drule FLOOKUP_parse_code_SOME_less_LENGTH >> simp[]) >>
         gvs[next_opcode_def, step_inst_def, finish_def, ignore_bind_def,
             bind_def, set_return_data_def, get_current_context_def,
             set_current_context_def, return_def, reraise_def]) >>
     gvs[next_opcode_def, ignore_bind_def, bind_def]) >>
  qpat_x_assum `frame_next _ _` mp_tac >>
  simp[frame_next_def] >>
  asm_rewrite_tac[] >>
  simp[handle_def, ignore_bind_def, bind_def] >>
  Cases_on `step_inst op es` >> rename1 `step_inst op es = (raw,u)` >>
  `same_frame_rel es u` by
    gvs[preserves_same_frame_def] >>
  `u.contexts <> [] /\ LENGTH u.contexts = LENGTH es.contexts` by
    (fs[same_frame_rel_def] >> Cases_on `u.contexts` >> gvs[]) >>
  Cases_on `raw` >> simp[]
  >- (Cases_on `inc_pc_or_jump op u` >>
      rename1 `inc_pc_or_jump op u = (pcresult,t)` >>
      `LENGTH t.contexts = LENGTH u.contexts /\
       frame_gas_left t = frame_gas_left u` by
        (drule_all frame_gas_left_inc_pc_or_jump >> simp[]) >>
      `t.contexts <> []` by (Cases_on `t.contexts` >> gvs[]) >>
      Cases_on `pcresult` >> simp[] >> strip_tac >> gvs[] >>
      drule_all handle_step_inl_pops >> simp[] >> decide_tac) >>
  strip_tac >>
  drule_all handle_step_inl_pops >> gvs[]
QED

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
