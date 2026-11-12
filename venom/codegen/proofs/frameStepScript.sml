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

Theorem consume_gas_frame_gas:
  consume_gas k es = (r,s') /\ 0 < frame_gas_left es /\
  k <= frame_gas_left es ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es = frame_gas_left s' + k
Proof
  namedCases_on `es.contexts` ["", "head tail"] >>
  simp[frame_gas_left_def] >> PairCases_on `head` >>
  simp[consume_gas_def, get_current_context_def, set_current_context_def,
       bind_def, ignore_bind_def, assert_def, return_def, fail_def,
       frame_gas_left_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), frame_gas_left_def] >> decide_tac
QED

Theorem assert_not_static_frame_gas:
  assert_not_static es = (r,s') ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left s' = frame_gas_left es
Proof
  namedCases_on `es.contexts` ["", "head tail"] >>
  simp[assert_not_static_def, get_static_def, get_current_context_def,
       bind_def, assert_def, return_def, fail_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem write_storage_frame_gas:
  write_storage address key value es = (r,s') ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left s' = frame_gas_left es
Proof
  simp[write_storage_def, update_accounts_def, return_def] >>
  strip_tac >> gvs[frame_gas_left_def]
QED

Theorem update_gas_refund_frame_gas:
  update_gas_refund updates es = (r,s') ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left s' = frame_gas_left es
Proof
  PairCases_on `updates` >>
  namedCases_on `es.contexts` ["", "head tail"] >>
  simp[update_gas_refund_def, get_current_context_def,
       set_current_context_def, bind_def, return_def, fail_def] >>
  rpt strip_tac >> gvs[frame_gas_left_def] >>
  PairCases_on `head` >> gvs[frame_gas_left_def]
QED

Theorem step_stack_gas_budget:
  es.contexts = (c,rb)::rest /\ c.gasUsed <= c.msgParams.gasLimit /\
  (!args. cost args <= B) /\ B <= c.msgParams.gasLimit - c.gasUsed /\
  (do args <- pop_stack n; consume_gas (cost args); push_stack (f args) od) es = (r,s') ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  strip_tac >>
  gvs[pop_stack_def, bind_def, ignore_bind_def,
      get_current_context_def, return_def, assert_def,
      set_current_context_def, consume_gas_def, push_stack_def,
      LET_THM, AllCaseEqs()] >>
  gvs[frame_gas_left_def] >>
  first_x_assum (qspec_then `TAKE n c.stack` mp_tac) >> decide_tac
QED

Theorem step_stack_fixed_gas_budget:
  (do args <- pop_stack n; consume_gas k; push_stack (f args) od) es = (r,s') ==>
  !c rb rest B.
  es.contexts = (c,rb)::rest /\ c.gasUsed <= c.msgParams.gasLimit /\
  k <= B /\ B <= c.msgParams.gasLimit - c.gasUsed ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  disch_tac >> rpt gen_tac >> strip_tac >>
  irule step_stack_gas_budget >>
  conj_tac >- (qexistsl_tac [`c`, `rb`, `rest`] >> simp[]) >>
  qexistsl_tac [`K k`, `f`, `n`] >> simp[]
QED

Theorem step_binop_gas_budget:
  step_binop op g es = (r,s') ==>
  !c rb rest B.
  es.contexts = (c,rb)::rest /\ c.gasUsed <= c.msgParams.gasLimit /\
  static_gas op <= B /\ B <= c.msgParams.gasLimit - c.gasUsed ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  rewrite_tac[step_binop_def] >> disch_tac >>
  metis_tac[Q.INST [`f` |-> `\args. g (EL 0 args) (EL 1 args)`]
         step_stack_fixed_gas_budget]
QED

Theorem step_monop_gas_budget:
  step_monop op g es = (r,s') ==>
  !c rb rest B.
  es.contexts = (c,rb)::rest /\ c.gasUsed <= c.msgParams.gasLimit /\
  static_gas op <= B /\ B <= c.msgParams.gasLimit - c.gasUsed ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  rewrite_tac[step_monop_def] >> disch_tac >>
  metis_tac[Q.INST [`f` |-> `\args. g (EL 0 args)`]
         step_stack_fixed_gas_budget]
QED

Theorem step_modop_gas_budget:
  step_modop op g es = (r,s') ==>
  !c rb rest B.
  es.contexts = (c,rb)::rest /\ c.gasUsed <= c.msgParams.gasLimit /\
  static_gas op <= B /\ B <= c.msgParams.gasLimit - c.gasUsed ==>
  r <> INR (SOME OutOfGas) /\
  frame_gas_left es <= frame_gas_left s' + B
Proof
  rewrite_tac[step_modop_def, LET_THM] >> disch_tac >>
  metis_tac[Q.INST [`f` |-> `\args. if w2n (EL 2 args) = 0 then 0w
                 else n2w (g (w2n (EL 0 args)) (w2n (EL 1 args))
                           MOD w2n (EL 2 args))`]
         step_stack_fixed_gas_budget]
QED

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

Theorem access_address_gas_observation:
  access_address addr s = (r,t) ==>
  t.contexts = s.contexts /\ r <> INR (SOME OutOfGas) /\
  (!n. r = INL n ==> n <= 2600)
Proof
  Cases_on `s.msdomain` >>
  simp[access_address_def, domain_check_def, set_domain_def,
       bind_def, ignore_bind_def, return_def, fail_def, LET_THM] >>
  rpt IF_CASES_TAC >>
  gvs[vfmConstantsTheory.warm_access_cost_def,
      vfmConstantsTheory.cold_access_cost_def] >>
  strip_tac >> gvs[]
QED
