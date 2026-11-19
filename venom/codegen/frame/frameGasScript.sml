(* Our frame with more gas, for the sufficient-gas theorems.
 *
 * TOP-LEVEL:
 *   add_frame_gas      - es with g more gas for its top frame
 *   frame_inst_at      - a state of the top frame's run and its instruction
 *   frame_inst_raises  - the top frame's instruction raises an exception
 *   frame_raises       - run_frame ends with the given frame exception
 *   frame_inst_raises_here - the raise at the frame's own state
 *   frame_inst_raises_mid  - a raise from a later state of the frame
 *   add_frame_gas_wf_state - add_frame_gas keeps wf_state
 *)
Theory frameGas
Ancestors
  callTrace vfmExecution vfmExecutionProp vfmContext vfmRunCall
  vfmStepLength vfmContextLength vfmWfState vfmDecreasesGas vfmHandleStep
  vfmSameFrame vfmAccountFrame vfmStoragePredicates
  list rich_list pair sum While relation

(* es with g more gas for our (top) frame.  Every frame on the stack gets
   g more gas limit and every caller g more gas used, so the callers'
   unused gas is unchanged and wf_state's gas invariants (gas_stack_ok,
   wf_context) still hold. *)
Definition add_frame_gas_def:
  add_frame_gas g es =
    case es.contexts of
      [] => es
    | (c, rb) :: rest =>
        es with contexts :=
          (c with msgParams updated_by (\p. p with gasLimit updated_by $+ g),
           rb) ::
          MAP (\(c, rb).
                 (c with <| gasUsed updated_by $+ g;
                            msgParams updated_by
                              (\p. p with gasLimit updated_by $+ g) |>,
                  rb)) rest
End

(* The instruction at s on the continuing prefix of run_frame, with
   the entry frame on top. *)
Definition frame_inst_at_def:
  frame_inst_at es s op <=>
    ?ctxt rb rest.
      RTC (\a b. LENGTH a.contexts >= LENGTH es.contexts /\
                 step_with (handle_step_frame (LENGTH es.contexts)) a =
                   (INL (), b)) es s /\
      s.contexts = (ctxt, rb) :: rest /\
      LENGTH s.contexts = LENGTH es.contexts /\
      case FLOOKUP ctxt.msgParams.parsed ctxt.pc of
        SOME op' => op = op'
      | NONE => op = if LENGTH ctxt.msgParams.code <= ctxt.pc then Stop
                     else Invalid
End

Theorem step_with_frame_boundary[local]:
  step_inner s = (INR e,pre) /\ LENGTH pre.contexts = n /\ ~vfm_abort e ==>
  step_with (handle_step_frame n) s = handle_create e pre
Proof
  simp[step_with_def, GSYM step_inner_def, handle_def,
       handle_step_frame_def, bind_def, get_num_contexts_def, return_def]
QED

Theorem run_frame_terminal:
  step_inner s = (INR e,raw) /\
  LENGTH raw.contexts = LENGTH s.contexts /\ ~vfm_abort e /\
  handle_create e raw = (INR exc : unit + exception option,pre) ==>
  run_frame s = SOME (INR exc,pre)
Proof
  strip_tac >>
  drule_all step_with_frame_boundary >> strip_tac >>
  fs[run_frame_def, Once OWHILE_THM] >>
  fs[Once OWHILE_THM]
QED

Theorem run_frame_terminal_call:
  step_inner s = (INR e,pre) /\ LENGTH pre.contexts = LENGTH s.contexts /\
  pre.contexts <> [] /\ (!a. (FST (HD pre.contexts)).msgParams.outputTo <> Code a) /\
  ~vfm_abort e ==> run_frame s = SOME (INR e,pre)
Proof
  strip_tac >> irule run_frame_terminal >>
  qexistsl_tac [`e`,`pre`] >> simp[] >>
  drule_all (INST_TYPE [alpha |-> ``:unit``]
    vfmStaticCallsTheory.handle_create_reraises) >> simp[reraise_def]
QED

Theorem step_inner_inst_raises:
  frame_inst_at s s op /\ step_inst op s = (INR e,t) ==>
  step_inner s = (INR e,t)
Proof
  rw[frame_inst_at_def, step_inner_def, get_current_context_def,
     bind_def, ignore_bind_def, return_def] >>
  Cases_on `FLOOKUP ctxt.msgParams.parsed ctxt.pc` >> gvs[] >>
  Cases_on `LENGTH ctxt.msgParams.code <= ctxt.pc` >> gvs[ignore_bind_def, bind_def]
QED

Theorem step_with_frame_continues[local]:
  0 < n /\ n <= LENGTH t.contexts ==>
  (step_with (handle_step_frame n) s = (INL (),t) <=> step s = (INL (),t))
Proof
  strip_tac >>
  simp[step_with_def, GSYM step_inner_def, step_eq_handle_step_inner,
       handle_def] >>
  Cases_on `step_inner s` >> Cases_on `q` >> simp[] >>
  rename1 `step_inner s = (INR e,u)` >>
  Cases_on `vfm_abort e` >>
  simp[handle_step_frame_def, handle_step_def, reraise_def, bind_def,
       get_num_contexts_def, return_def] >>
  Cases_on `LENGTH u.contexts = n` >> simp[] >>
  `?err pre. handle_create e u = (INR err : unit + exception option,pre)` by
    simp[handle_create_INR] >>
  fs[handle_def] >> strip_tac >>
  drule vfmHandleStepTheory.handle_create_preserves_length >> strip_tac >>
  `pre.contexts <> []` by (strip_tac >> gvs[]) >>
  drule_all handle_exception_inl_pops >> decide_tac
QED

(* A prefix ending at depth n or deeper stays at those depths. *)
Theorem frame_prefix_cong[local]:
  !n (f:execution_state -> unit execution_result) (g:execution_state -> unit execution_result).
    (!a b. n <= LENGTH b.contexts /\ f a = (INL (),b) ==>
           g a = (INL (),b)) ==>
    !s t. RTC (\a b. n <= LENGTH a.contexts /\ f a = (INL (),b)) s t ==>
      n <= LENGTH t.contexts ==>
      RTC (\a b. n <= LENGTH a.contexts /\ g a = (INL (),b)) s t
Proof
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac RTC_STRONG_INDUCT >> simp[] >> rpt strip_tac >>
  rename1 `f src = (INL (),next)` >> rename1 `RTC _ next dst` >>
  `n <= LENGTH next.contexts` by
    (qpat_x_assum `RTC _ next dst` mp_tac >> simp[Once RTC_CASES1] >>
     strip_tac >> gvs[]) >>
  irule (cj 2 RTC_RULES) >> metis_tac[]
QED

(* A step settling the frame would end below n. *)
Theorem frame_prefix_step[local]:
  0 < n /\ n <= LENGTH t.contexts ==>
  (RTC (\a b. n <= LENGTH a.contexts /\
              step_with (handle_step_frame n) a = (INL (),b)) s t <=>
   RTC (\a b. n <= LENGTH a.contexts /\ step a = (INL (),b)) s t)
Proof
  strip_tac >> eq_tac
  >- (mp_tac (Q.SPECL [`n`,`step_with (handle_step_frame n)`,`step`]
        frame_prefix_cong) >> metis_tac[step_with_frame_continues]) >>
  mp_tac (Q.SPECL [`n`,`step`,`step_with (handle_step_frame n)`]
    frame_prefix_cong) >> metis_tac[step_with_frame_continues]
QED

Theorem run_frame_loop_prefix[local]:
  !n s t.
    RTC (\a b. n <= LENGTH a.contexts /\
                step_with (handle_step_frame n) a = (INL (),b)) s t ==>
    OWHILE (ISL o FST) (step_with (handle_step_frame n) o SND) (INL (),s) =
    OWHILE (ISL o FST) (step_with (handle_step_frame n) o SND) (INL (),t)
Proof
  gen_tac >> ho_match_mp_tac RTC_INDUCT >> simp[] >> rpt strip_tac >>
  simp[Once OWHILE_THM]
QED

Theorem run_frame_prefix:
  RTC (\a b. LENGTH a.contexts >= LENGTH es.contexts /\
             step a = (INL (),b)) es s /\
  LENGTH s.contexts = LENGTH es.contexts /\ es.contexts <> [] ==>
  run_frame es = run_frame s
Proof
  strip_tac >>
  `0 < LENGTH es.contexts` by (Cases_on `es.contexts` >> gvs[]) >>
  `RTC (\a b. LENGTH es.contexts <= LENGTH a.contexts /\
              step_with (handle_step_frame (LENGTH es.contexts)) a =
                (INL (),b)) es s` by
    (mp_tac (Q.INST [`n` |-> `LENGTH es.contexts`, `s` |-> `es`, `t` |-> `s`]
      frame_prefix_step) >> fs[arithmeticTheory.GREATER_EQ]) >>
  drule run_frame_loop_prefix >> simp[run_frame_def]
QED

(* A continuing prefix at the entry depth agrees with ordinary stepping. *)
Theorem frame_inst_at_step:
  frame_inst_at es s op <=>
    ?ctxt rb rest.
      RTC (\a b. LENGTH a.contexts >= LENGTH es.contexts /\
                 step a = (INL (), b)) es s /\
      s.contexts = (ctxt, rb) :: rest /\
      LENGTH s.contexts = LENGTH es.contexts /\
      case FLOOKUP ctxt.msgParams.parsed ctxt.pc of
        SOME op' => op = op'
      | NONE => op = if LENGTH ctxt.msgParams.code <= ctxt.pc then Stop
                     else Invalid
Proof
  simp[frame_inst_at_def] >> eq_tac >> strip_tac >>
  `0 < LENGTH es.contexts` by gvs[] >>
  qexistsl_tac [`ctxt`,`rb`,`rest`] >> simp[] >>
  mp_tac (Q.INST [`n` |-> `LENGTH es.contexts`, `s` |-> `es`, `t` |-> `s`]
    frame_prefix_step) >> fs[arithmeticTheory.GREATER_EQ]
QED

(* Callee termination continues the entry frame. A non-abort terminal
   result is the entry frame's raw step followed by possible code deposit. *)
Theorem run_frame_step[local]:
  wf_state s /\ 0 < n /\ n <= LENGTH s.contexts ==>
  (!t. step_with (handle_step_frame n) s = (INL (),t) ==>
       step s = (INL (),t) /\ n <= LENGTH t.contexts) /\
  (!e pre. step_with (handle_step_frame n) s = (INR e,pre) /\ ~vfm_abort e ==>
       ?err raw. step_inner s = (INR err,raw) /\ ~vfm_abort err /\
                 LENGTH raw.contexts = n /\ handle_create err raw = (INR e : unit + exception option,pre))
Proof
  strip_tac >>
  `s.contexts <> []` by gvs[wf_state_def] >>
  simp[step_with_def, GSYM step_inner_def, step_eq_handle_step_inner,
       handle_def] >>
  Cases_on `step_inner s` >> Cases_on `q` >> simp[]
  >- (rpt strip_tac >> gvs[] >>
      drule_at (Pat `m s = _`) same_frame_or_grow_length >> simp[]) >>
  rename1 `step_inner s = (INR err,raw)` >>
  Cases_on `vfm_abort err` >>
  simp[handle_step_frame_def, handle_step_def, reraise_def, bind_def,
       get_num_contexts_def, return_def] >>
  `LENGTH s.contexts <= LENGTH raw.contexts` by
    (drule_at (Pat `m s = _`) same_frame_or_grow_length >> simp[]) >>
  `raw.contexts <> []` by (strip_tac >> gvs[]) >>
  Cases_on `LENGTH raw.contexts = n`
  >- (simp[] >> metis_tac[handle_create_INR, INR_neq_INL, PAIR_EQ]) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      `handle_step err raw = (INL (),t)` by fs[handle_step_def] >>
      drule_all handle_step_inl_pops >> decide_tac) >>
  rpt strip_tac >>
  `handle_step err raw = (INR e,pre)` by fs[handle_step_def] >>
  `LENGTH raw.contexts >= 2` by decide_tac >>
  `EVERY (wf_context o FST) raw.contexts` by
    (mp_tac decreases_gas_cred_step_inner >> simp[decreases_gas_cred_def] >>
     disch_then (qspec_then `s` mp_tac) >> gvs[wf_state_def]) >>
  drule_all step_inner_preserves_stack_room_gas_ok >> strip_tac >>
  drule_all handle_step_not_abort_returns_inl >> simp[]
QED

Theorem run_frame_loop_terminal[local]:
  !n p z.
  OWHILE (ISL o FST) (step_with (handle_step_frame n) o SND) p = SOME z ==>
  (~ISL (FST p) ==> p = z) /\
  !s e pre. p = (INL (),s) /\ z = (INR e,pre) /\ wf_state s /\
             0 < n /\ n <= LENGTH s.contexts /\ ~vfm_abort e ==>
    ?t err raw. RTC (\a b. n <= LENGTH a.contexts /\ step a = (INL (),b)) s t /\
                wf_state t /\ LENGTH t.contexts = n /\
                step_inner t = (INR err,raw) /\ ~vfm_abort err /\
                LENGTH raw.contexts = n /\ handle_create err raw = (INR e : unit + exception option,pre)
Proof
  gen_tac >> ho_match_mp_tac OWHILE_IND >> conj_tac
  >- (rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (Cases_on `FST p` >> gvs[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all run_frame_step >> strip_tac >>
  Cases_on `step_with (handle_step_frame n) s` >> Cases_on `q` >> gvs[]
  >- (rename1 `step_with (handle_step_frame n) s = (INL v,u)` >>
      Cases_on `v` >> gvs[] >>
      `wf_state u` by metis_tac[step_preserves_wf_state, SND] >>
      qpat_x_assum `wf_state u ==> _` mp_tac >> simp[] >>
      strip_tac >> qexistsl_tac [`t`,`err`,`raw`] >> simp[] >>
      irule (cj 2 RTC_RULES) >> qexists_tac `u` >> simp[]) >>
  gvs[] >> rename1 `step_inner s = (INR err,raw)` >>
  `LENGTH s.contexts <= LENGTH raw.contexts` by
    (qpat_x_assum `step_with _ _ = _` kall_tac >>
     qpat_x_assum `handle_create _ _ = _` kall_tac >>
     drule_at (Pat `m s = _`) same_frame_or_grow_length >> gvs[wf_state_def]) >>
  `LENGTH s.contexts = LENGTH raw.contexts` by decide_tac >>
  qexistsl_tac [`s`,`err`,`raw`] >> simp[]
QED

Theorem run_frame_end[local]:
  wf_state es /\ run_frame es = SOME (INR e,pre) /\ ~vfm_abort e ==>
  ?s err raw.
    RTC (\a b. LENGTH a.contexts >= LENGTH es.contexts /\ step a = (INL (),b)) es s /\
    wf_state s /\ LENGTH s.contexts = LENGTH es.contexts /\
    step_inner s = (INR err,raw) /\ ~vfm_abort err /\
    LENGTH raw.contexts = LENGTH es.contexts /\ handle_create err raw = (INR e : unit + exception option,pre)
Proof
  strip_tac >>
  `0 < LENGTH es.contexts` by (Cases_on `es.contexts` >> gvs[wf_state_def]) >>
  fs[run_frame_def] >> drule (cj 2 run_frame_loop_terminal) >> simp[arithmeticTheory.GREATER_EQ]
QED

(* The handler may catch a step_inst exception and pop the frame. A
   precompile runs inside the CALL that pushed its frame, so a raise at
   the greater depth belongs to the callee. *)
Definition frame_inst_raises_def:
  frame_inst_raises es exc op <=>
    ?s s'.
      frame_inst_at es s op /\
      step_inst op s = (INR (SOME exc), s') /\
      LENGTH s'.contexts = LENGTH es.contexts
End

Theorem step_inner_terminal_inst:
  s.contexts = (c,rb)::rest /\ step_inner s = (INR e,u) /\
  e <> SOME InvalidJumpDest /\ e <> SOME Impossible ==>
  ?op. frame_inst_at s s op /\ step_inst op s = (INR e,u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `step_inner s = _` mp_tac >>
  simp[step_inner_def, get_current_context_def, bind_def, return_def] >>
  Cases_on `FLOOKUP c.msgParams.parsed c.pc`
  >- (Cases_on `LENGTH c.msgParams.code <= c.pc` >>
      gvs[frame_inst_at_step] >> strip_tac >>
      goal_assum $ drule_at Any >> simp[]) >>
  rename1 `FLOOKUP c.msgParams.parsed c.pc = SOME op` >>
  gvs[ignore_bind_def] >>
  Cases_on `step_inst op s` >> Cases_on `FST (step_inst op s)` >> gvs[bind_def]
  >- (strip_tac >>
      drule inc_pc_or_jump_inr_eq >> gvs[]) >>
  strip_tac >> qexists_tac `op` >>
  gvs[frame_inst_at_step]
QED

(* Global aborts can occur in a callee and do not describe this frame's end. *)
Definition frame_raises_def:
  frame_raises es exc <=>
    ~vfm_abort (SOME exc) /\ ?pre. run_frame es = SOME (INR (SOME exc),pre)
End

Theorem frame_inst_raises_frame_raises:
  frame_inst_raises es exc op /\ ~vfm_abort (SOME exc) ==> frame_raises es exc
Proof
  rw[frame_inst_raises_def, frame_raises_def] >>
  `es.contexts <> [] /\ LENGTH s.contexts = LENGTH es.contexts /\
   RTC (\a b. LENGTH a.contexts >= LENGTH es.contexts /\
              step a = (INL (),b)) es s /\ frame_inst_at s s op` by
    (gvs[frame_inst_at_step] >> Cases_on `es.contexts` >> gvs[] >> metis_tac[]) >>
  drule_all run_frame_prefix >> strip_tac >>
  drule_all step_inner_inst_raises >> strip_tac >>
  qexists_tac `s'` >> simp[] >> irule run_frame_terminal >>
  qexistsl_tac [`SOME exc`,`s'`] >> simp[] >>
  irule (REWRITE_RULE [reraise_def]
         (INST_TYPE [alpha |-> ``:unit``] handle_create_reraises_when_some)) >>
  Cases_on `s'.contexts` >> gvs[]
QED

Theorem step_frame_msg_params:
  wf_state s /\ 0 < n /\ n <= LENGTH s.contexts /\ n <= LENGTH t.contexts /\
  step s = (r,t) ==>
  DROP (LENGTH t.contexts - n) (MAP (\p. (FST p).msgParams) t.contexts) =
  DROP (LENGTH s.contexts - n) (MAP (\p. (FST p).msgParams) s.contexts)
Proof
  strip_tac >> Cases_on `n < LENGTH s.contexts`
  >- (mp_tac (Q.INST [`k` |-> `n`] step_outer_msgParams) >>
      disch_then drule_all >> simp[]) >>
  `LENGTH s.contexts = n` by decide_tac >>
  Cases_on `LENGTH t.contexts = LENGTH s.contexts`
  >- (drule_all step_same_frame_foreign >> strip_tac >>
      Cases_on `s.contexts` >> Cases_on `t.contexts` >> gvs[wf_state_def]) >>
  `LENGTH s.contexts < LENGTH t.contexts` by decide_tac >>
  drule_all step_push_foreign >> strip_tac >>
  `LENGTH t.contexts - n = 1` by decide_tac >>
  Cases_on `s.contexts` >> Cases_on `t.contexts` >> gvs[wf_state_def] >>
  rename1 `t.contexts = child::cs` >> Cases_on `cs` >>
  gvs[] >>
  qpat_x_assum `MAP FST _ = MAP FST _`
    (mp_tac o AP_TERM ``MAP (\c. c.msgParams)``) >>
  simp[MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem frame_prefix_msg_params[local]:
  wf_state es /\ LENGTH s.contexts = LENGTH es.contexts /\
  RTC (\a b. LENGTH a.contexts >= LENGTH es.contexts /\
             step a = (INL (),b)) es s ==>
  (FST (HD s.contexts)).msgParams = (FST (HD es.contexts)).msgParams
Proof
  strip_tac >>
  `0 < LENGTH es.contexts` by (Cases_on `es.contexts` >> gvs[wf_state_def]) >>
  `wf_state s /\ (LENGTH es.contexts <= LENGTH s.contexts ==>
   DROP (LENGTH s.contexts - LENGTH es.contexts) (MAP (\p. (FST p).msgParams) s.contexts) =
   MAP (\p. (FST p).msgParams) es.contexts)` by
    (irule (BETA_RULE (Q.INST [`Q` |-> `\t. wf_state t /\
      (LENGTH es.contexts <= LENGTH t.contexts ==>
      DROP (LENGTH t.contexts - LENGTH es.contexts) (MAP (\p. (FST p).msgParams) t.contexts) =
      MAP (\p. (FST p).msgParams) es.contexts)`] run_call_reaches_inv)) >>
     simp[run_call_reaches_def, arithmeticTheory.GREATER_EQ] >> rpt strip_tac
     >- metis_tac[step_preserves_wf_state, SND]
     >- (gvs[] >> drule_all step_frame_msg_params >> simp[]) >>
     gvs[arithmeticTheory.GREATER_EQ]) >>
  Cases_on `s.contexts` >> Cases_on `es.contexts` >> gvs[]
QED

Theorem add_frame_gas_contexts:
  es.contexts = (c, rb) :: t ==>
  (add_frame_gas g es).contexts =
    (c with msgParams updated_by (\p. p with gasLimit updated_by $+ g), rb) ::
    MAP (\x. (FST x with <| gasUsed updated_by $+ g;
                            msgParams updated_by
                              (\p. p with gasLimit updated_by $+ g) |>,
              SND x)) t
Proof
  rw[add_frame_gas_def] >> simp[MAP_EQ_f, FORALL_PROD]
QED

Theorem add_frame_gas_fields:
  (add_frame_gas g es).rollback = es.rollback /\
  (add_frame_gas g es).txParams = es.txParams /\
  (add_frame_gas g es).msdomain = es.msdomain
Proof
  rw[add_frame_gas_def] >> CASE_TAC >> simp[] >> CASE_TAC >> simp[]
QED

Theorem gas_stack_ok_add_frame_gas[local]:
  es.contexts = (c, rb) :: t /\ wf_context c /\
  EVERY (wf_context o FST) t /\ gas_stack_ok es ==>
  gas_stack_ok (add_frame_gas g es)
Proof
  rw[gas_stack_ok_def] >>
  drule add_frame_gas_contexts >> disch_then (qspec_then `g` assume_tac) >>
  gvs[] >>
  first_x_assum (qspec_then `i` mp_tac) >>
  simp[EL_MAP, GSYM MAP_TAKE, MAP_MAP_o, combinTheory.o_DEF] >>
  simp[unused_gas_def, listTheory.SUM, MAP_MAP_o, combinTheory.o_DEF] >>
  gvs[wf_context_def]
QED

Theorem add_frame_gas_wf_state:
  !g es. wf_state es ==> wf_state (add_frame_gas g es)
Proof
  rpt strip_tac >>
  Cases_on `es.contexts` >- fs[wf_state_def] >>
  PairCases_on `h` >>
  `gas_stack_ok (add_frame_gas g es)` by
    (irule gas_stack_ok_add_frame_gas >> fs[wf_state_def]) >>
  drule add_frame_gas_contexts >> disch_then (qspec_then `g` assume_tac) >>
  gvs[wf_state_def, wf_context_def, all_accounts_def, stack_room_ok_def,
      outputTo_consistent_stack_def, outputTo_consistent_ctx_def,
      add_frame_gas_fields, EVERY_MAP, MAP_MAP_o, combinTheory.o_DEF] >>
  gvs[EVERY_MEM]
QED

Theorem add_frame_gas_calldata:
  !g es. (FST (HD (add_frame_gas g es).contexts)).msgParams.data =
         (FST (HD es.contexts)).msgParams.data
Proof
  rw[add_frame_gas_def] >> CASE_TAC >> simp[] >> CASE_TAC >> simp[]
QED

Theorem frame_inst_at_unique:
  frame_inst_at es s op /\ frame_inst_at es s op' ==> op = op'
Proof
  rw[frame_inst_at_step] >> gvs[] >>
  Cases_on `FLOOKUP ctxt.msgParams.parsed ctxt.pc` >> gvs[] >>
  Cases_on `LENGTH ctxt.msgParams.code <= ctxt.pc` >> gvs[]
QED

Theorem frame_inst_at_self:
  es.contexts <> [] /\
  (FST (HD es.contexts)).pc < LENGTH (FST (HD es.contexts)).msgParams.code /\
  next_opcode (FST (HD es.contexts)) = SOME op ==>
  frame_inst_at es es op
Proof
  Cases_on `es.contexts` >> simp[] >> PairCases_on `h` >>
  simp[frame_inst_at_step, next_opcode_def] >>
  strip_tac >> gvs[]
QED

Theorem frame_inst_at_prefix:
  RTC (\a b. LENGTH a.contexts >= LENGTH es.contexts /\
             step a = (INL (),b)) es es1 /\
  LENGTH es1.contexts = LENGTH es.contexts /\
  frame_inst_at es1 s op ==> frame_inst_at es s op
Proof
  rw[frame_inst_at_step] >> metis_tac[relationTheory.RTC_TRANS]
QED

(* The instruction s runs raises exc at our depth, from s itself. *)
Theorem frame_inst_raises_here:
  s.contexts = (ctxt, rb) :: rest /\
  (case FLOOKUP ctxt.msgParams.parsed ctxt.pc of
     SOME op' => op = op'
   | NONE => op = if LENGTH ctxt.msgParams.code <= ctxt.pc then Stop
                  else Invalid) /\
  step_inst op s = (INR (SOME exc), s') /\
  LENGTH s'.contexts = LENGTH s.contexts ==>
  frame_inst_raises s exc op
Proof
  rw[frame_inst_raises_def, frame_inst_at_step] >>
  qexistsl_tac [`s`, `s'`] >> simp[]
QED

(* A raise from a later state of the frame, reached at our depth or
   deeper, is a raise of the frame. *)
Theorem frame_inst_raises_mid:
  RTC (\a b. LENGTH a.contexts >= LENGTH es0.contexts /\
             step a = (INL (), b)) es0 es /\
  LENGTH es.contexts = LENGTH es0.contexts /\
  frame_inst_raises es exc op ==>
  frame_inst_raises es0 exc op
Proof
  rw[frame_inst_raises_def, frame_inst_at_step] >>
  qexistsl_tac [`s`, `s'`] >> gvs[] >>
  metis_tac[relationTheory.RTC_RTC]
QED

Theorem handle_create_none_no_stack_overflow[local]:
  handle_create NONE s <> (INR (SOME StackOverflow) : unit + exception option,t)
Proof
  simp[handle_create_def, bind_def, ignore_bind_def, get_return_data_def,
       get_output_to_def, get_current_context_def, return_def, fail_def,
       reraise_def, consume_gas_def, update_accounts_def, assert_def,
       set_current_context_def] >>
  Cases_on `s.contexts` >> gvs[] >> PairCases_on `h` >>
  Cases_on `h0.msgParams.outputTo` >> Cases_on `h0.returnData` >>
  simp[assert_def, fail_def, reraise_def, bind_def, ignore_bind_def,
       get_current_context_def, set_current_context_def, update_accounts_def,
       return_def, AllCaseEqs()]
QED

(* The exceptional frame end identifies an instruction in runtime. Code
   deposit can produce OutOfGas after a creation frame's final instruction. *)
Theorem frame_raises_inst_raises:
  wf_state es /\
  (exc = StackOverflow \/ exc = OutOfGas /\
   (!a. (FST (HD es.contexts)).msgParams.outputTo <> Code a)) ==>
  (frame_raises es exc <=> ?op. frame_inst_raises es exc op)
Proof
  disch_then (fn th => assume_tac (CONJUNCT1 th) >> assume_tac (CONJUNCT2 th)) >>
  eq_tac
  >- (pure_rewrite_tac [frame_raises_def] >> strip_tac >>
      drule_all run_frame_end >> strip_tac >>
      `s.contexts <> [] /\ raw.contexts <> []` by
        (Cases_on `s.contexts` >> Cases_on `raw.contexts` >> gvs[wf_state_def]) >>
      `err = SOME exc` by
        (Cases_on `err`
         >- (Cases_on `exc = StackOverflow` >> gvs[handle_create_none_no_stack_overflow] >>
             `same_frame_rel s raw` by
               (irule (INST_TYPE [alpha |-> ``:unit``] same_frame_or_grow_eq_length) >>
                simp[] >> qexistsl_tac [`step_inner`,`INR NONE`] >> simp[]) >>
             drule_all frame_prefix_msg_params >> strip_tac >>
             `!a. (FST (HD raw.contexts)).msgParams.outputTo <> Code a` by
               gvs[same_frame_rel_def] >>
             `handle_create NONE raw = (INR NONE : unit + exception option,raw)` by
               (irule (REWRITE_RULE [reraise_def]
                 (INST_TYPE [alpha |-> ``:unit``]
                   vfmStaticCallsTheory.handle_create_reraises)) >> simp[]) >>
             gvs[]) >>
         `handle_create (SOME x) raw = (INR (SOME x) : unit + exception option,raw)` by
           (irule (REWRITE_RULE [reraise_def]
             (INST_TYPE [alpha |-> ``:unit``] handle_create_reraises_when_some)) >>
            Cases_on `raw.contexts` >> gvs[]) >>
         gvs[]) >>
      `?c rb rest. s.contexts = (c,rb)::rest` by
        (Cases_on `s.contexts` >> gvs[] >> Cases_on `h` >> simp[]) >>
      Q.SUBGOAL_THEN `SOME exc <> SOME InvalidJumpDest /\ SOME exc <> SOME Impossible`
        strip_assume_tac >- (gvs[vfm_abort_def] >> metis_tac[]) >>
      qpat_x_assum `err = SOME exc` SUBST_ALL_TAC >>
      drule_all step_inner_terminal_inst >> strip_tac >>
      qexists_tac `op` >> simp[frame_inst_raises_def] >>
      qexistsl_tac [`s`,`raw`] >> simp[] >>
      drule_all frame_inst_at_prefix >> simp[]) >>
  strip_tac >> irule frame_inst_raises_frame_raises >>
  conj_tac >- gvs[vfm_abort_def] >> metis_tac[]
QED
