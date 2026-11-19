Theory requestCutOracleClip
Ancestors
  requestCutOracleReplay requestCutOracleFrames jointRequestCut
  frameRawProjection concretizePtrCoverageStaticMemReachability
  ptrDiscipline contextRawReachable contextCodegenRel opcodeClass ptrSafeRun
  instIdxIndep venomExecSemantics venomState venomInst list rich_list arithmetic
Libs
  BasicProvers

Theorem ok_outcome_clip_drop[local]:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  i.inst_opcode <> INVOKE /\ step_inst fuel C i s = OK t /\
  LENGTH t.vs_requests <= k ==>
  LENGTH s.vs_requests <= LENGTH t.vs_requests /\
  DROP (k - LENGTH t.vs_requests) t.vs_outcomes =
  DROP (k - LENGTH s.vs_requests) s.vs_outcomes
Proof
  strip_tac >> drule_all noninvoke_recorded_oracle_effect >> strip_tac >> simp[] >>
  `k - LENGTH s.vs_requests = SUC (k - SUC (LENGTH s.vs_requests))` by
    (fs[LENGTH_APPEND] >> decide_tac) >>
  Cases_on `s.vs_outcomes` >> gvs[] >> AP_THM_TAC >> AP_TERM_TAC >> decide_tac
QED

Theorem step_inst_ok_outcome_clip:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  i.inst_opcode <> INVOKE /\ step_inst fuel C i s = OK t /\
  LENGTH t.vs_requests <= k ==>
  step_inst fuel C i
    (s with vs_outcomes := TAKE (k - LENGTH s.vs_requests) s.vs_outcomes) =
  OK (t with vs_outcomes := TAKE (k - LENGTH t.vs_requests) t.vs_outcomes)
Proof
  strip_tac >> drule_all ok_outcome_clip_drop >> strip_tac >>
  qabbrev_tac `short = TAKE (k - LENGTH s.vs_requests) s.vs_outcomes` >>
  qabbrev_tac `tail = DROP (k - LENGTH s.vs_requests) s.vs_outcomes` >>
  `MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] ==>
   short <> []` by
    (strip_tac >> drule_all external_ok_records_request >> strip_tac >>
     `s.vs_outcomes <> []` by
       (drule_all noninvoke_recorded_oracle_effect >> strip_tac >> fs[]) >>
     `0 < k - LENGTH s.vs_requests` by decide_tac >>
     simp[Abbr `short`, TAKE_EQ_NIL]) >>
  `s.vs_outcomes = short ++ tail` by simp[Abbr `short`, Abbr `tail`, TAKE_DROP] >>
  `t.vs_outcomes = TAKE (k - LENGTH t.vs_requests) t.vs_outcomes ++ tail` by
    metis_tac[TAKE_DROP] >>
  mp_tac (Q.INST [`inst` |-> `i`, `os` |-> `short`, `tail` |-> `tail`]
    step_inst_noninvoke_outcome_prefix) >> simp[] >>
  Cases_on `step_inst fuel C i (s with vs_outcomes := short)` >>
  simp[exec_result_map_def] >> strip_tac >>
  rename1 `t = t0 with vs_outcomes := t0.vs_outcomes ++ tail` >>
  `t.vs_outcomes = t0.vs_outcomes ++ tail` by
    (qpat_assum `t = t0 with vs_outcomes := _`
       (mp_tac o Q.AP_TERM `\v. v.vs_outcomes`) >> simp[]) >>
  `t0.vs_outcomes = TAKE (k - LENGTH t.vs_requests) t.vs_outcomes` by
    metis_tac[APPEND_11] >>
  qpat_x_assum `t = t0 with vs_outcomes := _` SUBST_ALL_TAC >>
  fs[venom_state_component_equality]
QED

Theorem step_taint_outcome_clip[local]:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  i.inst_opcode <> INVOKE /\ step_inst fuel C i s = OK t /\
  LENGTH t.vs_requests <= k ==>
  step_taint i
    (s with vs_outcomes := TAKE (k - LENGTH s.vs_requests) s.vs_outcomes)
    (t with vs_outcomes := TAKE (k - LENGTH t.vs_requests) t.vs_outcomes) tn =
  step_taint i s t tn
Proof
  strip_tac >> drule_all step_inst_ok_outcome_clip >> disch_tac >>
  drule_all ok_outcome_clip_drop >> strip_tac >>
  qabbrev_tac `short_s = TAKE (k - LENGTH s.vs_requests) s.vs_outcomes` >>
  qabbrev_tac `short_t = TAKE (k - LENGTH t.vs_requests) t.vs_outcomes` >>
  qabbrev_tac `tail = DROP (k - LENGTH s.vs_requests) s.vs_outcomes` >>
  `short_s = [] ==> short_t = []` by
    (mp_tac (Q.INST [`inst` |-> `i`, `s` |-> `s with vs_outcomes := short_s`,
       `post` |-> `t with vs_outcomes := short_t`] noninvoke_recorded_oracle_effect) >>
     simp[] >> strip_tac >> fs[] >>
     strip_tac >> fs[]) >>
  `short_s ++ tail = s.vs_outcomes /\ short_t ++ tail = t.vs_outcomes` by
    (fs[Abbr `short_s`, Abbr `short_t`, Abbr `tail`] >> metis_tac[TAKE_DROP]) >>
  `(s with vs_outcomes := short_s ++ tail) = s /\
   (t with vs_outcomes := short_t ++ tail) = t` by
    simp[venom_state_component_equality] >>
  mp_tac (Q.INST [`i` |-> `i`, `tn` |-> `tn`, `tail` |-> `tail`,
      `s` |-> `s with vs_outcomes := short_s`,
      `t` |-> `t with vs_outcomes := short_t`] step_taint_outcome_suffix) >>
  simp[]
QED

Theorem enters_block_outcome_clip[local]:
  enters_block f s t ==>
  enters_block f
    (s with vs_outcomes := TAKE (k - LENGTH s.vs_requests) s.vs_outcomes)
    (t with vs_outcomes := TAKE (k - LENGTH t.vs_requests) t.vs_outcomes)
Proof
  strip_tac >> drule enters_block_oracle >> strip_tac >>
  fs[enters_block_def] >>
  qexists_tac `s_phi with vs_outcomes := TAKE (k - LENGTH s.vs_requests) s.vs_outcomes` >>
  simp[eval_phis_outcome_update, exec_result_map_def]
QED

Theorem setup_callee_outcome_clip[local]:
  setup_callee f args s = SOME t ==>
  setup_callee f args
    (s with vs_outcomes := TAKE (k - LENGTH s.vs_requests) s.vs_outcomes) =
  SOME (t with vs_outcomes := TAKE (k - LENGTH t.vs_requests) t.vs_outcomes)
Proof
  strip_tac >> drule calleeTransportTheory.setup_callee_oracle >>
  simp[setup_callee_outcome_update]
QED

Theorem intret_outcome_clip[local]:
  step_inst fuel C i s = IntRet ret t ==>
  step_inst fuel C i
    (s with vs_outcomes := TAKE (k - LENGTH s.vs_requests) s.vs_outcomes) =
  IntRet ret (t with vs_outcomes := TAKE (k - LENGTH t.vs_requests) t.vs_outcomes)
Proof
  strip_tac >> drule step_inst_intret_not_invoke >> strip_tac >>
  `step_inst_base i s = IntRet ret t` by fs[step_inst_non_invoke] >>
  `~MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]` by
    (drule step_inst_base_intret_opcodes >> strip_tac >> simp[]) >>
  drule step_inst_intret_requests >> strip_tac >>
  mp_tac (Q.INST [`inst` |-> `i`,
    `os` |-> `TAKE (k - LENGTH s.vs_requests) s.vs_outcomes`,
    `tail` |-> `DROP (k - LENGTH s.vs_requests) s.vs_outcomes`]
    step_inst_noninvoke_outcome_prefix) >>
  simp[TAKE_DROP] >>
  Cases_on `step_inst fuel C i
    (s with vs_outcomes := TAKE (k - LENGTH s.vs_requests) s.vs_outcomes)` >>
  simp[exec_result_map_def] >>
  rpt strip_tac >> gvs[venom_state_component_equality] >>
  metis_tac[TAKE_DROP, APPEND_11]
QED

Theorem frame_reachable_outcome_clip:
  !vs C stk PG G tn fn i s.
    frame_reachable vs C stk PG G tn fn i s ==>
    (!rq rqs. record_request rq rqs = rqs ++ [rq]) ==>
    LENGTH s.vs_requests <= k ==>
    frame_reachable
      (vs with vs_outcomes := TAKE (k - LENGTH vs.vs_requests) vs.vs_outcomes)
      C
      (MAP (\f. f with cf_state := (f.cf_state with
        vs_outcomes := TAKE (k - LENGTH f.cf_state.vs_requests)
          f.cf_state.vs_outcomes)) stk)
      PG G tn fn i
      (s with vs_outcomes := TAKE (k - LENGTH s.vs_requests) s.vs_outcomes)
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac >> rpt gen_tac >>
  strip_tac >> strip_tac >> strip_tac >> fs[]
  >- (irule frame_reachable_entry >> simp[] >>
      drule enters_block_outcome_clip >> disch_then (qspec_then `k` mp_tac) >>
      simp[] >> metis_tac[])
  >- (rename1 `step_inst fuel C i s = OK t` >>
      rename1 `active_inst fn inst' (t with vs_inst_idx := SUC s.vs_inst_idx)` >>
      drule_all ok_outcome_clip_drop >> strip_tac >>
      `LENGTH s.vs_requests <= k` by decide_tac >>
      drule_all step_inst_ok_outcome_clip >> disch_tac >>
      drule_all step_taint_outcome_clip >> disch_tac >>
      mp_tac (Q.SPECL
        [`vs with vs_outcomes := TAKE (k - LENGTH vs.vs_requests) vs.vs_outcomes`, `C`,
         `MAP (\f. f with cf_state := (f.cf_state with
           vs_outcomes := TAKE (k - LENGTH f.cf_state.vs_requests) f.cf_state.vs_outcomes)) stk`,
         `PG`, `G`, `tn`, `fn`, `i`, `inst'`,
         `s with vs_outcomes := TAKE (k - LENGTH s.vs_requests) s.vs_outcomes`,
         `t with vs_outcomes := TAKE (k - LENGTH t.vs_requests) t.vs_outcomes`,
         `fuel`] frame_reachable_next) >>
      simp[] >> fs[active_inst_def] >> metis_tac[])
  >- (rename1 `step_inst fuel C i s = OK t` >>
      rename1 `enters_block fn t u` >>
      rename1 `active_inst fn inst' u` >>
      `i.inst_opcode <> INVOKE` by (strip_tac >> fs[is_terminator_def]) >>
      `u.vs_requests = t.vs_requests` by metis_tac[enters_block_oracle] >>
      `LENGTH t.vs_requests <= k` by metis_tac[] >>
      drule_all ok_outcome_clip_drop >> strip_tac >>
      `LENGTH s.vs_requests <= k` by decide_tac >>
      drule_all step_inst_ok_outcome_clip >> disch_tac >>
      drule enters_block_outcome_clip >> disch_then (qspec_then `k` assume_tac) >>
      mp_tac (Q.SPECL
        [`vs with vs_outcomes := TAKE (k - LENGTH vs.vs_requests) vs.vs_outcomes`, `C`,
         `MAP (\f. f with cf_state := (f.cf_state with
           vs_outcomes := TAKE (k - LENGTH f.cf_state.vs_requests) f.cf_state.vs_outcomes)) stk`,
         `PG`, `G`, `tn`, `fn`, `i`, `inst'`,
         `s with vs_outcomes := TAKE (k - LENGTH s.vs_requests) s.vs_outcomes`,
         `t with vs_outcomes := TAKE (k - LENGTH t.vs_requests) t.vs_outcomes`,
         `u with vs_outcomes := TAKE (k - LENGTH u.vs_requests) u.vs_outcomes`,
         `fuel`] frame_reachable_block) >> simp[])
  >- (imp_res_tac calleeTransportTheory.setup_callee_oracle >>
      imp_res_tac enters_block_oracle >> fs[] >>
      imp_res_tac setup_callee_outcome_clip >> imp_res_tac enters_block_outcome_clip >>
      irule frame_reachable_call >> simp[] >> metis_tac[]) >>
  rename1 `step_inst fuel C i s = IntRet ret t` >>
  rename1 `active_inst f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)` >>
  drule step_inst_intret_requests >> strip_tac >>
  drule calleeTransportTheory.bind_outputs_oracle >> strip_tac >>
  `s'.vs_outcomes = t.vs_outcomes /\ s'.vs_requests = t.vs_requests` by
    (fs[adopt_return_fmp_def, merge_callee_state_def, AllCaseEqs()] >> metis_tac[]) >>
  `LENGTH s.vs_requests <= k` by metis_tac[] >>
  drule intret_outcome_clip >> disch_then (qspec_then `k` assume_tac) >>
  mp_tac (Q.SPECL
    [`vs with vs_outcomes := TAKE (k - LENGTH vs.vs_requests) vs.vs_outcomes`, `C`,
     `f with cf_state := (f.cf_state with
       vs_outcomes := TAKE (k - LENGTH f.cf_state.vs_requests) f.cf_state.vs_outcomes)`,
     `MAP (\f. f with cf_state := (f.cf_state with
       vs_outcomes := TAKE (k - LENGTH f.cf_state.vs_requests) f.cf_state.vs_outcomes)) stk`,
     `PG`, `G`, `tn`, `fn`, `i`,
     `s with vs_outcomes := TAKE (k - LENGTH s.vs_requests) s.vs_outcomes`, `ret`,
     `t with vs_outcomes := TAKE (k - LENGTH t.vs_requests) t.vs_outcomes`,
     `s' with vs_outcomes := TAKE (k - LENGTH s'.vs_requests) s'.vs_outcomes`, `inst'`,
     `fuel`] frame_reachable_ret) >>
  simp[merge_callee_outcome_update, bind_outputs_outcome_update, adopt_return_outcome_update] >>
  fs[active_inst_def] >> metis_tac[]
QED

Theorem raw_reachable_outcome_clip:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  EVERY wf_function C.ctx_functions /\
  raw_reachable vs C fn i s /\ LENGTH s.vs_requests <= k ==>
  raw_reachable (vs with vs_outcomes := TAKE (k - LENGTH vs.vs_requests) vs.vs_outcomes)
    C fn i (s with vs_outcomes := TAKE (k - LENGTH s.vs_requests) s.vs_outcomes)
Proof
  strip_tac >> drule ptr_raw_reachable_frame >> strip_tac >>
  drule frame_reachable_outcome_clip >> disch_then (qspec_then `k` mp_tac) >>
  (impl_tac >- simp[]) >> metis_tac[frame_reachable_raw]
QED
