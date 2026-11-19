Theory requestCutOracleFrames
Ancestors
  requestCutOracleReplay jointRequestCut ptrDiscipline contextCodegenRel codegenRel
  instIdxIndep opcodeClass venomExecSemantics venomState venomInst list
Libs
  BasicProvers

Theorem active_inst_outcome_update[simp]:
  active_inst f i (s with vs_outcomes := os) <=> active_inst f i s
Proof
  simp[active_inst_def]
QED

Theorem noninvoke_ok_oracle_length[local]:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  i.inst_opcode <> INVOKE /\ step_inst fuel C i s = OK t ==>
  LENGTH t.vs_requests + LENGTH t.vs_outcomes =
  LENGTH s.vs_requests + LENGTH s.vs_outcomes
Proof
  strip_tac >> drule_all noninvoke_recorded_oracle_effect >> strip_tac >> simp[] >>
  Cases_on `s.vs_outcomes` >> gvs[]
QED

Theorem frame_reachable_oracle_length:
  !vs C stk PG G tn fn inst s.
    frame_reachable vs C stk PG G tn fn inst s ==>
    (!rq rqs. record_request rq rqs = rqs ++ [rq]) ==>
    LENGTH s.vs_requests + LENGTH s.vs_outcomes =
    LENGTH vs.vs_requests + LENGTH vs.vs_outcomes
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac >> rpt gen_tac >>
  strip_tac >> strip_tac >> fs[]
  >- (drule enters_block_oracle >> simp[])
  >- (drule_all noninvoke_ok_oracle_length >> simp[])
  >- (rename1 `step_inst fuel C i s = OK t` >>
      `i.inst_opcode <> INVOKE` by (strip_tac >> fs[is_terminator_def]) >>
      drule_all noninvoke_ok_oracle_length >> drule enters_block_oracle >> simp[])
  >- (drule calleeTransportTheory.setup_callee_oracle >>
      drule enters_block_oracle >> simp[]) >>
  drule calleeTransportTheory.bind_outputs_oracle >>
  drule step_inst_intret_requests >> strip_tac >> strip_tac >>
  fs[adopt_return_fmp_def, merge_callee_state_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem enters_block_outcome_suffix[local]:
  enters_block f s t ==>
  enters_block f (s with vs_outcomes := s.vs_outcomes ++ tail)
    (t with vs_outcomes := t.vs_outcomes ++ tail)
Proof
  rw[enters_block_def] >> qexists_tac `bb` >> simp[eval_phis_outcome_update] >>
  drule venomExecProofsTheory.eval_phis_only_updates_vs_vars >>
  disch_then (mp_tac o Q.AP_TERM `\v. v.vs_outcomes`) >> simp[exec_result_map_def]
QED

Theorem setup_callee_outcome_suffix[local]:
  setup_callee f args s = SOME t ==>
  setup_callee f args (s with vs_outcomes := s.vs_outcomes ++ tail) =
    SOME (t with vs_outcomes := t.vs_outcomes ++ tail)
Proof
  strip_tac >> simp[setup_callee_outcome_update] >>
  drule calleeTransportTheory.setup_callee_oracle >> simp[]
QED

Theorem step_prov_outcome_update[simp]:
  step_prov PG G i (s with vs_outcomes := os) = step_prov PG G i s
Proof
  simp[step_prov_def, out_prov_def, lookup_var_def]
QED

Theorem entry_ghost_outcome_update[simp]:
  entry_prov f (s with vs_outcomes := os) G = entry_prov f s G /\
  entry_taint_vars f (s with vs_outcomes := os) tn = entry_taint_vars f s tn
Proof
  simp[entry_prov_def, entry_taint_vars_def]
QED

Theorem write_ranges_outcome_update[simp]:
  source_memory_write_ranges i (s with vs_outcomes := os) = source_memory_write_ranges i s
Proof
  Cases_on `i.inst_opcode` >>
  simp[source_memory_write_ranges_def, fixed_source_write_range_def,
       sized_source_write_range_def] >>
  rpt (PURE_TOP_CASE_TAC >> simp[])
QED

Theorem step_taint_outcome_suffix:
  (s.vs_outcomes = [] ==> t.vs_outcomes = []) ==>
  step_taint i (s with vs_outcomes := s.vs_outcomes ++ tail)
    (t with vs_outcomes := t.vs_outcomes ++ tail) tn = step_taint i s t tn
Proof
  Cases_on `s.vs_outcomes` >>
  simp[step_taint_def, mem_taint_def, step_writes_def, new_site_bytes_def,
       written_taint_def, out_taint_def, store_taint_def, imm_taint_def, APPEND_11]
QED

Theorem step_inst_ok_outcome_suffix[local]:
  i.inst_opcode <> INVOKE /\ step_inst fuel C i s = OK t ==>
  step_inst fuel C i (s with vs_outcomes := s.vs_outcomes ++ tail) =
  OK (t with vs_outcomes := t.vs_outcomes ++ tail)
Proof
  strip_tac >>
  mp_tac (Q.INST [`inst` |-> `i`, `r` |-> `OK t`]
    step_inst_noninvoke_success_outcome_suffix) >> simp[exec_result_map_def]
QED

Theorem frame_reachable_outcome_suffix:
  !vs C stk PG G tn fn inst s.
  frame_reachable vs C stk PG G tn fn inst s ==>
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) ==>
  frame_reachable (vs with vs_outcomes := vs.vs_outcomes ++ tail) C
    (MAP (\f. f with cf_state := (f.cf_state with
       vs_outcomes := f.cf_state.vs_outcomes ++ tail)) stk)
    PG G tn fn inst (s with vs_outcomes := s.vs_outcomes ++ tail)
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac >> rpt gen_tac >>
  strip_tac >> strip_tac >> fs[]
  >- (irule frame_reachable_entry >> simp[] >>
      drule enters_block_outcome_suffix >>
      disch_then (qspec_then `tail` assume_tac) >> fs[] >> metis_tac[])
  >- (rename1 `step_inst fuel C i s = OK t` >>
      `s.vs_outcomes = [] ==> t.vs_outcomes = []` by
        (drule_all noninvoke_recorded_oracle_effect >> strip_tac >> simp[]) >>
      `step_inst fuel C i (s with vs_outcomes := s.vs_outcomes ++ tail) =
       OK (t with vs_outcomes := t.vs_outcomes ++ tail)` by
        (irule step_inst_ok_outcome_suffix >> simp[]) >>
      drule step_taint_outcome_suffix >>
      disch_then (qspecl_then [`tn`, `tail`, `i`] assume_tac) >>
      `active_inst fn i (s with vs_outcomes := s.vs_outcomes ++ tail) /\
       active_inst fn inst'
         ((t with vs_outcomes := t.vs_outcomes ++ tail) with vs_inst_idx := SUC s.vs_inst_idx)` by
        (fs[active_inst_def] >> metis_tac[]) >>
      mp_tac (Q.SPECL [`vs with vs_outcomes := vs.vs_outcomes ++ tail`, `C`,
        `MAP (\f. f with cf_state := (f.cf_state with
          vs_outcomes := f.cf_state.vs_outcomes ++ tail)) stk`,
        `PG`, `G`, `tn`, `fn`, `i`, `inst'`,
        `s with vs_outcomes := s.vs_outcomes ++ tail`,
        `t with vs_outcomes := t.vs_outcomes ++ tail`, `fuel`] frame_reachable_next) >>
      simp[])
  >- (rename1 `step_inst fuel C i s = OK t` >>
      `i.inst_opcode <> INVOKE` by (strip_tac >> fs[is_terminator_def]) >>
      `step_inst fuel C i (s with vs_outcomes := s.vs_outcomes ++ tail) =
       OK (t with vs_outcomes := t.vs_outcomes ++ tail)` by
        (irule step_inst_ok_outcome_suffix >> simp[]) >>
      drule enters_block_outcome_suffix >> disch_then (qspec_then `tail` assume_tac) >>
      rename1 `enters_block fn t u` >>
      mp_tac (Q.SPECL [`vs with vs_outcomes := vs.vs_outcomes ++ tail`, `C`,
        `MAP (\f. f with cf_state := (f.cf_state with
          vs_outcomes := f.cf_state.vs_outcomes ++ tail)) stk`,
        `PG`, `G`, `tn`, `fn`, `i`, `inst'`,
        `s with vs_outcomes := s.vs_outcomes ++ tail`,
        `t with vs_outcomes := t.vs_outcomes ++ tail`,
        `u with vs_outcomes := u.vs_outcomes ++ tail`, `fuel`] frame_reachable_block) >>
      simp[])
  >- (imp_res_tac setup_callee_outcome_suffix >> imp_res_tac enters_block_outcome_suffix >>
      irule frame_reachable_call >> simp[] >> metis_tac[]) >>
  rename1 `step_inst fuel C i s = IntRet ret t` >>
  `i.inst_opcode <> INVOKE` by metis_tac[ptrSafeRunTheory.step_inst_intret_not_invoke] >>
  `step_inst fuel C i (s with vs_outcomes := s.vs_outcomes ++ tail) =
   IntRet ret (t with vs_outcomes := t.vs_outcomes ++ tail)` by
    (mp_tac (Q.INST [`inst` |-> `i`, `r` |-> `IntRet ret t`]
       step_inst_noninvoke_success_outcome_suffix) >> simp[exec_result_map_def]) >>
  drule calleeTransportTheory.bind_outputs_oracle >> strip_tac >>
  `s'.vs_outcomes = t.vs_outcomes` by
    (fs[adopt_return_fmp_def, merge_callee_state_def, AllCaseEqs()] >> metis_tac[]) >>
  mp_tac (Q.SPECL [`vs with vs_outcomes := vs.vs_outcomes ++ tail`, `C`,
    `f with cf_state := (f.cf_state with vs_outcomes := f.cf_state.vs_outcomes ++ tail)`,
    `MAP (\f. f with cf_state := (f.cf_state with
      vs_outcomes := f.cf_state.vs_outcomes ++ tail)) stk`,
    `PG`, `G`, `tn`, `fn`, `i`, `s with vs_outcomes := s.vs_outcomes ++ tail`,
    `ret`, `t with vs_outcomes := t.vs_outcomes ++ tail`,
    `s' with vs_outcomes := s'.vs_outcomes ++ tail`, `inst'`, `fuel`] frame_reachable_ret) >>
  simp[merge_callee_outcome_update, bind_outputs_outcome_update, adopt_return_outcome_update] >>
  fs[active_inst_def] >> metis_tac[]
QED
