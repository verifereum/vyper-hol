(* Reverse coverage of finite open observations by native raw reachability. *)
Theory dftOpenReverseRaw
Ancestors
  dftOpenHistory dftOpenReturnHistory dftOpenRawAdequacy dftOpenErase dftOpenAdequacy
  dftOpenMachine venomExecSemantics venomExecProofs venomInst venomInstProps
  contextRawReachable contextCodegenRel arithmetic list

Definition dft_reverse_at_def:
  dft_reverse_at vs0 ctx xs fn bb s n <=>
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    !inst. active_inst fn inst (dft_open_materialize xs n s) ==>
      raw_reachable vs0 ctx fn inst (dft_open_materialize xs n s)
End

Definition dft_reverse_enter_def:
  dft_reverse_enter vs0 ctx xs fn s n <=>
    !observed inst. enters_block fn (dft_open_materialize xs n s) observed /\
      active_inst fn inst observed ==> raw_reachable vs0 ctx fn inst observed
End

Definition dft_reverse_config_def:
  dft_reverse_config vs0 ctx xs (DftOpen ctl stack n) <=>
    case ctl of
      DftAt fn budget bb s => dft_reverse_at vs0 ctx xs fn bb s n
    | DftEnter fn budget s => dft_reverse_enter vs0 ctx xs fn s n
    | DftDone r => T
End

Theorem dft_reverse_active_lookup:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  active_inst fn inst (dft_open_materialize xs n s)
Proof
  simp[active_inst_def, get_instruction_def, dft_open_materialize_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  metis_tac[lookup_block_MEM, lookup_block_label]
QED

Theorem dft_reverse_initial:
  ctx.ctx_entry = SOME name /\ lookup_function name ctx.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl ==>
  dft_reverse_config vs0 ctx vs0.vs_gas_readings
    (DftOpen (DftEnter fn fuel
      (vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) [] 0)
Proof
  simp[dft_reverse_config_def, dft_reverse_enter_def, dft_open_materialize_def] >>
  rpt strip_tac >> irule raw_reachable_entry >> metis_tac[]
QED

Theorem dft_reverse_enter_at:
  dft_reverse_enter vs0 ctx xs fn s n /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s bb.bb_instructions = OK sp ==>
  dft_reverse_at vs0 ctx xs fn bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) n
Proof
  strip_tac >> simp[dft_reverse_at_def] >> conj_tac
  >- (drule eval_phis_preserves_current_bb >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `dft_reverse_enter _ _ _ _ _ _` mp_tac >>
  simp[dft_reverse_enter_def] >> disch_then irule >>
  simp[enters_block_def] >>
  qexists_tac `dft_open_materialize xs n sp` >>
  simp[dft_open_materialize_def] >>
  mp_tac (Q.SPECL [`bb.bb_instructions`, `s`] gasOracleReplayTheory.gas_eval_phis) >>
  simp[gasOracleReplayTheory.gas_replay_at_def] >>
  disch_then (qspec_then `DROP n xs` mp_tac) >>
  Cases_on `eval_phis (s with vs_gas_readings := DROP n xs) bb.bb_instructions` >>
  simp[stateEquivTheory.lift_result_def]
QED

Theorem dft_reverse_next:
  dft_reverse_at vs0 ctx xs fn bb s n /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ ~is_terminator inst.inst_opcode /\
  step_inst budget ctx inst (dft_open_materialize xs n s) = OK after /\
  dft_open_materialize xs m t = after with vs_inst_idx := SUC s.vs_inst_idx ==>
  dft_reverse_at vs0 ctx xs fn bb t m
Proof
  strip_tac >>
  `active_inst fn inst (dft_open_materialize xs n s)` by
    (irule dft_reverse_active_lookup >> gvs[dft_reverse_at_def]) >>
  `raw_reachable vs0 ctx fn inst (dft_open_materialize xs n s)` by
    gvs[dft_reverse_at_def] >>
  `after.vs_current_bb = s.vs_current_bb` by
    (drule_all step_preserves_control_flow >> simp[dft_open_materialize_def]) >>
  simp[dft_reverse_at_def] >> conj_tac
  >- (qpat_x_assum `dft_open_materialize _ _ _ = _`
        (mp_tac o Q.AP_TERM `\u. u.vs_current_bb`) >>
      gvs[dft_open_materialize_def, dft_reverse_at_def]) >>
  rpt strip_tac >>
  `dft_open_materialize xs m t =
    after with vs_inst_idx := SUC (dft_open_materialize xs n s).vs_inst_idx` by simp[] >>
  `active_inst fn inst' (after with vs_inst_idx :=
    SUC (dft_open_materialize xs n s).vs_inst_idx)` by simp[] >>
  drule_all raw_reachable_next >> simp[]
QED

Theorem dft_reverse_block:
  dft_reverse_at vs0 ctx xs fn bb s n /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ is_terminator inst.inst_opcode /\
  step_inst budget ctx inst (dft_open_materialize xs n s) = OK after /\
  ~after.vs_halted /\ dft_open_materialize xs m t = after ==>
  dft_reverse_enter vs0 ctx xs fn t m
Proof
  strip_tac >>
  `active_inst fn inst (dft_open_materialize xs n s)` by
    (irule dft_reverse_active_lookup >> gvs[dft_reverse_at_def]) >>
  `raw_reachable vs0 ctx fn inst (dft_open_materialize xs n s)` by
    gvs[dft_reverse_at_def] >>
  simp[dft_reverse_enter_def] >> rpt strip_tac >>
  irule raw_reachable_block >> metis_tac[]
QED

Theorem dft_reverse_callee:
  dft_reverse_at vs0 ctx xs fn bb caller n /\
  dft_history_push ctx c (DftCaller fn budget bb inst caller) rest callee start n ==>
  dft_reverse_enter vs0 ctx xs callee start n
Proof
  simp[dft_history_push_def] >> rpt strip_tac >> gvs[] >>
  `active_inst fn inst (dft_open_materialize xs n caller)` by
    (irule dft_reverse_active_lookup >> gvs[dft_reverse_at_def]) >>
  `raw_reachable vs0 ctx fn inst (dft_open_materialize xs n caller)` by
    gvs[dft_reverse_at_def] >>
  simp[dft_reverse_enter_def] >> rpt strip_tac >>
  irule raw_reachable_callee >> conj_tac >- simp[] >>
  qexistsl_tac [`args`, `fn`, `dft_open_materialize xs n start`,
    `inst`, `nm`, `ops`, `dft_open_materialize xs n caller`] >>
  simp[dft_open_setup_materialize, dft_open_materialize_def]
QED

Theorem dft_reverse_deliver[local]:
  dft_reverse_at vs0 ctx xs fn bb s n /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst budget ctx inst (dft_open_materialize xs n s) =
    dft_open_materialize_result xs m result ==>
  dft_reverse_config vs0 ctx xs
    (dft_open_deliver fn budget bb inst s stack m result)
Proof
  strip_tac >> Cases_on `result` >>
  simp[dft_open_deliver_def, dft_reverse_config_def] >>
  rename1 `OK after` >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (Cases_on `after.vs_halted` >>
      simp[dft_open_continue_def, dft_reverse_config_def] >>
      irule dft_reverse_block >>
      gvs[dft_open_materialize_result_def] >> metis_tac[]) >>
  simp[dft_open_continue_def, dft_reverse_config_def] >>
  irule dft_reverse_next >> gvs[dft_open_materialize_result_def] >>
  goal_assum (drule_at (Pat `step_inst _ _ _ _ = OK _`)) >>
  simp[dft_open_materialize_def]
QED

Theorem dft_reverse_at_step[local]:
  dft_sparse_oracle a xs /\ dft_reverse_at vs0 ctx xs fn bb s n ==>
  dft_reverse_config vs0 ctx xs
    (dft_open_next a ctx (DftOpen (DftAt fn budget bb s) stack n))
Proof
  strip_tac >> simp[Once dft_open_next_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[dft_reverse_config_def] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (simp[dft_open_invoke_def] >>
      Cases_on `decode_invoke inst` >- simp[dft_reverse_config_def] >>
      PairCases_on `x` >> simp[] >>
      Cases_on `lookup_function x0 ctx.ctx_functions`
      >- simp[dft_reverse_config_def] >>
      Cases_on `eval_operands x1 s` >- simp[dft_reverse_config_def] >>
      Cases_on `setup_callee x x' s` >- simp[dft_reverse_config_def] >>
      simp[dft_reverse_config_def] >> irule dft_reverse_callee >>
      simp[dft_history_push_def] >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = GAS`
  >- (Cases_on `?out. inst.inst_outputs = [out]`
      >- (pop_assum strip_assume_tac >> simp[] >>
          irule dft_reverse_deliver >> simp[] >>
          qexists_tac `n` >> simp[] >>
          drule_all dft_open_gas_materialize >>
          simp[Once step_inst_def, dft_open_materialize_result_def]) >>
      simp[] >> Cases_on `inst.inst_outputs` >>
      simp[dft_reverse_config_def] >> Cases_on `t` >>
      gvs[dft_reverse_config_def]) >>
  simp[] >> Cases_on `step_inst_base inst s` >>
  simp[dft_open_deliver_def, dft_reverse_config_def] >>
  rename1 `step_inst_base inst s = OK after` >>
  irule (dft_reverse_deliver |> Q.INST [`result` |-> `OK after`]
    |> SRULE [dft_open_deliver_def, dft_reverse_config_def]) >> simp[] >>
  qexists_tac `n` >> simp[] >>
  drule dft_open_base_materialize >>
  disch_then (qspecl_then [`xs`, `s`, `n`] mp_tac) >>
  simp[Once step_inst_def] >>
  Cases_on `step_inst_base inst s` >>
  Cases_on `step_inst_base inst (dft_open_materialize xs n s)` >>
  simp[dft_open_result_eq_def, dft_open_materialize_result_def,
       stateEquivTheory.lift_result_def]
QED

Theorem dft_reverse_enter_step[local]:
  dft_reverse_enter vs0 ctx xs fn s n ==>
  dft_reverse_config vs0 ctx xs
    (dft_open_next a ctx (DftOpen (DftEnter fn fuel s) stack n))
Proof
  strip_tac >> Cases_on `fuel` >> simp[dft_open_next_def, dft_reverse_config_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
  simp[dft_reverse_config_def] >>
  Cases_on `eval_phis s x.bb_instructions` >>
  simp[dft_reverse_config_def] >>
  irule dft_reverse_enter_at >> qexists_tac `s` >> simp[]
QED

Theorem dft_reverse_history:
  dft_sparse_oracle a xs /\
  dft_reverse_config vs0 ctx xs (DftOpen initial [] nstart) ==>
  dft_reverse_config vs0 ctx xs
    (FUNPOW (dft_open_next a ctx) j (DftOpen initial [] nstart))
Proof
  strip_tac >> completeInduct_on `j` >> Cases_on `j` >- gvs[] >>
  rename1 `SUC k` >>
  `dft_reverse_config vs0 ctx xs
    (FUNPOW (dft_open_next a ctx) k (DftOpen initial [] nstart))` by
    (first_x_assum irule >> decide_tac) >>
  simp[Once FUNPOW_SUC] >>
  Cases_on `FUNPOW (dft_open_next a ctx) k (DftOpen initial [] nstart)` >>
  rename1 `DftOpen ctl stack n` >> Cases_on `ctl`
  >- (irule dft_reverse_enter_step >> gvs[dft_reverse_config_def])
  >- (irule dft_reverse_at_step >> gvs[dft_reverse_config_def]) >>
  rename1 `DftDone result` >>
  Cases_on `result` >> Cases_on `stack` >>
  simp[dft_open_next_def, dft_open_return_def, dft_reverse_config_def] >>
  Cases_on `h` >> rename1 `DftCaller fn budget bb inst caller` >>
  Cases_on `bind_outputs inst.inst_outputs i.iret_values
    (adopt_return_fmp i (merge_callee_state caller v))` >>
  simp[dft_reverse_config_def] >>
  drule_all dft_history_live_return >> strip_tac >>
  `dft_reverse_at vs0 ctx xs fn bb caller n0` by
    (qpat_x_assum `!m. m < SUC k ==> _` (qspec_then `p` mp_tac) >>
     simp[dft_reverse_config_def] >> decide_tac) >>
  irule dft_reverse_deliver >> simp[dft_open_materialize_result_def] >>
  goal_assum (drule_at (Pat `step_inst _ _ _ _ = OK _`)) >> simp[]
QED

Theorem dft_open_observation_raw:
  ctx.ctx_entry = SOME name /\ lookup_function name ctx.ctx_functions = SOME entry /\
  fn_entry_label entry = SOME lbl /\ dft_sparse_oracle a vs0.vs_gas_readings /\
  FUNPOW (dft_open_next a ctx) j
    (DftOpen (DftEnter entry fuel
      (vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) [] 0) =
    DftOpen (DftAt fn budget bb ghost) stack n /\
  get_instruction bb ghost.vs_inst_idx = SOME inst ==>
  raw_reachable vs0 ctx fn inst (dft_open_materialize vs0.vs_gas_readings n ghost)
Proof
  strip_tac >>
  `dft_reverse_config vs0 ctx vs0.vs_gas_readings
    (DftOpen (DftEnter entry fuel
      (vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) [] 0)` by
    (irule dft_reverse_initial >> metis_tac[]) >>
  drule_all dft_reverse_history >> disch_then (qspec_then `j` mp_tac) >>
  simp[dft_reverse_config_def] >> strip_tac >>
  `active_inst fn inst (dft_open_materialize vs0.vs_gas_readings n ghost)` by
    (irule dft_reverse_active_lookup >> gvs[dft_reverse_at_def]) >>
  gvs[dft_reverse_at_def]
QED
