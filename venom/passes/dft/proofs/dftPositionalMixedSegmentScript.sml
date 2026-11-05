Theory dftPositionalMixedSegment
Ancestors
  dftPositionalGasSegment dftMixedSegmentAccount dftMixedCrossing
  dftMixedResidualProbe instIdxIndep dftOccurrenceOrdinaryClosure
  dftGasOrdinaryTrace dftOccurrenceOrdinaryStop dftOrdinaryEventTrace
  dftPositionalPhase dftPositionalRuntime dftPositionalEdit
  dftOccurrenceSuspended dftOccurrenceOrdinaryEdit dftOccurrenceReplay
  dftOccurrenceMachine dftOpenMachine dftOpenErase venomExecSemantics venomState
  venomInst list arithmetic

Theorem dft_pos_mixed_stack_zero[local]:
  LIST_REL (dft_pos_gas_frame C D) ls rs ==>
  MAP (dft_fill_frame 0) ls = ls /\ MAP (dft_fill_frame 0) rs = rs
Proof
  map_every qid_spec_tac [`rs`, `ls`] >> Induct >> Cases_on `rs` >>
  simp[dft_pos_gas_frame_def] >> rpt strip_tac >>
  gvs[dft_fill_frame_def] >> metis_tac[]
QED

Theorem dft_pos_mixed_success_records[local]:
  l.dft_occ_core = DftOpen (DftAt f 0 bb s) ls n /\
  r.dft_occ_core = DftOpen (DftAt g 0 bb' s) rs n /\
  MAP (dft_fill_frame 0) ls = ls /\ MAP (dft_fill_frame 0) rs = rs /\
  (ls = [] ==> l.dft_occ_saved = []) /\
  (rs = [] ==> r.dft_occ_saved = []) /\
  l.dft_occ_path = path /\ r.dft_occ_path = path /\
  l.dft_occ_visit = visit /\ r.dft_occ_visit = visit /\
  get_instruction bb s.vs_inst_idx = SOME gas /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME inst /\
  get_instruction bb' s.vs_inst_idx = SOME inst /\
  get_instruction bb' (SUC s.vs_inst_idx) = SOME gas /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\
  ~MEM (Var v) inst.inst_operands /\ ~MEM v inst.inst_outputs /\
  step_inst_base inst s = OK t ==>
  let after = (update_var v (w (path ++ [(visit,gas.inst_id)])) t)
                with vs_inst_idx := SUC (SUC s.vs_inst_idx) in
  FUNPOW (dft_occ_oracle_next w C) 2 l =
    l with dft_occ_core := DftOpen (DftAt f 0 bb after) ls (SUC n) /\
  FUNPOW (dft_occ_oracle_next w D) 2 r =
    r with dft_occ_core := DftOpen (DftAt g 0 bb' after) rs (SUC n)
Proof
  strip_tac >> simp_tac bool_ss [LET_THM, FUNPOW_2] >>
  `step_inst_base inst (update_var v (w (path ++ [(visit,gas.inst_id)])) s) =
     OK (update_var v (w (path ++ [(visit,gas.inst_id)])) t)` by
    metis_tac[dft_gas_value_ordinary_frame] >>
  `step_inst_base inst ((update_var v (w (path ++ [(visit,gas.inst_id)])) s)
      with vs_inst_idx := SUC s.vs_inst_idx) =
     OK ((update_var v (w (path ++ [(visit,gas.inst_id)])) t)
      with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[instIdxIndepTheory.step_inst_inst_idx_indep,
         instIdxIndepTheory.exec_result_map_def] >>
  qpat_assum `l.dft_occ_core = _` (mp_then Any mp_tac dft_suspend_gas_step) >>
  simp[] >> disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  drule_all dft_occ_ordinary_next >>
  disch_then (qspecl_then [`w`, `D`] assume_tac) >>
  conj_tac
  >- (asm_rewrite_tac[] >>
      qmatch_goalsub_abbrev_tac `dft_occ_oracle_next w C mid` >>
      `mid.dft_occ_core = DftOpen (DftAt f 0 bb
        ((update_var v (w (path ++ [(visit,gas.inst_id)])) s)
          with vs_inst_idx := SUC s.vs_inst_idx)) ls (SUC n)` by
        simp[Abbr `mid`] >>
      drule dft_occ_ordinary_next >> simp[update_var_inst_idx] >>
      disch_then (qspecl_then [`w`, `C`] mp_tac) >>
      simp[Abbr `mid`] >> Cases_on `ls` >>
      gvs[dft_occ_config_component_equality]) >>
  asm_rewrite_tac[] >>
  qmatch_goalsub_abbrev_tac `dft_occ_oracle_next w D mid` >>
  `mid.dft_occ_core = DftOpen (DftAt g 0 bb'
    (t with vs_inst_idx := SUC s.vs_inst_idx)) rs n` by simp[Abbr `mid`] >>
  drule dft_suspend_gas_step >> simp[Abbr `mid`] >>
  disch_then (qspecl_then [`w`, `D`] mp_tac) >>
  simp[update_var_def] >> Cases_on `rs` >>
  gvs[dft_occ_config_component_equality]
QED

Theorem dft_pos_mixed_pair_success:
  D = dft_pos_edit_ctx fi bi pre gas inst post C /\
  dft_pos_runtime_ready C fi bi pre gas inst post /\
  dft_pos_gas_phase C D fi bi pre l r /\
  l.dft_occ_core = DftOpen (DftAt f 0 bb s) ls n /\
  r.dft_occ_core = DftOpen (DftAt g 0 bb' s) rs n /\
  dft_pos_slot C D fi bi f g bb bb' /\
  s.vs_inst_idx = LENGTH pre /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\
  ~MEM (Var v) inst.inst_operands /\ ~MEM v inst.inst_outputs /\
  step_inst_base inst s = OK t ==>
  dft_pos_gas_phase C D fi bi pre
    (FUNPOW (dft_occ_oracle_next w C) 2 l)
    (FUNPOW (dft_occ_oracle_next w D) 2 r) /\
  dft_pos_segment_account C D w 2 2 l r
Proof
  strip_tac >>
  drule_all dft_pos_gas_selected_blocks >> strip_tac >>
  `LIST_REL (dft_pos_gas_frame C D) ls rs /\
   l.dft_occ_path = r.dft_occ_path /\ l.dft_occ_visit = r.dft_occ_visit /\
   l.dft_occ_saved = r.dft_occ_saved /\ LENGTH l.dft_occ_saved = LENGTH ls` by
    (fs[dft_pos_gas_phase_def] >> metis_tac[]) >>
  drule dft_pos_mixed_stack_zero >> strip_tac >>
  `(ls = [] ==> l.dft_occ_saved = []) /\
   (rs = [] ==> r.dft_occ_saved = [])` by
    (Cases_on `ls` >> Cases_on `rs` >> gvs[]) >>
  `get_instruction bb s.vs_inst_idx = SOME gas /\
   get_instruction bb (SUC s.vs_inst_idx) = SOME inst /\
   get_instruction bb' s.vs_inst_idx = SOME inst /\
   get_instruction bb' (SUC s.vs_inst_idx) = SOME gas` by
    simp[get_instruction_def, EL_APPEND_EQN, ADD1] >>
  `dft_pos_functions C D f g` by (fs[dft_pos_slot_def, dft_pos_functions_def] >> metis_tac[]) >>
  `r.dft_occ_path = r.dft_occ_path /\ r.dft_occ_visit = r.dft_occ_visit` by simp[] >>
  reverse conj_tac
  >- (drule_all dft_gas_ordinary_success_segment_account >> simp[]) >>
  drule_all dft_pos_mixed_success_records >>
  disch_then (qspecl_then [`w`, `D`, `C`] assume_tac) >>
  qpat_x_assum `D = _` kall_tac >>
  fs[LET_THM] >>
  simp[dft_pos_gas_phase_def, dft_pos_control_def, update_var_inst_idx] >>
  metis_tac[DECIDE ``SUC (SUC k) <> SUC k``]
QED

Theorem dft_pos_mixed_pair_abort:
  D = dft_pos_edit_ctx fi bi pre gas inst post C /\
  dft_pos_runtime_ready C fi bi pre gas inst post /\
  dft_pos_gas_phase C D fi bi pre l r /\
  l.dft_occ_core = DftOpen (DftAt f 0 bb s) ls n /\
  r.dft_occ_core = DftOpen (DftAt g 0 bb' s) rs n /\
  dft_pos_slot C D fi bi f g bb bb' /\
  s.vs_inst_idx = LENGTH pre /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\
  ~MEM (Var v) inst.inst_operands /\ ~MEM v inst.inst_outputs /\
  step_inst_base inst s = Abort a t ==>
  (FUNPOW (dft_occ_oracle_next w C) 2 l).dft_occ_core =
    DftOpen (DftDone (Abort a
      ((update_var v (w (l.dft_occ_path ++ [(l.dft_occ_visit,gas.inst_id)])) t)
        with vs_inst_idx := SUC s.vs_inst_idx))) ls (SUC n) /\
  (FUNPOW (dft_occ_oracle_next w D) 1 r).dft_occ_core =
    DftOpen (DftDone (Abort a t)) rs n /\
  (!i addr. ((?h. h < 2 /\ dft_occ_gas_event i addr
      (FUNPOW (dft_occ_oracle_next w C) h l)) <=>
      i = gas /\ addr = l.dft_occ_path ++ [(l.dft_occ_visit,gas.inst_id)]) /\
    ~(?h. h < 1 /\ dft_occ_gas_event i addr
      (FUNPOW (dft_occ_oracle_next w D) h r))) /\
  dft_occ_count (FUNPOW (dft_occ_oracle_next w C) 2 l) = SUC n /\
  dft_occ_count (FUNPOW (dft_occ_oracle_next w D) 1 r) = n /\
  (!j f i t. j < 2 /\ dft_open_observe f i t
      (FUNPOW (dft_occ_oracle_next w C) j l).dft_occ_core /\
      inst_mem_ranges i t <> [] ==>
    ?k g u. k < 1 /\ dft_pos_functions C D f g /\
      dft_open_observe g i u
        (FUNPOW (dft_occ_oracle_next w D) k r).dft_occ_core /\
      u.vs_memory = t.vs_memory /\ inst_mem_ranges i u = inst_mem_ranges i t) /\
  (!k g i u. k < 1 /\ dft_open_observe g i u
      (FUNPOW (dft_occ_oracle_next w D) k r).dft_occ_core /\
      inst_mem_ranges i u <> [] ==>
    ?j f t. j < 2 /\ dft_pos_functions C D f g /\
      dft_open_observe f i t
        (FUNPOW (dft_occ_oracle_next w C) j l).dft_occ_core /\
      u.vs_memory = t.vs_memory /\ inst_mem_ranges i t = inst_mem_ranges i u)
Proof
  strip_tac >>
  drule_all dft_pos_gas_selected_blocks >> strip_tac >>
  `LIST_REL (dft_pos_gas_frame C D) ls rs /\
   l.dft_occ_path = r.dft_occ_path /\ l.dft_occ_visit = r.dft_occ_visit /\
   l.dft_occ_saved = r.dft_occ_saved /\ LENGTH l.dft_occ_saved = LENGTH ls` by
    (fs[dft_pos_gas_phase_def] >> metis_tac[]) >>
  drule dft_pos_mixed_stack_zero >> strip_tac >>
  `(ls = [] ==> l.dft_occ_saved = [])` by
    (Cases_on `ls` >> gvs[]) >>
  `get_instruction bb s.vs_inst_idx = SOME gas /\
   get_instruction bb (SUC s.vs_inst_idx) = SOME inst /\
   get_instruction bb' s.vs_inst_idx = SOME inst` by
    simp[get_instruction_def, EL_APPEND_EQN, ADD1] >>
  `dft_pos_functions C D f g` by
    (fs[dft_pos_slot_def, dft_pos_functions_def] >> metis_tac[]) >>
  `l.dft_occ_path = l.dft_occ_path /\ l.dft_occ_visit = l.dft_occ_visit` by simp[] >>
  drule_all dft_gas_ordinary_stack_abort >>
  disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  drule_all dft_gas_ordinary_stack_abort >>
  disch_then (qspecl_then [`w`, `D`] assume_tac) >>
  drule_all dft_gas_ordinary_abort_prefix_account >>
  disch_then (qspec_then `w` assume_tac) >>
  drule_all dft_gas_ordinary_prefix_memory >>
  disch_then (qspec_then `w` assume_tac) >>
  qpat_x_assum `D = _` kall_tac >>
  fs[FUNPOW_1, FUNPOW_2] >>
  qpat_x_assum `!j f i t. _` mp_tac >> simp[]
QED


Theorem dft_pos_mixed_segment_next:
  D = dft_pos_edit_ctx fi bi pre gas inst post C /\
  dft_pos_runtime_ready C fi bi pre gas inst post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\
  ~MEM (Var v) inst.inst_operands /\ ~MEM v inst.inst_outputs /\
  dft_pos_gas_phase C D fi bi pre l r /\
  (!f g bb bb' s ls rs n.
    l.dft_occ_core = DftOpen (DftAt f 0 bb s) ls n /\
    r.dft_occ_core = DftOpen (DftAt g 0 bb' s) rs n /\
    dft_pos_slot C D fi bi f g bb bb' /\ s.vs_inst_idx = LENGTH pre ==>
    !e. step_inst_base inst s <> Error e) ==>
  (?a. (a = 1 \/ a = 2) /\
    dft_pos_gas_phase C D fi bi pre
      (FUNPOW (dft_occ_oracle_next w C) a l)
      (FUNPOW (dft_occ_oracle_next w D) a r) /\
    dft_pos_segment_account C D w a a l r) \/
  (?f g bb bb' s ls rs n code t.
    l.dft_occ_core = DftOpen (DftAt f 0 bb s) ls n /\
    r.dft_occ_core = DftOpen (DftAt g 0 bb' s) rs n /\
    dft_pos_slot C D fi bi f g bb bb' /\
    s.vs_inst_idx = LENGTH pre /\ step_inst_base inst s = Abort code t)
Proof
  strip_tac >>
  `?ctl ctl' ls rs n.
    l.dft_occ_core = DftOpen ctl ls n /\ r.dft_occ_core = DftOpen ctl' rs n /\
    dft_pos_control C D fi bi pre ctl ctl'` by
    (fs[dft_pos_gas_phase_def] >> metis_tac[]) >>
  qpat_x_assum `dft_pos_control _ _ _ _ _ _ _` mp_tac >>
  simp[dft_pos_control_def] >> strip_tac
  >- suspend "enter"
  >- suspend "at" >>
  suspend "done"
QED

Resume dft_pos_mixed_segment_next[enter]:
  gvs[] >> qexists `1` >>
  pure_rewrite_tac[FUNPOW_1] >> simp[] >> conj_tac
  >- (irule dft_pos_gas_enter_next >> goal_assum (drule_at Any) >> metis_tac[]) >>
  metis_tac[dftPositionalSegmentTheory.dft_pos_enter_account]
QED
Resume dft_pos_mixed_segment_next[done]:
  gvs[] >> qexists `1` >>
  pure_rewrite_tac[FUNPOW_1] >> simp[] >> conj_tac
  >- (irule dft_pos_gas_done_next >> goal_assum (drule_at Any) >> metis_tac[]) >>
  metis_tac[dftPositionalSegmentTheory.dft_pos_done_one_account]
QED
Resume dft_pos_mixed_segment_next[at]:
  gvs[] >> Cases_on `j = fi /\ k = bi /\ s.vs_inst_idx = LENGTH pre`
  >- suspend "pair" >>
  disj1_tac >> qexists `1` >> pure_rewrite_tac[FUNPOW_1] >> simp[] >> conj_tac
  >- (irule dft_pos_gas_at_outside_next >> goal_assum (drule_at Any) >> metis_tac[]) >>
  irule dftPositionalSegmentTheory.dft_pos_at_outside_account >>
  fs[dft_pos_gas_phase_def] >> metis_tac[]
QED
Resume dft_pos_mixed_segment_next[pair]:
  gvs[] >>
  `!e. step_inst_base inst s <> Error e` by metis_tac[] >>
  drule_all dft_ordinary_result_cases >> strip_tac
  >- (disj1_tac >> qexists `2` >> simp[] >>
      irule dft_pos_mixed_pair_success >> goal_assum (drule_at Any) >> metis_tac[]) >>
  disj2_tac >> goal_assum (drule_at Any) >> metis_tac[]
QED
Finalise dft_pos_mixed_segment_next

Theorem dft_pos_mixed_done_prefix_events[local]:
  (FUNPOW (dft_occ_oracle_next w C) k c).dft_occ_core =
    DftOpen (DftDone result) stack n ==>
  ((?h. h < SUC k /\ dft_occ_gas_event i addr
      (FUNPOW (dft_occ_oracle_next w C) h c)) <=>
   (?h. h < k /\ dft_occ_gas_event i addr
      (FUNPOW (dft_occ_oracle_next w C) h c)))
Proof
  strip_tac >> `~dft_occ_gas_event i addr
    (FUNPOW (dft_occ_oracle_next w C) k c)` by
    metis_tac[dft_done_no_gas_event] >>
  `!h. h < SUC k <=> h < k \/ h = k` by decide_tac >>
  simp[RIGHT_AND_OVER_OR, EXISTS_OR_THM]
QED

Theorem dft_pos_mixed_done_prefix_observe[local]:
  (FUNPOW (dft_occ_oracle_next w C) k c).dft_occ_core =
    DftOpen (DftDone result) stack n /\
  h < SUC k /\ dft_open_observe f i s
    (FUNPOW (dft_occ_oracle_next w C) h c).dft_occ_core ==>
  h < k
Proof
  strip_tac >> Cases_on `h = k` >> gvs[dft_open_observe_def]
QED

Theorem dft_pos_mixed_pair_abort_closed:
  D = dft_pos_edit_ctx fi bi pre gas inst post C /\
  dft_pos_runtime_ready C fi bi pre gas inst post /\
  dft_pos_gas_phase C D fi bi pre l r /\
  l.dft_occ_core = DftOpen (DftAt f 0 bb s) ls n /\
  r.dft_occ_core = DftOpen (DftAt g 0 bb' s) rs n /\
  dft_pos_slot C D fi bi f g bb bb' /\
  s.vs_inst_idx = LENGTH pre /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\
  ~MEM (Var v) inst.inst_operands /\ ~MEM v inst.inst_outputs /\
  step_inst_base inst s = Abort a t ==>
  dft_gas_ordinary_stopped
    (FUNPOW (dft_occ_oracle_next w C) 3 l)
    (FUNPOW (dft_occ_oracle_next w D) 2 r) /\
  dft_mixed_segment_events w C D gas inst l r 3 2 /\
  dft_occ_count (FUNPOW (dft_occ_oracle_next w C) 3 l) = SUC n /\
  dft_occ_count (FUNPOW (dft_occ_oracle_next w D) 2 r) = n /\
  (!i addr. ((?h. h < 3 /\ dft_occ_gas_event i addr
      (FUNPOW (dft_occ_oracle_next w C) h l)) <=>
      i = gas /\ addr = l.dft_occ_path ++ [(l.dft_occ_visit,gas.inst_id)]) /\
    ~(?h. h < 2 /\ dft_occ_gas_event i addr
      (FUNPOW (dft_occ_oracle_next w D) h r))) /\
  (!j f i t. j < 3 /\ dft_open_observe f i t
      (FUNPOW (dft_occ_oracle_next w C) j l).dft_occ_core /\
      inst_mem_ranges i t <> [] ==>
    ?k g u. k < 2 /\ dft_pos_functions C D f g /\
      dft_open_observe g i u
        (FUNPOW (dft_occ_oracle_next w D) k r).dft_occ_core /\
      u.vs_memory = t.vs_memory /\ inst_mem_ranges i u = inst_mem_ranges i t) /\
  (!k g i u. k < 2 /\ dft_open_observe g i u
      (FUNPOW (dft_occ_oracle_next w D) k r).dft_occ_core /\
      inst_mem_ranges i u <> [] ==>
    ?j f t. j < 3 /\ dft_pos_functions C D f g /\
      dft_open_observe f i t
        (FUNPOW (dft_occ_oracle_next w C) j l).dft_occ_core /\
      u.vs_memory = t.vs_memory /\ inst_mem_ranges i t = inst_mem_ranges i u)
Proof
  strip_tac >> drule_all dft_pos_mixed_pair_abort >>
  disch_then (qspec_then `w` strip_assume_tac) >>
  qpat_x_assum `D = _` kall_tac >>
  qpat_assum `(FUNPOW _ 2 l).dft_occ_core = _`
    (mp_then Any mp_tac dft_occ_abort_clear) >>
  disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  qpat_assum `(FUNPOW _ 1 r).dft_occ_core = _`
    (mp_then Any mp_tac dft_occ_abort_clear) >>
  disch_then (qspecl_then [`w`, `D`] assume_tac) >>
  `FUNPOW (dft_occ_oracle_next w C) 3 l =
     dft_occ_oracle_next w C (FUNPOW (dft_occ_oracle_next w C) 2 l) /\
   FUNPOW (dft_occ_oracle_next w D) 2 r =
     dft_occ_oracle_next w D (FUNPOW (dft_occ_oracle_next w D) 1 r)` by
    (`3 = SUC 2 /\ (2:num) = SUC 1` by decide_tac >>
     metis_tac[FUNPOW_SUC]) >>
  `dft_gas_ordinary_stopped
    (FUNPOW (dft_occ_oracle_next w C) 3 l)
    (FUNPOW (dft_occ_oracle_next w D) 2 r)` by
    (fs[FUNPOW_1] >> simp[dft_gas_ordinary_stopped_def]) >>
  `!i addr. ((?h. h < 3 /\ dft_occ_gas_event i addr
      (FUNPOW (dft_occ_oracle_next w C) h l)) <=>
      i = gas /\ addr = l.dft_occ_path ++ [(l.dft_occ_visit,gas.inst_id)]) /\
    ~(?h. h < 2 /\ dft_occ_gas_event i addr
      (FUNPOW (dft_occ_oracle_next w D) h r))` by
    (rpt gen_tac >>
     qpat_assum `(FUNPOW _ 2 l).dft_occ_core = _`
       (mp_then Any mp_tac dft_pos_mixed_done_prefix_events) >>
     qpat_assum `(FUNPOW _ 1 r).dft_occ_core = _`
       (mp_then Any mp_tac dft_pos_mixed_done_prefix_events) >>
     simp[] >> metis_tac[]) >>
  `dft_occ_count (FUNPOW (dft_occ_oracle_next w C) 3 l) = SUC n /\
   dft_occ_count (FUNPOW (dft_occ_oracle_next w D) 2 r) = n` by
    (fs[FUNPOW_1] >> simp[dft_occ_count_def]) >>
  simp[] >> conj_tac
  >- (simp[dft_mixed_segment_events_def] >> disj2_tac >> simp[] >>
      metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >>
      `j < 2` by
        (irule dft_pos_mixed_done_prefix_observe >>
         simp[] >> goal_assum (drule_at Any) >> metis_tac[]) >>
      qpat_x_assum `!j f i t. _` drule_all >> strip_tac >>
      `k < 2` by decide_tac >> metis_tac[]) >>
  rpt strip_tac >>
  `k < 1` by
    (irule dft_pos_mixed_done_prefix_observe >>
     simp[] >> goal_assum (drule_at Any) >>
     qpat_assum `(FUNPOW _ 1 r).dft_occ_core = _`
       (strip_assume_tac o REWRITE_RULE[FUNPOW_1]) >>
     goal_assum (drule_at Any)) >>
  qpat_x_assum `!k g i u. _` drule_all >> strip_tac >>
  `j < 3` by decide_tac >> metis_tac[]
QED
