Theory dftPositionalGasSegment
Ancestors
  dftPositionalSegment dftPositionalPhase dftPositionalRuntime
  dftPositionalEdit dftOccurrenceReplay dftOccurrenceMachine
  dftOpenErase dftOpenMachine venomExecSemantics venomState venomInst
  finite_map list arithmetic

Definition dft_pos_gas_frame_def:
  dft_pos_gas_frame C D l r <=>
    ?f g b b' inst s j k.
      l = DftCaller f 0 b inst s /\ r = DftCaller g 0 b' inst s /\
      dft_pos_slot C D j k f g b b' /\
      inst.inst_opcode = INVOKE /\
      get_instruction b s.vs_inst_idx = SOME inst /\
      get_instruction b' s.vs_inst_idx = SOME inst
End

Definition dft_pos_gas_phase_def:
  dft_pos_gas_phase C D fi bi pre l r <=>
    ?ctl ctl' ls rs n.
      l.dft_occ_core = DftOpen ctl ls n /\
      r.dft_occ_core = DftOpen ctl' rs n /\
      dft_pos_control C D fi bi pre ctl ctl' /\
      LIST_REL (dft_pos_gas_frame C D) ls rs /\
      l.dft_occ_path = r.dft_occ_path /\
      l.dft_occ_visit = r.dft_occ_visit /\
      l.dft_occ_saved = r.dft_occ_saved /\
      LENGTH l.dft_occ_saved = LENGTH ls
End

Theorem dft_pos_gas_phase_root:
  dft_pos_functions C D f g ==>
  dft_pos_gas_phase C D fi bi pre
    (dft_occ_init (DftOpen (DftEnter f 0 s) [] n))
    (dft_occ_init (DftOpen (DftEnter g 0 s) [] n))
Proof
  simp[dft_pos_gas_phase_def, dft_occ_init_def, dft_pos_control_def] >>
  metis_tac[]
QED

Theorem dft_pos_gas_phase_count:
  dft_pos_gas_phase C D fi bi pre l r ==>
  dft_occ_count l = dft_occ_count r
Proof
  simp[dft_pos_gas_phase_def] >> rpt strip_tac >> simp[dft_occ_count_def]
QED

Theorem dft_pos_gas_phase_terminal:
  dft_pos_gas_phase C D fi bi pre l r /\
  l.dft_occ_core = DftOpen (DftDone result) [] n ==>
  r.dft_occ_core = DftOpen (DftDone result) [] n
Proof
  simp[dft_pos_gas_phase_def, dft_pos_control_def] >> rpt strip_tac >> gvs[]
QED

Theorem dft_pos_gas_fill_twice[local,simp]:
  dft_fill_frame a (dft_fill_frame b fr) = dft_fill_frame a fr
Proof
  Cases_on `fr` >> simp[dft_fill_frame_def]
QED

Theorem dft_pos_gas_two_steps:
  bb.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\
  s.vs_inst_idx = LENGTH pre /\
  c.dft_occ_core = DftOpen (DftAt f 0 bb s) stack n ==>
  FUNPOW (dft_occ_oracle_next w C) 2 c =
    c with <|dft_occ_core := DftOpen (DftAt f 0 bb
      ((update_var v (w (c.dft_occ_path ++ [(c.dft_occ_visit,y.inst_id)]))
        (update_var u (w (c.dft_occ_path ++ [(c.dft_occ_visit,x.inst_id)])) s))
          with vs_inst_idx := LENGTH pre + 2))
      (MAP (dft_fill_frame 0) stack) (n + 2);
      dft_occ_saved := if stack = [] then [] else c.dft_occ_saved|>
Proof
  strip_tac >> Cases_on `c` >> gvs[] >> Cases_on `stack` >>
  simp[FUNPOW_2, dft_occ_oracle_next_def, dft_occ_address_def,
    dft_occ_next_def, dft_next_inf_def, dft_fill_def, dft_fill_control_def,
    dft_erase_def, dft_open_next_def, dft_open_deliver_def, dft_open_continue_def,
    get_instruction_def, EL_APPEND_EQN, is_terminator_def, dft_occ_update_def,
    update_var_def, dft_fill_frame_def, MAP_MAP_o, combinTheory.o_DEF, ADD1,
    dft_occ_config_component_equality] >>
  irule MAP_CONG >> simp[]
QED

Theorem dft_pos_gas_frame_zero[local]:
  dft_pos_gas_frame C D l r ==>
  dft_fill_frame 0 l = l /\ dft_fill_frame 0 r = r
Proof
  simp[dft_pos_gas_frame_def] >> rpt strip_tac >> simp[dft_fill_frame_def]
QED

Theorem dft_pos_gas_stack_zero[local]:
  LIST_REL (dft_pos_gas_frame C D) ls rs ==>
  MAP (dft_fill_frame 0) ls = ls /\ MAP (dft_fill_frame 0) rs = rs
Proof
  map_every qid_spec_tac [`rs`, `ls`] >> Induct >> Cases_on `rs` >> simp[] >>
  metis_tac[dft_pos_gas_frame_zero]
QED

Theorem dft_pos_gas_pair_phase:
  dft_pos_gas_phase C D fi bi pre l r /\
  l.dft_occ_core = DftOpen (DftAt f 0 bb s) ls n /\
  r.dft_occ_core = DftOpen (DftAt g 0 bb' s) rs n /\
  dft_pos_slot C D fi bi f g bb bb' /\
  bb.bb_instructions = pre ++ [x;y] ++ post /\
  bb'.bb_instructions = pre ++ [y;x] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\ u <> v /\
  s.vs_inst_idx = LENGTH pre ==>
  dft_pos_gas_phase C D fi bi pre
    (FUNPOW (dft_occ_oracle_next w C) 2 l)
    (FUNPOW (dft_occ_oracle_next w D) 2 r)
Proof
  strip_tac >>
  qpat_assum `l.dft_occ_core = _`
    (mp_then (Pat `_.dft_occ_core = _`) mp_tac dft_pos_gas_two_steps) >>
  disch_then drule_all >> disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  qpat_assum `r.dft_occ_core = _`
    (mp_then (Pat `_.dft_occ_core = _`) mp_tac dft_pos_gas_two_steps) >>
  disch_then drule_all >> disch_then (qspecl_then [`w`, `D`] assume_tac) >>
  fs[dft_pos_gas_phase_def] >>
  `MAP (dft_fill_frame 0) ls = ls /\ MAP (dft_fill_frame 0) rs = rs` by
    metis_tac[dft_pos_gas_stack_zero] >>
  simp[dft_pos_gas_phase_def] >>
  fs[dft_pos_control_def, update_var_def, FUPDATE_COMMUTES] >>
  Cases_on `ls` >> Cases_on `rs` >> gvs[] >> metis_tac[]
QED

Theorem dft_pos_gas_one_step:
  get_instruction bb s.vs_inst_idx = SOME x /\
  x.inst_opcode = GAS /\ x.inst_outputs = [u] /\
  c.dft_occ_core = DftOpen (DftAt f 0 bb s) stack n ==>
  dft_occ_oracle_next w C c = c with
    <|dft_occ_core := DftOpen (DftAt f 0 bb
      ((update_var u (w (c.dft_occ_path ++ [(c.dft_occ_visit,x.inst_id)])) s)
        with vs_inst_idx := SUC s.vs_inst_idx))
      (MAP (dft_fill_frame 0) stack) (SUC n);
      dft_occ_saved := if stack = [] then [] else c.dft_occ_saved|>
Proof
  strip_tac >> Cases_on `c` >> gvs[] >> Cases_on `stack` >>
  simp[dft_occ_oracle_next_def, dft_occ_address_def,
    dft_occ_next_def, dft_next_inf_def, dft_fill_def, dft_fill_control_def,
    dft_erase_def, dft_open_next_def, dft_open_deliver_def, dft_open_continue_def,
    is_terminator_def, dft_occ_update_def, update_var_def, dft_fill_frame_def,
    MAP_MAP_o, combinTheory.o_DEF, dft_occ_config_component_equality] >>
  irule MAP_CONG >> simp[]
QED

Theorem dft_pos_gas_pair_events:
  bb.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\
  s.vs_inst_idx = LENGTH pre /\
  c.dft_occ_core = DftOpen (DftAt f 0 bb s) stack n ==>
  ((?j. j < 2 /\ dft_occ_gas_event inst addr
      (FUNPOW (dft_occ_oracle_next w C) j c)) <=>
    (inst = x /\ addr = c.dft_occ_path ++ [(c.dft_occ_visit,x.inst_id)]) \/
    (inst = y /\ addr = c.dft_occ_path ++ [(c.dft_occ_visit,y.inst_id)]))
Proof
  strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME x` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  drule_all dft_pos_gas_one_step >>
  disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  `!j:num. j < 2 <=> j = 0 \/ j = 1` by decide_tac >>
  simp[RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  simp[dft_occ_gas_event_def, dft_occ_event_def, get_instruction_def,
    EL_APPEND_EQN, update_var_def, ADD1] >> metis_tac[]
QED

Theorem dft_pos_gas_pair_no_memory:
  bb.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\
  s.vs_inst_idx = LENGTH pre /\
  c.dft_occ_core = DftOpen (DftAt f 0 bb s) stack n ==>
  !j g inst t. j < 2 /\ dft_open_observe g inst t
    (FUNPOW (dft_occ_oracle_next w C) j c).dft_occ_core ==>
    inst_mem_ranges inst t = []
Proof
  strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME x` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  drule_all dft_pos_gas_one_step >>
  disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  `!j:num. j < 2 <=> j = 0 \/ j = 1` by decide_tac >>
  rpt strip_tac >> `j = 0 \/ j = 1` by decide_tac >>
  gvs[dft_open_observe_def, get_instruction_def,
    EL_APPEND_EQN, update_var_def, ADD1] >>
  simp[unitMemInvTheory.inst_mem_ranges_def,
    contextCodegenRelTheory.source_memory_read_ranges_def,
    codegenRelTheory.source_memory_write_ranges_def]
QED

Theorem dft_pos_gas_pair_account:
  l.dft_occ_core = DftOpen (DftAt f 0 bb s) ls n /\
  r.dft_occ_core = DftOpen (DftAt g 0 bb' s) rs n /\
  bb.bb_instructions = pre ++ [x;y] ++ post /\
  bb'.bb_instructions = pre ++ [y;x] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\
  s.vs_inst_idx = LENGTH pre /\
  l.dft_occ_path = r.dft_occ_path /\ l.dft_occ_visit = r.dft_occ_visit ==>
  dft_pos_segment_account C D w 2 2 l r
Proof
  strip_tac >>
  qpat_assum `l.dft_occ_core = _`
    (mp_then (Pat `_.dft_occ_core = _`) mp_tac dft_pos_gas_two_steps) >>
  disch_then drule_all >> disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  qpat_assum `r.dft_occ_core = _`
    (mp_then (Pat `_.dft_occ_core = _`) mp_tac dft_pos_gas_two_steps) >>
  disch_then drule_all >> disch_then (qspecl_then [`w`, `D`] assume_tac) >>
  simp[dft_pos_segment_account_def, dft_occ_count_def] >>
  conj_tac
  >- (rpt gen_tac >>
      qpat_assum `l.dft_occ_core = _`
        (mp_then (Pat `_.dft_occ_core = _`) mp_tac dft_pos_gas_pair_events) >>
      disch_then drule_all >>
      qpat_assum `r.dft_occ_core = _`
        (mp_then (Pat `_.dft_occ_core = _`) mp_tac dft_pos_gas_pair_events) >>
      disch_then drule_all >> metis_tac[]) >>
  conj_tac >> rpt strip_tac >>
  drule_all dft_pos_gas_pair_no_memory >> metis_tac[]
QED

Theorem dft_pos_gas_enter_next:
  D = dft_pos_edit_ctx fi bi pre x y post C /\
  dft_pos_runtime_ready C fi bi pre x y post /\
  dft_pos_gas_phase C D fi bi pre l r /\
  l.dft_occ_core = DftOpen (DftEnter f 0 s) ls n /\
  r.dft_occ_core = DftOpen (DftEnter g 0 s) rs n ==>
  dft_pos_gas_phase C D fi bi pre
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w D r)
Proof
  strip_tac >>
  `dft_pos_functions C D f g /\ LIST_REL (dft_pos_gas_frame C D) ls rs` by
    (fs[dft_pos_gas_phase_def, dft_pos_control_def] >> metis_tac[]) >>
  drule dft_pos_gas_stack_zero >> strip_tac >>
  `OPTREL (dft_pos_blocks C D f g)
    (lookup_block s.vs_current_bb f.fn_blocks)
    (lookup_block s.vs_current_bb g.fn_blocks)` by
    metis_tac[dft_pos_edit_block_lookup] >>
  Cases_on `lookup_block s.vs_current_bb f.fn_blocks`
  >- (fs[optionTheory.OPTREL_def] >>
      gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
        dft_fill_def, dft_fill_control_def, dft_open_next_def,
        dft_erase_def, dft_occ_update_def] >>
      simp[dft_pos_gas_phase_def, dft_pos_control_def] >>
      fs[dft_pos_gas_phase_def] >> metis_tac[]) >>
  rename1 `lookup_block s.vs_current_bb f.fn_blocks = SOME bb` >>
  fs[optionTheory.OPTREL_def] >>
  rename1 `lookup_block s.vs_current_bb g.fn_blocks = SOME bb'` >>
  `eval_phis s bb.bb_instructions = eval_phis s bb'.bb_instructions /\
   phi_prefix_length bb.bb_instructions = phi_prefix_length bb'.bb_instructions` by
    (fs[dft_pos_runtime_ready_def] >> metis_tac[dft_pos_edit_block_phis]) >>
  drule dftPositionalStepTheory.dft_pos_blocks_slot >> strip_tac >>
  `~(j = fi /\ k = bi /\
     phi_prefix_length bb.bb_instructions = SUC (LENGTH pre))` by
    (Cases_on `j = fi /\ k = bi` >> gvs[] >>
     fs[dft_pos_runtime_ready_def, dft_pos_slot_def] >> gvs[] >>
     `phi_prefix_length (pre ++ [x;y] ++ post) <= LENGTH pre` by
       (irule dftRecursiveFixedStepTheory.dft_fixed_phi_bound >> simp[]) >> decide_tac) >>
  Cases_on `eval_phis s bb'.bb_instructions` >>
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_erase_def, MAP_MAP_o, combinTheory.o_DEF, dft_occ_update_def] >>
  simp[dft_pos_gas_phase_def, dft_pos_control_def] >>
  Cases_on `ls` >> Cases_on `rs` >> gvs[SF ETA_ss] >>
  fs[dft_pos_gas_phase_def] >> metis_tac[]
QED

Theorem dft_pos_gas_return_control:
  dft_pos_runtime_ready C fi bi pre x y post /\ x.inst_opcode = GAS /\
  dft_pos_slot C D j k f g bb bb' /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_opcode = INVOKE ==>
  dft_pos_control C D fi bi pre
    (DftAt f 0 bb (t with vs_inst_idx := SUC s.vs_inst_idx))
    (DftAt g 0 bb' (t with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `~(j = fi /\ k = bi /\ s.vs_inst_idx = LENGTH pre)` by
    (strip_tac >> fs[dft_pos_runtime_ready_def, dft_pos_slot_def] >>
     gvs[get_instruction_def, EL_APPEND_EQN]) >>
  simp[dft_pos_control_def] >> metis_tac[]
QED

Theorem dft_pos_gas_done_next:
  dft_pos_runtime_ready C fi bi pre x y post /\ x.inst_opcode = GAS /\
  dft_pos_gas_phase C D fi bi pre l r /\
  l.dft_occ_core = DftOpen (DftDone result) ls n /\
  r.dft_occ_core = DftOpen (DftDone result) rs n ==>
  dft_pos_gas_phase C D fi bi pre
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w D r)
Proof
  strip_tac >>
  `LIST_REL (dft_pos_gas_frame C D) ls rs /\
   l.dft_occ_saved = r.dft_occ_saved /\ LENGTH l.dft_occ_saved = LENGTH ls` by
    (fs[dft_pos_gas_phase_def] >> metis_tac[]) >>
  Cases_on `?ret cs. result = IntRet ret cs`
  >- (pop_assum strip_assume_tac >> gvs[] >> suspend "return") >>
  `!ret cs. result <> IntRet ret cs` by metis_tac[] >>
  `dft_occ_oracle_next w C l = l with
      <|dft_occ_core := DftOpen (DftDone result) [] n; dft_occ_saved := []|> /\
   dft_occ_oracle_next w D r = r with
      <|dft_occ_core := DftOpen (DftDone result) [] n; dft_occ_saved := []|>` by
    metis_tac[dftPositionalReturnTheory.dft_pos_nonreturn_clear] >>
  simp[dft_pos_gas_phase_def, dft_pos_control_def] >>
  fs[dft_pos_gas_phase_def] >> metis_tac[]
QED

Resume dft_pos_gas_done_next[return]:
  Cases_on `ls` >> Cases_on `rs` >> gvs[]
  >- (gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
        dft_fill_def, dft_fill_control_def, dft_open_next_def,
        dft_open_return_def, dft_erase_def, dft_occ_update_def] >>
      simp[dft_pos_gas_phase_def, dft_pos_control_def] >>
      fs[dft_pos_gas_phase_def] >> metis_tac[]) >>
  fs[dft_pos_gas_frame_def] >> gvs[] >>
  Cases_on `l.dft_occ_saved` >> gvs[] >> PairCases_on `h` >>
  Cases_on `dft_restore inst.inst_outputs ret cs s`
  >- suspend "failed_restore" >>
  suspend "restored"
QED

Resume dft_pos_gas_done_next[failed_restore]:
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_open_return_def, dft_fill_frame_def, GSYM dftOccurrenceReturnTheory.dft_restore_def,
    dft_erase_def, dft_occ_update_def] >>
  simp[dft_pos_gas_phase_def, dft_pos_control_def] >>
  fs[dft_pos_gas_phase_def] >> metis_tac[]
QED

Resume dft_pos_gas_done_next[restored]:
  drule_all dft_pos_gas_return_control >> disch_then (qspec_then `x'` assume_tac) >>
  drule dft_pos_gas_stack_zero >> strip_tac >>
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_open_return_def, dft_fill_frame_def, GSYM dftOccurrenceReturnTheory.dft_restore_def,
    dft_open_deliver_def, dft_open_continue_def, is_terminator_def,
    dft_erase_def, dft_occ_update_def, MAP_MAP_o, combinTheory.o_DEF] >>
  simp[dft_pos_gas_phase_def, SF ETA_ss] >>
  Cases_on `r.dft_occ_saved` >> gvs[] >>
  fs[dft_pos_gas_phase_def] >> metis_tac[]
QED
Finalise dft_pos_gas_done_next

Theorem dft_pos_gas_at_outside_next:
  D = dft_pos_edit_ctx fi bi pre x y post C /\
  dft_pos_runtime_ready C fi bi pre x y post /\
  dft_pos_gas_phase C D fi bi pre l r /\
  l.dft_occ_core = DftOpen (DftAt f 0 b s) ls n /\
  r.dft_occ_core = DftOpen (DftAt g 0 b' s) rs n /\
  dft_pos_slot C D j k f g b b' /\
  (j <> fi \/ k <> bi \/
    (s.vs_inst_idx <> LENGTH pre /\ s.vs_inst_idx <> SUC (LENGTH pre))) ==>
  dft_pos_gas_phase C D fi bi pre
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w D r)
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `get_instruction b s.vs_inst_idx = get_instruction b' s.vs_inst_idx` by
    metis_tac[dftPositionalStepTheory.dft_pos_slot_instruction_outside] >>
  `LIST_REL (dft_pos_gas_frame C D) ls rs /\
   l.dft_occ_saved = r.dft_occ_saved /\ LENGTH l.dft_occ_saved = LENGTH ls /\
   l.dft_occ_path = r.dft_occ_path /\ l.dft_occ_visit = r.dft_occ_visit` by
    (fs[dft_pos_gas_phase_def] >> metis_tac[]) >>
  drule dft_pos_gas_stack_zero >> strip_tac >>
  Cases_on `get_instruction b' s.vs_inst_idx`
  >- suspend "missing" >>
  rename1 `get_instruction b' s.vs_inst_idx = SOME inst` >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- suspend "invoke" >>
  Cases_on `inst.inst_opcode = GAS`
  >- suspend "gas" >>
  suspend "ordinary"
QED

Resume dft_pos_gas_at_outside_next[missing]:
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_erase_def, dft_occ_update_def] >>
  simp[dft_pos_gas_phase_def, dft_pos_control_def] >>
  fs[dft_pos_gas_phase_def] >> metis_tac[]
QED

Resume dft_pos_gas_at_outside_next[ordinary]:
  `dft_pos_functions C D f g` by
    (fs[dft_pos_slot_def, dft_pos_functions_def] >> metis_tac[]) >>
  Cases_on `step_inst_base inst s`
  >- (Cases_on `is_terminator inst.inst_opcode`
      >- (Cases_on `v.vs_halted` >>
          gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
            dft_fill_def, dft_fill_control_def, dft_open_next_def,
            dft_open_deliver_def, dft_open_continue_def, dft_erase_def,
            MAP_MAP_o, combinTheory.o_DEF, dft_occ_update_def, SF ETA_ss] >>
          simp[dft_pos_gas_phase_def, dft_pos_control_def] >>
          Cases_on `ls` >> Cases_on `rs` >> gvs[] >>
          fs[dft_pos_gas_phase_def] >> metis_tac[]) >>
      gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
        dft_fill_def, dft_fill_control_def, dft_open_next_def,
        dft_open_deliver_def, dft_open_continue_def, dft_erase_def,
        MAP_MAP_o, combinTheory.o_DEF, dft_occ_update_def, SF ETA_ss] >>
      simp[dft_pos_gas_phase_def, dft_pos_control_def] >>
      Cases_on `ls` >> Cases_on `rs` >> gvs[] >>
      fs[dft_pos_gas_phase_def] >> metis_tac[]) >>
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_open_deliver_def, dft_erase_def,
    MAP_MAP_o, combinTheory.o_DEF, dft_occ_update_def, SF ETA_ss] >>
  simp[dft_pos_gas_phase_def, dft_pos_control_def] >>
  Cases_on `ls` >> Cases_on `rs` >> gvs[] >>
  fs[dft_pos_gas_phase_def] >> metis_tac[]
QED

Resume dft_pos_gas_at_outside_next[gas]:
  Cases_on `inst.inst_outputs` >>
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_erase_def, dft_occ_update_def, dft_occ_address_def]
  >- (simp[dft_pos_gas_phase_def, dft_pos_control_def] >>
      fs[dft_pos_gas_phase_def] >> metis_tac[]) >>
  Cases_on `t` >>
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_open_deliver_def, dft_open_continue_def, is_terminator_def,
    dft_erase_def, MAP_MAP_o, combinTheory.o_DEF, dft_occ_update_def,
    dft_occ_address_def, SF ETA_ss]
  >- (simp[dft_pos_gas_phase_def, dft_pos_control_def] >>
      Cases_on `ls` >> Cases_on `rs` >> gvs[] >>
      fs[dft_pos_gas_phase_def] >> metis_tac[]) >>
  simp[dft_pos_gas_phase_def, dft_pos_control_def] >>
  fs[dft_pos_gas_phase_def] >> metis_tac[]
QED

Resume dft_pos_gas_at_outside_next[invoke]:
  `dftRelationalEdit$dft_rel_interface C D (dft_pos_functions C D) (dft_pos_blocks C D)` by
    metis_tac[dft_pos_runtime_ready_interface] >>
  Cases_on `decode_invoke inst`
  >- suspend "bad_decode" >>
  PairCases_on `x'` >>
  `OPTREL (dft_pos_functions C D)
    (lookup_function x'0 C.ctx_functions) (lookup_function x'0 D.ctx_functions)` by
    fs[dftRelationalEditTheory.dft_rel_interface_def] >>
  Cases_on `lookup_function x'0 C.ctx_functions`
  >- suspend "bad_lookup" >>
  fs[optionTheory.OPTREL_def] >>
  rename1 `lookup_function x'0 C.ctx_functions = SOME callee` >>
  rename1 `lookup_function x'0 D.ctx_functions = SOME callee'` >>
  `!args. setup_callee callee args s = setup_callee callee' args s` by
    metis_tac[dftRelationalEditTheory.dft_rel_interface_def] >>
  Cases_on `eval_operands x'1 s`
  >- suspend "bad_args" >>
  rename1 `eval_operands x'1 s = SOME args` >>
  Cases_on `setup_callee callee' args s`
  >- suspend "bad_setup" >>
  `dft_pos_gas_frame C D (DftCaller f 0 b inst s) (DftCaller g 0 b' inst s)` by
    (simp[dft_pos_gas_frame_def] >> metis_tac[]) >>
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_open_invoke_def, dft_erase_def, MAP_MAP_o, combinTheory.o_DEF,
    dft_fill_frame_def, dft_occ_update_def, SF ETA_ss] >>
  simp[dft_pos_gas_phase_def, dft_pos_control_def] >>
  fs[dft_pos_gas_phase_def] >> metis_tac[]
QED

Resume dft_pos_gas_at_outside_next[bad_decode]:
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_open_invoke_def, dft_erase_def, dft_occ_update_def] >>
  simp[dft_pos_gas_phase_def, dft_pos_control_def] >>
  fs[dft_pos_gas_phase_def] >> metis_tac[]
QED
Resume dft_pos_gas_at_outside_next[bad_lookup]:
  fs[optionTheory.OPTREL_def] >>
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_open_invoke_def, dft_erase_def, dft_occ_update_def] >>
  simp[dft_pos_gas_phase_def, dft_pos_control_def] >>
  fs[dft_pos_gas_phase_def] >> metis_tac[]
QED
Resume dft_pos_gas_at_outside_next[bad_args]:
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_open_invoke_def, dft_erase_def, dft_occ_update_def] >>
  simp[dft_pos_gas_phase_def, dft_pos_control_def] >>
  fs[dft_pos_gas_phase_def] >> metis_tac[]
QED
Resume dft_pos_gas_at_outside_next[bad_setup]:
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_open_invoke_def, dft_erase_def, dft_occ_update_def] >>
  simp[dft_pos_gas_phase_def, dft_pos_control_def] >>
  fs[dft_pos_gas_phase_def] >> metis_tac[]
QED
Finalise dft_pos_gas_at_outside_next

Theorem dft_pos_gas_selected_blocks:
  D = dft_pos_edit_ctx fi bi pre x y post C /\
  dft_pos_runtime_ready C fi bi pre x y post /\
  dft_pos_slot C D fi bi f g bb bb' ==>
  bb.bb_instructions = pre ++ [x;y] ++ post /\
  bb'.bb_instructions = pre ++ [y;x] ++ post
Proof
  simp[dft_pos_runtime_ready_def, dft_pos_slot_def] >> rpt strip_tac >>
  gvs[dft_pos_edit_ctx_def, dft_pos_edit_fn_def, dft_pos_replace_el]
QED


Theorem dft_pos_gas_segment_next:
  D = dft_pos_edit_ctx fi bi pre x y post C /\
  dft_pos_runtime_ready C fi bi pre x y post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\ u <> v /\
  dft_pos_gas_phase C D fi bi pre l r ==>
  ?a. (a = 1 \/ a = 2) /\
    dft_pos_gas_phase C D fi bi pre
      (FUNPOW (dft_occ_oracle_next w C) a l)
      (FUNPOW (dft_occ_oracle_next w D) a r) /\
    dft_pos_segment_account C D w a a l r
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

Resume dft_pos_gas_segment_next[enter]:
  gvs[] >> qexists `1` >> pure_rewrite_tac[FUNPOW_1] >> simp[] >>
  conj_tac
  >- (irule dft_pos_gas_enter_next >> goal_assum (drule_at Any) >> metis_tac[]) >>
  metis_tac[dft_pos_enter_account]
QED
Resume dft_pos_gas_segment_next[done]:
  gvs[] >> qexists `1` >> pure_rewrite_tac[FUNPOW_1] >> simp[] >>
  conj_tac
  >- (irule dft_pos_gas_done_next >> goal_assum (drule_at Any) >> metis_tac[]) >>
  metis_tac[dft_pos_done_one_account]
QED
Resume dft_pos_gas_segment_next[at]:
  gvs[] >> Cases_on `j = fi /\ k = bi /\ s.vs_inst_idx = LENGTH pre`
  >- suspend "pair" >>
  qexists `1` >> pure_rewrite_tac[FUNPOW_1] >> simp[] >> conj_tac
  >- (irule dft_pos_gas_at_outside_next >> goal_assum (drule_at Any) >> metis_tac[]) >>
  irule dftPositionalSegmentTheory.dft_pos_at_outside_account >>
  fs[dft_pos_gas_phase_def] >> metis_tac[]
QED
Resume dft_pos_gas_segment_next[pair]:
  gvs[] >>
  `b.bb_instructions = pre ++ [x;y] ++ post /\
   b'.bb_instructions = pre ++ [y;x] ++ post` by
    metis_tac[dft_pos_gas_selected_blocks] >>
  qexists `2` >> simp[] >> conj_tac
  >- (irule dft_pos_gas_pair_phase >> goal_assum (drule_at Any) >> metis_tac[]) >>
  fs[dft_pos_gas_phase_def] >> metis_tac[dft_pos_gas_pair_account]
QED
Finalise dft_pos_gas_segment_next

Theorem dft_pos_gas_pair_segment:
  dft_pos_gas_phase C D fi bi pre l r /\
  l.dft_occ_core = DftOpen (DftAt f 0 bb s) ls n /\
  r.dft_occ_core = DftOpen (DftAt g 0 bb' s) rs n /\
  dft_pos_slot C D fi bi f g bb bb' /\
  bb.bb_instructions = pre ++ [x;y] ++ post /\
  bb'.bb_instructions = pre ++ [y;x] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\ u <> v /\
  s.vs_inst_idx = LENGTH pre ==>
  dft_pos_gas_phase C D fi bi pre
    (FUNPOW (dft_occ_oracle_next w C) 2 l)
    (FUNPOW (dft_occ_oracle_next w D) 2 r) /\
  dft_pos_segment_account C D w 2 2 l r
Proof
  strip_tac >> conj_tac
  >- (irule dft_pos_gas_pair_phase >> goal_assum (drule_at Any) >> metis_tac[]) >>
  fs[dft_pos_gas_phase_def] >> metis_tac[dft_pos_gas_pair_account]
QED
