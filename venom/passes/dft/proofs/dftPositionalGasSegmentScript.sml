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
