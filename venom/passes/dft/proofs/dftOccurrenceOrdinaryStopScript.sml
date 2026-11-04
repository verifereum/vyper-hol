Theory dftOccurrenceOrdinaryStop
Ancestors
  dftOccurrenceOrdinaryEdit dftOccurrenceOrdinaryObserve
  dftOccurrenceReplay dftOccurrenceMachine dftOpenErase dftOpenMachine
  venomExecSemantics venomInst list

Theorem dft_occ_ordinary_abort:
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\ step_inst_base inst s = Abort a t ==>
  (dft_occ_oracle_next w C c).dft_occ_core =
    DftOpen (DftDone (Abort a t)) (MAP (dft_fill_frame 0) stack) n
Proof
  strip_tac >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_open_deliver_def, dft_open_continue_def, dft_erase_def] >>
  `!f. dft_fill_frame 0 (dft_fill_frame 1 f) = dft_fill_frame 0 f` by
    (Cases >> simp[dft_fill_frame_def]) >>
  simp[MAP_MAP_o, combinTheory.o_DEF] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> REFL_TAC
QED
