Theory dftOccurrenceOrdinaryEdit
Ancestors
  dftOccurrenceReplay dftOccurrenceMachine dftOpenErase dftOpenMachine
  dftOrdinarySwap venomExecSemantics venomInst list

Theorem dft_occ_ordinary_next:
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\ step_inst_base inst s = OK t ==>
  dft_occ_oracle_next w C c = c with
    <| dft_occ_core := DftOpen
         (DftAt fn 0 bb (t with vs_inst_idx := SUC s.vs_inst_idx))
         (MAP (dft_fill_frame 0) stack) n;
       dft_occ_saved := if stack = [] then [] else c.dft_occ_saved |>
Proof
  strip_tac >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_open_deliver_def, dft_open_continue_def, dft_erase_def,
    MAP_MAP_o, combinTheory.o_DEF] >>
  `!f. dft_fill_frame 0 (dft_fill_frame 1 f) = dft_fill_frame 0 f` by
    (Cases >> simp[dft_fill_frame_def]) >>
  simp[] >> Cases_on `stack` >> simp[dft_occ_update_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> REFL_TAC
QED
