Theory dftMixedSegmentAccount
Ancestors
  dftMixedEventTrace dftMixedCrossing dftPositionalSegment
  dftPendingSuspension dftOccurrenceSuspended dftOccurrenceMachine dftOccurrenceReplay
  dftOpenMachine venomExecSemantics venomState list arithmetic

Theorem dft_gas_gas_prefix_no_memory:
  l.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  MAP (dft_fill_frame 0) stack = stack /\
  (stack = [] ==> l.dft_occ_saved = []) /\
  l.dft_occ_path = path /\ l.dft_occ_visit = visit /\
  get_instruction bb s.vs_inst_idx = SOME x /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME y /\
  x.inst_opcode = GAS /\ x.inst_outputs = [u] /\
  y.inst_opcode = GAS /\ y.inst_outputs = [v] ==>
  !j f inst t. j < 2 /\ dft_open_observe f inst t
    (FUNPOW (dft_occ_oracle_next w C) j l).dft_occ_core ==>
    inst_mem_ranges inst t = []
Proof
  strip_tac >> drule_all dft_suspend_gas_step >>
  disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  rpt strip_tac >> `j = 0 \/ j = 1` by decide_tac >>
  gvs[FUNPOW, dft_open_observe_def, update_var_inst_idx] >>
  simp[unitMemInvTheory.inst_mem_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def]
QED

Theorem dft_gas_gas_segment_account:
  l.dft_occ_core = DftOpen (DftAt fnL 0 bbL s) stackL nL /\
  r.dft_occ_core = DftOpen (DftAt fnR 0 bbR s) stackR nR /\
  MAP (dft_fill_frame 0) stackL = stackL /\
  MAP (dft_fill_frame 0) stackR = stackR /\
  (stackL = [] ==> l.dft_occ_saved = []) /\
  (stackR = [] ==> r.dft_occ_saved = []) /\
  l.dft_occ_path = path /\ r.dft_occ_path = path /\
  l.dft_occ_visit = visit /\ r.dft_occ_visit = visit /\
  get_instruction bbL s.vs_inst_idx = SOME x /\
  get_instruction bbL (SUC s.vs_inst_idx) = SOME y /\
  get_instruction bbR s.vs_inst_idx = SOME y /\
  get_instruction bbR (SUC s.vs_inst_idx) = SOME x /\
  x.inst_opcode = GAS /\ x.inst_outputs = [u] /\
  y.inst_opcode = GAS /\ y.inst_outputs = [v] /\ u <> v ==>
  dft_pos_segment_account C D w 2 2 l r
Proof
  strip_tac >>
  qpat_assum `l.dft_occ_core = _`
    (mp_then Any mp_tac dft_gas_gas_two_steps) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  qpat_assum `r.dft_occ_core = _`
    (mp_then Any mp_tac dft_gas_gas_two_steps) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`w`, `D`] assume_tac) >>
  simp[dft_pos_segment_account_def, dft_occ_count_def] >>
  conj_tac
  >- (rpt gen_tac >>
      qpat_assum `l.dft_occ_core = _`
        (mp_then Any mp_tac dft_gas_gas_prefix_events) >>
      disch_then drule_all >>
      qpat_assum `r.dft_occ_core = _`
        (mp_then Any mp_tac dft_gas_gas_prefix_events) >>
      disch_then drule_all >> metis_tac[]) >>
  conj_tac >> rpt strip_tac >>
  drule_all dft_gas_gas_prefix_no_memory >> metis_tac[]
QED
