Theory dftMixedSegmentAccount
Ancestors
  dftMixedEventTrace dftMixedCrossing dftPositionalSegment
  dftPendingSuspension dftOccurrenceSuspended dftOccurrenceMachine dftOccurrenceReplay
  dftOpenMachine dftOccurrenceOrdinaryEdit venomExecSemantics venomState list arithmetic

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

Theorem dft_gas_ordinary_prefix_memory:
  l.dft_occ_core = DftOpen (DftAt fnL 0 bbL s) stackL nL /\
  r.dft_occ_core = DftOpen (DftAt fnR 0 bbR s) stackR nR /\
  MAP (dft_fill_frame 0) stackL = stackL /\
  (stackL = [] ==> l.dft_occ_saved = []) /\
  l.dft_occ_path = path /\ l.dft_occ_visit = visit /\
  get_instruction bbL s.vs_inst_idx = SOME gas /\
  get_instruction bbL (SUC s.vs_inst_idx) = SOME inst /\
  get_instruction bbR s.vs_inst_idx = SOME inst /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  ~is_terminator inst.inst_opcode /\ ~MEM (Var v) inst.inst_operands /\
  dft_pos_functions C D fnL fnR ==>
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
  strip_tac >> drule_all dft_suspend_gas_step >>
  disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  drule_all dft_gas_ordinary_observation >>
  disch_then (qspecl_then [`w (path ++ [(visit,gas.inst_id)])`, `s`,
                            `SUC s.vs_inst_idx`] assume_tac) >>
  `!t. inst_mem_ranges gas t = []` by
    simp[unitMemInvTheory.inst_mem_ranges_def,
         contextCodegenRelTheory.source_memory_read_ranges_def,
         codegenRelTheory.source_memory_write_ranges_def] >>
  conj_tac
  >- (rpt strip_tac >> `j = 0 \/ j = 1` by decide_tac >>
      gvs[FUNPOW, dft_open_observe_def, update_var_inst_idx] >>
      qexistsl_tac [`0`, `fnR`, `s`] >>
      gvs[FUNPOW, dft_open_observe_def]) >>
  rpt strip_tac >> `k = 0` by decide_tac >>
  gvs[FUNPOW, dft_open_observe_def] >>
  qexistsl_tac [`1`, `fnL`,
    `(update_var v (w (l.dft_occ_path ++ [(l.dft_occ_visit,gas.inst_id)])) s)
       with vs_inst_idx := SUC s.vs_inst_idx`] >>
  gvs[FUNPOW, dft_open_observe_def, update_var_inst_idx]
QED

Theorem dft_gas_ordinary_abort_prefix_account:
  l.dft_occ_core = DftOpen (DftAt fnL 0 bbL s) stackL n /\
  r.dft_occ_core = DftOpen (DftAt fnR 0 bbR s) stackR n /\
  MAP (dft_fill_frame 0) stackL = stackL /\
  MAP (dft_fill_frame 0) stackR = stackR /\
  (stackL = [] ==> l.dft_occ_saved = []) /\
  l.dft_occ_path = path /\ l.dft_occ_visit = visit /\
  get_instruction bbL s.vs_inst_idx = SOME gas /\
  get_instruction bbL (SUC s.vs_inst_idx) = SOME inst /\
  get_instruction bbR s.vs_inst_idx = SOME inst /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\
  ~MEM (Var v) inst.inst_operands /\ ~MEM v inst.inst_outputs /\
  step_inst_base inst s = Abort a t /\ dft_pos_functions C D fnL fnR ==>
  (!i addr. ((?h. h < 2 /\ dft_occ_gas_event i addr
      (FUNPOW (dft_occ_oracle_next w C) h l)) <=>
      i = gas /\ addr = path ++ [(visit,gas.inst_id)]) /\
    ~(?h. h < 1 /\ dft_occ_gas_event i addr
      (FUNPOW (dft_occ_oracle_next w D) h r))) /\
  dft_occ_count (FUNPOW (dft_occ_oracle_next w C) 2 l) = SUC n /\
  dft_occ_count (FUNPOW (dft_occ_oracle_next w D) 1 r) = n
Proof
  strip_tac >> conj_tac
  >- (gen_tac >> gen_tac >>
      drule_all dft_gas_ordinary_abort_events >>
      disch_then (qspecl_then [`w`, `i`, `addr`, `C`] mp_tac) >>
      drule_all dft_ordinary_first_no_event >>
      metis_tac[]) >>
  drule_all dft_gas_ordinary_stack_abort >>
  disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  drule_all dft_gas_ordinary_stack_abort >>
  disch_then (qspecl_then [`w`, `D`] assume_tac) >>
  simp[FUNPOW_2, dft_occ_count_def]
QED

Theorem dft_gas_ordinary_success_segment_account:
  l.dft_occ_core = DftOpen (DftAt fnL 0 bbL s) stackL n /\
  r.dft_occ_core = DftOpen (DftAt fnR 0 bbR s) stackR n /\
  MAP (dft_fill_frame 0) stackL = stackL /\
  MAP (dft_fill_frame 0) stackR = stackR /\
  (stackL = [] ==> l.dft_occ_saved = []) /\
  (stackR = [] ==> r.dft_occ_saved = []) /\
  l.dft_occ_path = path /\ r.dft_occ_path = path /\
  l.dft_occ_visit = visit /\ r.dft_occ_visit = visit /\
  get_instruction bbL s.vs_inst_idx = SOME gas /\
  get_instruction bbL (SUC s.vs_inst_idx) = SOME inst /\
  get_instruction bbR s.vs_inst_idx = SOME inst /\
  get_instruction bbR (SUC s.vs_inst_idx) = SOME gas /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\
  ~MEM (Var v) inst.inst_operands /\ ~MEM v inst.inst_outputs /\
  step_inst_base inst s = OK t /\ dft_pos_functions C D fnL fnR ==>
  dft_pos_segment_account C D w 2 2 l r
Proof
  strip_tac >>
  drule_all dft_gas_ordinary_stack_square >>
  disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  drule_all dft_gas_ordinary_stack_square >>
  disch_then (qspecl_then [`w`, `D`] assume_tac) >>
  fs[LET_THM] >>
  simp[dft_pos_segment_account_def, FUNPOW_2, dft_occ_count_def] >>
  conj_tac
  >- (rpt gen_tac >>
      drule_all dft_gas_first_prefix_events >>
      drule_all dft_ordinary_first_prefix_events >> metis_tac[]) >>
  drule_all dft_gas_ordinary_prefix_memory >>
  disch_then (qspec_then `w` strip_assume_tac) >>
  conj_tac
  >- (rpt strip_tac >>
      `j < 2` by simp[] >>
      first_x_assum drule_all >> strip_tac >>
      qexistsl_tac [`k`, `g`, `u`] >> simp[]) >>
  qpat_assum `r.dft_occ_core = _`
    (mp_then Any mp_tac dft_occ_ordinary_next) >>
  simp[] >> disch_then (qspecl_then [`w`, `D`] assume_tac) >>
  rpt strip_tac >> `k = 0 \/ k = 1` by decide_tac
  >- (`k < 1` by simp[] >> first_x_assum drule_all >> metis_tac[]) >>
  gvs[FUNPOW, dft_open_observe_def] >>
  gvs[unitMemInvTheory.inst_mem_ranges_def,
      contextCodegenRelTheory.source_memory_read_ranges_def,
      codegenRelTheory.source_memory_write_ranges_def]
QED
