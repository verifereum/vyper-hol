Theory dftMixedEventTrace
Ancestors
  dftMixedCrossing dftOrdinaryEventTrace dftOccurrenceMachine
  dftOccurrenceReplay dftOccurrenceSuspended dftOccurrenceOrdinaryClosure
  dftOccurrenceOrdinaryEdit
  dftOpenMachine dftOpenErase venomExecSemantics venomState venomInst list arithmetic

Theorem dft_prefix_two_positions[local]:
  (?h:num. h < 2 /\ P h) <=> P 0 \/ P 1
Proof
  eq_tac
  >- (strip_tac >> `h = 0 \/ h = 1` by decide_tac >> gvs[]) >>
  strip_tac >- (qexists_tac `0` >> simp[]) >>
  qexists_tac `1` >> simp[]
QED

Theorem dft_gas_first_prefix_events:
  l.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  MAP (dft_fill_frame 0) stack = stack /\
  (stack = [] ==> l.dft_occ_saved = []) /\
  l.dft_occ_path = path /\ l.dft_occ_visit = visit /\
  get_instruction bb s.vs_inst_idx = SOME gas /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME inst /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\ inst.inst_opcode <> GAS ==>
  ((?h. h < 2 /\ dft_occ_gas_event i a
    (FUNPOW (dft_occ_oracle_next w C) h l)) <=>
    i = gas /\ a = path ++ [(visit,gas.inst_id)])
Proof
  strip_tac >> drule_all dft_suspend_gas_step >>
  disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  simp[dft_prefix_two_positions, FUNPOW] >>
  gvs[dft_occ_gas_event_def, dft_occ_event_def, dft_occ_address_def,
      update_var_inst_idx] >> metis_tac[]
QED

Theorem dft_gas_gas_prefix_events:
  l.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  MAP (dft_fill_frame 0) stack = stack /\
  (stack = [] ==> l.dft_occ_saved = []) /\
  l.dft_occ_path = path /\ l.dft_occ_visit = visit /\
  get_instruction bb s.vs_inst_idx = SOME x /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME y /\
  x.inst_opcode = GAS /\ x.inst_outputs = [u] /\
  y.inst_opcode = GAS /\ y.inst_outputs = [v] ==>
  ((?h. h < 2 /\ dft_occ_gas_event i a
      (FUNPOW (dft_occ_oracle_next w C) h l)) <=>
   (i = x /\ a = path ++ [(visit,x.inst_id)]) \/
   (i = y /\ a = path ++ [(visit,y.inst_id)]))
Proof
  strip_tac >> drule_all dft_suspend_gas_step >>
  disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  simp[dft_prefix_two_positions, FUNPOW] >>
  gvs[dft_occ_gas_event_def, dft_occ_event_def, dft_occ_address_def,
      update_var_inst_idx] >> metis_tac[]
QED

Theorem dft_ordinary_first_prefix_events:
  r.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  MAP (dft_fill_frame 0) stack = stack /\
  r.dft_occ_path = path /\ r.dft_occ_visit = visit /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME gas /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\ step_inst_base inst s = OK t ==>
  ((?h. h < 2 /\ dft_occ_gas_event i a
    (FUNPOW (dft_occ_oracle_next w C) h r)) <=>
    i = gas /\ a = path ++ [(visit,gas.inst_id)])
Proof
  strip_tac >> drule_all dft_occ_ordinary_next >>
  disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  simp[dft_prefix_two_positions, FUNPOW] >>
  gvs[dft_occ_gas_event_def, dft_occ_event_def, dft_occ_address_def] >> metis_tac[]
QED

Theorem dft_ordinary_first_no_event:
  r.dft_occ_core = DftOpen (DftAt fn fuel bb s) stack n /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_opcode <> GAS ==>
  ~(?h. h < 1 /\ dft_occ_gas_event i a
    (FUNPOW (dft_occ_oracle_next w C) h r))
Proof
  simp[] >> metis_tac[dft_at_no_gas_event]
QED

(* The hypotheses are the event-relevant subset of the stack square. The
   unary boundaries above apply unchanged when the two roles are reversed. *)
Theorem dft_gas_ordinary_success_events:
  l.dft_occ_core = DftOpen (DftAt fnL 0 bbL s) stackL n /\
  r.dft_occ_core = DftOpen (DftAt fnR 0 bbR s) stackR n /\
  MAP (dft_fill_frame 0) stackL = stackL /\
  MAP (dft_fill_frame 0) stackR = stackR /\
  (stackL = [] ==> l.dft_occ_saved = []) /\
  l.dft_occ_path = path /\ r.dft_occ_path = path /\
  l.dft_occ_visit = visit /\ r.dft_occ_visit = visit /\
  get_instruction bbL s.vs_inst_idx = SOME gas /\
  get_instruction bbL (SUC s.vs_inst_idx) = SOME inst /\
  get_instruction bbR s.vs_inst_idx = SOME inst /\
  get_instruction bbR (SUC s.vs_inst_idx) = SOME gas /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\ step_inst_base inst s = OK t ==>
  ((?h. h < 2 /\ dft_occ_gas_event i a
      (FUNPOW (dft_occ_oracle_next w C) h l)) <=>
    i = gas /\ a = path ++ [(visit,gas.inst_id)]) /\
  ((?h. h < 2 /\ dft_occ_gas_event i a
      (FUNPOW (dft_occ_oracle_next w C) h r)) <=>
    i = gas /\ a = path ++ [(visit,gas.inst_id)])
Proof
  strip_tac >> conj_tac
  >- (irule dft_gas_first_prefix_events >> metis_tac[]) >>
  irule dft_ordinary_first_prefix_events >> metis_tac[]
QED

Theorem dft_gas_ordinary_abort_events:
  l.dft_occ_core = DftOpen (DftAt fnL 0 bbL s) stackL n /\
  r.dft_occ_core = DftOpen (DftAt fnR 0 bbR s) stackR n /\
  MAP (dft_fill_frame 0) stackL = stackL /\
  (stackL = [] ==> l.dft_occ_saved = []) /\
  l.dft_occ_path = path /\ l.dft_occ_visit = visit /\
  get_instruction bbL s.vs_inst_idx = SOME gas /\
  get_instruction bbL (SUC s.vs_inst_idx) = SOME inst /\
  get_instruction bbR s.vs_inst_idx = SOME inst /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\ inst.inst_opcode <> GAS ==>
  ((?h. h < 2 /\ dft_occ_gas_event i a
      (FUNPOW (dft_occ_oracle_next w C) h l)) <=>
    i = gas /\ a = path ++ [(visit,gas.inst_id)]) /\
  ~(?h. h < 1 /\ dft_occ_gas_event i a
      (FUNPOW (dft_occ_oracle_next w C) h r))
Proof
  strip_tac >> conj_tac
  >- (irule dft_gas_first_prefix_events >> metis_tac[]) >>
  irule dft_ordinary_first_no_event >> metis_tac[]
QED
