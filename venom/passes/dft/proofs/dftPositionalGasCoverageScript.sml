Theory dftPositionalGasCoverage
Ancestors
  dftPositionalClosure dftPositionalLifecycle dftPositionalStep dftPositionalSegment
  dftPositionalPhase dftPositionalRuntime dftPositionalEdit
  dftOccurrenceMachine dftOpenMachine venomExecSemantics venomInst
  venomState list arithmetic

Theorem dft_pos_phase_gas_event:
  D = dft_pos_edit_ctx fi bi pre x call post C /\
  dft_pos_runtime_ready C fi bi pre x call post /\
  x.inst_opcode <> GAS /\ call.inst_opcode <> GAS /\
  dft_pos_phase C D fi bi pre x call post l r ==>
  !inst addr. dft_occ_gas_event inst addr l <=> dft_occ_gas_event inst addr r
Proof
  strip_tac >>
  qpat_x_assum `dft_pos_phase _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[dft_pos_phase_def] >> strip_tac >>
  qpat_x_assum `dft_pos_control _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[dft_pos_control_def] >> strip_tac
  >- (gvs[dft_occ_gas_event_def, dft_occ_event_def])
  >- suspend "at"
  >> gvs[dft_occ_gas_event_def, dft_occ_event_def]
QED

Resume dft_pos_phase_gas_event[at]:
  gvs[] >> Cases_on `j = fi /\ k = bi /\ s.vs_inst_idx = LENGTH pre`
  >- suspend "selected" >>
  `get_instruction b s.vs_inst_idx = get_instruction b' s.vs_inst_idx` by
    (irule dft_pos_slot_instruction_outside >> metis_tac[]) >>
  gvs[dft_occ_gas_event_def, dft_occ_event_def]
QED
Resume dft_pos_phase_gas_event[selected]:
  gvs[dft_pos_runtime_ready_def, dft_pos_slot_def,
      dft_pos_edit_ctx_selected, dft_pos_edit_fn_selected] >>
  simp[dft_occ_gas_event_def, dft_occ_event_def, get_instruction_def,
       EL_APPEND_EQN] >> metis_tac[]
QED
Finalise dft_pos_phase_gas_event

Theorem dft_pos_rooted_progress_account:
  D = dft_pos_edit_ctx fi bi pre x call post C /\
  dft_pos_runtime_ready C fi bi pre x call post /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  ctx_labels_bound Corig L /\ MEM rootfn C.ctx_functions /\
  fn_entry_label rootfn = SOME s0.vs_current_bb /\ s0.vs_labels = L /\
  rootL = dft_occ_init (DftOpen (DftEnter rootfn 0 s0) [] n0) /\
  ~dft_must_order x call /\ call.inst_opcode = INVOKE /\
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> ALLOCA /\ x.inst_opcode <> GAS /\ x.inst_opcode <> INVOKE /\
  dft_pos_rooted_phase w C D fi bi pre x call post rootL rootR l r ==>
  ?a b. (a = 1 \/ a = 2) /\ (b = 1 \/ b = 2) /\
    dft_pos_rooted_phase w C D fi bi pre x call post rootL rootR
      (FUNPOW (dft_occ_oracle_next w C) a l)
      (FUNPOW (dft_occ_oracle_next w D) b r) /\
    dft_pos_segment_account C D w a b l r
Proof
  strip_tac >> drule dft_pos_rooted_phase_project >> strip_tac >>
  `!f g bb bb' s ls n.
    dft_pos_slot C D fi bi f g bb bb' /\
    l.dft_occ_core = DftOpen (DftAt f 0 bb s) ls n /\
    s.vs_inst_idx = LENGTH pre ==>
    ?f0 b0. dft_recursive_crossing_ready f0 b0 bb pre x call post s` by
    (rpt strip_tac >>
     irule_at Any dft_pos_root_crossing_ready >> metis_tac[]) >>
  drule_all dft_pos_segment_next >>
  disch_then (qspec_then `w` (qx_choosel_then [`da`, `db`] strip_assume_tac)) >>
  qexistsl_tac [`da`, `db`] >>
  metis_tac[dft_pos_rooted_phase_extend]
QED

Theorem dft_pos_rooted_progress_gas:
  D = dft_pos_edit_ctx fi bi pre x call post C /\
  dft_pos_runtime_ready C fi bi pre x call post /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  ctx_labels_bound Corig L /\ MEM rootfn C.ctx_functions /\
  fn_entry_label rootfn = SOME s0.vs_current_bb /\ s0.vs_labels = L /\
  ~dft_must_order x call /\ call.inst_opcode = INVOKE /\
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> ALLOCA /\ x.inst_opcode <> GAS /\ x.inst_opcode <> INVOKE /\
  dft_pos_rooted_phase w C D fi bi pre x call post
    (dft_occ_init (DftOpen (DftEnter rootfn 0 s0) [] n0)) rootR l r ==>
  ?a b. 0 < a /\ a <= 2 /\ 0 < b /\ b <= 2 /\
    dft_pos_rooted_phase w C D fi bi pre x call post
      (dft_occ_init (DftOpen (DftEnter rootfn 0 s0) [] n0)) rootR
      (FUNPOW (dft_occ_oracle_next w C) a l)
      (FUNPOW (dft_occ_oracle_next w D) b r) /\
    (!inst addr.
      (?i. i < a /\ dft_occ_gas_event inst addr
        (FUNPOW (dft_occ_oracle_next w C) i l)) <=>
      (?j. j < b /\ dft_occ_gas_event inst addr
        (FUNPOW (dft_occ_oracle_next w D) j r)))
Proof
  strip_tac >>
  `dft_occ_init (DftOpen (DftEnter rootfn 0 s0) [] n0) =
   dft_occ_init (DftOpen (DftEnter rootfn 0 s0) [] n0)` by simp[] >>
  drule_all dft_pos_rooted_progress_account >>
  disch_then (qx_choosel_then [`a`, `b`] strip_assume_tac) >>
  qexistsl_tac [`a`, `b`] >> fs[dft_pos_segment_account_def]
QED
