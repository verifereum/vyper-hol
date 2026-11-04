Theory dftOccurrenceCallClosure
Ancestors
  dftOccurrenceCallCrossing dftOccurrenceCallStack dftOccurrenceSuspended
  dftOccurrenceGasEditTrace dftOccurrenceGasEdit dftOccurrenceMachine
  dftOpenMachine dftOpenErase unitMemInv venomState venomExecSemantics venomInst arithmetic list

Definition dft_mixed_phase_def:
  dft_mixed_phase bb0 pre gas call post v w l r <=>
    dft_mixed_sync bb0 pre gas call post v w l r \/
    dft_mixed_discharge bb0 pre gas call post v w l r \/
    dft_suspend_cleared l r
End

Definition dft_mixed_safe_sync_def:
  dft_mixed_safe_sync bb0 pre l <=>
    !fn s stack n. l.dft_occ_core = DftOpen (DftAt fn 0 bb0 s) stack n ==>
      s.vs_inst_idx <> SUC (LENGTH pre)
End

Theorem dft_mixed_cleared_next:
  dft_suspend_cleared l r ==>
  dft_suspend_cleared (dft_occ_oracle_next w C l) (dft_occ_oracle_next w E r)
Proof
  simp[dft_suspend_cleared_def] >> rpt strip_tac >>
  drule dft_mixed_done_clear >> simp[] >> disch_tac >>
  rev_drule dft_mixed_done_clear >> simp[] >> disch_tac >>
  metis_tac[dft_mixed_done_clear]
QED

Theorem dft_mixed_cleared_observe:
  dft_suspend_cleared l r ==>
  ~dft_open_observe fn inst s l.dft_occ_core /\
  ~dft_open_observe fn inst s r.dft_occ_core
Proof
  simp[dft_suspend_cleared_def, dft_open_observe_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem dft_mixed_discharge_observe:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  dft_mixed_discharge bb0 pre gas call post v w l r /\
  dft_open_observe fn inst s r.dft_occ_core ==>
  inst_mem_ranges inst s = []
Proof
  simp[dft_mixed_discharge_def] >> rpt strip_tac >>
  drule_all dft_mixed_pending_suspend >> strip_tac >>
  `get_instruction bbR (SUC callerR.vs_inst_idx) = SOME gas` by
    (gvs[dft_mixed_frame_def] >>
     simp[dft_gas_edit_block_def, get_instruction_def, EL_APPEND_EQN]) >>
  gvs[dft_suspend_resumed_def, dft_open_observe_def] >>
  irule dft_edit_gas_ranges >> metis_tac[]
QED

Theorem dft_mixed_sync_macro:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\ ~MEM v call.inst_outputs /\
  (!nm ops. decode_invoke call = SOME (nm,ops) ==> ~MEM (Var v) ops) /\
  dft_mixed_sync bb0 pre gas call post v w l r /\
  dft_mixed_safe_sync bb0 pre l ==>
  ?a. (a = 1 \/ a = 2) /\
    dft_mixed_phase bb0 pre gas call post v w
      (FUNPOW (dft_occ_oracle_next w C) a l)
      (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r)
Proof
  strip_tac >>
  `?ctl stack n. l.dft_occ_core = DftOpen ctl stack n /\
    dft_fill_control 0 ctl = ctl` by metis_tac[dft_mixed_sync_def] >>
  Cases_on `ctl`
  >- suspend "enter"
  >- suspend "at" >>
  suspend "done"
QED

Resume dft_mixed_sync_macro[enter]:
  gvs[dft_fill_control_def] >> qexists_tac `1` >>
  simp[FUNPOW_2, dft_mixed_phase_def] >> disj1_tac >>
  irule dft_mixed_sync_enter >> simp[]
QED

Resume dft_mixed_sync_macro[at]:
  gvs[dft_fill_control_def] >>
  rename1 `l.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n` >>
  Cases_on `bb = bb0 /\ s.vs_inst_idx = LENGTH pre`
  >- (gvs[] >> qexists_tac `2` >>
      simp[FUNPOW_2, dft_mixed_phase_def] >>
      metis_tac[dft_mixed_crossing]) >>
  qexists_tac `1` >> simp[FUNPOW_2, dft_mixed_phase_def] >> disj1_tac >>
  irule dft_mixed_sync_at >> simp[] >>
  metis_tac[dft_mixed_safe_sync_def]
QED

Resume dft_mixed_sync_macro[done]:
  qexists_tac `1` >> simp[FUNPOW_2, dft_mixed_phase_def] >>
  metis_tac[dft_mixed_sync_done]
QED

Finalise dft_mixed_sync_macro

Theorem dft_mixed_phase_macro:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\ ~MEM v call.inst_outputs /\
  (!nm ops. decode_invoke call = SOME (nm,ops) ==> ~MEM (Var v) ops) /\
  dft_mixed_phase bb0 pre gas call post v w l r /\
  (dft_mixed_sync bb0 pre gas call post v w l r ==> dft_mixed_safe_sync bb0 pre l) ==>
  ?a b. ((a = 1 /\ b = 1) \/ (a = 2 /\ b = 1) \/ (a = 0 /\ b = 1)) /\
    dft_mixed_phase bb0 pre gas call post v w
      (FUNPOW (dft_occ_oracle_next w C) a l)
      (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C)) b r)
Proof
  strip_tac >>
  qpat_x_assum `dft_mixed_phase _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [dft_mixed_phase_def])
  >- (`dft_mixed_safe_sync bb0 pre l` by metis_tac[] >>
      drule_all dft_mixed_sync_macro >>
      disch_then (qspec_then `C` strip_assume_tac) >>
      qexistsl_tac [`a`,`1`] >> gvs[FUNPOW_2])
  >- (qexistsl_tac [`0`,`1`] >> simp[FUNPOW_2, dft_mixed_phase_def] >>
      disj1_tac >> irule dft_mixed_discharge_next >> simp[]) >>
  qexistsl_tac [`1`,`1`] >> simp[FUNPOW_2, dft_mixed_phase_def] >>
  disj2_tac >> disj2_tac >> irule dft_mixed_cleared_next >> simp[]
QED
