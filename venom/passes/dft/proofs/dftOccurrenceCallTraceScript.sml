Theory dftOccurrenceCallTrace
Ancestors
  dftOccurrenceCallPosition dftOccurrenceCallClosure dftOccurrenceCallCrossing
  dftOccurrenceCallStack dftOccurrenceSuspended dftOccurrenceGasEdit
  dftOccurrenceMachine dftOpenMachine dftOpenErase arithmetic list

Definition dft_mixed_good_def:
  dft_mixed_good bb0 pre gas call post v w l r <=>
    (dft_mixed_sync bb0 pre gas call post v w l r /\
     dft_mixed_safe_sync bb0 pre l) \/
    dft_mixed_discharge bb0 pre gas call post v w l r \/
    dft_suspend_cleared l r
End

Theorem dft_mixed_good_phase:
  dft_mixed_good bb0 pre gas call post v w l r ==>
  dft_mixed_phase bb0 pre gas call post v w l r
Proof
  simp[dft_mixed_good_def, dft_mixed_phase_def] >> metis_tac[]
QED

Theorem dft_mixed_good_init:
  dft_mixed_good bb0 pre gas call post v w
    (dft_occ_init (DftOpen (DftEnter fn 0 s) [] nL))
    (dft_occ_init (DftOpen
      (DftEnter (dft_gas_edit_fn bb0 pre gas call post fn) 0 s) [] nR))
Proof
  simp[dft_mixed_good_def] >> disj1_tac >>
  simp[dft_mixed_init, dft_mixed_safe_sync_def, dft_occ_init_def]
QED

Theorem dft_mixed_good_next:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\ ~MEM v call.inst_outputs /\
  (!nm ops. decode_invoke call = SOME (nm,ops) ==> ~MEM (Var v) ops) /\
  dft_mixed_good bb0 pre gas call post v w l r ==>
  ?a. a <= 2 /\ dft_mixed_good bb0 pre gas call post v w
    (FUNPOW (dft_occ_oracle_next w C) a l)
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r)
Proof
  strip_tac >>
  qpat_x_assum `dft_mixed_good _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [dft_mixed_good_def])
  >- suspend "sync"
  >- (qexists_tac `0` >> simp[dft_mixed_good_def] >> disj1_tac >>
      irule dft_mixed_discharge_next_safe >> simp[]) >>
  qexists_tac `1` >> simp[dft_mixed_good_def] >>
  disj2_tac >> disj2_tac >> irule dft_mixed_cleared_next >> simp[]
QED

Resume dft_mixed_good_next[sync]:
  `?ctl stack n. l.dft_occ_core = DftOpen ctl stack n /\
    dft_fill_control 0 ctl = ctl` by metis_tac[dft_mixed_sync_def] >>
  Cases_on `ctl`
  >- suspend "enter"
  >- suspend "at" >>
  qexists_tac `1` >> simp[dft_mixed_good_def] >>
  metis_tac[dft_mixed_sync_done_safe]
QED

Resume dft_mixed_good_next[enter]:
  gvs[dft_fill_control_def] >> qexists_tac `1` >>
  simp[dft_mixed_good_def] >> disj1_tac >>
  irule dft_mixed_sync_enter_safe >> simp[]
QED

Resume dft_mixed_good_next[at]:
  gvs[dft_fill_control_def] >>
  rename1 `l.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n` >>
  Cases_on `bb = bb0 /\ s.vs_inst_idx = LENGTH pre`
  >- (gvs[] >> qexists_tac `2` >> simp[FUNPOW_2, dft_mixed_good_def] >>
      `dft_mixed_safe_sync bb pre
        (dft_occ_oracle_next w C (dft_occ_oracle_next w C l))` by
        metis_tac[dft_mixed_crossing_position] >>
      metis_tac[dft_mixed_crossing]) >>
  qexists_tac `1` >> simp[dft_mixed_good_def] >> disj1_tac >>
  irule dft_mixed_sync_at_safe >> simp[] >>
  metis_tac[dft_mixed_safe_sync_def]
QED

Finalise dft_mixed_good_next

Theorem dft_mixed_good_prefix:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\ ~MEM v call.inst_outputs /\
  (!nm ops. decode_invoke call = SOME (nm,ops) ==> ~MEM (Var v) ops) ==>
  !n l r. dft_mixed_good bb0 pre gas call post v w l r ==>
  ?m. m <= 2 * n /\ dft_mixed_good bb0 pre gas call post v w
    (FUNPOW (dft_occ_oracle_next w C) m l)
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C)) n r)
Proof
  strip_tac >> Induct_on `n`
  >- (rpt strip_tac >> qexists_tac `0` >> simp[]) >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  drule_all dft_mixed_good_next >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  qexists_tac `a + m` >>
  simp[FUNPOW_ADD, FUNPOW_SUC] >> decide_tac
QED

Theorem dft_mixed_phase_prefix:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\ ~MEM v call.inst_outputs /\
  (!nm ops. decode_invoke call = SOME (nm,ops) ==> ~MEM (Var v) ops) /\
  dft_mixed_good bb0 pre gas call post v w l r ==>
  !n. ?m. m <= 2 * n /\ dft_mixed_phase bb0 pre gas call post v w
    (FUNPOW (dft_occ_oracle_next w C) m l)
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C)) n r)
Proof
  metis_tac[dft_mixed_good_prefix, dft_mixed_good_phase]
QED
