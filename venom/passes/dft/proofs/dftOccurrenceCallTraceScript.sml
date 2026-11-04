Theory dftOccurrenceCallTrace
Ancestors
  dftOccurrenceCallPosition dftOccurrenceCallClosure dftOccurrenceCallCrossing
  dftOccurrenceCallStack dftOccurrenceSuspended dftOccurrenceGasEdit
  dftOccurrenceMachine dftOccurrenceReplay dftOpenMachine dftOpenErase arithmetic list

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

Theorem dft_mixed_sync_positive:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\ ~MEM v call.inst_outputs /\
  (!nm ops. decode_invoke call = SOME (nm,ops) ==> ~MEM (Var v) ops) /\
  dft_mixed_sync bb0 pre gas call post v w l r /\ dft_mixed_safe_sync bb0 pre l ==>
  ?a. 1 <= a /\ a <= 2 /\ dft_mixed_good bb0 pre gas call post v w
    (FUNPOW (dft_occ_oracle_next w C) a l)
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r)
Proof
  strip_tac >>
  `?ctl stack n. l.dft_occ_core = DftOpen ctl stack n /\
    dft_fill_control 0 ctl = ctl` by metis_tac[dft_mixed_sync_def] >>
  Cases_on `ctl`
  >- (gvs[dft_fill_control_def] >> qexists_tac `1` >>
      simp[dft_mixed_good_def] >> disj1_tac >>
      irule dft_mixed_sync_enter_safe >> simp[])
  >- suspend "at" >>
  qexists_tac `1` >> simp[dft_mixed_good_def] >>
  metis_tac[dft_mixed_sync_done_safe]
QED

Resume dft_mixed_sync_positive[at]:
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

Finalise dft_mixed_sync_positive

Theorem dft_mixed_good_two_progress:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\ ~MEM v call.inst_outputs /\
  (!nm ops. decode_invoke call = SOME (nm,ops) ==> ~MEM (Var v) ops) /\
  dft_mixed_good bb0 pre gas call post v w l r ==>
  ?a. 1 <= a /\ a <= 4 /\ dft_mixed_good bb0 pre gas call post v w
    (FUNPOW (dft_occ_oracle_next w C) a l)
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C)) 2 r)
Proof
  strip_tac >> Cases_on `dft_mixed_discharge bb0 pre gas call post v w l r`
  >- (drule_all dft_mixed_discharge_next_safe >>
      disch_then (qspec_then `C` strip_assume_tac) >>
      drule_all dft_mixed_sync_positive >>
      disch_then (qspec_then `C` strip_assume_tac) >>
      qexists_tac `a` >> simp[FUNPOW_2] >> decide_tac) >>
  `?a. 1 <= a /\ a <= 2 /\ dft_mixed_good bb0 pre gas call post v w
    (FUNPOW (dft_occ_oracle_next w C) a l)
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C) r)` by
    (gvs[dft_mixed_good_def]
     >- (drule_all dft_mixed_sync_positive >>
         disch_then (qspec_then `C` strip_assume_tac) >>
         qexists_tac `a` >> gvs[dft_mixed_good_def]) >>
     qexists_tac `1` >> simp[dft_mixed_good_def] >>
     disj2_tac >> disj2_tac >> irule dft_mixed_cleared_next >> simp[]) >>
  drule_all dft_mixed_good_next >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  qexists_tac `a' + a` >> simp[FUNPOW_ADD, FUNPOW_2] >> decide_tac
QED

Theorem dft_mixed_good_cofinal:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\ ~MEM v call.inst_outputs /\
  (!nm ops. decode_invoke call = SOME (nm,ops) ==> ~MEM (Var v) ops) ==>
  !j l r. dft_mixed_good bb0 pre gas call post v w l r ==>
  ?m. j <= m /\ m <= 4 * j /\ dft_mixed_good bb0 pre gas call post v w
    (FUNPOW (dft_occ_oracle_next w C) m l)
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C)) (2*j) r)
Proof
  strip_tac >> Induct_on `j`
  >- (rpt strip_tac >> qexists_tac `0` >> simp[]) >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  drule_all dft_mixed_good_two_progress >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  qexists_tac `a + m` >>
  `2 * SUC j = 2 + 2*j` by decide_tac >>
  simp[FUNPOW_ADD] >> metis_tac[FUNPOW_COMM]
QED

Theorem dft_mixed_good_root:
  dft_mixed_good bb0 pre gas call post v w l r ==>
  ((?n. l.dft_occ_core = DftOpen (DftDone result) [] n) <=>
   (?n. r.dft_occ_core = DftOpen (DftDone result) [] n))
Proof
  simp[dft_mixed_good_def] >> strip_tac
  >- (gvs[dft_mixed_sync_def] >>
      drule dft_mixed_stack_lengths >> strip_tac >>
      Cases_on `ctl` >> gvs[dft_edit_control_def] >>
      Cases_on `tL` >> Cases_on `tR` >> gvs[])
  >- gvs[dft_mixed_discharge_def, dft_suspend_resumed_def] >>
  gvs[dft_suspend_cleared_def]
QED

Theorem dft_occ_oracle_root_absorb:
  (?n. x.dft_occ_core = DftOpen (DftDone result) [] n) ==>
  !k. ?n. (FUNPOW (dft_occ_oracle_next w C) k x).dft_occ_core =
    DftOpen (DftDone result) [] n
Proof
  strip_tac >> Induct_on `k` >> simp[FUNPOW_SUC] >>
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
      dft_erase_def, dft_fill_def, dft_fill_control_def, dft_open_next_def,
      dft_open_return_def] >>
  Cases_on `result` >> simp[dft_fill_def, dft_fill_control_def]
QED

Theorem dft_mixed_source_terminal:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\ ~MEM v call.inst_outputs /\
  (!nm ops. decode_invoke call = SOME (nm,ops) ==> ~MEM (Var v) ops) /\
  dft_mixed_good bb0 pre gas call post v w l r /\
  (FUNPOW (dft_occ_oracle_next w C) j l).dft_occ_core =
    DftOpen (DftDone result) [] nL ==>
  ?k nR. (FUNPOW (dft_occ_oracle_next w
    (dft_gas_edit_ctx bb0 pre gas call post C)) k r).dft_occ_core =
    DftOpen (DftDone result) [] nR
Proof
  strip_tac >> drule_all dft_mixed_good_cofinal >>
  disch_then (qspecl_then [`C`, `j`] mp_tac) >>
  simp[] >> strip_tac >>
  `?d. m = d + j` by (qexists_tac `m-j` >> decide_tac) >>
  `?n. (FUNPOW (dft_occ_oracle_next w C) m l).dft_occ_core =
     DftOpen (DftDone result) [] n` by
    (gvs[FUNPOW_ADD] >> irule dft_occ_oracle_root_absorb >> metis_tac[]) >>
  drule dft_mixed_good_root >> disch_then (qspec_then `result` mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem dft_mixed_target_terminal:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\ ~MEM v call.inst_outputs /\
  (!nm ops. decode_invoke call = SOME (nm,ops) ==> ~MEM (Var v) ops) /\
  dft_mixed_good bb0 pre gas call post v w l r /\
  (FUNPOW (dft_occ_oracle_next w
    (dft_gas_edit_ctx bb0 pre gas call post C)) j r).dft_occ_core =
    DftOpen (DftDone result) [] nR ==>
  ?k nL. (FUNPOW (dft_occ_oracle_next w C) k l).dft_occ_core =
    DftOpen (DftDone result) [] nL
Proof
  strip_tac >> drule_all dft_mixed_good_prefix >>
  disch_then (qspecl_then [`C`, `j`] mp_tac) >>
  simp[] >> strip_tac >>
  drule dft_mixed_good_root >> disch_then (qspec_then `result` mp_tac) >>
  simp[] >> metis_tac[]
QED
