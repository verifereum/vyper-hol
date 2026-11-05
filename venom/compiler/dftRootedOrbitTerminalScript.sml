Theory dftRootedOrbitTerminal
Ancestors
  dftRootedGasOrbit dftRootedMixedOrbit dftPositionalGasSegment
  dftPositionalPhase dftGasOrdinaryTrace dftOccurrenceMachine
  dftOpenMachine dftOccurrenceReplay dftOpenErase venomExecSemantics arithmetic

(* Cleared terminal cores absorb steps, independently of occurrence metadata. *)
Theorem dft_root_terminal_next[local]:
  c.dft_occ_core = DftOpen (DftDone rr) [] n ==>
  (dft_occ_oracle_next w C c).dft_occ_core = DftOpen (DftDone rr) [] n
Proof
  Cases_on `rr` >>
  simp[dft_occ_oracle_next_def, dft_next_inf_def, dft_fill_def,
    dft_fill_control_def, dft_open_next_def, dft_open_return_def, dft_erase_def]
QED

Theorem dft_root_terminal_iter[local]:
  !k c. c.dft_occ_core = DftOpen (DftDone rr) [] n ==>
  (FUNPOW (dft_occ_oracle_next w C) k c).dft_occ_core =
    DftOpen (DftDone rr) [] n
Proof
  Induct_on `k` >> simp[FUNPOW_SUC] >>
  metis_tac[dft_root_terminal_next]
QED

Theorem dft_root_terminal_later:
  (FUNPOW (dft_occ_oracle_next w C) j c).dft_occ_core =
    DftOpen (DftDone rr) [] n /\ j <= k ==>
  (FUNPOW (dft_occ_oracle_next w C) k c).dft_occ_core =
    DftOpen (DftDone rr) [] n
Proof
  strip_tac >> `k = (k-j) + j` by decide_tac >>
  metis_tac[FUNPOW_ADD, dft_root_terminal_iter]
QED

Theorem dft_root_gas_phase_terminal_backward[local]:
  dft_pos_gas_phase C D fi bi pre l r /\
  r.dft_occ_core = DftOpen (DftDone rr) [] n ==>
  l.dft_occ_core = DftOpen (DftDone rr) [] n
Proof
  simp[dft_pos_gas_phase_def, dft_pos_control_def] >> rpt strip_tac >> gvs[]
QED

Theorem dft_root_gas_orbit_terminal_forward:
  dftRootedGasOrbit$dft_pos_gas_orbit_cuts C D w fi bi pre c d A B /\
  (FUNPOW (dft_occ_oracle_next w C) j c).dft_occ_core =
    DftOpen (DftDone rr) [] n ==>
  ?k. (FUNPOW (dft_occ_oracle_next w D) k d).dft_occ_core =
    DftOpen (DftDone rr) [] n
Proof
  rewrite_tac[dftRootedGasOrbitTheory.dft_pos_gas_orbit_cuts_def] >> strip_tac >>
  `j <= A j` by metis_tac[] >>
  `(FUNPOW (dft_occ_oracle_next w C) (A j) c).dft_occ_core =
    DftOpen (DftDone rr) [] n` by metis_tac[dft_root_terminal_later] >>
  qexists_tac `B j` >> metis_tac[dft_pos_gas_phase_terminal]
QED

Theorem dft_root_gas_orbit_terminal_backward:
  dftRootedGasOrbit$dft_pos_gas_orbit_cuts C D w fi bi pre c d A B /\
  (FUNPOW (dft_occ_oracle_next w D) k d).dft_occ_core =
    DftOpen (DftDone rr) [] n ==>
  ?j. (FUNPOW (dft_occ_oracle_next w C) j c).dft_occ_core =
    DftOpen (DftDone rr) [] n
Proof
  rewrite_tac[dftRootedGasOrbitTheory.dft_pos_gas_orbit_cuts_def] >> strip_tac >>
  `k <= B k` by metis_tac[] >>
  `(FUNPOW (dft_occ_oracle_next w D) (B k) d).dft_occ_core =
    DftOpen (DftDone rr) [] n` by metis_tac[dft_root_terminal_later] >>
  qexists_tac `A k` >> metis_tac[dft_root_gas_phase_terminal_backward]
QED

Theorem dft_root_mixed_terminal_forward[local]:
  (dft_pos_gas_phase C D fi bi pre l r \/ dft_gas_ordinary_stopped l r) /\
  l.dft_occ_core = DftOpen (DftDone rr) [] n ==>
  ?rr' m. r.dft_occ_core = DftOpen (DftDone rr') [] m /\
    ((rr' = rr /\ m = n) \/ (?a s t. rr = Abort a s /\ rr' = Abort a t))
Proof
  strip_tac
  >- metis_tac[dft_pos_gas_phase_terminal] >>
  gvs[dft_gas_ordinary_stopped_def] >> metis_tac[]
QED

Theorem dft_root_mixed_terminal_backward[local]:
  (dft_pos_gas_phase C D fi bi pre l r \/ dft_gas_ordinary_stopped l r) /\
  r.dft_occ_core = DftOpen (DftDone rr) [] n ==>
  ?rr' m. l.dft_occ_core = DftOpen (DftDone rr') [] m /\
    ((rr' = rr /\ m = n) \/ (?a s t. rr = Abort a s /\ rr' = Abort a t))
Proof
  strip_tac
  >- metis_tac[dft_root_gas_phase_terminal_backward] >>
  gvs[dft_gas_ordinary_stopped_def] >> metis_tac[]
QED

Theorem dft_root_mixed_orbit_terminal_forward:
  dft_pos_mixed_orbit_cuts C D w fi bi pre gas inst c d A B /\
  (FUNPOW (dft_occ_oracle_next w C) j c).dft_occ_core =
    DftOpen (DftDone rr) [] n ==>
  ?k rr' m. (FUNPOW (dft_occ_oracle_next w D) k d).dft_occ_core =
    DftOpen (DftDone rr') [] m /\
    ((rr' = rr /\ m = n) \/ (?a s t. rr = Abort a s /\ rr' = Abort a t))
Proof
  rewrite_tac[dft_pos_mixed_orbit_cuts_def] >> strip_tac >>
  `j <= A j` by metis_tac[] >>
  `(FUNPOW (dft_occ_oracle_next w C) (A j) c).dft_occ_core =
    DftOpen (DftDone rr) [] n` by metis_tac[dft_root_terminal_later] >>
  qexists_tac `B j` >> irule dft_root_mixed_terminal_forward >>
  metis_tac[]
QED

Theorem dft_root_mixed_orbit_terminal_backward:
  dft_pos_mixed_orbit_cuts C D w fi bi pre gas inst c d A B /\
  (FUNPOW (dft_occ_oracle_next w D) k d).dft_occ_core =
    DftOpen (DftDone rr) [] n ==>
  ?j rr' m. (FUNPOW (dft_occ_oracle_next w C) j c).dft_occ_core =
    DftOpen (DftDone rr') [] m /\
    ((rr' = rr /\ m = n) \/ (?a s t. rr = Abort a s /\ rr' = Abort a t))
Proof
  rewrite_tac[dft_pos_mixed_orbit_cuts_def] >> strip_tac >>
  `k <= B k` by metis_tac[] >>
  `(FUNPOW (dft_occ_oracle_next w D) (B k) d).dft_occ_core =
    DftOpen (DftDone rr) [] n` by metis_tac[dft_root_terminal_later] >>
  qexists_tac `A k` >> irule dft_root_mixed_terminal_backward >>
  metis_tac[]
QED

Theorem dft_root_mixed_orbit_halt_forward:
  dft_pos_mixed_orbit_cuts C D w fi bi pre gas inst c d A B /\
  (FUNPOW (dft_occ_oracle_next w C) j c).dft_occ_core =
    DftOpen (DftDone (Halt s)) [] n ==>
  ?k. (FUNPOW (dft_occ_oracle_next w D) k d).dft_occ_core =
    DftOpen (DftDone (Halt s)) [] n
Proof
  strip_tac >> drule_all dft_root_mixed_orbit_terminal_forward >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem dft_root_mixed_orbit_halt_backward:
  dft_pos_mixed_orbit_cuts C D w fi bi pre gas inst c d A B /\
  (FUNPOW (dft_occ_oracle_next w D) k d).dft_occ_core =
    DftOpen (DftDone (Halt s)) [] n ==>
  ?j. (FUNPOW (dft_occ_oracle_next w C) j c).dft_occ_core =
    DftOpen (DftDone (Halt s)) [] n
Proof
  strip_tac >> drule_all dft_root_mixed_orbit_terminal_backward >>
  strip_tac >> gvs[] >> metis_tac[]
QED
