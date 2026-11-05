Theory dftOrdinaryObservation
Ancestors
  dftOrbitObservation dftRootedOrbitTerminal dftPositionalRootedOrbit dftPositionalLifecycle
  dftPositionalPhase list

Theorem dft_pos_phase_done_forward[local]:
  dft_pos_phase C D fi bi pre x call post c d /\
  c.dft_occ_core = DftOpen (DftDone rr) [] n ==>
  ?m. d.dft_occ_core = DftOpen (DftDone rr) [] m
Proof
  simp[dft_pos_phase_def] >> rpt strip_tac >>
  gvs[dft_pos_control_def] >>
  Cases_on `certs` >> gvs[dft_pos_stack_def]
QED

Theorem dft_ordinary_orbit_terminal_forward:
  dft_pos_rooted_orbit_cuts w C D fi bi pre x call post c d A B /\
  (FUNPOW (dft_occ_oracle_next w C) j c).dft_occ_core =
    DftOpen (DftDone rr) [] n ==>
  ?k m. (FUNPOW (dft_occ_oracle_next w D) k d).dft_occ_core =
    DftOpen (DftDone rr) [] m
Proof
  rewrite_tac[dft_pos_rooted_orbit_cuts_def] >> strip_tac >>
  `j <= A j` by metis_tac[] >>
  `(FUNPOW (dft_occ_oracle_next w C) (A j) c).dft_occ_core =
    DftOpen (DftDone rr) [] n` by metis_tac[dft_root_terminal_later] >>
  qpat_x_assum `!n. dft_pos_rooted_phase _ _ _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `j` mp_tac) >>
  simp[dft_pos_rooted_phase_def] >> strip_tac >>
  drule_all dft_pos_phase_done_forward >> metis_tac[]
QED

Theorem dft_ordinary_orbit_observation_forward:
  dft_pos_rooted_orbit_cuts w C D fi bi pre x call post c d A B ==>
  dft_orbit_observation w C D c d
Proof
  strip_tac >> rewrite_tac[dft_orbit_observation_def] >> conj_tac
  >- (rpt strip_tac >> drule_all dft_ordinary_orbit_terminal_forward >>
      metis_tac[dft_terminal_observation_refl]) >>
  rpt strip_tac >> drule_all dft_pos_rooted_orbit_observe_backward >> metis_tac[]
QED

Theorem dft_pos_phase_done_backward[local]:
  dft_pos_phase C D fi bi pre x call post c d /\
  d.dft_occ_core = DftOpen (DftDone rr) [] n ==>
  ?m. c.dft_occ_core = DftOpen (DftDone rr) [] m
Proof
  simp[dft_pos_phase_def] >> rpt strip_tac >>
  gvs[dft_pos_control_def] >>
  Cases_on `certs` >> gvs[dft_pos_stack_def]
QED

Theorem dft_ordinary_orbit_terminal_backward:
  dft_pos_rooted_orbit_cuts w C D fi bi pre x call post c d A B /\
  (FUNPOW (dft_occ_oracle_next w D) k d).dft_occ_core =
    DftOpen (DftDone rr) [] n ==>
  ?j m. (FUNPOW (dft_occ_oracle_next w C) j c).dft_occ_core =
    DftOpen (DftDone rr) [] m
Proof
  rewrite_tac[dft_pos_rooted_orbit_cuts_def] >> strip_tac >>
  `k <= B k` by metis_tac[] >>
  `(FUNPOW (dft_occ_oracle_next w D) (B k) d).dft_occ_core =
    DftOpen (DftDone rr) [] n` by metis_tac[dft_root_terminal_later] >>
  qpat_x_assum `!n. dft_pos_rooted_phase _ _ _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `k` mp_tac) >>
  simp[dft_pos_rooted_phase_def] >> strip_tac >>
  drule_all dft_pos_phase_done_backward >> metis_tac[]
QED

Theorem dft_ordinary_orbit_observation_backward:
  dft_pos_rooted_orbit_cuts w C D fi bi pre x call post c d A B ==>
  dft_orbit_observation w D C d c
Proof
  strip_tac >> rewrite_tac[dft_orbit_observation_def] >> conj_tac
  >- (rpt strip_tac >> drule_all dft_ordinary_orbit_terminal_backward >>
      metis_tac[dft_terminal_observation_refl]) >>
  rpt strip_tac >> drule_all dft_pos_rooted_orbit_observe_forward >> metis_tac[]
QED
