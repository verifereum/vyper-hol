Theory dftPendingObservation
Ancestors
  dftOrbitObservation dftPositionalPendingOrbit

Theorem dft_pending_observation_forward:
  (!i. i <= A i /\ i <= B i) /\
  (!i. dft_pos_pending_aligned_phase w C D fi bi pre gas call post
    (FST (Z i)) (SND (Z i))
    (FUNPOW (dft_occ_oracle_next w C) (A i) l)
    (FUNPOW (dft_occ_oracle_next w D) (B i) r)) /\
  (!j. ?n. B n <= j /\ j < B (SUC n)) /\
  (!n. pending_segment_account C D w
    (A (SUC n) - A n) (B (SUC n) - B n)
    (FUNPOW (dft_occ_oracle_next w C) (A n) l)
    (FUNPOW (dft_occ_oracle_next w D) (B n) r)
    (dft_pos_pending_gas_events (FST (Z n)) ++ SND (Z n))
    (dft_pos_pending_gas_events (FST (Z (SUC n))) ++ SND (Z (SUC n)))) ==>
  dft_orbit_observation w C D l r
Proof
  strip_tac >> rewrite_tac[dft_orbit_observation_def] >> conj_tac
  >- (rpt strip_tac >> drule_all dft_pending_orbit_terminal_forward >>
      metis_tac[dft_terminal_observation_refl]) >>
  rpt strip_tac >>
  drule_all (SRULE [] (Q.INST [`ledger` |-> `\n. dft_pos_pending_gas_events (FST (Z n)) ++ SND (Z n)`]
    dft_pending_orbit_observe_backward)) >> metis_tac[]
QED

Theorem dft_pending_observation_backward:
  (!i. i <= A i /\ i <= B i) /\
  (!i. dft_pos_pending_aligned_phase w C D fi bi pre gas call post
    (FST (Z i)) (SND (Z i))
    (FUNPOW (dft_occ_oracle_next w C) (A i) l)
    (FUNPOW (dft_occ_oracle_next w D) (B i) r)) /\
  (!j. ?n. A n <= j /\ j < A (SUC n)) /\
  (!n. pending_segment_account C D w
    (A (SUC n) - A n) (B (SUC n) - B n)
    (FUNPOW (dft_occ_oracle_next w C) (A n) l)
    (FUNPOW (dft_occ_oracle_next w D) (B n) r)
    (dft_pos_pending_gas_events (FST (Z n)) ++ SND (Z n))
    (dft_pos_pending_gas_events (FST (Z (SUC n))) ++ SND (Z (SUC n)))) ==>
  dft_orbit_observation w D C r l
Proof
  strip_tac >> rewrite_tac[dft_orbit_observation_def] >> conj_tac
  >- (rpt strip_tac >> drule_all dft_pending_orbit_terminal_backward >>
      metis_tac[dft_terminal_observation_refl]) >>
  rpt strip_tac >>
  drule_all (SRULE [] (Q.INST [`ledger` |-> `\n. dft_pos_pending_gas_events (FST (Z n)) ++ SND (Z n)`]
    dft_pending_orbit_observe_forward)) >> metis_tac[]
QED
