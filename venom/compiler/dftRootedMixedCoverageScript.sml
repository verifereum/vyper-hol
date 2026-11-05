Theory dftRootedMixedCoverage
Ancestors
  dftRootedMixedOrbit dftRootedMixedSegment dftPositionalSegment
  dftCofinalSegments dftOccurrenceMachine arithmetic

Theorem dft_mixed_segment_observe_forward[local]:
  (dft_pos_segment_account C D w a b l r \/
   dft_pos_mixed_exception C D w gas inst a b l r) /\
  j < a /\ dft_open_observe f i s
    (FUNPOW (dft_occ_oracle_next w C) j l).dft_occ_core /\
  inst_mem_ranges i s <> [] ==>
  ?k g t. k < b /\ dft_pos_functions C D f g /\
    dft_open_observe g i t
      (FUNPOW (dft_occ_oracle_next w D) k r).dft_occ_core /\
    t.vs_memory = s.vs_memory /\ inst_mem_ranges i t = inst_mem_ranges i s
Proof
  rw[dft_pos_segment_account_def, dft_pos_mixed_exception_def] >> metis_tac[]
QED

Theorem dft_mixed_segment_observe_backward[local]:
  (dft_pos_segment_account C D w a b l r \/
   dft_pos_mixed_exception C D w gas inst a b l r) /\
  k < b /\ dft_open_observe g i t
    (FUNPOW (dft_occ_oracle_next w D) k r).dft_occ_core /\
  inst_mem_ranges i t <> [] ==>
  ?j f s. j < a /\ dft_pos_functions C D f g /\
    dft_open_observe f i s
      (FUNPOW (dft_occ_oracle_next w C) j l).dft_occ_core /\
    t.vs_memory = s.vs_memory /\ inst_mem_ranges i t = inst_mem_ranges i s
Proof
  rw[dft_pos_segment_account_def, dft_pos_mixed_exception_def] >> metis_tac[]
QED

Theorem dft_pos_mixed_orbit_observe_forward:
  dft_pos_mixed_orbit_cuts C D w fi bi pre gas inst c d A B /\
  dft_open_observe f i s (FUNPOW (dft_occ_oracle_next w C) j c).dft_occ_core /\
  inst_mem_ranges i s <> [] ==>
  ?k g t. dft_pos_functions C D f g /\
    dft_open_observe g i t (FUNPOW (dft_occ_oracle_next w D) k d).dft_occ_core /\
    t.vs_memory = s.vs_memory /\ inst_mem_ranges i t = inst_mem_ranges i s
Proof
  rewrite_tac[dft_pos_mixed_orbit_cuts_def, LET_THM] >> BETA_TAC >> strip_tac >>
  qpat_x_assum `!j. ?n. A n <= j /\ j < A (SUC n)`
    (qspec_then `j` strip_assume_tac) >>
  `j - A n < A (SUC n) - A n` by decide_tac >>
  `dft_open_observe f i s
    (FUNPOW (dft_occ_oracle_next w C) (j - A n)
      (FUNPOW (dft_occ_oracle_next w C) (A n) c)).dft_occ_core` by
    metis_tac[dft_cut_offset] >>
  qpat_x_assum `!n. 0 < _ /\ _` (qspec_then `n` (fn th => map_every assume_tac (CONJUNCTS th))) >>
  drule_all dft_mixed_segment_observe_forward >> strip_tac >>
  qexistsl_tac [`k + B n`, `g`, `t`] >> simp[FUNPOW_ADD]
QED

Theorem dft_pos_mixed_orbit_observe_backward:
  dft_pos_mixed_orbit_cuts C D w fi bi pre gas inst c d A B /\
  dft_open_observe g i t (FUNPOW (dft_occ_oracle_next w D) k d).dft_occ_core /\
  inst_mem_ranges i t <> [] ==>
  ?j f s. dft_pos_functions C D f g /\
    dft_open_observe f i s (FUNPOW (dft_occ_oracle_next w C) j c).dft_occ_core /\
    t.vs_memory = s.vs_memory /\ inst_mem_ranges i t = inst_mem_ranges i s
Proof
  rewrite_tac[dft_pos_mixed_orbit_cuts_def, LET_THM] >> BETA_TAC >> strip_tac >>
  qpat_x_assum `!j. ?n. B n <= j /\ j < B (SUC n)`
    (qspec_then `k` strip_assume_tac) >>
  `k - B n < B (SUC n) - B n` by decide_tac >>
  `dft_open_observe g i t
    (FUNPOW (dft_occ_oracle_next w D) (k - B n)
      (FUNPOW (dft_occ_oracle_next w D) (B n) d)).dft_occ_core` by
    metis_tac[dft_cut_offset] >>
  qpat_x_assum `!n. 0 < _ /\ _` (qspec_then `n` (fn th => map_every assume_tac (CONJUNCTS th))) >>
  drule_all dft_mixed_segment_observe_backward >> strip_tac >>
  qexistsl_tac [`j + A n`, `f`, `s`] >> simp[FUNPOW_ADD]
QED

Theorem dft_mixed_segment_gas_backward[local]:
  (dft_pos_segment_account C D w a b l r \/
   dft_pos_mixed_exception C D w gas inst a b l r) /\
  k < b /\ dft_occ_gas_event i addr (FUNPOW (dft_occ_oracle_next w D) k r) ==>
  ?j. j < a /\ dft_occ_gas_event i addr (FUNPOW (dft_occ_oracle_next w C) j l)
Proof
  rw[dft_pos_segment_account_def, dft_pos_mixed_exception_def] >> metis_tac[]
QED

Theorem dft_pos_mixed_orbit_gas_backward:
  dft_pos_mixed_orbit_cuts C D w fi bi pre gas inst c d A B /\
  dft_occ_gas_event i addr (FUNPOW (dft_occ_oracle_next w D) k d) ==>
  ?j. dft_occ_gas_event i addr (FUNPOW (dft_occ_oracle_next w C) j c)
Proof
  rewrite_tac[dft_pos_mixed_orbit_cuts_def, LET_THM] >> BETA_TAC >> strip_tac >>
  qpat_x_assum `!j. ?n. B n <= j /\ j < B (SUC n)`
    (qspec_then `k` strip_assume_tac) >>
  `k - B n < B (SUC n) - B n` by decide_tac >>
  `dft_occ_gas_event i addr
    (FUNPOW (dft_occ_oracle_next w D) (k - B n)
      (FUNPOW (dft_occ_oracle_next w D) (B n) d))` by
    metis_tac[dft_cut_offset] >>
  qpat_x_assum `!n. 0 < _ /\ _`
    (qspec_then `n` (fn th => map_every assume_tac (CONJUNCTS th))) >>
  drule_all dft_mixed_segment_gas_backward >> strip_tac >>
  qexists_tac `j + A n` >> simp[FUNPOW_ADD]
QED

Theorem dft_pos_mixed_orbit_gas_forward:
  dft_pos_mixed_orbit_cuts C D w fi bi pre gas inst c d A B /\
  dft_occ_gas_event i addr (FUNPOW (dft_occ_oracle_next w C) j c) ==>
  (?k. dft_occ_gas_event i addr (FUNPOW (dft_occ_oracle_next w D) k d)) \/
  (?n. A n <= j /\ j < A (SUC n) /\
    dft_pos_mixed_exception C D w gas inst
      (A (SUC n) - A n) (B (SUC n) - B n)
      (FUNPOW (dft_occ_oracle_next w C) (A n) c)
      (FUNPOW (dft_occ_oracle_next w D) (B n) d) /\
    i = gas /\ addr = (FUNPOW (dft_occ_oracle_next w C) (A n) c).dft_occ_path ++
      [((FUNPOW (dft_occ_oracle_next w C) (A n) c).dft_occ_visit,gas.inst_id)])
Proof
  rewrite_tac[dft_pos_mixed_orbit_cuts_def, LET_THM] >> BETA_TAC >> strip_tac >>
  qpat_x_assum `!j. ?n. A n <= j /\ j < A (SUC n)`
    (qspec_then `j` strip_assume_tac) >>
  `j - A n < A (SUC n) - A n` by decide_tac >>
  `dft_occ_gas_event i addr
    (FUNPOW (dft_occ_oracle_next w C) (j - A n)
      (FUNPOW (dft_occ_oracle_next w C) (A n) c))` by
    metis_tac[dft_cut_offset] >>
  qpat_x_assum `!n. 0 < _ /\ _` (qspec_then `n` strip_assume_tac)
  >- (disj1_tac >>
      qpat_x_assum `dft_pos_segment_account _ _ _ _ _ _ _` mp_tac >>
      rewrite_tac[dft_pos_segment_account_def] >> strip_tac >>
      `?k. k < B (SUC n) - B n /\ dft_occ_gas_event i addr
        (FUNPOW (dft_occ_oracle_next w D) k
          (FUNPOW (dft_occ_oracle_next w D) (B n) d))` by metis_tac[] >>
      qexists_tac `k + B n` >> simp[FUNPOW_ADD]) >>
  disj2_tac >> qexists_tac `n` >> simp[] >>
  qpat_x_assum `dft_pos_mixed_exception _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[dft_pos_mixed_exception_def] >> strip_tac >> metis_tac[]
QED
