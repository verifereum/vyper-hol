Theory dftRootedMixedSupport
Ancestors
  dftRootedMixedCoverage dftRootedMixedOrbit dftRootedMixedSegment
  dftGasOrdinaryTrace dftOccurrenceOrdinaryStop dftOccurrenceMachine
  dftOpenMachine arithmetic

Theorem dft_mixed_abort_core_funpow[local]:
  c.dft_occ_core = DftOpen (DftDone (Abort a s)) [] n ==>
  (FUNPOW (dft_occ_oracle_next w C) p c).dft_occ_core =
    DftOpen (DftDone (Abort a s)) [] n
Proof
  strip_tac >> Induct_on `p` >- simp[FUNPOW] >>
  rewrite_tac[FUNPOW_SUC] >> metis_tac[dft_occ_abort_clear]
QED

Theorem dft_gas_ordinary_stopped_funpow:
  dft_gas_ordinary_stopped l r ==>
  dft_gas_ordinary_stopped (FUNPOW (dft_occ_oracle_next w C) p l)
    (FUNPOW (dft_occ_oracle_next w D) q r)
Proof
  rw[dft_gas_ordinary_stopped_def] >>
  qexistsl_tac [`a`, `s`, `t`, `n`, `m`] >>
  metis_tac[dft_mixed_abort_core_funpow]
QED

Theorem dft_mixed_cuts_mono[local]:
  (!n. (A:num->num) n < A (SUC n)) ==> !m n. m <= n ==> A m <= A n
Proof
  strip_tac >> gen_tac >> Induct
  >- simp[] >> strip_tac >> Cases_on `m = SUC n` >- simp[] >>
  `m <= n` by decide_tac >>
  first_x_assum drule >>
  qpat_x_assum `!n. A n < A (SUC n)` (qspec_then `n` mp_tac) >> decide_tac
QED

Theorem dft_mixed_exception_not_stopped[local]:
  dft_pos_mixed_exception C D w gas inst a b l r ==>
  ~dft_gas_ordinary_stopped l r
Proof
  rw[dft_pos_mixed_exception_def, dft_gas_ordinary_stopped_def] >> gvs[]
QED

Theorem dft_mixed_exception_later_stopped[local]:
  (!h. A h < A (SUC h) /\ B h < B (SUC h)) /\ n < m /\
  dft_pos_mixed_exception C D w gas inst
    (A (SUC n) - A n) (B (SUC n) - B n)
    (FUNPOW (dft_occ_oracle_next w C) (A n) c)
    (FUNPOW (dft_occ_oracle_next w D) (B n) d) ==>
  dft_gas_ordinary_stopped
    (FUNPOW (dft_occ_oracle_next w C) (A m) c)
    (FUNPOW (dft_occ_oracle_next w D) (B m) d)
Proof
  strip_tac >>
  `(!h. A h < A (SUC h)) /\ (!h. B h < B (SUC h))` by metis_tac[] >>
  `A (SUC n) <= A m /\ B (SUC n) <= B m` by
    (conj_tac >> irule dft_mixed_cuts_mono >> simp[] >> decide_tac) >>
  `dft_gas_ordinary_stopped
    (FUNPOW (dft_occ_oracle_next w C) (A (SUC n)) c)
    (FUNPOW (dft_occ_oracle_next w D) (B (SUC n)) d)` by
    (fs[dft_pos_mixed_exception_def, GSYM FUNPOW_ADD] >>
     gvs[SUB_ADD]) >>
  drule dft_gas_ordinary_stopped_funpow >>
  disch_then (qspec_then `w` (qspecl_then
    [`B m - B (SUC n)`, `A m - A (SUC n)`, `D`, `C`] mp_tac)) >>
  simp[GSYM FUNPOW_ADD, SUB_ADD]
QED

Theorem dft_pos_mixed_exception_index_unique:
  dft_pos_mixed_orbit_cuts C D w fi bi pre gas inst c d A B /\
  dft_pos_mixed_exception C D w gas inst
    (A (SUC n) - A n) (B (SUC n) - B n)
    (FUNPOW (dft_occ_oracle_next w C) (A n) c)
    (FUNPOW (dft_occ_oracle_next w D) (B n) d) /\
  dft_pos_mixed_exception C D w gas inst
    (A (SUC m) - A m) (B (SUC m) - B m)
    (FUNPOW (dft_occ_oracle_next w C) (A m) c)
    (FUNPOW (dft_occ_oracle_next w D) (B m) d) ==>
  n = m
Proof
  strip_tac >>
  `!h. A h < A (SUC h) /\ B h < B (SUC h)` by
    fs[dft_pos_mixed_orbit_cuts_def] >>
  Cases_on `n < m`
  >- (drule_all dft_mixed_exception_later_stopped >>
      metis_tac[dft_mixed_exception_not_stopped]) >>
  Cases_on `m < n`
  >- (drule_all dft_mixed_exception_later_stopped >>
      metis_tac[dft_mixed_exception_not_stopped]) >> decide_tac
QED

Theorem dft_pos_mixed_unmatched_support_unique:
  dft_pos_mixed_orbit_cuts C D w fi bi pre gas inst c d A B /\
  dft_occ_gas_event i addr (FUNPOW (dft_occ_oracle_next w C) j c) /\
  dft_occ_gas_event i' addr' (FUNPOW (dft_occ_oracle_next w C) j' c) /\
  ~(?k. dft_occ_gas_event i addr (FUNPOW (dft_occ_oracle_next w D) k d)) /\
  ~(?k. dft_occ_gas_event i' addr' (FUNPOW (dft_occ_oracle_next w D) k d)) ==>
  i = i' /\ addr = addr'
Proof
  strip_tac >>
  `?n. A n <= j /\ j < A (SUC n) /\
    dft_pos_mixed_exception C D w gas inst
      (A (SUC n) - A n) (B (SUC n) - B n)
      (FUNPOW (dft_occ_oracle_next w C) (A n) c)
      (FUNPOW (dft_occ_oracle_next w D) (B n) d) /\
    i = gas /\ addr = (FUNPOW (dft_occ_oracle_next w C) (A n) c).dft_occ_path ++
      [((FUNPOW (dft_occ_oracle_next w C) (A n) c).dft_occ_visit,gas.inst_id)]` by
    metis_tac[dft_pos_mixed_orbit_gas_forward] >>
  `?m. A m <= j' /\ j' < A (SUC m) /\
    dft_pos_mixed_exception C D w gas inst
      (A (SUC m) - A m) (B (SUC m) - B m)
      (FUNPOW (dft_occ_oracle_next w C) (A m) c)
      (FUNPOW (dft_occ_oracle_next w D) (B m) d) /\
    i' = gas /\ addr' = (FUNPOW (dft_occ_oracle_next w C) (A m) c).dft_occ_path ++
      [((FUNPOW (dft_occ_oracle_next w C) (A m) c).dft_occ_visit,gas.inst_id)]` by
    metis_tac[dft_pos_mixed_orbit_gas_forward] >>
  `n = m` by metis_tac[dft_pos_mixed_exception_index_unique] >>
  gvs[]
QED
