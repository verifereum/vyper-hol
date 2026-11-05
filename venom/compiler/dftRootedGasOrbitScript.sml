Theory dftRootedGasOrbit
Ancestors
  dftPositionalGasSegment dftPositionalSegment dftCofinalSegments
  dftOccurrenceMachine dftOpenMachine arithmetic

Definition dft_pos_gas_orbit_cuts_def:
  dft_pos_gas_orbit_cuts C D w fi bi pre c d A B <=>
    A 0 = 0 /\ B 0 = 0 /\
    (!n. A n < A (SUC n) /\ B n < B (SUC n)) /\
    (!n. n <= A n /\ n <= B n) /\
    (!j. ?n. A n <= j /\ j < A (SUC n)) /\
    (!j. ?n. B n <= j /\ j < B (SUC n)) /\
    (!n. dft_pos_gas_phase C D fi bi pre
      (FUNPOW (dft_occ_oracle_next w C) (A n) c)
      (FUNPOW (dft_occ_oracle_next w D) (B n) d)) /\
    (!n. dft_pos_segment_account C D w
      (A (SUC n) - A n) (B (SUC n) - B n)
      (FUNPOW (dft_occ_oracle_next w C) (A n) c)
      (FUNPOW (dft_occ_oracle_next w D) (B n) d))
End

Theorem dft_pos_gas_orbit_segments:
  D = dft_pos_edit_ctx fi bi pre x y post C /\
  dft_pos_runtime_ready C fi bi pre x y post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\ u <> v /\
  dft_pos_gas_phase C D fi bi pre c d ==>
  ?A B. dft_pos_gas_orbit_cuts C D w fi bi pre c d A B
Proof
  strip_tac >>
  `!l r. dft_pos_gas_phase C D fi bi pre l r ==>
    ?a b. 0 < a /\ 0 < b /\
    dft_pos_gas_phase C D fi bi pre
      (FUNPOW (dft_occ_oracle_next w C) a l)
      (FUNPOW (dft_occ_oracle_next w D) b r) /\
    dft_pos_segment_account C D w a b l r` by
    (rpt strip_tac >> drule_all dft_pos_gas_segment_next >>
     disch_then (qspec_then `w` strip_assume_tac) >>
     qexistsl_tac [`a`, `a`] >> gvs[]) >>
  drule_all dft_cofinal_segments >> strip_tac >>
  qexistsl_tac [`A`, `B`] >> simp[dft_pos_gas_orbit_cuts_def]
QED

Theorem dft_pos_gas_root_orbit_segments:
  D = dft_pos_edit_ctx fi bi pre x y post C /\
  dft_pos_runtime_ready C fi bi pre x y post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\ u <> v /\
  dft_pos_functions C D f g ==>
  ?A B. dft_pos_gas_orbit_cuts C D w fi bi pre
    (dft_occ_init (DftOpen (DftEnter f 0 s) [] n))
    (dft_occ_init (DftOpen (DftEnter g 0 s) [] n)) A B
Proof
  strip_tac >> irule dft_pos_gas_orbit_segments >>
  conj_tac >- metis_tac[dft_pos_gas_phase_root] >>
  metis_tac[]
QED

Theorem dft_pos_gas_orbit_observe_forward:
  dft_pos_gas_orbit_cuts C D w fi bi pre c d A B /\
  dft_open_observe f i s (FUNPOW (dft_occ_oracle_next w C) j c).dft_occ_core /\
  inst_mem_ranges i s <> [] ==>
  ?k g t. dft_pos_functions C D f g /\
    dft_open_observe g i t (FUNPOW (dft_occ_oracle_next w D) k d).dft_occ_core /\
    t.vs_memory = s.vs_memory /\ inst_mem_ranges i t = inst_mem_ranges i s
Proof
  rewrite_tac[dft_pos_gas_orbit_cuts_def] >> strip_tac >>
  qpat_x_assum `!j. ?n. A n <= j /\ j < A (SUC n)`
    (qspec_then `j` strip_assume_tac) >>
  `j - A n < A (SUC n) - A n` by decide_tac >>
  `dft_open_observe f i s
    (FUNPOW (dft_occ_oracle_next w C) (j - A n)
      (FUNPOW (dft_occ_oracle_next w C) (A n) c)).dft_occ_core` by
    metis_tac[dft_cut_offset] >>
  qpat_x_assum `!n. dft_pos_segment_account _ _ _ _ _ _ _`
    (qspec_then `n` mp_tac) >>
  rewrite_tac[dft_pos_segment_account_def] >> strip_tac >>
  qpat_x_assum `!j f i s. j < A (SUC n) - A n /\ _ ==> _`
    (qspecl_then [`j - A n`, `f`, `i`, `s`] mp_tac) >>
  simp[] >> strip_tac >> qexistsl_tac [`k + B n`, `g`, `t`] >> simp[FUNPOW_ADD]
QED

Theorem dft_pos_gas_orbit_observe_backward:
  dft_pos_gas_orbit_cuts C D w fi bi pre c d A B /\
  dft_open_observe g i t (FUNPOW (dft_occ_oracle_next w D) k d).dft_occ_core /\
  inst_mem_ranges i t <> [] ==>
  ?j f s. dft_pos_functions C D f g /\
    dft_open_observe f i s (FUNPOW (dft_occ_oracle_next w C) j c).dft_occ_core /\
    t.vs_memory = s.vs_memory /\ inst_mem_ranges i t = inst_mem_ranges i s
Proof
  rewrite_tac[dft_pos_gas_orbit_cuts_def] >> strip_tac >>
  qpat_x_assum `!j. ?n. B n <= j /\ j < B (SUC n)`
    (qspec_then `k` strip_assume_tac) >>
  `k - B n < B (SUC n) - B n` by decide_tac >>
  `dft_open_observe g i t
    (FUNPOW (dft_occ_oracle_next w D) (k - B n)
      (FUNPOW (dft_occ_oracle_next w D) (B n) d)).dft_occ_core` by
    metis_tac[dft_cut_offset] >>
  qpat_x_assum `!n. dft_pos_segment_account _ _ _ _ _ _ _`
    (qspec_then `n` mp_tac) >>
  rewrite_tac[dft_pos_segment_account_def] >> strip_tac >>
  qpat_x_assum `!k g i t. k < B (SUC n) - B n /\ _ ==> _`
    (qspecl_then [`k - B n`, `g`, `i`, `t`] mp_tac) >>
  simp[] >> strip_tac >> qexistsl_tac [`j + A n`, `f`, `s`] >> simp[FUNPOW_ADD]
QED

Theorem dft_pos_gas_orbit_gas_forward:
  dft_pos_gas_orbit_cuts C D w fi bi pre c d A B /\
  dft_occ_gas_event i addr (FUNPOW (dft_occ_oracle_next w C) j c) ==>
  ?k. dft_occ_gas_event i addr (FUNPOW (dft_occ_oracle_next w D) k d)
Proof
  rewrite_tac[dft_pos_gas_orbit_cuts_def] >> strip_tac >>
  qpat_x_assum `!j. ?n. A n <= j /\ j < A (SUC n)`
    (qspec_then `j` strip_assume_tac) >>
  `j - A n < A (SUC n) - A n` by decide_tac >>
  `dft_occ_gas_event i addr
    (FUNPOW (dft_occ_oracle_next w C) (j - A n)
      (FUNPOW (dft_occ_oracle_next w C) (A n) c))` by
    metis_tac[dft_cut_offset] >>
  qpat_x_assum `!n. dft_pos_segment_account _ _ _ _ _ _ _`
    (qspec_then `n` mp_tac) >>
  rewrite_tac[dft_pos_segment_account_def] >> strip_tac >>
  `?k. k < B (SUC n) - B n /\ dft_occ_gas_event i addr
    (FUNPOW (dft_occ_oracle_next w D) k
      (FUNPOW (dft_occ_oracle_next w D) (B n) d))` by metis_tac[] >>
  qexists_tac `k + B n` >> simp[FUNPOW_ADD]
QED

Theorem dft_pos_gas_orbit_gas_backward:
  dft_pos_gas_orbit_cuts C D w fi bi pre c d A B /\
  dft_occ_gas_event i addr (FUNPOW (dft_occ_oracle_next w D) k d) ==>
  ?j. dft_occ_gas_event i addr (FUNPOW (dft_occ_oracle_next w C) j c)
Proof
  rewrite_tac[dft_pos_gas_orbit_cuts_def] >> strip_tac >>
  qpat_x_assum `!j. ?n. B n <= j /\ j < B (SUC n)`
    (qspec_then `k` strip_assume_tac) >>
  `k - B n < B (SUC n) - B n` by decide_tac >>
  `dft_occ_gas_event i addr
    (FUNPOW (dft_occ_oracle_next w D) (k - B n)
      (FUNPOW (dft_occ_oracle_next w D) (B n) d))` by
    metis_tac[dft_cut_offset] >>
  qpat_x_assum `!n. dft_pos_segment_account _ _ _ _ _ _ _`
    (qspec_then `n` mp_tac) >>
  rewrite_tac[dft_pos_segment_account_def] >> strip_tac >>
  `?j. j < A (SUC n) - A n /\ dft_occ_gas_event i addr
    (FUNPOW (dft_occ_oracle_next w C) j
      (FUNPOW (dft_occ_oracle_next w C) (A n) c))` by metis_tac[] >>
  qexists_tac `j + A n` >> simp[FUNPOW_ADD]
QED
