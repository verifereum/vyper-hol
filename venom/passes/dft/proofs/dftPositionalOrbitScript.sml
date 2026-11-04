Theory dftPositionalOrbit
Ancestors
  dftCofinalSegments dftPositionalSegment dftPositionalPhase dftPositionalRuntime
  dftOccurrenceMachine dftOpenMachine contextRawReachable venomExecSemantics
  venomState arithmetic list

Definition dft_pos_orbit_ready_def:
  dft_pos_orbit_ready fi bi pre x call post w C D Corig Dorig l r <=>
    D = dft_pos_edit_ctx fi bi pre x call post C /\
    dft_pos_runtime_ready C fi bi pre x call post /\
    dft_original_context Corig C /\ dft_original_context Dorig D /\
    dft_pos_phase C D fi bi pre x call post l r /\
    (!j f g bb bb' s ls n.
      dft_pos_slot C D fi bi f g bb bb' /\
      (FUNPOW (dft_occ_oracle_next w C) j l).dft_occ_core =
        DftOpen (DftAt f 0 bb s) ls n /\ s.vs_inst_idx = LENGTH pre ==>
      ?f0 b0. dft_recursive_crossing_ready f0 b0 bb pre x call post s)
End

Definition dft_pos_orbit_cuts_def:
  dft_pos_orbit_cuts fi bi pre x call post w C D l r A B <=>
    A 0 = 0 /\ B 0 = 0 /\
    (!n. A n < A (SUC n) /\ B n < B (SUC n)) /\
    (!n. n <= A n /\ n <= B n) /\
    (!j. ?n. A n <= j /\ j < A (SUC n)) /\
    (!j. ?n. B n <= j /\ j < B (SUC n)) /\
    (!n. dft_pos_phase C D fi bi pre x call post
      (FUNPOW (dft_occ_oracle_next w C) (A n) l)
      (FUNPOW (dft_occ_oracle_next w D) (B n) r)) /\
    (!n. dft_pos_segment_account C D w
      (A (SUC n) - A n) (B (SUC n) - B n)
      (FUNPOW (dft_occ_oracle_next w C) (A n) l)
      (FUNPOW (dft_occ_oracle_next w D) (B n) r))
End

Theorem dft_pos_orbit_segments:
  dft_pos_orbit_ready fi bi pre x call post w C D Corig Dorig l r ==>
  ?A B. dft_pos_orbit_cuts fi bi pre x call post w C D l r A B
Proof
  rewrite_tac[dft_pos_orbit_ready_def] >> strip_tac >>
  qabbrev_tac `L = dft_occ_oracle_next w C` >>
  qabbrev_tac `R = dft_occ_oracle_next w D` >>
  qabbrev_tac `P = \u v. dft_pos_phase C D fi bi pre x call post u v /\
    ?j. u = FUNPOW L j l` >>
  qabbrev_tac `H = dft_pos_segment_account C D w` >>
  `P l r /\ (!u v. P u v ==> ?a b. 0 < a /\ 0 < b /\
    P (FUNPOW L a u) (FUNPOW R b v) /\ H a b u v)` by
    (conj_tac >- (simp[Abbr `P`] >> conj_tac >- metis_tac[] >>
       qexists `0` >> simp[]) >>
     simp[Abbr `P`] >> rpt strip_tac >>
     `?a b. (a = 1 \/ a = 2) /\ (b = 1 \/ b = 2) /\
       dft_pos_phase C D fi bi pre x call post
         (FUNPOW L a (FUNPOW L j l)) (FUNPOW R b v) /\
       H a b (FUNPOW L j l) v` by
       (simp[Abbr `H`, Abbr `L`, Abbr `R`] >>
        irule dft_pos_segment_next >> simp[] >> metis_tac[]) >>
     (qexistsl [`a`, `b`] >>
      conj_tac >- decide_tac >> conj_tac >- decide_tac >>
      conj_tac >- (conj_tac >- metis_tac[] >>
        qexists `a+j` >> simp[FUNPOW_ADD]) >> metis_tac[])) >>
  drule_all dft_cofinal_segments >> strip_tac >>
  qexistsl [`A`, `B`] >>
  gvs[dft_pos_orbit_cuts_def, Abbr `P`, Abbr `H`, Abbr `L`, Abbr `R`]
QED

Theorem dft_pos_orbit_cut_exists[local]:
  (!j. ?n. A n <= j /\ j < A (SUC n)) ==>
  ((?j. E (FUNPOW L j c)) <=>
   ?n j. j < A (SUC n) - A n /\ E (FUNPOW L j (FUNPOW L (A n) c)))
Proof
  strip_tac >> eq_tac >> strip_tac
  >- (first_x_assum (qspec_then `j` strip_assume_tac) >>
      qexistsl [`n`, `j - A n`] >> conj_tac >- decide_tac >>
      metis_tac[dft_cut_offset]) >>
  qexists `j + A n` >> simp[FUNPOW_ADD]
QED

Theorem dft_pos_orbit_gas_events:
  dft_pos_orbit_cuts fi bi pre x call post w C D l r A B ==>
  !inst addr.
    ((?j. dft_occ_gas_event inst addr (FUNPOW (dft_occ_oracle_next w C) j l)) <=>
     (?k. dft_occ_gas_event inst addr (FUNPOW (dft_occ_oracle_next w D) k r)))
Proof
  rewrite_tac[dft_pos_orbit_cuts_def] >> strip_tac >> rpt gen_tac >>
  `((?j. dft_occ_gas_event inst addr (FUNPOW (dft_occ_oracle_next w C) j l)) <=>
    ?n j. j < A (SUC n) - A n /\ dft_occ_gas_event inst addr
      (FUNPOW (dft_occ_oracle_next w C) j
        (FUNPOW (dft_occ_oracle_next w C) (A n) l)))` by
    metis_tac[dft_pos_orbit_cut_exists] >>
  `((?k. dft_occ_gas_event inst addr (FUNPOW (dft_occ_oracle_next w D) k r)) <=>
    ?n k. k < B (SUC n) - B n /\ dft_occ_gas_event inst addr
      (FUNPOW (dft_occ_oracle_next w D) k
        (FUNPOW (dft_occ_oracle_next w D) (B n) r)))` by
    metis_tac[dft_pos_orbit_cut_exists] >>
  fs[dft_pos_segment_account_def] >> metis_tac[]
QED

Theorem dft_pos_orbit_observe_forward:
  dft_pos_orbit_cuts fi bi pre x call post w C D l r A B /\
  dft_open_observe f inst s (FUNPOW (dft_occ_oracle_next w C) j l).dft_occ_core /\
  inst_mem_ranges inst s <> [] ==>
  ?k g t. dft_pos_functions C D f g /\
    dft_open_observe g inst t (FUNPOW (dft_occ_oracle_next w D) k r).dft_occ_core /\
    t.vs_memory = s.vs_memory /\ inst_mem_ranges inst t = inst_mem_ranges inst s
Proof
  rewrite_tac[dft_pos_orbit_cuts_def] >> strip_tac >>
  qpat_x_assum `!j. ?n. A n <= j /\ j < A (SUC n)`
    (qspec_then `j` strip_assume_tac) >>
  `j - A n < A (SUC n) - A n` by decide_tac >>
  `dft_open_observe f inst s
    (FUNPOW (dft_occ_oracle_next w C) (j - A n)
      (FUNPOW (dft_occ_oracle_next w C) (A n) l)).dft_occ_core` by
    metis_tac[dft_cut_offset] >>
  qpat_x_assum `!n. dft_pos_segment_account _ _ _ _ _ _ _`
    (qspec_then `n` mp_tac) >>
  rewrite_tac[dft_pos_segment_account_def] >> strip_tac >>
  qpat_x_assum `!j f inst s. _ ==> ?k g t. k < _ /\ _ /\
    dft_open_observe g inst t (FUNPOW (dft_occ_oracle_next w D) k _).dft_occ_core /\ _`
    (qspecl_then [`j - A n`, `f`, `inst`, `s`] mp_tac) >>
  simp[] >> strip_tac >> qexistsl [`k + B n`, `g`, `t`] >> simp[FUNPOW_ADD]
QED

Theorem dft_pos_orbit_observe_backward:
  dft_pos_orbit_cuts fi bi pre x call post w C D l r A B /\
  dft_open_observe g inst t (FUNPOW (dft_occ_oracle_next w D) k r).dft_occ_core /\
  inst_mem_ranges inst t <> [] ==>
  ?j f s. dft_pos_functions C D f g /\
    dft_open_observe f inst s (FUNPOW (dft_occ_oracle_next w C) j l).dft_occ_core /\
    t.vs_memory = s.vs_memory /\ inst_mem_ranges inst t = inst_mem_ranges inst s
Proof
  rewrite_tac[dft_pos_orbit_cuts_def] >> strip_tac >>
  qpat_x_assum `!j. ?n. B n <= j /\ j < B (SUC n)`
    (qspec_then `k` strip_assume_tac) >>
  `k - B n < B (SUC n) - B n` by decide_tac >>
  `dft_open_observe g inst t
    (FUNPOW (dft_occ_oracle_next w D) (k - B n)
      (FUNPOW (dft_occ_oracle_next w D) (B n) r)).dft_occ_core` by
    metis_tac[dft_cut_offset] >>
  qpat_x_assum `!n. dft_pos_segment_account _ _ _ _ _ _ _`
    (qspec_then `n` mp_tac) >>
  rewrite_tac[dft_pos_segment_account_def] >> strip_tac >>
  qpat_x_assum `!k g inst t. _ ==> ?j f s. j < _ /\ _`
    (qspecl_then [`k - B n`, `g`, `inst`, `t`] mp_tac) >>
  simp[] >> strip_tac >> qexistsl [`j + A n`, `f`, `s`] >> simp[FUNPOW_ADD]
QED
