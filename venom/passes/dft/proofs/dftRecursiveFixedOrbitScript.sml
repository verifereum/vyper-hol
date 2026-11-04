Theory dftRecursiveFixedOrbit
Ancestors
  dftCofinalSegments dftRecursiveFixedSegment dftRecursiveFixedPhase
  dftOccurrenceMachine dftOpenMachine contextRawReachable
  venomExecSemantics arithmetic list

Definition dft_fixed_orbit_ready_def:
  dft_fixed_orbit_ready q pre x call post w C Corig Dorig c d <=>
    dft_fixed_phase q pre x call post c d /\
    q.bb_instructions = pre ++ [x;call] ++ post /\
    ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
    x.inst_opcode <> GAS /\ x.inst_opcode <> ALLOCA /\ call.inst_opcode = INVOKE /\
    dft_original_context Corig C /\
    dft_original_context Dorig (dft_gas_edit_ctx q pre x call post C) /\
    (!j fn s ls n.
      (FUNPOW (dft_occ_oracle_next w C) j c).dft_occ_core =
        DftOpen (DftAt fn 0 q s) ls n /\ s.vs_inst_idx = LENGTH pre ==>
      ?f b. dft_recursive_crossing_ready f b q pre x call post s)
End

Definition dft_fixed_orbit_cuts_def:
  dft_fixed_orbit_cuts q pre x call post w C c d A B <=>
    A 0 = 0 /\ B 0 = 0 /\
    (!n. A n < A (SUC n) /\ B n < B (SUC n)) /\
    (!n. n <= A n /\ n <= B n) /\
    (!j. ?n. A n <= j /\ j < A (SUC n)) /\
    (!j. ?n. B n <= j /\ j < B (SUC n)) /\
    (!n. dft_fixed_phase q pre x call post
      (FUNPOW (dft_occ_oracle_next w C) (A n) c)
      (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C)) (B n) d)) /\
    (!n. dft_fixed_segment_account q pre x call post w C
      (dft_gas_edit_ctx q pre x call post C)
      (A (SUC n) - A n) (B (SUC n) - B n)
      (FUNPOW (dft_occ_oracle_next w C) (A n) c)
      (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C)) (B n) d))
End

Theorem dft_fixed_orbit_segments:
  dft_fixed_orbit_ready q pre x call post w C Corig Dorig c d ==>
  ?A B. dft_fixed_orbit_cuts q pre x call post w C c d A B
Proof
  rewrite_tac[dft_fixed_orbit_ready_def] >> strip_tac >>
  qabbrev_tac `L = dft_occ_oracle_next w C` >>
  qabbrev_tac `R = dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C)` >>
  qabbrev_tac `P = \u v. dft_fixed_phase q pre x call post u v /\
    ?j. u = FUNPOW L j c` >>
  qabbrev_tac `H = dft_fixed_segment_account q pre x call post w C
    (dft_gas_edit_ctx q pre x call post C)` >>
  `P c d /\ (!u v. P u v ==> ?a b. 0 < a /\ 0 < b /\
    P (FUNPOW L a u) (FUNPOW R b v) /\ H a b u v)` by
    (conj_tac >- (simp[Abbr `P`] >> qexists `0` >> simp[]) >>
     simp[Abbr `P`] >> rpt strip_tac >>
     `?a b. (a = 1 \/ a = 2) /\ (b = 1 \/ b = 2) /\
       dft_fixed_phase q pre x call post
         (FUNPOW L a (FUNPOW L j c)) (FUNPOW R b v) /\
       H a b (FUNPOW L j c) v` by
       (simp[Abbr `H`, Abbr `L`, Abbr `R`] >>
        irule dft_fixed_segment_next >> simp[] >> metis_tac[]) >>
     (qexistsl [`a`, `b`] >>
      conj_tac >- decide_tac >> conj_tac >- decide_tac >>
      conj_tac >- (conj_tac >- metis_tac[] >>
        qexists `a+j` >> simp[FUNPOW_ADD]) >> metis_tac[])) >>
  drule_all dft_cofinal_segments >> strip_tac >>
  qexistsl [`A`, `B`] >>
  gvs[dft_fixed_orbit_cuts_def, Abbr `P`, Abbr `H`, Abbr `L`, Abbr `R`]
QED

Theorem dft_orbit_cut_exists[local]:
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

Theorem dft_fixed_orbit_gas_events:
  dft_fixed_orbit_cuts q pre x call post w C c d A B ==>
  !inst addr.
    ((?j. dft_occ_gas_event inst addr (FUNPOW (dft_occ_oracle_next w C) j c)) <=>
     (?k. dft_occ_gas_event inst addr
       (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C)) k d)))
Proof
  rewrite_tac[dft_fixed_orbit_cuts_def] >> strip_tac >>
  rpt gen_tac >>
  `((?j. dft_occ_gas_event inst addr (FUNPOW (dft_occ_oracle_next w C) j c)) <=>
    ?n j. j < A (SUC n) - A n /\ dft_occ_gas_event inst addr
      (FUNPOW (dft_occ_oracle_next w C) j
        (FUNPOW (dft_occ_oracle_next w C) (A n) c)))` by
    metis_tac[dft_orbit_cut_exists] >>
  `((?k. dft_occ_gas_event inst addr
       (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C)) k d)) <=>
    ?n k. k < B (SUC n) - B n /\ dft_occ_gas_event inst addr
      (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C)) k
        (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C)) (B n) d)))` by
    metis_tac[dft_orbit_cut_exists] >>
  fs[dft_fixed_segment_account_def] >> metis_tac[]
QED

Theorem dft_fixed_orbit_observe_forward:
  dft_fixed_orbit_cuts q pre x call post w C c d A B /\
  dft_open_observe fn inst s (FUNPOW (dft_occ_oracle_next w C) j c).dft_occ_core /\
  inst_mem_ranges inst s <> [] ==>
  ?k t. dft_open_observe (dft_gas_edit_fn q pre x call post fn) inst t
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C)) k d).dft_occ_core /\
    t.vs_memory = s.vs_memory /\ inst_mem_ranges inst t = inst_mem_ranges inst s
Proof
  rewrite_tac[dft_fixed_orbit_cuts_def] >> strip_tac >>
  qpat_x_assum `!j. ?n. A n <= j /\ j < A (SUC n)`
    (qspec_then `j` strip_assume_tac) >>
  `j - A n < A (SUC n) - A n` by decide_tac >>
  `dft_open_observe fn inst s
    (FUNPOW (dft_occ_oracle_next w C) (j - A n)
      (FUNPOW (dft_occ_oracle_next w C) (A n) c)).dft_occ_core` by
    metis_tac[dft_cut_offset] >>
  qpat_x_assum `!n. dft_fixed_segment_account _ _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `n` mp_tac) >>
  rewrite_tac[dft_fixed_segment_account_def] >> strip_tac >>
  qpat_x_assum `!j fn inst s. _ ==> ?k t. k < _ /\ dft_open_observe _ _ _ _ /\ _`
    (qspecl_then [`j - A n`, `fn`, `inst`, `s`] mp_tac) >>
  simp[] >> strip_tac >> qexistsl [`k + B n`, `t`] >> simp[FUNPOW_ADD]
QED

Theorem dft_fixed_orbit_observe_backward:
  dft_fixed_orbit_cuts q pre x call post w C c d A B /\
  dft_open_observe fn inst t
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C)) k d).dft_occ_core /\
  inst_mem_ranges inst t <> [] ==>
  ?j f s. fn = dft_gas_edit_fn q pre x call post f /\
    dft_open_observe f inst s (FUNPOW (dft_occ_oracle_next w C) j c).dft_occ_core /\
    t.vs_memory = s.vs_memory /\ inst_mem_ranges inst t = inst_mem_ranges inst s
Proof
  rewrite_tac[dft_fixed_orbit_cuts_def] >> strip_tac >>
  qpat_x_assum `!j. ?n. B n <= j /\ j < B (SUC n)`
    (qspec_then `k` strip_assume_tac) >>
  `k - B n < B (SUC n) - B n` by decide_tac >>
  `dft_open_observe fn inst t
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C)) (k - B n)
      (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C)) (B n) d)).dft_occ_core` by
    metis_tac[dft_cut_offset] >>
  qpat_x_assum `!n. dft_fixed_segment_account _ _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `n` mp_tac) >>
  rewrite_tac[dft_fixed_segment_account_def] >> strip_tac >>
  qpat_x_assum `!k fn inst t. _ ==> ?j f s. j < _ /\ _`
    (qspecl_then [`k - B n`, `fn`, `inst`, `t`] mp_tac) >>
  simp[] >> strip_tac >> qexistsl [`j + A n`, `f`, `s`] >> simp[FUNPOW_ADD]
QED
