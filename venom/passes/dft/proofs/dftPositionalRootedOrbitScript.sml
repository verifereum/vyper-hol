Theory dftPositionalRootedOrbit
Ancestors
  dftPositionalGasCoverage dftPositionalSegment dftPositionalLifecycle
  dftCofinalSegments dftOccurrenceMachine dftOpenMachine
  contextRawReachable venomExecSemantics venomState arithmetic list

Definition dft_pos_rooted_orbit_cuts_def:
  dft_pos_rooted_orbit_cuts w C D fi bi pre x call post rootL rootR A B <=>
    A 0 = 0 /\ B 0 = 0 /\
    (!n. A n < A (SUC n) /\ B n < B (SUC n)) /\
    (!n. n <= A n /\ n <= B n) /\
    (!j. ?n. A n <= j /\ j < A (SUC n)) /\
    (!j. ?n. B n <= j /\ j < B (SUC n)) /\
    (!n. dft_pos_rooted_phase w C D fi bi pre x call post rootL rootR
      (FUNPOW (dft_occ_oracle_next w C) (A n) rootL)
      (FUNPOW (dft_occ_oracle_next w D) (B n) rootR)) /\
    (!n. dft_pos_segment_account C D w (A (SUC n) - A n) (B (SUC n) - B n)
      (FUNPOW (dft_occ_oracle_next w C) (A n) rootL)
      (FUNPOW (dft_occ_oracle_next w D) (B n) rootR))
End

Theorem dft_pos_rooted_orbit_segments:
  D = dft_pos_edit_ctx fi bi pre x call post C /\
  dft_pos_runtime_ready C fi bi pre x call post /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  ctx_labels_bound Corig L /\ MEM rootfn C.ctx_functions /\
  fn_entry_label rootfn = SOME s0.vs_current_bb /\ s0.vs_labels = L /\
  rootL = dft_occ_init (DftOpen (DftEnter rootfn 0 s0) [] n0) /\
  ~dft_must_order x call /\ call.inst_opcode = INVOKE /\
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> ALLOCA /\ x.inst_opcode <> GAS /\ x.inst_opcode <> INVOKE /\
  dft_pos_rooted_phase w C D fi bi pre x call post rootL rootR rootL rootR ==>
  ?A B. dft_pos_rooted_orbit_cuts w C D fi bi pre x call post rootL rootR A B
Proof
  strip_tac >>
  qabbrev_tac `P = dft_pos_rooted_phase w C D fi bi pre x call post rootL rootR` >>
  `P rootL rootR /\
   (!u v. P u v ==> ?a b. 0 < a /\ 0 < b /\
     P (FUNPOW (dft_occ_oracle_next w C) a u)
       (FUNPOW (dft_occ_oracle_next w D) b v) /\
     dft_pos_segment_account C D w a b u v)` by
    (conj_tac >- simp[Abbr `P`] >>
     qpat_x_assum `P rootL rootR` kall_tac >>
     rpt gen_tac >> simp[NoAsms, Abbr `P`] >> strip_tac >>
     drule_all dft_pos_rooted_progress_account >>
     disch_then (qx_choosel_then [`a`, `b`] strip_assume_tac) >>
     qexistsl_tac [`a`, `b`] >> fs[]) >>
  drule_all dft_cofinal_segments >> strip_tac >>
  qexistsl_tac [`A`, `B`] >>
  gvs[dft_pos_rooted_orbit_cuts_def, Abbr `P`]
QED

Theorem dft_pos_orbit_cut_exists[local]:
  (!j. ?n. A n <= j /\ j < A (SUC n)) ==>
  ((?j. E (FUNPOW L j c)) <=>
   ?n j. j < A (SUC n) - A n /\ E (FUNPOW L j (FUNPOW L (A n) c)))
Proof
  strip_tac >> eq_tac >> strip_tac
  >- (first_x_assum (qspec_then `j` strip_assume_tac) >>
      qexistsl_tac [`n`, `j - A n`] >> conj_tac >- decide_tac >>
      metis_tac[dft_cut_offset]) >>
  qexists_tac `j + A n` >> simp[FUNPOW_ADD]
QED

Theorem dft_pos_rooted_orbit_gas_events:
  dft_pos_rooted_orbit_cuts w C D fi bi pre x call post rootL rootR A B ==>
  !inst addr.
    ((?j. dft_occ_gas_event inst addr (FUNPOW (dft_occ_oracle_next w C) j rootL)) <=>
     (?k. dft_occ_gas_event inst addr (FUNPOW (dft_occ_oracle_next w D) k rootR)))
Proof
  rewrite_tac[dft_pos_rooted_orbit_cuts_def] >> strip_tac >> rpt gen_tac >>
  `((?j. dft_occ_gas_event inst addr (FUNPOW (dft_occ_oracle_next w C) j rootL)) <=>
    ?n j. j < A (SUC n) - A n /\ dft_occ_gas_event inst addr
      (FUNPOW (dft_occ_oracle_next w C) j
        (FUNPOW (dft_occ_oracle_next w C) (A n) rootL)))` by
    metis_tac[dft_pos_orbit_cut_exists] >>
  `((?k. dft_occ_gas_event inst addr (FUNPOW (dft_occ_oracle_next w D) k rootR)) <=>
    ?n k. k < B (SUC n) - B n /\ dft_occ_gas_event inst addr
      (FUNPOW (dft_occ_oracle_next w D) k
        (FUNPOW (dft_occ_oracle_next w D) (B n) rootR)))` by
    metis_tac[dft_pos_orbit_cut_exists] >>
  fs[dft_pos_segment_account_def] >> metis_tac[]
QED

Theorem dft_pos_rooted_orbit_observe_forward:
  dft_pos_rooted_orbit_cuts w C D fi bi pre x call post rootL rootR A B /\
  dft_open_observe f inst s (FUNPOW (dft_occ_oracle_next w C) j rootL).dft_occ_core /\
  inst_mem_ranges inst s <> [] ==>
  ?k g t. dft_pos_functions C D f g /\
    dft_open_observe g inst t (FUNPOW (dft_occ_oracle_next w D) k rootR).dft_occ_core /\
    t.vs_memory = s.vs_memory /\ inst_mem_ranges inst t = inst_mem_ranges inst s
Proof
  rewrite_tac[dft_pos_rooted_orbit_cuts_def] >> strip_tac >>
  qpat_x_assum `!j. ?n. A n <= j /\ j < A (SUC n)`
    (qspec_then `j` strip_assume_tac) >>
  `j - A n < A (SUC n) - A n` by decide_tac >>
  `dft_open_observe f inst s
    (FUNPOW (dft_occ_oracle_next w C) (j - A n)
      (FUNPOW (dft_occ_oracle_next w C) (A n) rootL)).dft_occ_core` by
    metis_tac[dft_cut_offset] >>
  qpat_x_assum `!n. dft_pos_segment_account _ _ _ _ _ _ _`
    (qspec_then `n` mp_tac) >>
  rewrite_tac[dft_pos_segment_account_def] >> strip_tac >>
  qpat_x_assum `!j f inst s. j < A (SUC n) - A n /\ _ ==> _`
    (qspecl_then [`j - A n`, `f`, `inst`, `s`] mp_tac) >>
  simp[] >> strip_tac >> qexistsl_tac [`k + B n`, `g`, `t`] >> simp[FUNPOW_ADD]
QED

Theorem dft_pos_rooted_orbit_observe_backward:
  dft_pos_rooted_orbit_cuts w C D fi bi pre x call post rootL rootR A B /\
  dft_open_observe g inst t (FUNPOW (dft_occ_oracle_next w D) k rootR).dft_occ_core /\
  inst_mem_ranges inst t <> [] ==>
  ?j f s. dft_pos_functions C D f g /\
    dft_open_observe f inst s (FUNPOW (dft_occ_oracle_next w C) j rootL).dft_occ_core /\
    t.vs_memory = s.vs_memory /\ inst_mem_ranges inst t = inst_mem_ranges inst s
Proof
  rewrite_tac[dft_pos_rooted_orbit_cuts_def] >> strip_tac >>
  qpat_x_assum `!j. ?n. B n <= j /\ j < B (SUC n)`
    (qspec_then `k` strip_assume_tac) >>
  `k - B n < B (SUC n) - B n` by decide_tac >>
  `dft_open_observe g inst t
    (FUNPOW (dft_occ_oracle_next w D) (k - B n)
      (FUNPOW (dft_occ_oracle_next w D) (B n) rootR)).dft_occ_core` by
    metis_tac[dft_cut_offset] >>
  qpat_x_assum `!n. dft_pos_segment_account _ _ _ _ _ _ _`
    (qspec_then `n` mp_tac) >>
  rewrite_tac[dft_pos_segment_account_def] >> strip_tac >>
  qpat_x_assum `!k g inst t. _ ==> ?j f s. j < _ /\ _`
    (qspecl_then [`k - B n`, `g`, `inst`, `t`] mp_tac) >>
  simp[] >> strip_tac >> qexistsl_tac [`j + A n`, `f`, `s`] >> simp[FUNPOW_ADD]
QED
