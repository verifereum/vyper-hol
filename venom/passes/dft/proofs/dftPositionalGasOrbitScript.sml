Theory dftPositionalGasOrbit
Ancestors
  dftCofinalSegments dftPositionalGasSegment dftPositionalSegment
  dftPositionalPhase dftPositionalRuntime dftOccurrenceMachine dftOpenMachine
  dftOccurrenceReplay dftOpenErase
  contextRawReachable venomExecSemantics venomState arithmetic list

Definition dft_pos_gas_orbit_cuts_def:
  dft_pos_gas_orbit_cuts fi bi pre w C D l r A B <=>
    A 0 = 0 /\ B 0 = 0 /\
    (!n. A n < A (SUC n) /\ B n < B (SUC n)) /\
    (!n. n <= A n /\ n <= B n) /\
    (!j. ?n. A n <= j /\ j < A (SUC n)) /\
    (!j. ?n. B n <= j /\ j < B (SUC n)) /\
    (!n. dft_pos_gas_phase C D fi bi pre
      (FUNPOW (dft_occ_oracle_next w C) (A n) l)
      (FUNPOW (dft_occ_oracle_next w D) (B n) r)) /\
    (!n. dft_pos_segment_account C D w
      (A (SUC n) - A n) (B (SUC n) - B n)
      (FUNPOW (dft_occ_oracle_next w C) (A n) l)
      (FUNPOW (dft_occ_oracle_next w D) (B n) r))
End

Theorem dft_pos_gas_orbit_segments:
  D = dft_pos_edit_ctx fi bi pre x y post C /\
  dft_pos_runtime_ready C fi bi pre x y post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\ u <> v /\
  dft_pos_gas_phase C D fi bi pre l r ==>
  ?A B. dft_pos_gas_orbit_cuts fi bi pre w C D l r A B
Proof
  strip_tac >>
  qabbrev_tac `L = dft_occ_oracle_next w C` >>
  qabbrev_tac `R = dft_occ_oracle_next w D` >>
  qabbrev_tac `P = dft_pos_gas_phase C D fi bi pre` >>
  qabbrev_tac `H = dft_pos_segment_account C D w` >>
  `P l r /\ (!l r. P l r ==> ?a b. 0 < a /\ 0 < b /\
    P (FUNPOW L a l) (FUNPOW R b r) /\ H a b l r)` by
    (conj_tac >- simp[Abbr `P`] >> rpt strip_tac >>
     `?a. (a = 1 \/ a = 2) /\ P (FUNPOW L a l') (FUNPOW R a r') /\
       H a a l' r'` by
       (simp[Abbr `P`, Abbr `L`, Abbr `R`, Abbr `H`] >>
        irule dft_pos_gas_segment_next >> metis_tac[]) >>
     qexistsl [`a`, `a`] >> simp[] >> decide_tac) >>
  drule_all dft_cofinal_segments >> strip_tac >>
  qexistsl [`A`, `B`] >>
  gvs[dft_pos_gas_orbit_cuts_def, Abbr `P`, Abbr `H`, Abbr `L`, Abbr `R`]
QED

Theorem dft_pos_gas_root_segments:
  D = dft_pos_edit_ctx fi bi pre x y post C /\
  dft_pos_runtime_ready C fi bi pre x y post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\ u <> v /\
  dft_pos_functions C D f g ==>
  ?A B. dft_pos_gas_orbit_cuts fi bi pre w C D
    (dft_occ_init (DftOpen (DftEnter f 0 s) [] n))
    (dft_occ_init (DftOpen (DftEnter g 0 s) [] n)) A B
Proof
  strip_tac >> irule dft_pos_gas_orbit_segments >>
  metis_tac[dft_pos_gas_phase_root]
QED

Theorem dft_pos_gas_orbit_cut_exists[local]:
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

Theorem dft_pos_gas_orbit_events:
  dft_pos_gas_orbit_cuts fi bi pre w C D l r A B ==>
  !inst addr.
    ((?j. dft_occ_gas_event inst addr (FUNPOW (dft_occ_oracle_next w C) j l)) <=>
     (?k. dft_occ_gas_event inst addr (FUNPOW (dft_occ_oracle_next w D) k r)))
Proof
  rewrite_tac[dft_pos_gas_orbit_cuts_def] >> strip_tac >> rpt gen_tac >>
  `((?j. dft_occ_gas_event inst addr (FUNPOW (dft_occ_oracle_next w C) j l)) <=>
    ?n j. j < A (SUC n) - A n /\ dft_occ_gas_event inst addr
      (FUNPOW (dft_occ_oracle_next w C) j
        (FUNPOW (dft_occ_oracle_next w C) (A n) l)))` by
    metis_tac[dft_pos_gas_orbit_cut_exists] >>
  `((?k. dft_occ_gas_event inst addr (FUNPOW (dft_occ_oracle_next w D) k r)) <=>
    ?n k. k < B (SUC n) - B n /\ dft_occ_gas_event inst addr
      (FUNPOW (dft_occ_oracle_next w D) k
        (FUNPOW (dft_occ_oracle_next w D) (B n) r)))` by
    metis_tac[dft_pos_gas_orbit_cut_exists] >>
  fs[dft_pos_segment_account_def] >> metis_tac[]
QED

Theorem dft_pos_gas_orbit_observe_forward:
  dft_pos_gas_orbit_cuts fi bi pre w C D l r A B /\
  dft_open_observe f inst s (FUNPOW (dft_occ_oracle_next w C) j l).dft_occ_core /\
  inst_mem_ranges inst s <> [] ==>
  ?k g t. dft_pos_functions C D f g /\
    dft_open_observe g inst t (FUNPOW (dft_occ_oracle_next w D) k r).dft_occ_core /\
    t.vs_memory = s.vs_memory /\ inst_mem_ranges inst t = inst_mem_ranges inst s
Proof
  rewrite_tac[dft_pos_gas_orbit_cuts_def] >> strip_tac >>
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

Theorem dft_pos_gas_orbit_observe_backward:
  dft_pos_gas_orbit_cuts fi bi pre w C D l r A B /\
  dft_open_observe g inst t (FUNPOW (dft_occ_oracle_next w D) k r).dft_occ_core /\
  inst_mem_ranges inst t <> [] ==>
  ?j f s. dft_pos_functions C D f g /\
    dft_open_observe f inst s (FUNPOW (dft_occ_oracle_next w C) j l).dft_occ_core /\
    t.vs_memory = s.vs_memory /\ inst_mem_ranges inst t = inst_mem_ranges inst s
Proof
  rewrite_tac[dft_pos_gas_orbit_cuts_def] >> strip_tac >>
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

(* A terminal empty-stack core is absorbing.  Advancing to a cofinal cut
   therefore also covers a terminal position inside a segment. *)
Theorem dft_pos_gas_terminal_next[local]:
  c.dft_occ_core = DftOpen (DftDone result) [] n ==>
  (dft_occ_oracle_next w C c).dft_occ_core = DftOpen (DftDone result) [] n
Proof
  Cases_on `result` >>
  simp[dft_occ_oracle_next_def, dft_next_inf_def, dft_fill_def,
    dft_fill_control_def, dft_open_next_def, dft_open_return_def, dft_erase_def]
QED

Theorem dft_pos_gas_terminal_iter[local]:
  !k c. c.dft_occ_core = DftOpen (DftDone result) [] n ==>
  (FUNPOW (dft_occ_oracle_next w C) k c).dft_occ_core =
    DftOpen (DftDone result) [] n
Proof
  Induct_on `k` >> simp[FUNPOW_SUC] >>
  metis_tac[dft_pos_gas_terminal_next]
QED

Theorem dft_pos_gas_terminal_later[local]:
  (FUNPOW (dft_occ_oracle_next w C) j l).dft_occ_core =
    DftOpen (DftDone result) [] n /\ j <= k ==>
  (FUNPOW (dft_occ_oracle_next w C) k l).dft_occ_core =
    DftOpen (DftDone result) [] n
Proof
  strip_tac >>
  `k = (k-j) + j` by decide_tac >>
  metis_tac[FUNPOW_ADD, dft_pos_gas_terminal_iter]
QED

Theorem dft_pos_gas_orbit_terminal_forward:
  dft_pos_gas_orbit_cuts fi bi pre w C D l r A B /\
  (FUNPOW (dft_occ_oracle_next w C) j l).dft_occ_core =
    DftOpen (DftDone result) [] n ==>
  ?k. (FUNPOW (dft_occ_oracle_next w D) k r).dft_occ_core =
    DftOpen (DftDone result) [] n
Proof
  rewrite_tac[dft_pos_gas_orbit_cuts_def] >> strip_tac >>
  `j <= A j` by metis_tac[] >>
  `(FUNPOW (dft_occ_oracle_next w C) (A j) l).dft_occ_core =
    DftOpen (DftDone result) [] n` by
    metis_tac[dft_pos_gas_terminal_later] >>
  qexists `B j` >> metis_tac[dft_pos_gas_phase_terminal]
QED

Theorem dft_pos_gas_orbit_terminal_backward:
  dft_pos_gas_orbit_cuts fi bi pre w C D l r A B /\
  (FUNPOW (dft_occ_oracle_next w D) k r).dft_occ_core =
    DftOpen (DftDone result) [] n ==>
  ?j. (FUNPOW (dft_occ_oracle_next w C) j l).dft_occ_core =
    DftOpen (DftDone result) [] n
Proof
  rewrite_tac[dft_pos_gas_orbit_cuts_def] >> strip_tac >>
  `k <= B k` by metis_tac[] >>
  `(FUNPOW (dft_occ_oracle_next w D) (B k) r).dft_occ_core =
    DftOpen (DftDone result) [] n` by
    metis_tac[dft_pos_gas_terminal_later] >>
  qexists `A k` >>
  qpat_x_assum `!n. dft_pos_gas_phase _ _ _ _ _ _ _`
    (qspec_then `k` mp_tac) >>
  simp[dft_pos_gas_phase_def, dft_pos_control_def] >>
  rpt strip_tac >> gvs[]
QED
