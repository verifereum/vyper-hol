Theory dftGasOrdinaryOrbit
Ancestors
  dftGasOrdinaryTrace dftOriginalOrbit dftOriginalRuntime
  dftOccurrenceOrdinaryClosure dftOccurrenceGasEdit dftOccurrenceCallTrace
  dftOpenMachine dftOpenErase list arithmetic

Theorem dft_gas_ordinary_endpoint_root:
  dft_gas_ordinary_endpoint q pre x y post c d /\
  c.dft_occ_core = DftOpen (DftDone r) [] n ==>
  ?r' n'. d.dft_occ_core = DftOpen (DftDone r') [] n' /\
    dft_ordinary_result_rel r r'
Proof
  strip_tac >> fs[dft_gas_ordinary_endpoint_def]
  >- (irule dft_ordinary_endpoint_root >>
      simp[dft_ordinary_endpoint_def] >> metis_tac[]) >>
  fs[dft_gas_ordinary_stopped_def, dft_ordinary_result_rel_def] >> metis_tac[]
QED

Theorem dft_original_mixed_orbit_cofinal:
  !m c d.
  dft_original_gas_ordinary_environment Corig C L q pre x y post /\
  dft_original_label_ready C L c /\ dft_gas_ordinary_endpoint q pre x y post c d ==>
  ?p r. m <= p /\ m <= r /\
    dft_gas_ordinary_endpoint q pre x y post
      (FUNPOW (dft_occ_oracle_next w C) p c)
      (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) r d) /\
    dft_original_label_ready C L (FUNPOW (dft_occ_oracle_next w C) p c)
Proof
  Induct
  >- (rpt strip_tac >> qexistsl_tac [`0`, `0`] >> simp[FUNPOW]) >>
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  drule_all dft_original_mixed_endpoint_segment >>
  disch_then (qspec_then `w` strip_assume_tac) >>
  qexistsl_tac [`p + k`, `r + j`] >>
  conj_tac >- decide_tac >> conj_tac >- decide_tac >>
  gvs[GSYM FUNPOW_ADD, ADD_COMM]
QED

Theorem dft_original_mixed_orbit_terminal:
  dft_original_gas_ordinary_environment Corig C L q pre x y post /\
  dft_original_label_ready C L c /\ dft_gas_ordinary_endpoint q pre x y post c d /\
  (FUNPOW (dft_occ_oracle_next w C) h c).dft_occ_core =
    DftOpen (DftDone r) [] n ==>
  ?j r' n'.
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) j d).dft_occ_core =
      DftOpen (DftDone r') [] n' /\ dft_ordinary_result_rel r r'
Proof
  strip_tac >> drule_all dft_original_mixed_orbit_cofinal >>
  disch_then (qspecl_then [`w`, `h`] strip_assume_tac) >>
  `?delta. p = delta + h` by (qexists_tac `p - h` >> decide_tac) >>
  `?n. (FUNPOW (dft_occ_oracle_next w C) p c).dft_occ_core =
     DftOpen (DftDone r) [] n` by
    (gvs[FUNPOW_ADD] >> irule dft_occ_oracle_root_absorb >> metis_tac[]) >>
  drule_all dft_gas_ordinary_endpoint_root >> metis_tac[]
QED

Theorem dft_original_mixed_root_terminal:
  dft_original_gas_ordinary_environment Corig C s.vs_labels q pre x y post /\
  dft_original_function f fn /\ fn_reachable f s.vs_current_bb /\
  strict_dom_vars_defined f s /\ MEM fn C.ctx_functions ==>
  !h r n'.
    (FUNPOW (dft_occ_oracle_next w C) h
      (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))).dft_occ_core =
        DftOpen (DftDone r) [] n' ==>
    ?j r' n''.
      (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) j
        (dft_occ_init (DftOpen
          (DftEnter (dft_gas_edit_fn q pre x y post fn) 0 s) [] n))).dft_occ_core =
        DftOpen (DftDone r') [] n'' /\ dft_ordinary_result_rel r r'
Proof
  strip_tac >>
  `dft_original_label_ready C s.vs_labels
    (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))` by
    (irule dft_original_label_root >> metis_tac[]) >>
  `dft_gas_ordinary_endpoint q pre x y post
    (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))
    (dft_occ_init (DftOpen
      (DftEnter (dft_gas_edit_fn q pre x y post fn) 0 s) [] n))` by
    simp[dft_gas_ordinary_endpoint_def, dft_ordinary_sync_init] >>
  rpt strip_tac >> irule dft_original_mixed_orbit_terminal >> metis_tac[]
QED
