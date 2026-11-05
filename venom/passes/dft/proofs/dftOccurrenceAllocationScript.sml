(* One oracle anchored to an entire numeric trajectory, not a fuel prefix. *)
Theory dftOccurrenceAllocation
Ancestors
  dftOccurrenceOrdinals dftOccurrenceReplay dftOccurrenceFreshness
  dftOccurrenceMachine dftSparseOracle pred_set list arithmetic words

Definition dft_numeric_event_time_def:
  dft_numeric_event_time a C c addr =
    @j. ?inst. dft_occ_gas_event inst addr (FUNPOW (dft_occ_next a C) j c)
End

Definition dft_target_oracle_def:
  dft_target_oracle a C c addr =
    if ?j inst. dft_occ_gas_event inst addr (FUNPOW (dft_occ_next a C) j c)
    then a (dft_occ_count
      (FUNPOW (dft_occ_next a C) (dft_numeric_event_time a C c addr) c))
    else 0w
End

Theorem dft_numeric_event_time_exists:
  (?j inst. dft_occ_gas_event inst addr (FUNPOW (dft_occ_next a C) j c)) ==>
  ?inst. dft_occ_gas_event inst addr
    (FUNPOW (dft_occ_next a C) (dft_numeric_event_time a C c addr) c)
Proof
  simp[dft_numeric_event_time_def] >> metis_tac[SELECT_AX]
QED

Theorem dft_numeric_event_time_eq:
  dft_ctx_ids C /\ dft_occ_valid c /\
  dft_occ_gas_event inst addr (FUNPOW (dft_occ_next a C) j c) ==>
  dft_numeric_event_time a C c addr = j
Proof
  rpt strip_tac >>
  `?i. dft_occ_gas_event i addr
    (FUNPOW (dft_occ_next a C) (dft_numeric_event_time a C c addr) c)` by
    (irule dft_numeric_event_time_exists >> metis_tac[]) >>
  metis_tac[dft_occ_gas_event_unique]
QED

Theorem dft_target_oracle_read:
  dft_ctx_ids C /\ dft_occ_valid c /\
  dft_occ_gas_event inst addr (FUNPOW (dft_occ_next a C) j c) ==>
  dft_target_oracle a C c addr = a (dft_occ_count (FUNPOW (dft_occ_next a C) j c))
Proof
  rpt strip_tac >> drule_all dft_numeric_event_time_eq >> strip_tac >>
  simp[dft_target_oracle_def] >> metis_tac[]
QED

Theorem dft_target_oracle_absent:
  (~?j inst. dft_occ_gas_event inst addr (FUNPOW (dft_occ_next a C) j c)) ==>
  dft_target_oracle a C c addr = 0w
Proof
  simp[dft_target_oracle_def]
QED

Theorem dft_target_oracle_nonzero_event:
  dft_target_oracle a C c addr <> 0w ==>
  (?inst. dft_occ_gas_event inst addr
    (FUNPOW (dft_occ_next a C) (dft_numeric_event_time a C c addr) c)) /\
  a (dft_occ_count (FUNPOW (dft_occ_next a C)
    (dft_numeric_event_time a C c addr) c)) <> 0w
Proof
  simp[dft_target_oracle_def] >> IF_CASES_TAC >> simp[] >>
  metis_tac[dft_numeric_event_time_exists]
QED

Theorem dft_target_oracle_finite_support:
  dft_ctx_ids C /\ dft_occ_valid c /\ dft_sparse_oracle a xs ==>
  FINITE {addr | dft_target_oracle a C c addr <> 0w}
Proof
  strip_tac >>
  irule (FINITE_INJ |> INST_TYPE [beta |-> ``:num``]) >>
  qexistsl_tac [`\addr. dft_occ_count (FUNPOW (dft_occ_next a C)
    (dft_numeric_event_time a C c addr) c)`, `count (LENGTH xs)`] >>
  simp[INJ_DEF] >> conj_tac
  >- (rpt strip_tac >> drule dft_target_oracle_nonzero_event >> strip_tac >>
      gvs[dft_sparse_oracle_def] >>
      Cases_on `dft_occ_count (FUNPOW (dft_occ_next a C)
        (dft_numeric_event_time a C c addr) c) < LENGTH xs` >> gvs[]) >>
  rpt strip_tac >>
  dxrule dft_target_oracle_nonzero_event >> strip_tac >>
  dxrule dft_target_oracle_nonzero_event >> strip_tac >>
  `dft_numeric_event_time a C c addr = dft_numeric_event_time a C c addr'` by
    metis_tac[dft_occ_gas_ordinal_unique] >>
  metis_tac[dft_occ_gas_event_deterministic]
QED

Theorem dft_target_oracle_prefix_compatible:
  dft_ctx_ids C /\ dft_occ_valid c ==>
  !j. dft_occ_prefix_compatible (dft_target_oracle a C c) a C c j
Proof
  strip_tac >> simp[dft_occ_prefix_compatible_iff,
    dft_occ_numeric_compatible_def, dft_occ_compatible_def] >>
  metis_tac[dft_target_oracle_read]
QED

Theorem dft_target_oracle_exists:
  dft_ctx_ids C /\ dft_occ_valid c /\ dft_sparse_oracle a xs ==>
  ?w. FINITE {addr | w addr <> 0w} /\
      (!j inst addr. dft_occ_gas_event inst addr
        (FUNPOW (dft_occ_next a C) j c) ==>
        w addr = a (dft_occ_count (FUNPOW (dft_occ_next a C) j c))) /\
      (!addr. (~?j inst. dft_occ_gas_event inst addr
        (FUNPOW (dft_occ_next a C) j c)) ==> w addr = 0w) /\
      (!j. dft_occ_prefix_compatible w a C c j)
Proof
  strip_tac >> qexists_tac `dft_target_oracle a C c` >>
  metis_tac[dft_target_oracle_finite_support, dft_target_oracle_read,
    dft_target_oracle_absent, dft_target_oracle_prefix_compatible]
QED
