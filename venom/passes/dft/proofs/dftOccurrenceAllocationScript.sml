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

Definition dft_source_event_time_def:
  dft_source_event_time w C c n = @j.
    dft_occ_count (FUNPOW (dft_occ_oracle_next w C) j c) = n /\
    ?inst addr. dft_occ_gas_event inst addr (FUNPOW (dft_occ_oracle_next w C) j c)
End

Definition dft_source_oracle_def:
  dft_source_oracle w C c n =
    if ?j inst addr. dft_occ_count (FUNPOW (dft_occ_oracle_next w C) j c) = n /\
         dft_occ_gas_event inst addr (FUNPOW (dft_occ_oracle_next w C) j c)
    then w (dft_occ_address (FUNPOW (dft_occ_oracle_next w C)
      (dft_source_event_time w C c n) c))
    else 0w
End

Theorem dft_source_event_time_exists:
  (?j inst addr. dft_occ_count (FUNPOW (dft_occ_oracle_next w C) j c) = n /\
    dft_occ_gas_event inst addr (FUNPOW (dft_occ_oracle_next w C) j c)) ==>
  dft_occ_count (FUNPOW (dft_occ_oracle_next w C)
    (dft_source_event_time w C c n) c) = n /\
  ?inst addr. dft_occ_gas_event inst addr (FUNPOW (dft_occ_oracle_next w C)
    (dft_source_event_time w C c n) c)
Proof
  simp[dft_source_event_time_def] >> metis_tac[SELECT_AX]
QED

Theorem dft_source_event_time_eq:
  dft_occ_gas_event inst addr (FUNPOW (dft_occ_oracle_next w C) j c) ==>
  dft_source_event_time w C c
    (dft_occ_count (FUNPOW (dft_occ_oracle_next w C) j c)) = j
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `dft_source_event_time w C c n` >>
  `dft_occ_count (FUNPOW (dft_occ_oracle_next w C)
      (dft_source_event_time w C c n) c) = n /\
   ?i ad. dft_occ_gas_event i ad (FUNPOW (dft_occ_oracle_next w C)
      (dft_source_event_time w C c n) c)` by
    (irule dft_source_event_time_exists >> metis_tac[]) >>
  metis_tac[dft_occ_oracle_gas_ordinal_unique]
QED

Theorem dft_source_oracle_read:
  dft_occ_gas_event inst addr (FUNPOW (dft_occ_oracle_next w C) j c) ==>
  dft_source_oracle w C c (dft_occ_count (FUNPOW (dft_occ_oracle_next w C) j c)) = w addr
Proof
  strip_tac >> drule dft_source_event_time_eq >> strip_tac >>
  drule dft_occ_gas_address >> strip_tac >>
  simp[dft_source_oracle_def] >> metis_tac[]
QED

Theorem dft_source_oracle_nonzero_event:
  dft_source_oracle w C c n <> 0w ==>
  dft_occ_count (FUNPOW (dft_occ_oracle_next w C)
    (dft_source_event_time w C c n) c) = n /\
  (?inst addr. dft_occ_gas_event inst addr (FUNPOW (dft_occ_oracle_next w C)
    (dft_source_event_time w C c n) c)) /\
  w (dft_occ_address (FUNPOW (dft_occ_oracle_next w C)
    (dft_source_event_time w C c n) c)) <> 0w
Proof
  simp[dft_source_oracle_def] >> IF_CASES_TAC >> simp[] >>
  metis_tac[dft_source_event_time_exists]
QED

Theorem dft_source_oracle_finite_support:
  dft_ctx_ids C /\ dft_occ_valid c /\ FINITE {addr | w addr <> 0w} ==>
  FINITE {n | dft_source_oracle w C c n <> 0w}
Proof
  strip_tac >> irule (FINITE_INJ |> INST_TYPE [beta |-> ``:(num # num) list``]) >>
  qexistsl_tac [`\n. dft_occ_address (FUNPOW (dft_occ_oracle_next w C)
    (dft_source_event_time w C c n) c)`, `{addr | w addr <> 0w}`] >>
  simp[INJ_DEF] >> conj_tac
  >- metis_tac[dft_source_oracle_nonzero_event] >>
  rpt strip_tac >>
  dxrule dft_source_oracle_nonzero_event >> strip_tac >>
  dxrule dft_source_oracle_nonzero_event >> strip_tac >>
  `dft_source_event_time w C c n = dft_source_event_time w C c n'` by
    metis_tac[dft_occ_oracle_gas_event_unique, dft_occ_gas_address] >>
  metis_tac[]
QED

Theorem dft_source_oracle_prefix_compatible:
  !j. dft_occ_prefix_compatible w (dft_source_oracle w C c) C c j
Proof
  simp[dft_occ_prefix_compatible_def, dft_occ_compatible_def] >>
  metis_tac[dft_source_oracle_read]
QED

Theorem dft_source_oracle_exists:
  dft_ctx_ids C /\ dft_occ_valid c /\ FINITE {addr | w addr <> 0w} ==>
  ?a ys. dft_sparse_oracle a ys /\
    (!j. dft_occ_prefix_compatible w a C c j)
Proof
  strip_tac >>
  `FINITE {n | dft_source_oracle w C c n <> 0w}` by
    metis_tac[dft_source_oracle_finite_support] >>
  drule (iffRL dft_sparse_oracle_finite_support) >> strip_tac >>
  qexistsl_tac [`dft_source_oracle w C c`, `xs`] >>
  simp[dft_source_oracle_prefix_compatible]
QED

Theorem dft_two_root_oracles_exist:
  dft_ctx_ids C /\ dft_occ_valid c /\
  dft_ctx_ids D /\ dft_occ_valid d /\ dft_sparse_oracle b xs ==>
  ?w a ys. FINITE {addr | w addr <> 0w} /\ dft_sparse_oracle a ys /\
    (!j. dft_occ_prefix_compatible w a C c j) /\
    (!j. dft_occ_prefix_compatible w b D d j)
Proof
  strip_tac >> drule_all dft_target_oracle_exists >> strip_tac >>
  `?a ys. dft_sparse_oracle a ys /\
    (!j. dft_occ_prefix_compatible w a C c j)` by
    (irule dft_source_oracle_exists >> simp[]) >>
  metis_tac[]
QED
