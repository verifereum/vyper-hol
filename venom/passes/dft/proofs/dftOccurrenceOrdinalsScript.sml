(* Whole-orbit freshness for address-driven execution. *)
Theory dftOccurrenceOrdinals
Ancestors
  dftOccurrenceReplay dftOccurrenceFreshness dftOccurrenceMachine
  dftOpenErase dftOpenMachine dftOpenHistory venomExecSemantics venomInst arithmetic list

Theorem dft_occ_oracle_valid_next:
  dft_ctx_ids C /\ dft_occ_valid c ==>
  dft_occ_valid (dft_occ_oracle_next w C c)
Proof
  simp[dft_occ_oracle_next_def] >> metis_tac[dft_occ_valid_next]
QED

Theorem dft_occ_oracle_future_next:
  dft_ctx_ids C /\ dft_occ_valid c /\
  dft_occ_future (dft_occ_oracle_next w C c) addr ==>
  dft_occ_future c addr
Proof
  simp[dft_occ_oracle_next_def] >> metis_tac[dft_occ_future_next]
QED

Theorem dft_occ_oracle_event_retired:
  dft_ctx_ids C /\ dft_occ_valid c /\ dft_occ_event inst addr c ==>
  ~dft_occ_future (dft_occ_oracle_next w C c) addr
Proof
  simp[dft_occ_oracle_next_def] >> metis_tac[dft_occ_event_retired]
QED

Theorem dft_occ_oracle_valid_iter:
  !j c. dft_ctx_ids C /\ dft_occ_valid c ==>
  dft_occ_valid (FUNPOW (dft_occ_oracle_next w C) j c)
Proof
  Induct >> simp[FUNPOW_SUC] >> metis_tac[dft_occ_oracle_valid_next]
QED

Theorem dft_occ_oracle_future_iter:
  !j c. dft_ctx_ids C /\ dft_occ_valid c /\
  dft_occ_future (FUNPOW (dft_occ_oracle_next w C) j c) addr ==>
  dft_occ_future c addr
Proof
  Induct >> simp[FUNPOW_SUC] >> rpt strip_tac >>
  metis_tac[dft_occ_oracle_valid_iter, dft_occ_oracle_future_next]
QED

Theorem dft_occ_oracle_event_later:
  dft_ctx_ids C /\ dft_occ_valid c /\ dft_occ_event inst addr c ==>
  ~dft_occ_event inst' addr (FUNPOW (dft_occ_oracle_next w C) (SUC j) c)
Proof
  rpt strip_tac >>
  `~dft_occ_future (dft_occ_oracle_next w C c) addr` by
    metis_tac[dft_occ_oracle_event_retired] >>
  `dft_occ_valid (dft_occ_oracle_next w C c)` by
    metis_tac[dft_occ_oracle_valid_next] >>
  `dft_occ_valid (FUNPOW (dft_occ_oracle_next w C) j (dft_occ_oracle_next w C c))` by
    metis_tac[dft_occ_oracle_valid_iter] >>
  gvs[FUNPOW] >>
  metis_tac[dft_occ_event_future, dft_occ_oracle_future_iter]
QED

Theorem dft_occ_oracle_event_unique:
  dft_ctx_ids C /\ dft_occ_valid c /\
  dft_occ_event inst addr (FUNPOW (dft_occ_oracle_next w C) j c) /\
  dft_occ_event inst' addr (FUNPOW (dft_occ_oracle_next w C) k c) ==> j = k
Proof
  wlog_tac `j <= k` [`j`, `k`, `inst`, `inst'`] >- metis_tac[LESS_EQ_CASES] >>
  rpt strip_tac >> Cases_on `j = k` >- simp[] >>
  `?d. k = SUC d + j` by (qexists_tac `k - j - 1` >> decide_tac) >>
  qpat_x_assum `k = _` SUBST_ALL_TAC >>
  qpat_x_assum `dft_occ_event inst' _ _` mp_tac >>
  pure_rewrite_tac [FUNPOW_ADD] >> strip_tac >>
  `dft_occ_valid (FUNPOW (dft_occ_oracle_next w C) j c)` by
    metis_tac[dft_occ_oracle_valid_iter] >>
  metis_tac[dft_occ_oracle_event_later]
QED

Theorem dft_occ_oracle_gas_event_unique:
  dft_ctx_ids C /\ dft_occ_valid c /\
  dft_occ_gas_event inst addr (FUNPOW (dft_occ_oracle_next w C) j c) /\
  dft_occ_gas_event inst' addr (FUNPOW (dft_occ_oracle_next w C) k c) ==> j = k
Proof
  simp[dft_occ_gas_event_def] >> metis_tac[dft_occ_oracle_event_unique]
QED

Theorem dft_occ_gas_event_deterministic:
  dft_occ_gas_event inst addr c /\ dft_occ_gas_event inst' addr' c ==>
  inst = inst' /\ addr = addr'
Proof
  simp[dft_occ_gas_event_def] >> metis_tac[dft_occ_event_deterministic]
QED

Theorem dft_ordinal_counter_fill[local,simp]:
  dft_history_counter (dft_fill b core) = dft_history_counter core
Proof
  Cases_on `core` >> simp[dft_fill_def, dft_history_counter_def]
QED

Theorem dft_ordinal_counter_next[local]:
  dft_occ_count (dft_occ_next a C c) =
  dft_history_counter (dft_open_next a C (dft_fill 1 c.dft_occ_core))
Proof
  simp[dft_occ_count_def, dft_occ_next_def, dft_next_inf_def, dft_erase_def] >>
  Cases_on `dft_open_next a C (dft_fill 1 c.dft_occ_core)` >>
  simp[dft_fill_def, dft_history_counter_def]
QED

Theorem dft_ordinal_invoke_counter[local,simp]:
  dft_history_counter (dft_open_invoke C fn b bb inst s stack n) = n
Proof
  simp[dft_open_invoke_def] >> CASE_TAC >> simp[dft_history_counter_def] >>
  rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >> simp[] >>
  CASE_TAC >> simp[dft_history_counter_def] >>
  CASE_TAC >> simp[dft_history_counter_def] >>
  CASE_TAC >> simp[dft_history_counter_def]
QED

Theorem dft_occ_next_count:
  dft_occ_count (dft_occ_next a C c) = dft_occ_count c +
    (if ?inst addr. dft_occ_gas_event inst addr c then 1 else 0)
Proof
  Cases_on `c.dft_occ_core` >>
  rename1 `c.dft_occ_core = DftOpen ctl stack n` >>
  Cases_on `ctl`
  >- (simp[dft_ordinal_counter_next, dft_occ_count_def,
        dft_occ_gas_event_def, dft_occ_event_def, dft_fill_def,
        dft_fill_control_def, dft_open_next_def] >>
      CASE_TAC >> simp[dft_history_counter_def] >>
      CASE_TAC >> simp[dft_history_counter_def])
  >- (simp[dft_ordinal_counter_next, dft_occ_count_def,
        dft_occ_gas_event_def, dft_occ_event_def, dft_fill_def,
        dft_fill_control_def, dft_open_next_def] >>
      Cases_on `get_instruction b v.vs_inst_idx` >> simp[dft_history_counter_def] >>
      rename1 `get_instruction _ _ = SOME inst` >>
      Cases_on `inst.inst_opcode = INVOKE` >> simp[] >>
      Cases_on `inst.inst_opcode = GAS` >> simp[] >>
      Cases_on `inst.inst_outputs` >> simp[dft_history_counter_def] >>
      Cases_on `t` >> simp[dft_history_counter_def]) >>
  simp[dft_ordinal_counter_next, dft_occ_count_def,
       dft_occ_gas_event_def, dft_occ_event_def, dft_fill_def,
       dft_fill_control_def, dft_open_next_def]
QED

Theorem dft_occ_oracle_next_count:
  dft_occ_count (dft_occ_oracle_next w C c) = dft_occ_count c +
    (if ?inst addr. dft_occ_gas_event inst addr c then 1 else 0)
Proof
  simp[dft_occ_oracle_next_def, dft_occ_next_count]
QED

Theorem dft_ordinal_iter_mono[local]:
  (!c. (height c : num) <= height (next c)) ==>
  !j k c. j <= k ==> height (FUNPOW next j c) <= height (FUNPOW next k c)
Proof
  strip_tac >>
  `!d c. height c <= height (FUNPOW next d c)` by
    (Induct >> simp[FUNPOW_SUC] >> metis_tac[LESS_EQ_TRANS]) >>
  rpt strip_tac >> `k = (k-j) + j` by decide_tac >>
  metis_tac[FUNPOW_ADD]
QED

Theorem dft_ordinal_event_strict[local]:
  (!c. (height c : num) <= height (next c)) /\
  (!c. read_event c ==> height c < height (next c)) ==>
  !j k c. j < k /\ read_event (FUNPOW next j c) ==>
  height (FUNPOW next j c) < height (FUNPOW next k c)
Proof
  strip_tac >> rpt strip_tac >>
  `height (FUNPOW next j c) < height (FUNPOW next (SUC j) c)` by
    simp[FUNPOW_SUC] >>
  `height (FUNPOW next (SUC j) c) <= height (FUNPOW next k c)` by
    (irule dft_ordinal_iter_mono >> simp[]) >>
  decide_tac
QED

Theorem dft_occ_count_mono:
  j <= k ==> dft_occ_count (FUNPOW (dft_occ_next a C) j c) <=
             dft_occ_count (FUNPOW (dft_occ_next a C) k c)
Proof
  strip_tac >> irule dft_ordinal_iter_mono >> simp[dft_occ_next_count]
QED

Theorem dft_occ_oracle_count_mono:
  j <= k ==> dft_occ_count (FUNPOW (dft_occ_oracle_next w C) j c) <=
             dft_occ_count (FUNPOW (dft_occ_oracle_next w C) k c)
Proof
  strip_tac >> irule dft_ordinal_iter_mono >> simp[dft_occ_oracle_next_count]
QED

Theorem dft_occ_gas_count_strict:
  j < k /\ dft_occ_gas_event inst addr (FUNPOW (dft_occ_next a C) j c) ==>
  dft_occ_count (FUNPOW (dft_occ_next a C) j c) <
  dft_occ_count (FUNPOW (dft_occ_next a C) k c)
Proof
  strip_tac >> irule dft_ordinal_event_strict >>
  conj_tac >- simp[dft_occ_next_count] >>
  conj_tac >- (qexists_tac `\u. dft_occ_gas_event inst addr u` >>
    simp[dft_occ_next_count] >> rpt strip_tac >>
    IF_CASES_TAC >> gvs[] >> metis_tac[]) >> simp[]
QED

Theorem dft_occ_oracle_gas_count_strict:
  j < k /\ dft_occ_gas_event inst addr (FUNPOW (dft_occ_oracle_next w C) j c) ==>
  dft_occ_count (FUNPOW (dft_occ_oracle_next w C) j c) <
  dft_occ_count (FUNPOW (dft_occ_oracle_next w C) k c)
Proof
  strip_tac >> irule dft_ordinal_event_strict >>
  conj_tac >- simp[dft_occ_oracle_next_count] >>
  conj_tac >- (qexists_tac `\u. dft_occ_gas_event inst addr u` >>
    simp[dft_occ_oracle_next_count] >> rpt strip_tac >>
    IF_CASES_TAC >> gvs[] >> metis_tac[]) >> simp[]
QED

Theorem dft_occ_gas_ordinal_unique:
  dft_occ_gas_event inst addr (FUNPOW (dft_occ_next a C) j c) /\
  dft_occ_gas_event inst' addr' (FUNPOW (dft_occ_next a C) k c) /\
  dft_occ_count (FUNPOW (dft_occ_next a C) j c) =
  dft_occ_count (FUNPOW (dft_occ_next a C) k c) ==> j = k
Proof
  strip_tac >> Cases_on `j = k` >- simp[] >>
  `j < k \/ k < j` by decide_tac >>
  drule_all dft_occ_gas_count_strict >> simp[]
QED

Theorem dft_occ_oracle_gas_ordinal_unique:
  dft_occ_gas_event inst addr (FUNPOW (dft_occ_oracle_next w C) j c) /\
  dft_occ_gas_event inst' addr' (FUNPOW (dft_occ_oracle_next w C) k c) /\
  dft_occ_count (FUNPOW (dft_occ_oracle_next w C) j c) =
  dft_occ_count (FUNPOW (dft_occ_oracle_next w C) k c) ==> j = k
Proof
  strip_tac >> Cases_on `j = k` >- simp[] >>
  `j < k \/ k < j` by decide_tac >>
  drule_all dft_occ_oracle_gas_count_strict >> simp[]
QED
