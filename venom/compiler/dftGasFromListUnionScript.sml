Theory dftGasFromListUnion
Ancestors
  dftGasFromListTraceNames dftGasFromListTracePrefix dftGasFromListReadings
  dftGasFromListTraceDefs list rich_list pair pred_set arithmetic

Definition recorded_def:
  recorded ctx s e w <=> ?n. MEM (e,w) (trace_gas (trace_context n ctx s))
End

Definition list_oracle_def:
  list_oracle ctx s e = if ?w. recorded ctx s e w then @w. recorded ctx s e w else 0w
End

Theorem context_gas_prefix:
  n <= m ==> ?xs. trace_gas (trace_context m ctx s) =
    trace_gas (trace_context n ctx s) ++ xs
Proof
  strip_tac >> drule trace_context_prefix >>
  disch_then (qspecl_then [`s`,`ctx`] strip_assume_tac) >>
  simp[]
QED

Theorem distinct_key_unique[local]:
  !xs e w z. ALL_DISTINCT (MAP FST xs) /\ MEM (e,w) xs /\ MEM (e,z) xs ==> w = z
Proof
  Induct >> simp[] >> Cases_on `h` >> simp[] >> rpt strip_tac >> gvs[] >>
  metis_tac[MEM_MAP, FST]
QED

Theorem recorded_functional:
  EVERY (\fn. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
    fn.fn_blocks) ctx.ctx_functions /\ recorded ctx s e w /\ recorded ctx s e z ==>
  w = z
Proof
  simp[recorded_def] >> rpt strip_tac >>
  rename1 `MEM (e,w) (trace_gas (trace_context n ctx s))` >>
  rename1 `MEM (e,z) (trace_gas (trace_context m ctx s))` >>
  `?xs. trace_gas (trace_context (MAX n m) ctx s) =
    trace_gas (trace_context n ctx s) ++ xs` by
    (irule context_gas_prefix >> simp[]) >>
  `?ys. trace_gas (trace_context (MAX n m) ctx s) =
    trace_gas (trace_context m ctx s) ++ ys` by
    (irule context_gas_prefix >> simp[]) >>
  `ALL_DISTINCT (MAP FST (trace_gas (trace_context (MAX n m) ctx s)))` by
    (irule trace_context_gas_names_distinct >> simp[]) >>
  metis_tac[distinct_key_unique, MEM_APPEND]
QED

Theorem list_oracle_recorded:
  EVERY (\fn. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
    fn.fn_blocks) ctx.ctx_functions /\ recorded ctx s e w ==>
  list_oracle ctx s e = w
Proof
  strip_tac >> simp[list_oracle_def] >>
  `?z. recorded ctx s e z` by metis_tac[] >> simp[] >>
  SELECT_ELIM_TAC >> metis_tac[recorded_functional]
QED

Theorem context_gas_index_unique:
  k < LENGTH (trace_gas (trace_context n ctx s)) /\
  k < LENGTH (trace_gas (trace_context m ctx s)) ==>
  EL k (trace_gas (trace_context n ctx s)) =
  EL k (trace_gas (trace_context m ctx s))
Proof
  strip_tac >>
  `?xs. trace_gas (trace_context (MAX n m) ctx s) =
    trace_gas (trace_context n ctx s) ++ xs` by
    (irule context_gas_prefix >> simp[]) >>
  `?ys. trace_gas (trace_context (MAX n m) ctx s) =
    trace_gas (trace_context m ctx s) ++ ys` by
    (irule context_gas_prefix >> simp[]) >>
  `EL k (trace_gas (trace_context (MAX n m) ctx s)) =
   EL k (trace_gas (trace_context n ctx s))` by metis_tac[EL_APPEND1] >>
  `EL k (trace_gas (trace_context (MAX n m) ctx s)) =
   EL k (trace_gas (trace_context m ctx s))` by metis_tac[EL_APPEND1] >>
  metis_tac[]
QED

Definition indexed_event_def:
  indexed_event ctx s k = @e. ?n.
    k < LENGTH (trace_gas (trace_context n ctx s)) /\
    e = FST (EL k (trace_gas (trace_context n ctx s)))
End

Theorem indexed_event_eq:
  k < LENGTH (trace_gas (trace_context n ctx s)) ==>
  indexed_event ctx s k = FST (EL k (trace_gas (trace_context n ctx s)))
Proof
  strip_tac >> simp[indexed_event_def] >> SELECT_ELIM_TAC >>
  conj_tac >- metis_tac[] >> rpt strip_tac >>
  metis_tac[context_gas_index_unique]
QED

Theorem list_oracle_finite:
  FINITE {e | list_oracle ctx s e <> 0w}
Proof
  irule SUBSET_FINITE >>
  qexists_tac `IMAGE (indexed_event ctx s) (count (LENGTH s.vs_gas_readings))` >>
  simp[SUBSET_DEF] >> rpt strip_tac >>
  rename1 `list_oracle ctx s e <> 0w` >>
  qpat_x_assum `list_oracle _ _ _ <> _` mp_tac >>
  simp[list_oracle_def] >>
  Cases_on `?w. recorded ctx s e w` >> simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `w <> 0w` >>
  `recorded ctx s e w` by (simp[Abbr `w`] >> metis_tac[SELECT_AX]) >>
  qpat_x_assum `recorded _ _ _ _` mp_tac >>
  simp[recorded_def, MEM_EL] >> strip_tac >>
  rename1 `k < LENGTH (trace_gas (trace_context n ctx s))` >>
  `k < LENGTH s.vs_gas_readings` by
    (irule trace_context_nonzero_bound >> qexistsl_tac [`ctx`,`n`] >> simp[] >> metis_tac[SND]) >>
  qexists_tac `k` >> simp[] >> drule indexed_event_eq >> simp[] >> metis_tac[FST]
QED

Theorem list_oracle_trace_agrees:
  EVERY (\fn. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
    fn.fn_blocks) ctx.ctx_functions ==>
  trace_agrees (list_oracle ctx s) (trace_context n ctx s)
Proof
  strip_tac >> simp[trace_agrees_def, EVERY_MEM] >>
  rpt strip_tac >> rename1 `MEM ew (trace_gas _)` >> Cases_on `ew` >> simp[] >>
  irule list_oracle_recorded >> simp[recorded_def] >> metis_tac[]
QED
