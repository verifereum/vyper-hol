Theory requestCutKeyedPrefix
Ancestors
  dftGasFromListTraceDefs dftGasFromListReadings gasOracleReplay
  venomState list rich_list arithmetic

Theorem take_map_prefix[local]:
  !xs. TAKE (LENGTH xs) (MAP f xs ++ ys) = MAP f xs
Proof
  Induct >> simp[]
QED

(* Once the packet identifies the reached dynamic keys, native trace
   replay fixes their values from the selected tape. *)
Theorem request_cut_native_keyed_prefix_zip:
  s = (root with vs_gas_readings := gs ++ tail) /\
  hist = trace_gas (trace_blocks p d fuel C fn s) /\
  keys = MAP FST hist ++ rest /\ LENGTH gs = LENGTH keys ==>
  ?l. l <= LENGTH keys /\
      hist = ZIP (TAKE l keys,TAKE l gs)
Proof
  strip_tac >>
  `LENGTH hist <= LENGTH keys /\ LENGTH hist <= LENGTH gs` by simp[] >>
  `MAP SND hist = gas_prefix (LENGTH hist) (gs ++ tail)` by
    (qpat_assum `hist = _` (fn th => PURE_REWRITE_TAC [th]) >>
     simp[cj 3 trace_gas_lengths, cj 3 trace_gas_readings]) >>
  `MAP SND hist = TAKE (LENGTH hist) gs` by
    (qpat_assum `MAP SND hist = gas_prefix _ _` SUBST1_TAC >>
     simp[gas_prefix_def, TAKE_APPEND1, APPEND_ASSOC]) >>
  `TAKE (LENGTH hist) keys = MAP FST hist` by
    (qpat_assum `keys = _` SUBST1_TAC >> simp[take_map_prefix]) >>
  qexists_tac `LENGTH hist` >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `TAKE (LENGTH hist) keys = _` SUBST1_TAC >>
  qpat_assum `MAP SND hist = TAKE _ _` (SUBST1_TAC o SYM) >>
  simp_tac std_ss [ZIP_MAP_MAP, pairTheory.PAIR, MAP_ID]
QED
