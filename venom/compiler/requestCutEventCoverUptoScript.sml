Theory requestCutEventCoverUpto
Ancestors
  requestCutEventPrefix requestCutNativeEventCover requestCutNativeTraceOrder
  dftGasFromListRestore dftGasFromListTraceDefs dftGasFromListReplayBoundary
  dftGasToListTrace dftGasToListFuel dftGasToListReachWitness dftGasOracleDefs
  contextCodegenRel passSimulationDefs venomExecSemantics venomInst venomState
  list rich_list arithmetic

val nativeItems = ``\ws (rows:list_visit list).
  FLAT (MAP (\((p,d,id),fn,i,s).
    TraceVisit p d fn i (s with vs_gas_readings := ws) ::
    if i.inst_opcode = GAS then [TraceGas (p,d,id)] else []) rows)``;
val nativeVisit = ``\ws ((p,d,id:num),fn,i,s). TraceVisit p d fn i (s with vs_gas_readings := ws)``;
val selectVisit = ``\row. case row of TraceVisit _ _ _ _ _ => T | _ => F``;

Theorem native_items_visits[local,simp]:
  !rows ws. FILTER ^selectVisit (^nativeItems ws rows) = MAP (^nativeVisit ws) rows
Proof
  BETA_TAC >> Induct >> simp[] >>
  gen_tac >> PairCases_on `h` >> gen_tac >>
  Cases_on `h4.inst_opcode = GAS` >> simp[]
QED

Theorem projected_prefix_agree[local]:
  MAP f before <<= MAP f rows ==>
  LENGTH before <= LENGTH rows /\
  !n. n < LENGTH before ==> f (EL n before) = f (EL n rows)
Proof
  strip_tac >> drule IS_PREFIX_LENGTH >> simp[] >> strip_tac >> simp[] >>
  fs[IS_PREFIX_APPEND] >> rpt strip_tac >>
  qpat_assum `MAP f rows = _` (mp_tac o Q.AP_TERM `EL n`) >>
  simp[EL_MAP, EL_APPEND1]
QED

Theorem projected_visits_prefix[local]:
  ^nativeItems ws before <<= ^nativeItems ws rows ==>
  MAP (^nativeVisit ws) before <<= MAP (^nativeVisit ws) rows
Proof
  simp[IS_PREFIX_APPEND] >> strip_tac >>
  pop_assum (mp_tac o Q.AP_TERM `FILTER ^selectVisit`) >>
  simp[FILTER_APPEND, BETA_RULE native_items_visits] >>
  metis_tac[]
QED

(* A recording step on the agreed prefix bounds every event visit at the
   same request cut, even when the native source's later GAS keys differ. *)
Theorem request_cut_native_event_cover_upto:
  EVERY wf_function C.ctx_functions /\
  EVERY (\fn. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)) fn.fn_blocks)
    C.ctx_functions /\
  dftGasFromListTraceDefs$trace_context fuel C (initial with vs_gas_readings := filling) =
    pre ++ ((p,d,i.inst_id),fn,i,s)::after /\
  trace_agrees orc pre /\ i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
  step_inst n C i s = OK u /\ k < LENGTH u.vs_requests /\
  ev_reachable orc initial C a e g inst t /\ LENGTH t.vs_requests <= k ==>
  ?ws. raw_reachable (initial with vs_gas_readings := filling) C g inst (t with vs_gas_readings := ws)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `ev_reachable orc initial C a e g inst t`
    (mp_tac o MATCH_MP ev_reachable_trace_item) >>
  simp[] >> disch_then (qx_choose_then `m` assume_tac) >>
  qabbrev_tac `bound = MAX fuel m` >>
  qabbrev_tac `trace = dftGasToListTrace$trace_context orc bound C initial` >>
  `MEM (TraceVisit a e g inst t) trace` by
    (mp_tac (Q.INST [`ctx` |-> `C`, `s` |-> `initial`, `fuel` |-> `m`, `larger` |-> `bound`]
      trace_context_fuel_extension) >>
     simp[Abbr `bound`, trace_extension_def] >> strip_tac >>
     simp[Abbr `trace`, MEM_APPEND]) >>
  qabbrev_tac `past = pre ++ [((p,d,i.inst_id),fn,i,s)]` >>
  `past <<= dftGasFromListTraceDefs$trace_context fuel C (initial with vs_gas_readings := filling) /\
   trace_agrees orc past` by simp[Abbr `past`, trace_agrees_cons, visit_gas_def] >>
  `^nativeItems initial.vs_gas_readings past <<= trace` by
    (irule IS_PREFIX_TRANS >>
     qexists_tac `dftGasToListTrace$trace_context orc fuel C initial` >>
     conj_tac >~ [`_ <<= trace`]
     >- (mp_tac (Q.INST [`ctx` |-> `C`, `s` |-> `initial`, `larger` |-> `bound`]
          trace_context_fuel_extension) >>
         simp[Abbr `bound`, trace_extension_def, IS_PREFIX_APPEND, Abbr `trace`]) >>
     mp_tac (Q.INST [`s` |-> `initial`, `pre` |-> `past`]
       request_cut_native_context_event_prefix) >> simp[]) >>
  mp_tac (Q.INST [`C` |-> `C`, `fuel` |-> `bound`, `v` |-> `initial`, `orc` |-> `orc`]
    request_cut_canonical_native_trace) >>
  qpat_assum `Abbrev (trace = _)`
    (fn eq => PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] eq)]) >>
  disch_then (qx_choose_then `readings` assume_tac) >>
  qabbrev_tac `rows = dftGasFromListTraceDefs$trace_context bound C
    (initial with vs_gas_readings := readings)` >>
  `MAP (^nativeVisit initial.vs_gas_readings) past <<=
    MAP (^nativeVisit initial.vs_gas_readings) rows` by
    (irule projected_visits_prefix >> metis_tac[]) >>
  drule projected_prefix_agree >> strip_tac >>
  `?j. j < LENGTH rows /\ ^nativeVisit initial.vs_gas_readings (EL j rows) =
     TraceVisit a e g inst t` by
    (`MEM (TraceVisit a e g inst t) (FILTER ^selectVisit trace)` by simp[MEM_FILTER] >>
     qpat_assum `trace = _` (fn eq => RULE_ASSUM_TAC (REWRITE_RULE [eq])) >>
     fs[BETA_RULE native_items_visits, MEM_EL, EL_MAP] >> metis_tac[]) >>
  `LENGTH pre < LENGTH past /\ LENGTH pre < LENGTH rows` by fs[Abbr `past`] >>
  `EL (LENGTH pre) past = ((p,d,i.inst_id),fn,i,s)` by simp[Abbr `past`, EL_APPEND_EQN] >>
  `^nativeVisit initial.vs_gas_readings (EL (LENGTH pre) rows) =
     TraceVisit p d fn i (s with vs_gas_readings := initial.vs_gas_readings)` by
    (first_x_assum (qspec_then `LENGTH pre` mp_tac) >> simp[]) >>
  `?key x. EL (LENGTH pre) rows = (key,fn,i,x) /\
    x with vs_gas_readings := initial.vs_gas_readings =
    s with vs_gas_readings := initial.vs_gas_readings` by
    (qabbrev_tac `row = EL (LENGTH pre) rows` >> PairCases_on `row` >> gvs[] >> metis_tac[]) >>
  `?key y. EL j rows = (key,g,inst,y) /\
    t = (y with vs_gas_readings := initial.vs_gas_readings)` by
    (qabbrev_tac `row = EL j rows` >> PairCases_on `row` >> gvs[] >> metis_tac[]) >>
  `x = (s with vs_gas_readings := x.vs_gas_readings)` by
    (qpat_assum `x with vs_gas_readings := _ = _`
       (mp_tac o Q.AP_TERM `\z. z with vs_gas_readings := x.vs_gas_readings`) >>
     simp[venom_state_component_equality]) >>
  `step_inst n C i x = OK (u with vs_gas_readings := x.vs_gas_readings)` by
    (mp_tac (Q.INST [`inst` |-> `i`, `gs` |-> `x.vs_gas_readings`] step_base_restore) >>
     qpat_x_assum `step_inst n C i s = OK u` mp_tac >>
     simp[step_inst_non_invoke, restore_rel_cases] >> metis_tac[]) >>
  `j <= LENGTH pre` by
    (spose_not_then assume_tac >> `LENGTH pre < j` by decide_tac >>
     mp_tac (Q.INST [`a` |-> `LENGTH (pre:list_visit list)`, `b` |-> `j`,
       `v` |-> `initial with vs_gas_readings := readings`, `s` |-> `x`, `t` |-> `y`,
       `fuel` |-> `bound`, `key` |-> `key`, `key'` |-> `key'`,
       `fn'` |-> `g`, `i'` |-> `inst`, `u` |-> `u with vs_gas_readings := x.vs_gas_readings`]
       native_trace_requests_after_step) >>
     (impl_tac >- (rpt conj_tac >> simp[Abbr `rows`])) >> fs[]) >>
  `j < LENGTH past` by fs[Abbr `past`] >>
  `^nativeVisit initial.vs_gas_readings (EL j past) = TraceVisit a e g inst t` by
    (qpat_assum `!n. n < LENGTH past ==> _` (qspec_then `j` mp_tac) >> simp[]) >>
  `?id z. EL j past = ((a,e,id),g,inst,z) /\
    t = (z with vs_gas_readings := initial.vs_gas_readings)` by
    (qabbrev_tac `row = EL j past` >> PairCases_on `row` >> gvs[] >> metis_tac[]) >>
  `?before after'.
    dftGasFromListTraceDefs$trace_context fuel C (initial with vs_gas_readings := filling) =
      before ++ ((a,e,id),g,inst,z)::after'` by
    (qexistsl_tac [`TAKE j past`, `DROP (SUC j) past ++ after`] >>
     `DROP j past = ((a,e,id),g,inst,z)::DROP (SUC j) past` by
       simp[Once DROP_EL_CONS, GSYM arithmeticTheory.ADD1] >>
     `past = TAKE j past ++ ((a,e,id),g,inst,z)::DROP (SUC j) past` by
       metis_tac[TAKE_DROP] >>
     qpat_assum `trace_context _ _ _ = _` SUBST1_TAC >>
     qpat_assum `Abbrev (past = _)` (mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     metis_tac[APPEND_ASSOC, APPEND]) >>
  drule_all request_cut_native_trace_reachable >> strip_tac >>
  `t with vs_gas_readings := z.vs_gas_readings = z` by
    fs[venom_state_component_equality] >>
  qexists_tac `z.vs_gas_readings` >> simp[]
QED
