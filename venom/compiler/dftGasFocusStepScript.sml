Theory dftGasFocusStep
Ancestors
  dftGasMask dftGasFromListTraceSuccessor dftGasFromListTraceNames
  dftGasFromListReadings dftGasFromListTracePrefix dftGasFromListTraceDefs
  dftGasFromListLookup
  dftGasFromListTraceLift dftGasFromListOpenTrace frameExecutionPrefix
  dftRunRel dftIndexedExec dftBlockSim dftShape dftStructural
  gasEvents venomExecSemantics venomWf venomInst venomState
  list rich_list sorting alist arithmetic

(* One actual GAS step of the canonical chronological construction.
   Prefix compatibility and preservation of old visits also preserve the
   separately retained historical call joins; no call entry is reselected. *)
Theorem dft_gas_occurrence_prefix_step:
  !row_order.
  EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
    f.fn_blocks) C8.ctx_functions /\
  j < LENGTH (trace_context N C8 vs0) /\
  EL j (trace_context N C8 vs0) = ((p,d,inst.inst_id),fn,inst,s) /\
  obs = trace_gas (TAKE j (trace_context N C8 vs0)) /\
  vs0.vs_gas_readings = MAP SND obs ++ s.vs_gas_readings /\
  wf_function fn /\ active_inst fn inst s /\
  inst.inst_opcode = GAS /\ inst.inst_outputs = [out] /\
  s.vs_gas_readings = w::rest /\
  z = (update_var out w (s with vs_gas_readings := rest)) with
    vs_inst_idx := SUC s.vs_inst_idx /\
  active_inst fn next z /\
  bb.bb_instructions = pseudos ++ xs /\
  bb'.bb_instructions = pseudos ++ ys /\
  lookup_block be.vs_current_bb source_fn.fn_blocks = SOME bb /\
  lookup_block be.vs_current_bb fn.fn_blocks = SOME bb' /\
  s.vs_current_bb = be.vs_current_bb /\
  be.vs_inst_idx = LENGTH pseudos /\
  LENGTH pseudos <= s.vs_inst_idx /\
  get_instruction bb' s.vs_inst_idx = SOME inst /\
  h0 <= j /\
  get_instruction bb' be.vs_inst_idx = SOME first /\
  EL h0 (trace_context N C8 vs0) = ((p,d,first.inst_id),fn,first,be) /\
  PERM row_order (COUNT_LIST (LENGTH xs)) /\
  LIST_REL (\q y. q < LENGTH xs /\
    y.inst_id = (EL q xs).inst_id /\ from_block [EL q xs] y) row_order ys /\
  ALL_DISTINCT (MAP (\i. i.inst_id) xs) /\
  done = TAKE (s.vs_inst_idx - LENGTH pseudos) row_order /\
  (!F. N <= F ==>
    FOLDR (dft_exec_cons F C8) OK
      (TAKE (s.vs_inst_idx - LENGTH pseudos) ys) be = OK s) /\
  LENGTH ms = LENGTH xs /\
  LIST_REL (\m es. LENGTH m = LENGTH es) ms ess /\
  (!q. q < LENGTH xs /\ (EL q xs).inst_opcode = GAS ==>
    EL q ms = [ALOOKUP obs (p,d,(EL q xs).inst_id)] /\
    EL q ess = [(source_fn.fn_name,(EL q xs).inst_id)]) /\
  (!F k kgss tail.
    N <= F /\ k <= LENGTH xs /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
    (!q. q < k /\ (EL q xs).inst_opcode = INVOKE ==> MEM q done) /\
    LIST_REL (LIST_REL (\slot x. slot = NONE \/ slot = SOME x))
      (TAKE k ms) kgss ==>
    (?extra. FLAT (TAKE k ess) =
      gas_events_block F C7 source_fn.fn_name
        <|bb_label := be.vs_current_bb; bb_instructions :=
          REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
        (be with vs_gas_readings := FLAT kgss ++ tail) ++ extra) /\
    (!u. FOLDR (dft_exec_cons F C7) OK (TAKE k xs)
        (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
      gas_events_block F C7 source_fn.fn_name
        <|bb_label := be.vs_current_bb; bb_instructions :=
          REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
        (be with vs_gas_readings := FLAT kgss ++ tail) = FLAT (TAKE k ess) /\
      u.vs_gas_readings = tail /\
      !tail'. FOLDR (dft_exec_cons F C7) OK (TAKE k xs)
          (be with vs_gas_readings := FLAT kgss ++ tail') =
          OK (u with vs_gas_readings := tail') /\
        gas_events_block F C7 source_fn.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
          (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess))) ==>
  !b. ?M q ms' obs'.
    MAX N b <= M /\
    q = EL (s.vs_inst_idx - LENGTH pseudos) row_order /\
    q < LENGTH xs /\ EL q xs = inst /\
    SUC j < LENGTH (trace_context M C8 vs0) /\
    EL (SUC j) (trace_context M C8 vs0) = ((p,d,next.inst_id),fn,next,z) /\
    (!h. h <= j ==>
      EL h (trace_context M C8 vs0) = EL h (trace_context N C8 vs0)) /\
    obs' = trace_gas (TAKE (SUC j) (trace_context M C8 vs0)) /\
    obs' = obs ++ [((p,d,inst.inst_id),w)] /\
    vs0.vs_gas_readings = MAP SND obs' ++ z.vs_gas_readings /\
    (!entry. execution_prefix C8 fn entry inst s ==>
      execution_prefix C8 fn entry next z) /\
    (!d0 fuel entry.
      MEM ((p,d,inst.inst_id),fn,inst,s)
        (trace_blocks p d0 fuel C8 fn entry) ==>
      ?fuel'. MEM ((p,d,next.inst_id),fn,next,z)
        (trace_blocks p d0 fuel' C8 fn entry)) /\
    EL q ms = [NONE] /\
    EL q ess = [(source_fn.fn_name,inst.inst_id)] /\
    ms' = LUPDATE [SOME w] q ms /\
    LENGTH ms' = LENGTH xs /\
    LIST_REL (\m es. LENGTH m = LENGTH es) ms' ess /\
    PERM (MAP THE (FILTER IS_SOME (FLAT ms')))
      (MAP THE (FILTER IS_SOME (FLAT ms)) ++ [w]) /\
    (!r. r < LENGTH xs /\ (EL r xs).inst_opcode = GAS ==>
      EL r ms' = [ALOOKUP obs' (p,d,(EL r xs).inst_id)] /\
      EL r ess = [(source_fn.fn_name,(EL r xs).inst_id)]) /\
    (!k kgss. k <= LENGTH xs /\
      LIST_REL (LIST_REL (\slot x. slot = NONE \/ slot = SOME x))
        (TAKE k ms') kgss ==>
      LIST_REL (LIST_REL (\slot x. slot = NONE \/ slot = SOME x))
        (TAKE k ms) kgss) /\
    TAKE (z.vs_inst_idx - LENGTH pseudos) row_order = done ++ [q] /\
    (!F. M <= F ==>
      FOLDR (dft_exec_cons F C8) OK
        (TAKE (z.vs_inst_idx - LENGTH pseudos) ys) be = OK z) /\
    (!c us. c.inst_opcode = INVOKE /\ dft_gas_swap_pair inst c /\
      EVERY (\uw. ~MEM (Var (FST uw)) c.inst_operands /\
        ~MEM (FST uw) c.inst_outputs) us ==>
      EVERY (\uw. ~MEM (Var (FST uw)) c.inst_operands /\
        ~MEM (FST uw) c.inst_outputs) (us ++ [(out,w)]) /\
      !a. FOLDL (\t uw. update_var (FST uw) (SND uw) t) a (us ++ [(out,w)]) =
        update_var out w (FOLDL (\t uw. update_var (FST uw) (SND uw) t) a us)) /\
    !F k kgss tail.
      M <= F /\ k <= LENGTH xs /\
      EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k xs) /\
      (!r. r < k /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (done ++ [q])) /\
      LIST_REL (LIST_REL (\slot x. slot = NONE \/ slot = SOME x))
        (TAKE k ms') kgss ==>
      (?extra. FLAT (TAKE k ess) =
        gas_events_block F C7 source_fn.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
          (be with vs_gas_readings := FLAT kgss ++ tail) ++ extra) /\
      (!u. FOLDR (dft_exec_cons F C7) OK (TAKE k xs)
          (be with vs_gas_readings := FLAT kgss ++ tail) = OK u ==>
        gas_events_block F C7 source_fn.fn_name
          <|bb_label := be.vs_current_bb; bb_instructions :=
            REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
          (be with vs_gas_readings := FLAT kgss ++ tail) = FLAT (TAKE k ess) /\
        u.vs_gas_readings = tail /\
        !tail'. FOLDR (dft_exec_cons F C7) OK (TAKE k xs)
            (be with vs_gas_readings := FLAT kgss ++ tail') =
            OK (u with vs_gas_readings := tail') /\
          gas_events_block F C7 source_fn.fn_name
            <|bb_label := be.vs_current_bb; bb_instructions :=
              REPLICATE be.vs_inst_idx (mk_inst 0 STOP [] []) ++ TAKE k xs|>
            (be with vs_gas_readings := FLAT kgss ++ tail') = FLAT (TAKE k ess))
Proof
  gen_tac >> strip_tac >>
  qabbrev_tac `t = s.vs_inst_idx - LENGTH pseudos` >>
  `t < LENGTH ys /\ EL t ys = inst` by
    (qpat_x_assum `get_instruction bb' s.vs_inst_idx = SOME inst` mp_tac >>
     simp[get_instruction_def] >> strip_tac >>
     gvs[EL_APPEND_EQN, Abbr `t`]) >>
  `LENGTH row_order = LENGTH ys /\ LENGTH row_order = LENGTH xs` by
    metis_tac[LIST_REL_LENGTH, PERM_LENGTH, LENGTH_COUNT_LIST] >>
  qabbrev_tac `q = EL t row_order` >>
  `q < LENGTH xs /\ inst.inst_id = (EL q xs).inst_id /\
    from_block [EL q xs] inst` by
    (qpat_x_assum `LIST_REL _ row_order ys` mp_tac >>
     simp[LIST_REL_EL_EQN] >> strip_tac >>
     first_x_assum (qspec_then `t` mp_tac) >> simp[Abbr `q`]) >>
  `EL q xs = inst` by
    (qpat_x_assum `from_block [EL q xs] inst` mp_tac >>
     simp[from_block_def] >> strip_tac >> gvs[] >>
     drule flip_operands_special_opcode >> simp[]) >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    simp[is_terminator_def] >>
  `step_inst 0 C8 inst s = OK (update_var out w (s with vs_gas_readings := rest))` by
    (mp_tac (Q.INST [`fuel` |-> `0`, `ctx` |-> `C8`, `s` |-> `s`,
       `inst` |-> `inst`, `x` |-> `out`]
      (SPEC_ALL dftBlockSimTheory.step_inst_gas_single)) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     qpat_assum `s.vs_gas_readings = w::rest`
       (fn reads => simp_tac (srw_ss()) [reads])) >>
  `ALL_DISTINCT (MAP FST (trace_context N C8 vs0))` by
    metis_tac[trace_context_names_distinct] >>
  `ALOOKUP obs (p,d,inst.inst_id) = NONE` by suspend "fresh" >>
  `EL q ms = [NONE] /\ EL q ess = [(source_fn.fn_name,inst.inst_id)]` by
    metis_tac[] >>
  qabbrev_tac `ms' = LUPDATE [SOME w] q ms` >>
  `LENGTH ms' = LENGTH xs /\ LIST_REL (\m es. LENGTH m = LENGTH es) ms' ess /\
    PERM (MAP THE (FILTER IS_SOME (FLAT ms')))
      (MAP THE (FILTER IS_SOME (FLAT ms)) ++ [w])` by suspend "rows" >>
  `!k kgss. k <= LENGTH xs /\
    LIST_REL (LIST_REL (\slot x. slot = NONE \/ slot = SOME x))
      (TAKE k ms') kgss ==>
    LIST_REL (LIST_REL (\slot x. slot = NONE \/ slot = SOME x))
      (TAKE k ms) kgss` by suspend "prefix_compat" >>
  gen_tac >>
  mp_tac (Q.INST [`ctx` |-> `C8`, `n` |-> `N`, `t` |-> `s`,
    `u` |-> `update_var out w (s with vs_gas_readings := rest)`,
    `f` |-> `0`] (SPEC_ALL trace_context_next_cut)) >>
  (impl_tac >- metis_tac[]) >>
  disch_then (qspec_then `b` (qx_choose_then `M` strip_assume_tac)) >>
  `N <= M` by
    (qpat_x_assum `MAX N b <= M` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[MAX_DEF] >> rw[] >> decide_tac) >>
  qabbrev_tac `obs' = obs ++ [((p,d,inst.inst_id),w)]` >>
  qexistsl_tac [`M`, `q`, `ms'`, `obs'`] >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- simp[Abbr `q`, Abbr `t`]
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- metis_tac[]
  >- suspend "history"
  >- suspend "observations"
  >- simp[Abbr `obs'`]
  >- suspend "readings"
  >- suspend "execution_prefix"
  >- suspend "local_trace"
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- simp[Abbr `ms'`]
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- suspend "row_observations"
  >- first_assum ACCEPT_TAC
  >- suspend "done"
  >- suspend "actual_prefix"
  >- suspend "pending"
  >> suspend "source_prefix"
QED

Resume dft_gas_occurrence_prefix_step[fresh]:
  `trace_context N C8 vs0 = TAKE j (trace_context N C8 vs0) ++
    ((p,d,inst.inst_id),fn,inst,s)::DROP (SUC j) (trace_context N C8 vs0)` by
    (qpat_assum `j < LENGTH (trace_context N C8 vs0)`
       (mp_tac o MATCH_MP rich_listTheory.TAKE_DROP_SUC) >>
     qpat_assum `EL j (trace_context N C8 vs0) = _`
       (fn visit => simp_tac pure_ss [visit, APPEND, GSYM APPEND_ASSOC]) >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `~MEM (p,d,inst.inst_id) (MAP FST (TAKE j (trace_context N C8 vs0)))` by
    (qpat_assum `trace_context N C8 vs0 = _` (fn decomp =>
       qpat_x_assum `ALL_DISTINCT (MAP FST _)`
         (mp_tac o ONCE_REWRITE_RULE [decomp])) >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[MAP_APPEND, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `~MEM (p,d,inst.inst_id) (MAP FST obs)` by
    metis_tac[trace_gas_name_mem] >>
  simp[ALOOKUP_NONE]
QED

Resume dft_gas_occurrence_prefix_step[rows]:
  mp_tac (Q.INST [`j` |-> `q`, `unused` |-> `[]`,
    `initial_readings` |-> `MAP THE (FILTER IS_SOME (FLAT ms)) ++ [w]`]
    (INST_TYPE [``:'a`` |-> ``:bytes32``,
      ``:'b`` |-> ``:string # num``]
      (SPEC_ALL occurrence_packet_gas_refinement))) >>
  simp[Abbr `ms'`] >> metis_tac[LIST_REL_LENGTH, LENGTH_LUPDATE]
QED

Resume dft_gas_occurrence_prefix_step[prefix_compat]:
  rpt gen_tac >> strip_tac >>
  `k <= LENGTH ms` by metis_tac[] >>
  qunabbrev_tac `ms'` >>
  qpat_x_assum `LIST_REL _ (TAKE k (LUPDATE _ _ _)) kgss` mp_tac >>
  qpat_assum `EL q ms = [NONE]` mp_tac >>
  qpat_assum `k <= LENGTH ms` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  strip_tac >> simp[LIST_REL_EL_EQN] >> strip_tac >> strip_tac >>
  qpat_x_assum `k = LENGTH kgss` SUBST_ALL_TAC >>
  qx_gen_tac `n` >> strip_tac >>
  qpat_x_assum `!n. n < LENGTH kgss ==> _`
    (qspec_then `n` mp_tac) >>
  simp[EL_TAKE, EL_LUPDATE] >>
  Cases_on `n = q` >> gvs[LIST_REL_CONS1]
QED

Resume dft_gas_occurrence_prefix_step[history]:
  rpt strip_tac >> irule trace_context_visit_preserved >>
  metis_tac[LESS_EQ_LESS_TRANS]
QED

Resume dft_gas_occurrence_prefix_step[observations]:
  qunabbrev_tac `obs'` >>
  qpat_assum `TAKE (SUC j) (trace_context M C8 vs0) = _`
    (fn cut => pure_rewrite_tac[cut, trace_gas_append]) >>
  qpat_assum `obs = trace_gas _` (SUBST1_TAC o SYM) >>
  qpat_assum `inst.inst_opcode = GAS` mp_tac >>
  qpat_assum `s.vs_gas_readings = w::rest` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[trace_gas_def, visit_gas_def]
QED

Resume dft_gas_occurrence_prefix_step[readings]:
  simp[Abbr `obs'`, update_var_def, MAP_APPEND, APPEND_ASSOC]
QED

Resume dft_gas_occurrence_prefix_step[execution_prefix]:
  rpt strip_tac >>
  qpat_x_assum `z = _` SUBST_ALL_TAC >>
  irule execution_prefix_next >> goal_assum (drule_at Any) >>
  metis_tac[]
QED

Resume dft_gas_occurrence_prefix_step[local_trace]:
  rpt strip_tac >>
  drule (cj 3 trace_cofinal) >>
  disch_then (qx_choose_then `local_bb` strip_assume_tac) >>
  `s.vs_current_bb = z.vs_current_bb` by simp[update_var_def] >>
  `get_instruction local_bb z.vs_inst_idx = SOME next` by
    (mp_tac (Q.INST [`fn` |-> `fn`, `inst` |-> `next`, `s` |-> `z`]
       (SPEC_ALL wf_active_lookup)) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (qx_choose_then `next_bb` strip_assume_tac) >> metis_tac[]) >>
  `MEM ((p,d,next.inst_id),fn,next,z)
    (open_trace p d 0 C8 fn local_bb s)` by
    (drule_all open_trace_next >>
     disch_then (qspecl_then [`p`,`fn`,`d`] SUBST1_TAC) >>
     simp[open_trace_def, trace_step_noninvoke, Once (cj 2 trace_defs)]) >>
  qpat_x_assum `!k b. ?m. _` (qspecl_then [`0`,`0`] strip_assume_tac) >>
  metis_tac[]
QED

Resume dft_gas_occurrence_prefix_step[row_observations]:
  rpt strip_tac >>
  `EL r ms = [ALOOKUP obs (p,d,(EL r xs).inst_id)] /\
    EL r ess = [(source_fn.fn_name,(EL r xs).inst_id)]` by metis_tac[] >>
  Cases_on `r = q` >> simp[Abbr `ms'`, Abbr `obs'`, EL_LUPDATE, ALOOKUP_APPEND]
  >- gvs[] >>
  `(EL r xs).inst_id <> inst.inst_id` by
    (qpat_x_assum `ALL_DISTINCT (MAP (\i. i.inst_id) xs)` mp_tac >>
     simp[ALL_DISTINCT_EL_IMP, EL_MAP] >> metis_tac[]) >> simp[]
QED

Resume dft_gas_occurrence_prefix_step[done]:
  `z.vs_inst_idx - LENGTH pseudos = SUC t` by
    simp[Abbr `t`, update_var_def] >>
  simp[TAKE_SUC, Abbr `q`, Abbr `t`]
QED

Resume dft_gas_occurrence_prefix_step[actual_prefix]:
  `EVERY (\i. ~is_terminator i.inst_opcode) (TAKE t ys)` by suspend "nonterm" >>
  `TAKE (z.vs_inst_idx - LENGTH pseudos) ys = TAKE t ys ++ [inst]` by
    simp[Abbr `t`, update_var_def, TAKE_SUC] >>
  rpt strip_tac >>
  `FOLDR (dft_exec_cons F C8) OK (TAKE t ys) be = OK s` by
    (qpat_x_assum `!F. N <= F ==> _` (qspec_then `F` mp_tac) >>
     simp[Abbr `t`] >> metis_tac[LESS_EQ_TRANS]) >>
  simp[FOLDR_APPEND, Once dft_exec_prefix_continue,
    dft_exec_cons_def, step_inst_gas_single]
QED

Resume dft_gas_occurrence_prefix_step[nonterm]:
  `bb_well_formed bb'` by
    metis_tac[wf_function_def, lookup_block_def, FIND_MEM] >>
  fs[EVERY_EL, LENGTH_TAKE, bb_well_formed_def] >>
  rpt strip_tac >>
  `LENGTH pseudos + n < LENGTH bb'.bb_instructions /\
    EL (LENGTH pseudos + n) bb'.bb_instructions = EL n ys` by
    simp[EL_APPEND_EQN] >>
  `LENGTH pseudos + n = PRE (LENGTH bb'.bb_instructions)` by metis_tac[] >>
  `s.vs_inst_idx < LENGTH bb'.bb_instructions` by
    gvs[get_instruction_def] >>
  fs[Abbr `t`] >> decide_tac
QED

Resume dft_gas_occurrence_prefix_step[pending]:
  rpt strip_tac >>
  `~MEM (Var out) c.inst_operands /\ ~MEM out c.inst_outputs` by
    metis_tac[dft_swap_output_frame, MEM] >>
  simp[EVERY_APPEND, FOLDL_APPEND]
QED

Resume dft_gas_occurrence_prefix_step[source_prefix]:
  rpt gen_tac >> strip_tac >>
  `!r. r < k /\ (EL r xs).inst_opcode = INVOKE ==> MEM r done` by
    (rpt strip_tac >>
     `MEM r (done ++ [q])` by metis_tac[] >>
     fs[MEM_APPEND] >> metis_tac[]) >>
  qpat_x_assum `!F k kgss tail. N <= F /\ _ ==> _`
    (qspecl_then [`F`, `k`, `kgss`, `tail`] mp_tac) >>
  (impl_tac >- metis_tac[LESS_EQ_TRANS]) >> simp[]
QED

Finalise dft_gas_occurrence_prefix_step
