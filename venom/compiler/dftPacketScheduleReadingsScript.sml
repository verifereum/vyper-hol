Theory dftPacketScheduleReadings
Ancestors
  dftRunRel dftIndexedExec venomExecSemantics venomInst venomState
  list rich_list sorting option

Theorem scheduled_fold_snoc_ok[local]:
  EVERY (\i. ~is_terminator i.inst_opcode) pre /\
  ~is_terminator inst.inst_opcode /\
  FOLDR (dft_exec_cons n C) OK (pre ++ [inst]) be = OK s ==>
  ?u v. FOLDR (dft_exec_cons n C) OK pre be = OK u /\
    step_inst n C inst u = OK v /\ s.vs_gas_readings = v.vs_gas_readings
Proof
  strip_tac >>
  qpat_x_assum `FOLDR _ _ (pre ++ [inst]) _ = _` mp_tac >>
  simp[FOLDR_APPEND] >> simp[Once dft_exec_prefix_continue] >>
  Cases_on `FOLDR (dft_exec_cons n C) OK pre be` >> simp[] >>
  rename1 `dft_exec_cons n C inst OK u = _ ==> _` >>
  Cases_on `step_inst n C inst u` >> simp[dft_exec_cons_def] >>
  strip_tac >> gvs[]
QED

Theorem scheduled_prefix_readings[local]:
  !sched k s.
    k <= LENGTH ys /\ k <= LENGTH sched /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k ys) /\
    FOLDR (dft_exec_cons n C) OK (TAKE k ys) be = OK s /\
    (!i u v. i < k /\ FOLDR (dft_exec_cons n C) OK (TAKE i ys) be = OK u /\
      step_inst n C (EL i ys) u = OK v ==>
      PERM (MAP THE (FILTER IS_SOME (EL (EL i sched) ms)) ++ v.vs_gas_readings)
        u.vs_gas_readings) ==>
    PERM (MAP THE (FILTER IS_SOME (FLAT (MAP (\q. EL q ms) (TAKE k sched)))) ++
      s.vs_gas_readings) be.vs_gas_readings
Proof
  gen_tac >> Induct >> simp[] >> rpt strip_tac >>
  `k < LENGTH ys /\ k < LENGTH sched` by decide_tac >>
  `TAKE (SUC k) ys = TAKE k ys ++ [EL k ys]` by simp[TAKE_SUC_BY_TAKE, SNOC_APPEND] >>
  `TAKE (SUC k) sched = TAKE k sched ++ [EL k sched]` by simp[TAKE_SUC_BY_TAKE, SNOC_APPEND] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (TAKE k ys) /\
   ~is_terminator (EL k ys).inst_opcode` by fs[EVERY_APPEND] >>
  `?u v. FOLDR (dft_exec_cons n C) OK (TAKE k ys) be = OK u /\
      step_inst n C (EL k ys) u = OK v /\ s.vs_gas_readings = v.vs_gas_readings` by
    (irule scheduled_fold_snoc_ok >> fs[]) >>
  `PERM (MAP THE (FILTER IS_SOME (EL (EL k sched) ms)) ++ s.vs_gas_readings)
      u.vs_gas_readings` by (first_x_assum (qspecl_then [`k`,`u`,`v`] mp_tac) >> simp[]) >>
  `PERM (MAP THE (FILTER IS_SOME (FLAT (MAP (\q. EL q ms) (TAKE k sched)))) ++
      u.vs_gas_readings) be.vs_gas_readings` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >> metis_tac[prim_recTheory.LESS_SUC]) >>
  simp[MAP_APPEND, FLAT_APPEND, FILTER_APPEND] >>
  irule PERM_TRANS >> goal_assum (drule_at Any) >>
  rewrite_tac[GSYM APPEND_ASSOC, CONJUNCT1 PERM_APPEND_IFF] >> metis_tac[]
QED

Theorem dft_packet_schedule_readings:
  !n C ys sched ms ct be s.
    LENGTH sched = LENGTH ys /\ LENGTH ys = LENGTH ms /\ LENGTH ms = SUC ct /\
    PERM sched (COUNT_LIST (LENGTH ms)) /\ EL (EL ct sched) ms = [] /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE ct ys) /\
    FOLDR (dft_exec_cons n C) OK (TAKE ct ys) be = OK s /\
    (!i u v. i < ct /\ FOLDR (dft_exec_cons n C) OK (TAKE i ys) be = OK u /\
      step_inst n C (EL i ys) u = OK v ==>
      PERM (MAP THE (FILTER IS_SOME (EL (EL i sched) ms)) ++ v.vs_gas_readings)
        u.vs_gas_readings) ==>
    PERM (MAP THE (FILTER IS_SOME (FLAT ms)) ++ s.vs_gas_readings)
      be.vs_gas_readings
Proof
  rpt strip_tac >>
  `MAP (\q. EL q ms) (COUNT_LIST (LENGTH ms)) = ms` by
    simp[LIST_EQ_REWRITE, LENGTH_COUNT_LIST, el_map_count] >>
  `PERM (MAP (\q. EL q ms) sched) (MAP (\q. EL q ms) (COUNT_LIST (LENGTH ms)))` by
    (irule PERM_MAP >> simp[]) >>
  `PERM (MAP (\q. EL q ms) sched) ms` by metis_tac[] >>
  `PERM (MAP THE (FILTER IS_SOME (FLAT ms)) ++ s.vs_gas_readings)
        (MAP THE (FILTER IS_SOME (FLAT (MAP (\q. EL q ms) sched))) ++ s.vs_gas_readings)` by
    (simp[PERM_APPEND_IFF] >> irule PERM_MAP >> irule PERM_FILTER >>
     irule PERM_FLAT >> metis_tac[PERM_SYM]) >>
  `TAKE (SUC ct) sched = sched` by metis_tac[TAKE_LENGTH_ID] >>
  `FLAT (MAP (\q. EL q ms) sched) = FLAT (MAP (\q. EL q ms) (TAKE ct sched))` by
    (qpat_x_assum `TAKE (SUC ct) sched = sched`
       (GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) empty_rewrites o single o SYM) >>
     `ct < LENGTH sched` by decide_tac >>
     simp[TAKE_SUC_BY_TAKE, SNOC_APPEND, MAP_APPEND, FLAT_APPEND]) >>
  irule PERM_TRANS >> goal_assum (drule_at Any) >> simp[] >>
  irule scheduled_prefix_readings >> simp[] >>
  qexistsl [`C`, `n`, `ys`] >> simp[]
QED
