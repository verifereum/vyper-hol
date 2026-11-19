Theory dftPacketNativeSlice
Ancestors
  dftGasFromListTraceDefs dftIndexedExec rich_list list venomInst venomState

Theorem native_trace_block_prefix_split:
  !k s t.
    s.vs_inst_idx + k <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode)
      (TAKE k (DROP s.vs_inst_idx bb.bb_instructions)) /\
    FOLDR (dft_exec_cons fuel C) OK
      (TAKE k (DROP s.vs_inst_idx bb.bb_instructions)) s = OK t ==>
    t.vs_inst_idx = s.vs_inst_idx + k /\
    trace_block p d fuel C fn bb s =
      trace_block p d fuel C fn
        (bb with bb_instructions := TAKE (s.vs_inst_idx + k) bb.bb_instructions) s ++
      trace_block p d fuel C fn bb t
Proof
  Induct_on `k`
  >- (simp[] >> rpt strip_tac >>
      simp[Once trace_defs, get_instruction_def, LENGTH_TAKE]) >>
  rpt gen_tac >> strip_tac >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >>
  `DROP s.vs_inst_idx bb.bb_instructions =
    EL s.vs_inst_idx bb.bb_instructions ::
    DROP (SUC s.vs_inst_idx) bb.bb_instructions` by
      simp[DROP_CONS_EL] >>
  gvs[TAKE_def, dft_exec_cons_def, AllCaseEqs()] >>
  first_x_assum (qspec_then `t' with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (EL s.vs_inst_idx bb.bb_instructions)` by simp[get_instruction_def] >>
  `get_instruction
      (bb with bb_instructions := TAKE (SUC k + s.vs_inst_idx) bb.bb_instructions)
      s.vs_inst_idx = SOME (EL s.vs_inst_idx bb.bb_instructions)` by
    simp[get_instruction_def, EL_TAKE] >>
  drule trace_block_visit >>
  disch_then (qspecl_then [`p`,`fuel`,`fn`,`d`,`C`] assume_tac) >>
  qpat_x_assum `get_instruction (_ with bb_instructions := _) _ = _` kall_tac >>
  drule trace_block_visit >>
  disch_then (qspecl_then [`p`,`fuel`,`fn`,`d`,`C`] assume_tac) >>
  gvs[arithmeticTheory.ADD_CLAUSES, APPEND_ASSOC]
QED

Theorem native_trace_embedded_prefix_cut:
  s.vs_inst_idx + k <= LENGTH bb.bb_instructions /\
  EVERY (\i. ~is_terminator i.inst_opcode)
    (TAKE k (DROP s.vs_inst_idx bb.bb_instructions)) /\
  FOLDR (dft_exec_cons fuel C) OK
    (TAKE k (DROP s.vs_inst_idx bb.bb_instructions)) s = OK t /\
  ALL_DISTINCT (MAP FST R) /\ h <= LENGTH R /\
  R = TAKE h R ++ trace_block p d fuel C fn bb s ++ rest /\
  get_instruction bb t.vs_inst_idx = SOME i /\
  j < LENGTH R /\ EL j R = ((p,d,i.inst_id),fn,i,t) ==>
  TAKE j R = TAKE h R ++
    trace_block p d fuel C fn
      (bb with bb_instructions := TAKE (s.vs_inst_idx + k) bb.bb_instructions) s
Proof
  rpt strip_tac >>
  drule_all native_trace_block_prefix_split >>
  disch_then (qspecl_then [`p`,`fn`,`d`] strip_assume_tac) >>
  qmatch_goalsub_abbrev_tac `TAKE h R ++ pref` >>
  `?suffix. trace_block p d fuel C fn bb t =
    ((p,d,i.inst_id),fn,i,t)::suffix` by
    (drule trace_block_visit >> simp[]) >>
  `R = (TAKE h R ++ pref) ++ [((p,d,i.inst_id),fn,i,t)] ++
      (suffix ++ rest)` by (simp[Abbr `pref`, APPEND_ASSOC] >> gvs[]) >>
  pop_assum $ mk_asm "embed" >>
  drule ALL_DISTINCT_EL_APPEND >>
  disch_then (qspecl_then
    [`MAP FST (TAKE h R ++ pref)`, `MAP FST (suffix ++ rest)`, `j`] mp_tac) >>
  simp[EL_MAP] >>
  (impl_tac >-
    (asm "embed" (fn th =>
       CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV th)))) >> simp[])) >> strip_tac >>
  `j = LENGTH (TAKE h R ++ pref)` by simp[] >>
  qpat_x_assum `j = LENGTH _` SUBST1_TAC >>
  asm "embed" (fn th =>
    CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV th)))) >>
  CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV (GSYM APPEND_ASSOC)))) >>
  rewrite_tac[TAKE_LENGTH_APPEND]
QED
