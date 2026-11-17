Theory loweringBudgetStoreRecorder
Ancestors
  loweringCallBudgetHistory loweringBudgetCursorCuts exprLoweringProps
  contextCodegenRel venomExecSemantics venomInst venomInstProofs1 gasEvents
  instIdxIndep opcodeClass list rich_list

Theorem budget_history_unique[local]:
  !checked cfg root h marks p.
    lower_budget_path checked cfg root h marks p ==>
    !marks' q. lower_budget_path checked cfg root h marks' q ==>
      marks' = marks /\ q = p
Proof
  ho_match_mp_tac lower_budget_path_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  once_rewrite_tac[lower_budget_path_cases] >>
  strip_tac >> gvs[GSYM SNOC_APPEND] >>
  metis_tac[]
QED

Theorem lower_budget_path_history_unique:
  !checked cfg root h marks p marks' q.
    lower_budget_path checked cfg root h marks p /\
    lower_budget_path checked cfg root h marks' q ==>
    marks' = marks /\ q = p
Proof
  metis_tac[budget_history_unique]
QED

Theorem lower_budget_path_take:
  !checked cfg root h marks q.
    lower_budget_path checked cfg root h marks q ==>
    !n. n <= LENGTH h ==>
      ?pn mn. lower_budget_path checked cfg root (TAKE n h) mn pn /\
        IS_PREFIX marks mn /\ (n = LENGTH h ==> pn = q /\ mn = marks)
Proof
  ho_match_mp_tac lower_budget_path_strongind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac
  >- (gvs[] >> metis_tac[lower_budget_path_entry]) >>
  (Cases_on `n = LENGTH (h ++ [ARB:lower_budget_event])`
  >- (fs[LENGTH_APPEND] >> simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG] >>
      once_rewrite_tac[lower_budget_path_cases] >>
      simp[GSYM SNOC_APPEND] >> gvs[] >> metis_tac[]) >>
  `n <= LENGTH h` by gvs[] >>
  first_x_assum drule >> strip_tac >>
  qexistsl [`pn`, `mn`] >> simp[TAKE_APPEND1] >>
  fs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC])
QED

Theorem budget_store_snoc[local]:
  !D lo explicit ctx root h marks p e marks' q i.
    lower_budget_path F (D,lo,explicit,ctx) root h marks p /\
    lower_budget_path F (D,lo,explicit,ctx) root (h ++ [e]) marks' q /\
    (!j. active_inst p.bp_fn j p.bp_state ==> j = i) /\
    MEM i.inst_opcode [ADD; MSTORE] ==>
    marks' = marks /\ q.bp_fn = p.bp_fn /\ q.bp_stack = p.bp_stack /\
    q.bp_params = p.bp_params /\
    ~lower_event_consumes e /\ ~lower_event_allocates e /\
    ?t. step_inst_base i p.bp_state = OK t /\
        q.bp_state = t with vs_inst_idx := SUC p.bp_state.vs_inst_idx
Proof
  rpt gen_tac >> strip_tac >>
  `!m r. lower_budget_path F (D,lo,explicit,ctx) root h m r ==>
      m = marks /\ r = p` by metis_tac[lower_budget_path_history_unique] >>
  qpat_x_assum `lower_budget_path _ _ _ h marks p` kall_tac >>
  qpat_x_assum `lower_budget_path _ _ _ (_ ++ [_]) _ _` mp_tac >>
  once_rewrite_tac[lower_budget_path_cases] >> strip_tac >>> NTH_GOAL (gvs[GSYM SNOC_APPEND]) 1 >>
  full_simp_tac pure_ss [pairTheory.PAIR_EQ, GSYM SNOC_APPEND, SNOC_11] >>
  qpat_x_assum `!m r. lower_budget_path _ _ _ _ m r ==> _` drule >>
  strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  gvs[MEM, is_terminator_def, Once step_inst_def,
      lower_event_consumes_def, lower_event_allocates_def,
      gas_events_step_def] >>
  drule step_inst_base_intret_opcodes >> simp[]
QED

Theorem store_code_budget_segment_control[local]:
  !hs D lo explicit ctx root h0 marks0 p marks q sa sb code.
    lower_budget_path F (D,lo,explicit,ctx) root h0 marks0 p /\
    lower_budget_path F (D,lo,explicit,ctx) root (h0 ++ hs) marks q /\
    fn_has_code sa sb p.bp_fn /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) p.bp_fn.fn_blocks) /\
    same_blocks sa sb /\ sb.cs_current_insts = sa.cs_current_insts ++ code /\
    p.bp_state.vs_current_bb = sa.cs_current_bb /\
    p.bp_state.vs_inst_idx = LENGTH sa.cs_current_insts /\
    EVERY (\i. MEM i.inst_opcode [ADD; MSTORE]) code /\
    LENGTH hs <= LENGTH code ==>
    marks = marks0 /\ q.bp_fn = p.bp_fn /\ q.bp_stack = p.bp_stack /\
    q.bp_params = p.bp_params /\
    q.bp_state.vs_current_bb = p.bp_state.vs_current_bb /\
    q.bp_state.vs_inst_idx = p.bp_state.vs_inst_idx + LENGTH hs /\
    EVERY (\e. ~lower_event_consumes e /\ ~lower_event_allocates e) hs /\
    ?t. run_inst_seq (TAKE (LENGTH hs) code) p.bp_state = OK t /\
        q.bp_state = t with vs_inst_idx := p.bp_state.vs_inst_idx + LENGTH hs /\
        t.vs_inst_idx = p.bp_state.vs_inst_idx
Proof
  Induct using SNOC_INDUCT
  >- (rpt gen_tac >> simp[] >> strip_tac >>
      `marks = marks0 /\ q = p` by metis_tac[lower_budget_path_history_unique] >>
      qpat_x_assum `q = p` SUBST_ALL_TAC >>
      simp[run_inst_seq_def] >>
      qpat_x_assum `p.bp_state.vs_inst_idx = _`
        (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `LENGTH hs < LENGTH code` by gvs[] >>
  qpat_assum `lower_budget_path _ _ _ (h0 ++ SNOC _ hs) _ _` mp_tac >>
  rewrite_tac[SNOC_APPEND, APPEND_ASSOC] >> strip_tac >>
  drule lower_budget_path_take >>
  disch_then (qspec_then `LENGTH (h0 ++ hs)` mp_tac) >>
  simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG] >> strip_tac >>
  `LENGTH hs <= LENGTH code` by simp[] >>
  first_x_assum drule_all >> strip_tac >>
  `!j. active_inst pn.bp_fn j pn.bp_state ==> j = EL (LENGTH hs) code` by
    (rpt strip_tac >>
     `pn.bp_state.vs_current_bb = sb.cs_current_bb /\
      pn.bp_state.vs_inst_idx < LENGTH sb.cs_current_insts` by
       fs[same_blocks_def] >>
     `fn_has_code sa sb pn.bp_fn /\
      ALL_DISTINCT (MAP (\bb. bb.bb_label) pn.bp_fn.fn_blocks)` by metis_tac[] >>
     drule_all embedded_current_active_inst >>
     disch_then (qspec_then `j` mp_tac) >>
     simp[EL_APPEND2]) >>
  `MEM (EL (LENGTH hs) code).inst_opcode [ADD; MSTORE]` by
    (qpat_x_assum `EVERY (\i. MEM i.inst_opcode _) code` mp_tac >>
     simp[EVERY_EL] >> disch_then (qspec_then `LENGTH hs` mp_tac) >> simp[]) >>
  drule_all budget_store_snoc >> strip_tac >>
  `~is_terminator (EL (LENGTH hs) code).inst_opcode` by
    fs[MEM, is_terminator_def] >>
  `t'.vs_current_bb = pn.bp_state.vs_current_bb` by
    metis_tac[cj 10 step_inst_base_preserves_all] >>
  `t'.vs_inst_idx = pn.bp_state.vs_inst_idx` by
    metis_tac[step_inst_base_preserves_inst_idx] >>
  `?u. step_inst_base (EL (LENGTH hs) code) t = OK u /\
       t' = u with vs_inst_idx := p.bp_state.vs_inst_idx + LENGTH hs` by
    (qpat_x_assum `step_inst_base _ pn.bp_state = _` mp_tac >>
     asm_rewrite_tac[step_inst_inst_idx_indep] >>
     Cases_on `step_inst_base (EL (LENGTH hs) code) t` >>
     simp[step_inst_inst_idx_indep, exec_result_map_def]) >>
  `u.vs_inst_idx = p.bp_state.vs_inst_idx` by
    metis_tac[step_inst_base_preserves_inst_idx] >>
  `u.vs_current_bb = sa.cs_current_bb` by
    (qpat_x_assum `t'.vs_current_bb = _` mp_tac >> simp[]) >>
  simp[] >> qexists_tac `u` >>
  conj_tac
  >- (rewrite_tac[GSYM arithmeticTheory.ADD1] >>
      asm_simp_tac std_ss [TAKE_SUC_BY_TAKE, SNOC_APPEND] >>
      drule run_inst_seq_append >>
      disch_then (qspec_then `[EL (LENGTH hs) code]` mp_tac) >>
      simp[run_inst_seq_def]) >>
  `SUC (LENGTH sa.cs_current_insts + LENGTH hs) =
   LENGTH sa.cs_current_insts + (LENGTH hs + 1)` by decide_tac >>
  simp[]
QED

Theorem store_code_budget_segment:
  !D lo explicit ctx root h0 marks0 p hs marks q sa sb code.
    lower_budget_path F (D,lo,explicit,ctx) root h0 marks0 p /\
    lower_budget_path F (D,lo,explicit,ctx) root (h0 ++ hs) marks q /\
    fn_has_code sa sb p.bp_fn /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) p.bp_fn.fn_blocks) /\
    same_blocks sa sb /\ sb.cs_current_insts = sa.cs_current_insts ++ code /\
    p.bp_state.vs_current_bb = sa.cs_current_bb /\
    p.bp_state.vs_inst_idx = LENGTH sa.cs_current_insts /\
    EVERY (\i. MEM i.inst_opcode [ADD; MSTORE]) code /\
    LENGTH hs <= LENGTH code ==>
    marks = marks0 /\ q.bp_fn = p.bp_fn /\ q.bp_stack = p.bp_stack /\
    q.bp_params = p.bp_params /\
    EVERY (\e. ~lower_event_consumes e /\ ~lower_event_allocates e) hs /\
    ?t. run_inst_seq (TAKE (LENGTH hs) code) p.bp_state = OK t /\
        q.bp_state = t with vs_inst_idx := p.bp_state.vs_inst_idx + LENGTH hs
Proof
  rpt gen_tac >> strip_tac >>
  drule_all store_code_budget_segment_control >> metis_tac[]
QED
