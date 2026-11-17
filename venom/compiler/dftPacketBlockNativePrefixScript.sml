Theory dftPacketBlockNativePrefix
Ancestors
  dftGasFromListOpenTrace dftGasFromListTracePrefix dftGasFromListLookup
  dftGasFromListTraceDefs venomInstProofs venomExecProofs venomExecSemantics
  rich_list arithmetic

Theorem open_trace_prefix[local]:
  n <= m ==>
  ?rest. open_trace p d m C fn bb s = open_trace p d n C fn bb s ++ rest
Proof
  strip_tac >> rewrite_tac[open_trace_def] >>
  Cases_on `?msg. exec_block n C bb s = Error msg`
  >- (pop_assum strip_assume_tac >>
      drule (cj 2 trace_prefix) >>
      disch_then (qspecl_then [`p`,`d`,`C`,`fn`,`bb`,`s`] strip_assume_tac) >>
      simp[] >> qmatch_goalsub_abbrev_tac `suffix ++ tail` >>
      qexists_tac `suffix ++ tail` >> simp[APPEND_ASSOC]) >>
  `!msg. exec_block n C bb s <> Error msg` by metis_tac[] >>
  `exec_block m C bb s = exec_block n C bb s` by
    (irule (cj 2 fuel_mono) >> simp[] >> qexists_tac `n` >> simp[]) >>
  `trace_block p d m C fn bb s = trace_block p d n C fn bb s` by
    (irule (cj 2 trace_stable) >> simp[]) >>
  simp[] >> Cases_on `exec_block n C bb s` >> simp[] >>
  rename1 `exec_block n C bb s = OK post` >>
  Cases_on `post.vs_halted` >> simp[] >>
  drule (cj 3 trace_prefix) >>
  disch_then (qspecl_then [`p`,`d`,`C`,`fn`,`post`] strip_assume_tac) >>
  qexists_tac `suffix` >> simp[APPEND_ASSOC]
QED

Theorem indexed_trace_cofinal[local]:
  (!P D n C fn inst s. !h p d g i t.
    h < LENGTH (trace_step P D n C fn inst s) /\
    EL h (trace_step P D n C fn inst s) = ((p,d,i.inst_id),g,i,t) ==>
    ?bb. lookup_block t.vs_current_bb g.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME i /\
      (!k b. ?m rest. b <= m /\
        trace_step P D m C fn inst s =
          TAKE h (trace_step P D n C fn inst s) ++
          open_trace p d k C g bb t ++ rest)) /\
  (!P D n C fn outer s. !h p d g i t.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME outer /\
    h < LENGTH (trace_block P D n C fn outer s) /\
    EL h (trace_block P D n C fn outer s) = ((p,d,i.inst_id),g,i,t) ==>
    ?bb. lookup_block t.vs_current_bb g.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME i /\
      (!k b. ?m rest. b <= m /\
        open_trace P D m C fn outer s =
          TAKE h (trace_block P D n C fn outer s) ++
          open_trace p d k C g bb t ++ rest)) /\
  (!P D n C fn s. !h p d g i t.
    h < LENGTH (trace_blocks P D n C fn s) /\
    EL h (trace_blocks P D n C fn s) = ((p,d,i.inst_id),g,i,t) ==>
    ?bb. lookup_block t.vs_current_bb g.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME i /\
      (!k b. ?m rest. b <= m /\
        trace_blocks P D m C fn s =
          TAKE h (trace_blocks P D n C fn s) ++
          open_trace p d k C g bb t ++ rest))
Proof
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume indexed_trace_cofinal[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE` >> gvs[cj 1 trace_defs] >>
  Cases_on `decode_invoke inst` >> gvs[] >>
  rename1 `decode_invoke inst = SOME pair` >> PairCases_on `pair` >>
  Cases_on `lookup_function pair0 C.ctx_functions` >> gvs[] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  Cases_on `eval_operands pair1 s` >> gvs[] >>
  rename1 `eval_operands _ _ = SOME args` >>
  Cases_on `setup_callee callee args s` >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `bb` >> simp[] >> rpt gen_tac >>
  first_x_assum (qspecl_then [`k`,`b`] strip_assume_tac) >>
  qexistsl_tac [`m`,`rest`] >> simp[cj 1 trace_defs]
QED

Resume indexed_trace_cofinal[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction outer s.vs_inst_idx`
  >- (qpat_x_assum `h < _` mp_tac >> simp[Once (cj 2 trace_defs)]) >>
  rename1 `get_instruction outer s.vs_inst_idx = SOME head` >>
  drule_then assume_tac trace_block_visit >>
  Cases_on `h`
  >- (gvs[] >> rpt gen_tac >>
      `?rest. open_trace P D (MAX k b) C fn outer s =
        open_trace P D k C fn outer s ++ rest` by
        (irule open_trace_prefix >> simp[]) >>
      qexistsl_tac [`MAX k b`,`rest`] >> simp[]) >>
  rename1 `SUC h` >> gvs[] >>
  Cases_on `h < LENGTH (trace_step P D n C fn head s)`
  >- (gvs[EL_APPEND, TAKE_APPEND] >>
      qpat_x_assum `!h p d g i t. _` drule_all >> strip_tac >>
      qexists_tac `bb` >> simp[] >> rpt gen_tac >>
      first_x_assum (qspecl_then [`k`,`b`] strip_assume_tac) >>
      qexists_tac `m` >> simp[] >>
      `h - LENGTH (trace_step P D n C fn head s) = 0` by decide_tac >>
      simp[open_trace_def] >>
      pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[]) >>
  Cases_on `step_inst n C head s` >> gvs[] >>
  rename1 `step_inst n C head s = OK post` >>
  Cases_on `is_terminator head.inst_opcode` >> gvs[] >>
  drule_all step_preserves_control_flow >> strip_tac >>
  gvs[EL_APPEND] >>
  `h - LENGTH (trace_step P D n C fn head s) <
    LENGTH (trace_block P D n C fn outer
      (post with vs_inst_idx := SUC s.vs_inst_idx))` by decide_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `bb` >> simp[] >> rpt gen_tac >>
  first_x_assum (qspecl_then [`k`,`MAX n b`] strip_assume_tac) >>
  `n <= m /\ b <= m` by (gvs[MAX_DEF] >> decide_tac) >>
  `step_inst m C head s = OK post` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `n` >> simp[]) >>
  `trace_step P D m C fn head s = trace_step P D n C fn head s` by
    (irule (cj 1 trace_stable) >> simp[]) >>
  qexistsl_tac [`m`,`rest`] >> simp[] >>
  drule_all open_trace_next >>
  disch_then (qspecl_then [`P`,`fn`,`D`] SUBST1_TAC) >>
  simp[TAKE_APPEND, APPEND_ASSOC]
QED

Resume indexed_trace_cofinal[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `n` >- gvs[] >> rename1 `SUC n` >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- (qpat_x_assum `h < _` mp_tac >> simp[Once (cj 3 trace_defs)]) >>
  rename1 `lookup_block _ _ = SOME outer` >>
  Cases_on `eval_phis s outer.bb_instructions` >> gvs[]
  >- (rename1 `eval_phis s outer.bb_instructions = OK sp` >>
  drule_all trace_blocks_enter >> disch_then assume_tac >> gvs[] >>
  `sp.vs_current_bb = s.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  qmatch_asmsub_abbrev_tac `exec_block n C outer start` >>
  Cases_on `h < LENGTH (trace_block P (SUC D) n C fn outer start)`
  >- ((gvs[EL_APPEND] >>
      qpat_x_assum `!h p d g i t. _` drule_all >> strip_tac >>
      qexists_tac `bb` >> simp[] >> rpt gen_tac >>
      first_x_assum (qspecl_then [`k`,`b`] strip_assume_tac) >>
      qexistsl_tac [`SUC m`,`rest`] >> simp[TAKE_APPEND] >>
      drule_all trace_blocks_open >>
      disch_then (qspecl_then [`P`,`m`,`D`,`C`] SUBST1_TAC) >>
      simp[Abbr `start`] >> (gvs[dftGasFromListOpenTraceTheory.open_trace_def]))) >>
  Cases_on `exec_block n C outer start` >> gvs[] >>
  rename1 `exec_block _ _ _ _ = OK post` >>
  Cases_on `post.vs_halted` >> gvs[] >>
  gvs[EL_APPEND] >>
  `h - LENGTH (trace_block P (SUC D) n C fn outer start) <
    LENGTH (trace_blocks P (SUC D) n C fn post)` by decide_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `bb` >> simp[] >> rpt gen_tac >>
  first_x_assum (qspecl_then [`k`,`MAX n b`] strip_assume_tac) >>
  `n <= m /\ b <= m` by (gvs[MAX_DEF] >> decide_tac) >>
  `exec_block m C outer start = OK post` by
    (irule (cj 2 fuel_mono) >> simp[] >> qexists_tac `n` >> simp[]) >>
  `trace_block P (SUC D) m C fn outer start = trace_block P (SUC D) n C fn outer start` by
    (irule (cj 2 trace_stable) >> simp[]) >>
  qexistsl_tac [`SUC m`,`rest`] >> simp[] >>
  unabbrev_all_tac >> once_rewrite_tac[cj 3 trace_defs] >>
  simp[TAKE_APPEND, APPEND_ASSOC]) >>
  qpat_x_assum `h < LENGTH _` mp_tac >>
  simp[Once (cj 3 trace_defs)]
QED

Finalise indexed_trace_cofinal

Theorem dft_packet_block_native_prefix:
  j < LENGTH (trace_blocks [] 0 N C root_tf root_entry) /\
  EL j (trace_blocks [] 0 N C root_tf root_entry) = ((p,d,c.inst_id),tf,c,s) /\
  wf_function tf /\ active_inst tf c s /\ is_terminator c.inst_opcode /\
  c.inst_opcode <> INVOKE /\ c.inst_opcode <> GAS /\
  step_inst f C c s = OK post /\ ~post.vs_halted /\
  enters_block tf post s1 /\ active_inst tf next s1 ==>
  ?N' bt sp. N <= N' /\ SUC d <= N' /\
    lookup_block post.vs_current_bb tf.fn_blocks = SOME bt /\
    eval_phis post bt.bb_instructions = OK sp /\
    s1 = sp with vs_inst_idx := phi_prefix_length bt.bb_instructions /\
    get_instruction bt s1.vs_inst_idx = SOME next /\
    SUC j < LENGTH (trace_blocks [] 0 N' C root_tf root_entry) /\
    TAKE (SUC j) (trace_blocks [] 0 N' C root_tf root_entry) =
      TAKE (SUC j) (trace_blocks [] 0 N C root_tf root_entry) /\
    EL (SUC j) (trace_blocks [] 0 N' C root_tf root_entry) =
      ((p,SUC d,next.inst_id),tf,next,s1) /\
    trace_gas (TAKE (SUC j) (trace_blocks [] 0 N' C root_tf root_entry)) =
      trace_gas (TAKE j (trace_blocks [] 0 N C root_tf root_entry))
Proof
  rpt strip_tac >> drule_all entered_active_lookup >>
  disch_then (qx_choose_then `bt` (qx_choose_then `sp` strip_assume_tac)) >>
  drule_all (cj 3 indexed_trace_cofinal) >> strip_tac >>
  first_x_assum (qspecl_then [`1`,`MAX N (SUC d)`] strip_assume_tac) >>
  `step_inst 1 C c s = OK post` by
    metis_tac[step_inst_non_invoke] >>
  `open_trace p d 1 C tf bb s =
     ((p,d,c.inst_id),tf,c,s)::open_trace p (SUC d) 0 C tf bt s1` by
    (simp[open_trace_def, Once trace_defs, trace_step_noninvoke] >>
     simp[Once exec_block_def, trace_blocks_open] >>
     simp[Once (cj 3 trace_defs)]) >>
  `?tail. open_trace p (SUC d) 0 C tf bt s1 =
    ((p,SUC d,next.inst_id),tf,next,s1)::tail` by
    (simp[open_trace_def, Once trace_defs] >> metis_tac[]) >>
  qexistsl_tac [`m`,`bt`,`sp`] >>
  `N <= m /\ SUC d <= m` by (gvs[MAX_DEF] >> decide_tac) >>
  `LENGTH (TAKE j (trace_blocks [] 0 N C root_tf root_entry)) = j` by simp[] >>
  simp[TAKE_APPEND, EL_APPEND, TAKE_SUC_BY_TAKE, SNOC_APPEND,
       trace_gas_def, visit_gas_def] >>
  simp[TAKE_TAKE_T] >>
  `j - (j + SUC (SUC (LENGTH tail))) = 0` by decide_tac >> simp[]
QED
