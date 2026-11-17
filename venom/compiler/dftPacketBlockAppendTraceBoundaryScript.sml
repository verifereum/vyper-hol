Theory dftPacketBlockAppendTraceBoundary
Ancestors
  dftPacketBlockAppendNative dftPacketOperationalPrefix dftGasFromListRestore
  dftGasFromListTraceDefs
  dftRunRel gasEvents venomExecSemantics venomInst venomState venomExecProofs list rich_list arithmetic

Theorem dft_packet_block_append_trace:
  !F. SUC d <= F /\
  trace_blocks [] 0 F C root_fn root_input =
    before ++ [((p,d,i.inst_id),sf,i,
      be with vs_gas_readings := gb ++ g1 ++ tail)] ++ after /\
  lookup_block be.vs_current_bb sf.fn_blocks = SOME bb /\
  get_instruction bb be.vs_inst_idx = SOME i /\
  exec_block (F-d) C bb (be with vs_gas_readings := gb ++ g1 ++ tail) =
    OK (post with vs_gas_readings := g1 ++ tail) /\
  ~post.vs_halted /\
  lookup_block post.vs_current_bb sf.fn_blocks = SOME bb1 /\
  eval_phis post bb1.bb_instructions = OK sp1 /\
  s1 = sp1 with vs_inst_idx := phi_prefix_length bb1.bb_instructions /\
  get_instruction bb1 s1.vs_inst_idx = SOME first /\
  trace_gas before = ZIP (K0,g0) /\
  trace_gas (trace_block p d (F-d) C sf bb
    (be with vs_gas_readings := gb ++ g1 ++ tail)) = ZIP (Kb,gb) /\
  LENGTH K0 = LENGTH g0 /\ LENGTH Kb = LENGTH gb /\ LENGTH K1 = LENGTH g1 /\
  bb1.bb_instructions = ps1 ++ xs1 /\
  EVERY (\i. is_pseudo i.inst_opcode) ps1 /\
  EVERY (\i. ~is_pseudo i.inst_opcode) xs1 /\
  R = (\entry. case eval_phis entry bb1.bb_instructions of
    OK sp =>
      (gas_events_block (F-SUC d) C sf.fn_name
        (bb1 with bb_instructions :=
          TAKE (phi_prefix_length bb1.bb_instructions) bb1.bb_instructions ++ z1)
        (sp with vs_inst_idx := phi_prefix_length bb1.bb_instructions),
       FOLDR (dft_exec_cons (F-SUC d) C) OK z1
        (sp with vs_inst_idx := phi_prefix_length bb1.bb_instructions))
    | other => ([],other)) /\
  R (post with vs_gas_readings := g1 ++ tail) = (events,OK u) /\
  ((s1.vs_inst_idx < LENGTH ps1 /\ q1 = 0 /\ g1 = [] /\ K1 = [] /\
    z1 = DROP (phi_prefix_length bb1.bb_instructions) (TAKE s1.vs_inst_idx ps1) /\
    u = s1 with vs_gas_readings := tail) \/
   (s1.vs_inst_idx = LENGTH ps1 /\ q1 < LENGTH xs1 /\
    EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q1 xs1) /\
    z1 = DROP (phi_prefix_length bb1.bb_instructions) ps1 ++ TAKE q1 xs1 /\
    FOLDR (dft_exec_cons (F-SUC d) C) OK (TAKE q1 xs1)
      (s1 with vs_gas_readings := g1 ++ tail) = OK u /\
    trace_gas (trace_block p (SUC d) (F-SUC d) C sf
      (bb1 with bb_instructions := TAKE (LENGTH ps1 + q1) bb1.bb_instructions)
      (s1 with vs_gas_readings := g1 ++ tail)) = ZIP (K1,g1))) ==>
  ?before1 after1.
    trace_blocks [] 0 F C root_fn root_input = before1 ++
      [((p,SUC d,(EL (LENGTH z1)
          (DROP (phi_prefix_length bb1.bb_instructions) bb1.bb_instructions)).inst_id),sf,
        EL (LENGTH z1) (DROP (phi_prefix_length bb1.bb_instructions) bb1.bb_instructions),u)] ++ after1 /\
    trace_gas before1 = ZIP (K0 ++ Kb ++ K1,g0 ++ gb ++ g1)
Proof
  gen_tac >> rename1 `SUC d <= fuel` >> strip_tac >>
  `eval_phis (post with vs_gas_readings := g1 ++ tail) bb1.bb_instructions =
    OK (sp1 with vs_gas_readings := g1 ++ tail)` by
    (mp_tac (Q.INST [`gs` |-> `g1 ++ tail`, `s` |-> `post`,
       `insts` |-> `bb1.bb_instructions`] eval_phis_restore) >>
     gvs[restore_rel_def,AllCaseEqs()])
  >- suspend "pseudo"
  >> suspend "body"
QED

Resume dft_packet_block_append_trace[pseudo]:
  `z1 = []` by gvs[DROP_TAKE] >>
  gvs[] >>
  `EL 0 (DROP (phi_prefix_length bb1.bb_instructions) bb1.bb_instructions) = first` by
    gvs[get_instruction_def,EL_DROP] >>
  qpat_assum `trace_blocks [] 0 _ _ _ _ = _`
    (fn th => pure_once_rewrite_tac [GSYM th]) >>
  irule (SRULE [] (Q.INST [`k` |-> `0`, `K1` |-> `[]`, `gs1` |-> `[]`]
    (SPEC_ALL dft_packet_native_next_partial_cut))) >>
  simp[] >>
  goal_assum (drule_at (Pat `exec_block _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `trace_gas (trace_block _ _ _ _ _ _ _) = _`)) >>
  simp[] >>
  qexistsl_tac [`after`,`before`] >>
  gvs[get_instruction_def] >>
  simp[Once (cj 2 trace_defs),get_instruction_def]
QED

Resume dft_packet_block_append_trace[body]:
  `phi_prefix_length bb1.bb_instructions = LENGTH ps1` by gvs[] >>
  `z1 = TAKE q1 xs1` by gvs[DROP_LENGTH_TOO_LONG] >>
  `u.vs_inst_idx = LENGTH ps1 + q1` by
    (mp_tac dft_packet_block_prefix_operational >>
     disch_then (qspecl_then [`fuel-SUC d`,`C`,`sf.fn_name`,`bb1`,
       `s1 with vs_gas_readings := g1 ++ tail`,`q1`] mp_tac) >>
     simp[DROP_APPEND,LET_THM] >> gvs[]) >>
  `get_instruction bb1 u.vs_inst_idx =
    SOME (EL (LENGTH z1)
      (DROP (phi_prefix_length bb1.bb_instructions) bb1.bb_instructions))` by
    simp[get_instruction_def,EL_APPEND2,DROP_APPEND] >>
  qpat_assum `trace_blocks [] 0 _ _ _ _ = _`
    (fn th => pure_once_rewrite_tac [GSYM th]) >>
  irule (SRULE [] (SPEC_ALL dft_packet_native_next_partial_cut)) >>
  simp[] >>
  goal_assum (drule_at (Pat `exec_block _ _ _ _ = _`)) >>
  simp[] >>
  qexistsl_tac [`after`,`before`,`first`,`q1`] >>
  gvs[DROP_APPEND,ADD_COMM]
QED

Finalise dft_packet_block_append_trace
