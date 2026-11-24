(* Straight-line observations of the actual fixed proxy buffer run. *)
Theory bodyFullProxyBufferSpine
Ancestors
  fragGasSeqAbort fragGasOrigin frameGasEvents fragExec stmtReasonLitFragMemory
  venomInstProofs venomExecSemantics venomInst venomState compileEnv
  relation rich_list list arithmetic exprLoweringProps instIdxIndep

Definition proxy_buffer_step_def:
  proxy_buffer_step a b explicit ctx fn s t <=>
    s.vs_current_bb = b.cs_current_bb /\ s.vs_inst_idx < LENGTH b.cs_current_insts /\
    (?bb inst. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME inst /\
      a.cs_next_id <= inst.inst_id /\ inst.inst_id < b.cs_next_id) /\
    gas_origin_edge F explicit ctx fn s [] (OK t)
End

Theorem straight_run_proxy_buffer_steps[local]:
  !code s t bb a b explicit ctx fn.
    ~s.vs_halted /\ s.vs_current_bb = b.cs_current_bb /\
    s.vs_inst_idx + LENGTH code <= LENGTH b.cs_current_insts /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
      ~is_terminator i.inst_opcode /\ a.cs_next_id <= i.inst_id /\
      i.inst_id < b.cs_next_id) code /\
    run_inst_seq code s = OK t ==>
    RTC (proxy_buffer_step a b explicit ctx fn) s
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH code)
Proof
  Induct >- (simp[run_inst_seq_def] >> rpt strip_tac >> gvs[] >>
             `s with vs_inst_idx := s.vs_inst_idx = s` by
               simp[venom_state_component_equality] >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[run_inst_seq_def] >>
  rename1 `step_inst_base h s = OK u` >>
  `step_inst 0 ctx h s = OK u` by simp[step_inst_non_invoke] >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_halted, step_preserves_control_flow] >>
  irule (cj 2 RTC_RULES) >>
  qexists_tac `u with vs_inst_idx := SUC s.vs_inst_idx` >> conj_tac
  >- (`s.vs_inst_idx < LENGTH b.cs_current_insts` by decide_tac >>
      simp[proxy_buffer_step_def, gas_origin_edge_def] >>
      qexists_tac `0` >>
      simp[gas_events_step_plain]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
  first_x_assum (qspecl_then [`u with vs_inst_idx := SUC s.vs_inst_idx`,
    `t with vs_inst_idx := SUC s.vs_inst_idx`,`bb`,`a`,`b`,`explicit`,`ctx`,`fn`] mp_tac) >>
  simp[run_inst_seq_inst_idx, exec_result_map_def, ADD_CLAUSES]
QED

Theorem proxy_buffer_steps_run:
  fn_has_code a b fn /\ b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ code /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts /\
  ~s.vs_halted /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
    ~is_terminator i.inst_opcode /\ a.cs_next_id <= i.inst_id /\
    i.inst_id < b.cs_next_id) code /\
  run_inst_seq code s = OK t ==>
  RTC (proxy_buffer_step a b explicit ctx fn) s
    (t with vs_inst_idx := LENGTH b.cs_current_insts)
Proof
  strip_tac >> drule_all fn_has_code_code >> strip_tac >>
  qpat_assum `b.cs_current_insts = _` (fn th => once_rewrite_tac [th]) >>
  pure_rewrite_tac[LENGTH_APPEND] >>
  qpat_assum `s.vs_inst_idx = _` (fn th => once_rewrite_tac [GSYM th]) >>
  irule straight_run_proxy_buffer_steps >> simp[] >> metis_tac[]
QED

Theorem proxy_buffer_steps_join:
  a.cs_next_id <= m.cs_next_id /\ m.cs_next_id <= b.cs_next_id /\
  m.cs_current_bb = b.cs_current_bb /\
  LENGTH m.cs_current_insts <= LENGTH b.cs_current_insts /\
  RTC (proxy_buffer_step a m explicit ctx fn) s u /\
  RTC (proxy_buffer_step m b explicit ctx fn) u t ==>
  RTC (proxy_buffer_step a b explicit ctx fn) s t
Proof
  strip_tac >> irule RTC_TRANS >> qexists_tac `u` >> conj_tac
  >- (irule RTC_MONOTONE >> first_assum (irule_at Any) >>
      simp[proxy_buffer_step_def] >> rpt strip_tac >> simp[] >>
      metis_tac[LESS_EQ_LESS_TRANS, LESS_LESS_EQ_TRANS]) >>
  irule RTC_MONOTONE >> first_assum (irule_at Any) >>
  simp[proxy_buffer_step_def] >> metis_tac[LESS_EQ_TRANS]
QED

(* Package the layout evidence with the spine so adjacent spans compose. *)
Definition proxy_buffer_span_def:
  proxy_buffer_span a b explicit ctx fn s t <=>
    a.cs_next_id <= b.cs_next_id /\ a.cs_current_bb = b.cs_current_bb /\
    LENGTH a.cs_current_insts <= LENGTH b.cs_current_insts /\
    RTC (proxy_buffer_step a b explicit ctx fn) s t
End

Theorem proxy_buffer_span_run:
  fn_has_code a b fn /\ b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ code /\ a.cs_next_id <= b.cs_next_id /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts /\
  ~s.vs_halted /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
    ~is_terminator i.inst_opcode /\ a.cs_next_id <= i.inst_id /\
    i.inst_id < b.cs_next_id) code /\
  run_inst_seq code s = OK t ==>
  proxy_buffer_span a b explicit ctx fn s
    (t with vs_inst_idx := LENGTH b.cs_current_insts)
Proof
  strip_tac >> rewrite_tac[proxy_buffer_span_def] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (sym_tac >> first_assum ACCEPT_TAC) >>
  TRY (simp[] >> NO_TAC) >>
  irule proxy_buffer_steps_run >> metis_tac[]
QED

Theorem proxy_buffer_span_trans:
  proxy_buffer_span a m explicit ctx fn s u /\
  proxy_buffer_span m b explicit ctx fn u t ==>
  proxy_buffer_span a b explicit ctx fn s t
Proof
  simp[proxy_buffer_span_def] >> strip_tac >>
  irule proxy_buffer_steps_join >> qexistsl_tac [`m`,`u`] >> asm_rewrite_tac[]
QED
