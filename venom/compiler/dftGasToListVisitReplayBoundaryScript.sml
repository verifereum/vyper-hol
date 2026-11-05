Theory dftGasToListVisitReplayBoundary
Ancestors
  dftGasToListReplay dftGasToListTrace dftGasToListVisitEdge
  contextRawReachable contextCodegenRel gasOracleReplay venomExecSemantics
  venomExecProofs venomInst stepWriteFootprintBase list rich_list arithmetic

Definition head_reachable_def:
  head_reachable vs0 ctx fn s ws <=>
  !j. active_inst fn j s ==>
    raw_reachable vs0 ctx fn j (s with vs_gas_readings := ws)
End

Definition entry_reachable_def:
  entry_reachable vs0 ctx fn s ws <=>
  !z. enters_block fn s z ==> head_reachable vs0 ctx fn z ws
End

Definition visits_reachable_def:
  visits_reachable vs0 ctx ws ts <=>
  !n p d fn inst t. MEM (n,p,d,fn,inst,t) (trace_visits 0 ts) ==>
    raw_reachable vs0 ctx fn inst (t with vs_gas_readings := DROP n ws)
End

Theorem trace_visits_shift:
  !ts a b n p d fn inst t.
  MEM (n,p,d,fn,inst,t) (trace_visits (a+b) ts) <=>
  ?k. n = a+k /\ MEM (k,p,d,fn,inst,t) (trace_visits b ts)
Proof
  Induct >> simp[trace_visits_def] >>
  Cases_on `h` >> simp[trace_visits_def, GSYM ADD_SUC] >>
  rpt gen_tac >> first_x_assum (qspecl_then [`a`, `SUC b`] mp_tac) >>
  simp[ADD_SUC] >> metis_tac[]
QED

Theorem visits_reachable_append:
  visits_reachable vs0 ctx ws (xs ++ ys) <=>
  visits_reachable vs0 ctx ws xs /\
  visits_reachable vs0 ctx (DROP (LENGTH (trace_events xs)) ws) ys
Proof
  simp[visits_reachable_def, trace_visits_append,
    SRULE [] (Q.SPECL [`ys`, `LENGTH (trace_events xs)`, `0`] trace_visits_shift),
    DROP_DROP_T, ADD_COMM] >> metis_tac[]
QED

Theorem visits_reachable_nil[simp]:
  visits_reachable vs0 ctx ws []
Proof
  simp[visits_reachable_def, trace_visits_def]
QED

Theorem visits_reachable_visit[simp]:
  visits_reachable vs0 ctx ws (TraceVisit p d fn inst t :: ts) <=>
  raw_reachable vs0 ctx fn inst (t with vs_gas_readings := ws) /\
  visits_reachable vs0 ctx ws ts
Proof
  simp[visits_reachable_def, trace_visits_def, DISJ_IMP_THM,
       FORALL_AND_THM]
QED

Theorem visits_reachable_gas[simp]:
  visits_reachable vs0 ctx ws (TraceGas e :: ts) <=>
  visits_reachable vs0 ctx (DROP 1 ws) ts
Proof
  simp[visits_reachable_def, trace_visits_def,
    SRULE [] (Q.SPECL [`ts`, `1`, `0`] trace_visits_shift),
    DROP_DROP_T, ADD_COMM] >> metis_tac[]
QED

Theorem head_reachable_next:
  raw_reachable vs0 ctx fn inst (s with vs_gas_readings := ws) /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  step_inst k ctx inst (s with vs_gas_readings := ws) =
    OK (u with vs_gas_readings := rest) ==>
  head_reachable vs0 ctx fn (u with vs_inst_idx := SUC s.vs_inst_idx) rest
Proof
  rpt strip_tac >> simp[head_reachable_def] >> rpt strip_tac >>
  drule (cj 2 raw_reachable_rules) >>
  disch_then (qspecl_then [`j`, `u with vs_gas_readings := rest`, `k`] mp_tac) >>
  gvs[active_inst_def] >> metis_tac[]
QED

Theorem entry_reachable_jump:
  raw_reachable vs0 ctx fn inst (s with vs_gas_readings := ws) /\
  active_inst fn inst s /\ is_terminator inst.inst_opcode /\
  step_inst k ctx inst (s with vs_gas_readings := ws) =
    OK (u with vs_gas_readings := rest) /\ ~u.vs_halted ==>
  entry_reachable vs0 ctx fn u rest
Proof
  rpt strip_tac >> simp[entry_reachable_def, head_reachable_def] >>
  rpt strip_tac >> drule enters_block_gas_update >>
  disch_then (qspec_then `rest` assume_tac) >>
  `active_inst fn inst (s with vs_gas_readings := ws)` by simp[] >>
  `active_inst fn j (z with vs_gas_readings := rest)` by simp[] >>
  `~(u with vs_gas_readings := rest).vs_halted` by simp[] >>
  drule_all (cj 3 raw_reachable_rules) >> simp[]
QED

Theorem entry_reachable_callee:
  raw_reachable vs0 ctx caller callinst (s with vs_gas_readings := ws) /\
  active_inst caller callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs ==>
  entry_reachable vs0 ctx callee cs ws
Proof
  rpt strip_tac >> simp[entry_reachable_def, head_reachable_def] >>
  rpt strip_tac >> drule enters_block_gas_update >>
  disch_then (qspec_then `ws` assume_tac) >>
  `setup_callee callee args (s with vs_gas_readings := ws) =
     SOME (cs with vs_gas_readings := ws)` by simp[gas_setup_callee] >>
  `active_inst caller callinst (s with vs_gas_readings := ws)` by simp[] >>
  `active_inst callee j (z with vs_gas_readings := ws)` by simp[] >>
  `eval_operands ops (s with vs_gas_readings := ws) = SOME args` by simp[] >>
  drule_all (cj 4 raw_reachable_rules) >> simp[]
QED

Theorem entry_reachable_context:
  ctx.ctx_entry = SOME nm /\
  lookup_function nm ctx.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl ==>
  entry_reachable (s with vs_gas_readings := readings) ctx fn
    (s with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) readings
Proof
  rpt strip_tac >> simp[entry_reachable_def, head_reachable_def] >>
  rpt strip_tac >> drule enters_block_gas_update >>
  disch_then (qspec_then `readings` assume_tac) >>
  irule (cj 1 raw_reachable_rules) >> simp[] >>
  gvs[enters_block_def]
QED

Theorem replay_block_entry_geometry:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s bb.bb_instructions = OK sp ==>
  enters_block fn s (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) /\
  lookup_block (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions).vs_current_bb
    fn.fn_blocks = SOME bb
Proof
  rpt strip_tac >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  simp[enters_block_def] >> qexists_tac `bb` >> simp[] >>
  qexists_tac `sp` >> simp[]
QED
