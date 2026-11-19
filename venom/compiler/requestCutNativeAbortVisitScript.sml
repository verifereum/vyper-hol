Theory requestCutNativeAbortVisit
Ancestors
  dftGasFromListTraceDefs dftGasFromListTracePrefix dftGasFromListLocator
  dftGasFromListReplayBoundary requestCutDftPrefixReach dftGasOracleDefs
  contextCodegenRel venomExecSemantics venomInst venomState venomWf list rich_list arithmetic alist

(* The last visit is the primitive abort even when it is in a callee. *)
Theorem native_trace_primitive_abort:
  (!p d fuel ctx fn outer s.
    !key f i t a u.
    MEM (key,f,i,t) (trace_step p d fuel ctx fn outer s) /\
    i.inst_opcode <> INVOKE /\ step_inst_base i t = Abort a u ==>
    step_inst fuel ctx outer s = Abort a u /\
    ?pre. trace_step p d fuel ctx fn outer s = pre ++ [(key,f,i,t)]) /\
  (!p d fuel ctx fn bb s.
    !key f i t a u.
    MEM (key,f,i,t) (trace_block p d fuel ctx fn bb s) /\
    i.inst_opcode <> INVOKE /\ step_inst_base i t = Abort a u ==>
    exec_block fuel ctx bb s = Abort a u /\
    ?pre. trace_block p d fuel ctx fn bb s = pre ++ [(key,f,i,t)]) /\
  (!p d fuel ctx fn s.
    !key f i t a u.
    MEM (key,f,i,t) (trace_blocks p d fuel ctx fn s) /\
    i.inst_opcode <> INVOKE /\ step_inst_base i t = Abort a u ==>
    run_blocks fuel ctx fn s = Abort a u /\
    ?pre. trace_blocks p d fuel ctx fn s = pre ++ [(key,f,i,t)])
Proof
  ho_match_mp_tac trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume native_trace_primitive_abort[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `outer.inst_opcode = INVOKE`
  >- (Cases_on `decode_invoke outer`
      >- simp[Once trace_defs] >>
      rename1 `decode_invoke outer = SOME pair` >> PairCases_on `pair` >>
      Cases_on `lookup_function pair0 ctx.ctx_functions`
      >- simp[Once trace_defs] >>
      rename1 `lookup_function pair0 ctx.ctx_functions = SOME callee` >>
      Cases_on `eval_operands pair1 s`
      >- simp[Once trace_defs] >>
      rename1 `eval_operands pair1 s = SOME args` >>
      Cases_on `setup_callee callee args s`
      >- simp[Once trace_defs] >>
      simp[Once trace_defs] >> strip_tac >>
      gvs[] >> first_x_assum drule_all >> strip_tac >>
      simp[step_inst_def, Once trace_defs] >> metis_tac[]) >>
  simp[trace_step_noninvoke]
QED

Resume native_trace_primitive_abort[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[Once trace_defs] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME outer` >>
  once_rewrite_tac[cj 2 trace_defs, exec_block_def] >> simp[MEM_APPEND] >>
  strip_tac
  >- (gvs[] >> simp[step_inst_non_invoke, trace_step_noninvoke])
  >- (gvs[] >> first_x_assum drule_all >> strip_tac >> simp[] >>
      metis_tac[APPEND]) >>
  Cases_on `step_inst fuel ctx outer s` >> gvs[] >>
  Cases_on `is_terminator outer.inst_opcode` >> gvs[] >>
  metis_tac[APPEND, APPEND_ASSOC]
QED

Resume native_trace_primitive_abort[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  namedCases_on `fuel` ["", "small"]
  >- simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[Once (cj 3 trace_defs)] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  once_rewrite_tac[cj 3 trace_defs, run_blocks_def] >> simp[MEM_APPEND] >>
  strip_tac
  >- (gvs[] >> first_x_assum drule_all >> strip_tac >> simp[] >> metis_tac[]) >>
  rename1 `eval_phis s bb.bb_instructions = OK s_phi` >>
  qmatch_asmsub_abbrev_tac `exec_block small ctx bb entry` >>
  Cases_on `exec_block small ctx bb entry` >> gvs[] >>
  rename1 `exec_block small ctx bb entry = OK result` >>
  Cases_on `result.vs_halted` >> gvs[] >>
  metis_tac[APPEND_ASSOC]
QED

Finalise native_trace_primitive_abort

Theorem native_trace_context_primitive_abort:
  MEM ((p,d,i.inst_id),fn,i,t) (trace_context fuel ctx s) /\
  i.inst_opcode <> INVOKE /\ step_inst_base i t = Abort a u ==>
  run_context fuel ctx s = Abort a u /\
  ?pre. trace_context fuel ctx s = pre ++ [((p,d,i.inst_id),fn,i,t)]
Proof
  Cases_on `ctx.ctx_entry` >- simp[trace_context_def] >>
  rename1 `ctx.ctx_entry = SOME nm` >>
  Cases_on `lookup_function nm ctx.ctx_functions` >- simp[trace_context_def] >>
  rename1 `lookup_function nm ctx.ctx_functions = SOME entry_fn` >>
  Cases_on `fn_entry_label entry_fn` >>
  simp[trace_context_def, trace_function_def, run_context_def, run_function_def] >>
  metis_tac[cj 3 native_trace_primitive_abort]
QED


Theorem native_terminal_trace_cover:
  EVERY wf_function C.ctx_functions /\
  (!err. run_context bound C v <> Error err) /\
  trace_agrees orc (trace_context bound C v) /\
  raw_reachable v C fn i s ==>
  ?p d. ev_reachable orc (v with vs_gas_readings := ws) C p d fn i
          (s with vs_gas_readings := ws)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all raw_reachable_trace >> strip_tac >>
  `trace_context (MAX bound fuel) C v = trace_context bound C v` by
    (Cases_on `C.ctx_entry` >> simp[trace_context_def, run_context_def] >>
     rename1 `C.ctx_entry = SOME nm` >>
     Cases_on `lookup_function nm C.ctx_functions` >> simp[] >>
     rename1 `lookup_function nm C.ctx_functions = SOME root` >>
     Cases_on `fn_entry_label root` >> simp[trace_function_def, run_function_def] >>
     irule (cj 3 trace_stable) >> fs[run_context_def, run_function_def]) >>
  `fuel <= MAX bound fuel` by simp[] >>
  drule trace_context_prefix >>
  disch_then (qspecl_then [`v`, `C`] strip_assume_tac) >>
  `MEM ((p,d,i.inst_id),fn,i,s) (trace_context bound C v)` by
    metis_tac[MEM_APPEND] >>
  qpat_assum `MEM _ (trace_context bound C v)`
    (strip_assume_tac o ONCE_REWRITE_RULE [MEM_SPLIT]) >>
  qexistsl_tac [`p`, `d`] >>
  irule trace_context_prefix_visit >>
  qexistsl_tac [`bound`, `i.inst_id`, `l2`, `l1`] >>
  rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `trace_context bound C v = l1 ++ _` (fn eq =>
    qpat_assum `trace_agrees orc (trace_context bound C v)`
      (mp_tac o PURE_REWRITE_RULE [eq, trace_agrees_append])) >>
  simp_tac bool_ss []
QED


(* A non-GAS abort at the endpoint leaves the observations complete. *)
Theorem native_observed_abort_cover:
  EVERY wf_function C.ctx_functions /\
  tr = trace_context bound C v /\ ALL_DISTINCT (MAP FST tr) /\
  j < LENGTH tr /\ EL j tr = ((p,d,i.inst_id),fn,i,s) /\
  obs = trace_gas (TAKE j tr) /\ ALL_DISTINCT (MAP FST obs) /\
  i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
  step_inst_base i s = Abort a u /\
  raw_reachable v C f inst t ==>
  ?path depth. ev_reachable
    (\key. case ALOOKUP (obs ++ filling) key of NONE => 0w | SOME w => w)
    v C path depth f inst (t with vs_gas_readings := v.vs_gas_readings)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM ((p,d,i.inst_id),fn,i,s) (trace_context bound C v)` by
    (qpat_assum `tr = _` (fn eq => PURE_REWRITE_TAC [GSYM eq]) >>
     simp[NoAsms, MEM_EL] >> qexists_tac `j` >> PURE_ASM_REWRITE_TAC [] >> simp[]) >>
  drule_all native_trace_context_primitive_abort >> strip_tac >>
  `tr = pre ++ [((p,d,i.inst_id),fn,i,s)]` by metis_tac[] >>
  `j = LENGTH pre` by
    (qspecl_then [`MAP (FST:list_visit -> gas_event) tr`, `j`, `LENGTH pre`]
       mp_tac ALL_DISTINCT_EL_IMP >>
     `LENGTH pre < LENGTH tr` by simp[] >>
     `EL (LENGTH pre) tr = ((p,d,i.inst_id),fn,i,s)` by
       (qpat_assum `tr = pre ++ _` SUBST1_TAC >> simp[EL_APPEND_EQN]) >>
     simp_tac (srw_ss()) [NoAsms, LENGTH_MAP, EL_MAP] >>
     PURE_ASM_REWRITE_TAC [] >> simp[]) >>
  `trace_gas tr = obs` by
    (qpat_assum `obs = _` SUBST1_TAC >>
     qpat_assum `j = _` (fn eq => PURE_REWRITE_TAC [eq]) >>
     qpat_assum `tr = pre ++ _` (fn eq => PURE_REWRITE_TAC [eq]) >>
     simp[TAKE_LENGTH_APPEND, trace_gas_def, visit_gas_def, MAP_APPEND, FLAT_APPEND]) >>
  `trace_agrees (\key. case ALOOKUP (obs ++ filling) key of
      NONE => 0w | SOME w => w) tr` by
    (PURE_REWRITE_TAC[trace_agrees_def, EVERY_MEM] >>
     qpat_assum `trace_gas tr = obs` SUBST1_TAC >>
     Cases >> rpt strip_tac >> rename1 `MEM (key,value) obs` >>
     `ALOOKUP obs key = SOME value` by metis_tac[ALOOKUP_ALL_DISTINCT_MEM] >>
     simp[ALOOKUP_APPEND]) >>
  `v with vs_gas_readings := v.vs_gas_readings = v` by
    simp[venom_state_component_equality] >>
  mp_tac (Q.INST [`i` |-> `inst`, `fn` |-> `f`, `s` |-> `t`,
    `ws` |-> `v.vs_gas_readings`, `orc` |->
      `\key. case ALOOKUP (obs ++ filling) key of NONE => 0w | SOME w => w`]
    native_terminal_trace_cover) >>
  qpat_assum `tr = trace_context bound C v` (fn eq => PURE_REWRITE_TAC [GSYM eq]) >>
  simp[]
QED
