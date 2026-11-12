Theory deployOutcomesFreeTransport
Ancestors
  deployOutcomesFreeStep deployOutcomesFreeRuns deployOutcomesFreeFrames
  deployOutcomesFreeBoundary unitMemInv lowerDloadDefs ctxLookupAgreeHelpers ptrDiscipline venomExecSemantics dftCommutation venomInst

Theorem outcomes_entry_step:
  EVERY (\i. ~MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts entry) /\
  active_inst entry i u ==>
  step_inst fuel ctx i (u with vs_outcomes := os) =
  map_result_state (\t. t with vs_outcomes := os) (step_inst fuel ctx i u)
Proof
  strip_tac >> irule outcomes_step_inst >> drule_all EVERY_active_inst >> simp[]
QED

Theorem outcomes_entry_raw_reachable:
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME entry /\
  EVERY (\i. ~MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts entry) ==>
  !s os f i t. raw_reachable (s with vs_outcomes := os) ctx f i t ==>
    f = entry /\ ?t0. raw_reachable s ctx f i t0 /\ t = (t0 with vs_outcomes := os)
Proof
  strip_tac >>
  mp_tac raw_reachable_outcomes_replace >>
  impl_tac
  >- (simp[outcomes_enters_block] >> conj_tac
      >- (gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
      rpt strip_tac >> drule_all outcomes_entry_step >>
      simp[] >> metis_tac[map_result_state_OK]) >> simp[]
QED

Theorem mem_inv_outcomes_replace:
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME entry /\
  EVERY (\i. ~MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts entry) /\
  (!c f i t os. M c f i (t with vs_outcomes := os) = M c f i t) /\
  mem_inv M ctx s ==>
  mem_inv M ctx (s with vs_outcomes := os)
Proof
  strip_tac >> mp_tac outcomes_entry_raw_reachable >> simp[] >> strip_tac >>
  gvs[mem_inv_raw_reachable] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem outcomes_entry_frames:
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME entry /\
  EVERY (\i. ~MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts entry) /\
  frame_reachable (s with vs_outcomes := os) ctx stk PG G tn fn inst t ==>
  stk = [] /\ fn = entry /\
  ?t0. frame_reachable s ctx stk PG G tn fn inst t0 /\ t = (t0 with vs_outcomes := os)
Proof
  strip_tac >> drule outcomes_frames_transport >>
  disch_then (qspecl_then [`s`, `os`, `name`, `entry`] mp_tac) >>
  simp[outcomes_enters_block] >> impl_tac
  >- (rpt strip_tac >> drule_all outcomes_entry_step >>
      simp[] >> metis_tac[map_result_state_OK]) >> simp[]
QED

Theorem ptr_discipline_outcomes_replace:
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME entry /\
  EVERY (\i. ~MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts entry) /\
  ptr_discipline lo ctx s ==>
  ptr_discipline lo ctx (s with vs_outcomes := os)
Proof
  strip_tac >> gvs[ptr_discipline_def] >> qexists_tac `P` >> simp[] >>
  rpt strip_tac >>
  drule_all (SRULE [] outcomes_entry_frames) >> strip_tac >>
  gvs[] >> metis_tac[outcomes_state_predicates]
QED

Theorem outcomes_entry_final_taint:
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME entry /\
  EVERY (\i. ~MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts entry) /\
  final_taint (s with vs_outcomes := os) ctx t tn R ==>
  ?t0. final_taint s ctx t0 tn R /\ t = (t0 with vs_outcomes := os)
Proof
  strip_tac >> mp_tac outcomes_final_taint_transport >> simp[outcomes_enters_block] >>
  impl_tac
  >- (conj_tac >> rpt strip_tac >> drule_all outcomes_entry_step >>
      simp[] >> metis_tac[map_result_state_OK, map_result_state_Halt]) >> simp[]
QED

Theorem raw_mem_ok_outcomes_replace[simp]:
  raw_mem_ok ctx fn inst (s with vs_outcomes := os) = raw_mem_ok ctx fn inst s
Proof
  simp[raw_mem_ok_def, unitTransformDefsTheory.inst_mem_ok_in_fn_def,
       unitTransformDefsTheory.inst_mem_below_frontier_def]
QED

Theorem raw_unit_memory_ok_outcomes_replace:
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME entry /\
  EVERY (\i. ~MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts entry) /\
  raw_unit_memory_ok ctx s ==>
  raw_unit_memory_ok ctx (s with vs_outcomes := os)
Proof
  simp[raw_unit_memory_ok_mem_inv] >> strip_tac >>
  irule mem_inv_outcomes_replace >> simp[] >> qexistsl_tac [`entry`, `name`] >> simp[]
QED

Theorem dload_predicates_outcomes_replace[simp]:
  dload_offset_ok ctx fn inst (s with vs_outcomes := os) = dload_offset_ok ctx fn inst s /\
  dload_headroom_ok ctx fn inst (s with vs_outcomes := os) = dload_headroom_ok ctx fn inst s /\
  inst_dload_in_section inst (s with vs_outcomes := os) = inst_dload_in_section inst s
Proof
  simp[dload_offset_ok_def, dload_headroom_ok_def, memSafeRunTheory.inst_dload_in_section_def]
QED

Theorem dload_offset_ok_outcomes_replace:
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME entry /\
  EVERY (\i. ~MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts entry) /\
  mem_inv dload_offset_ok ctx s ==>
  mem_inv dload_offset_ok ctx (s with vs_outcomes := os)
Proof
  strip_tac >> irule mem_inv_outcomes_replace >> gvs[]
QED

Theorem dload_headroom_ok_outcomes_replace:
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME entry /\
  EVERY (\i. ~MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts entry) /\
  mem_inv dload_headroom_ok ctx s ==>
  mem_inv dload_headroom_ok ctx (s with vs_outcomes := os)
Proof
  strip_tac >> irule mem_inv_outcomes_replace >> gvs[]
QED

Theorem dload_in_section_outcomes_replace:
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME entry /\
  EVERY (\i. ~MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts entry) /\
  mem_inv (\c f inst t. inst_dload_in_section inst t /\ t.vs_code = code /\ t.vs_data_section = data) ctx s ==>
  mem_inv (\c f inst t. inst_dload_in_section inst t /\ t.vs_code = code /\ t.vs_data_section = data) ctx (s with vs_outcomes := os)
Proof
  strip_tac >> irule mem_inv_outcomes_replace >> gvs[]
QED

Theorem taint_within_outcomes_replace:
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME entry /\
  EVERY (\i. ~MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts entry) /\
  taint_within D ctx s ==>
  taint_within D ctx (s with vs_outcomes := os)
Proof
  strip_tac >> gvs[taint_within_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule_all (SRULE [] outcomes_entry_frames) >> strip_tac >> gvs[] >>
      drule_all (SRULE [] outcomes_entry_step) >> simp[] >> strip_tac >> gvs[] >>
      metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  drule_all (SRULE [] outcomes_entry_final_taint) >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem exec_block_outcomes_replace:
  EVERY (\i. ~MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) bb.bb_instructions ==>
  !fuel s os. exec_block fuel ctx bb (s with vs_outcomes := os) =
    map_result_state (\t. t with vs_outcomes := os) (exec_block fuel ctx bb s)
Proof
  strip_tac >> gen_tac >>
  measureInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >> rpt strip_tac >>
  CONV_TAC (BINOP_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[map_result_state_def] >>
  rename1 `SOME inst` >>
  `~MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]`
    by (drule_all EVERY_get_instruction >> simp[]) >>
  simp[outcomes_step_inst] >> Cases_on `step_inst fuel ctx inst s` >>
  simp[map_result_state_def] >> IF_CASES_TAC
  >- (Cases_on `v'.vs_halted` >> simp[map_result_state_def]) >>
  first_x_assum (qspec_then `SUC s.vs_inst_idx` mp_tac) >>
  impl_tac >- (gvs[get_instruction_def] >> decide_tac) >>
  disch_then (qspec_then `v' with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >> simp[]
QED

Theorem run_block_entry_outcomes_replace:
  EVERY (\i. ~MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) bb.bb_instructions ==>
  run_block fuel ctx bb (s with vs_outcomes := os) =
    map_result_state (\t. t with vs_outcomes := os) (run_block fuel ctx bb s)
Proof
  strip_tac >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs >>
  simp[run_block_def, outcomes_eval_phis, map_result_state_def] >>
  drule exec_block_outcomes_replace >>
  disch_then (qspecl_then [`ctx`, `fuel`, `s' with vs_inst_idx := phi_prefix_length bb.bb_instructions`, `os`] mp_tac) >> simp[]
QED

Theorem run_context_entry_outcomes_replace:
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME entry /\
  EVERY (\i. ~MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts entry) ==>
  !fuel s os. run_context fuel ctx (s with vs_outcomes := os) =
    map_result_state (\t. t with vs_outcomes := os) (run_context fuel ctx s)
Proof
  strip_tac >> mp_tac (Q.INST [`fn` |-> `entry`] run_context_outcomes_replace) >> impl_tac
  >- (simp[] >> rpt strip_tac >>
      `EVERY (\i. ~MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) bb.bb_instructions`
        by metis_tac[EVERY_fn_block] >>
      simp[run_block_entry_outcomes_replace] >>
      Cases_on `run_block fuel ctx bb s` >> simp[map_result_state_def]) >>
  strip_tac >> rpt gen_tac >> simp[] >>
  Cases_on `run_context fuel ctx s` >> simp[map_result_state_def]
QED
