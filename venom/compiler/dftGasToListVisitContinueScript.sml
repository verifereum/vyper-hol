Theory dftGasToListVisitContinue
Ancestors
  dftGasToListVisitEdge dftGasToListFuel dftGasToListReachTrace
  dftGasToListTrace dftGasOracleDefs contextCodegenRel venomExecProofs
  venomExecSemantics venomInst venomWf list arithmetic

Theorem trace_extension_item_mem:
  trace_extension r ts r' ts' /\ MEM v ts ==> MEM v ts'
Proof
  simp[trace_extension_def] >> rpt strip_tac >> simp[]
QED

Theorem trace_item_fuel_preserved:
  (!orc p d fuel ctx inst s larger v.
    fuel <= larger /\ MEM v (trace_step orc p d fuel ctx inst s) ==>
    MEM v (trace_step orc p d larger ctx inst s)) /\
  (!orc p d fuel ctx fn bb s larger v.
    fuel <= larger /\ MEM v (trace_block orc p d fuel ctx fn bb s) ==>
    MEM v (trace_block orc p d larger ctx fn bb s)) /\
  (!orc p d fuel ctx fn s larger v.
    fuel <= larger /\ MEM v (trace_blocks orc p d fuel ctx fn s) ==>
    MEM v (trace_blocks orc p d larger ctx fn s))
Proof
  metis_tac[trace_fuel_extension, trace_extension_item_mem]
QED

Theorem trace_context_item_fuel_preserved:
  fuel <= larger /\ MEM v (trace_context orc fuel ctx s) ==>
  MEM v (trace_context orc larger ctx s)
Proof
  metis_tac[trace_context_fuel_extension, trace_extension_item_mem]
QED

Theorem trace_extension_result:
  trace_extension r ts r' ts' /\ (!err. r <> Error err) ==> r' = r
Proof
  simp[trace_extension_def] >> metis_tac[]
QED

Theorem ev_step_OK_fuel:
  fuel <= larger /\ ev_step orc p d fuel ctx inst s = OK u ==>
  ev_step orc p d larger ctx inst s = OK u
Proof
  strip_tac >> drule (cj 1 trace_fuel_extension) >>
  disch_then (qspecl_then [`orc`,`p`,`d`,`ctx`,`inst`,`s`] mp_tac) >>
  simp[] >> strip_tac >> drule trace_extension_result >> simp[]
QED

Theorem ev_block_OK_fuel:
  fuel <= larger /\ ev_block orc p d fuel ctx bb s = OK u ==>
  ev_block orc p d larger ctx bb s = OK u
Proof
  strip_tac >> drule (cj 2 trace_fuel_extension) >>
  disch_then (qspecl_then [`orc`,`p`,`d`,`ctx`,`fn`,`bb`,`s`] mp_tac) >>
  simp[] >> strip_tac >> drule trace_extension_result >> simp[]
QED

Theorem ev_blocks_OK_fuel:
  fuel <= larger /\ ev_blocks orc p d fuel ctx fn s = OK u ==>
  ev_blocks orc p d larger ctx fn s = OK u
Proof
  strip_tac >> drule (cj 3 trace_fuel_extension) >>
  disch_then (qspecl_then [`orc`,`p`,`d`,`ctx`,`fn`,`s`] mp_tac) >>
  simp[] >> strip_tac >> drule trace_extension_result >> simp[]
QED

Theorem trace_eventual_continuation:
  (!orc p d fuel ctx inst s.
    !v w tag. EVERY wf_function ctx.ctx_functions /\
      MEM v (trace_step orc p d fuel ctx inst s) /\ visit_edge orc ctx v w tag ==>
      !bound. ?larger. fuel <= larger /\ bound <= larger /\
        MEM w (trace_step orc p d larger ctx inst s)) /\
  (!orc p d fuel ctx fn bb s.
    !v w tag. EVERY wf_function ctx.ctx_functions /\ wf_function fn /\
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      MEM v (trace_block orc p d fuel ctx fn bb s) /\ visit_edge orc ctx v w tag ==>
      !bound. ?larger. fuel <= larger /\ bound <= larger /\
        (MEM w (trace_block orc p d larger ctx fn bb s) \/
         ?u. tag = SOME(p,d,fn,u) /\ ev_block orc p d larger ctx bb s = OK u)) /\
  (!orc p d fuel ctx fn s.
    !v w tag. EVERY wf_function ctx.ctx_functions /\ wf_function fn /\
      MEM v (trace_blocks orc p d fuel ctx fn s) /\ visit_edge orc ctx v w tag ==>
      !bound. ?larger. fuel <= larger /\ bound <= larger /\
        MEM w (trace_blocks orc p d larger ctx fn s))
Proof
  ho_match_mp_tac oracle_trace_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED

Resume trace_eventual_continuation[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gen_tac >>
  Cases_on `inst.inst_opcode = GAS`
  >- gvs[trace_step_eq, Once visit_edge_cases] >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (Cases_on `decode_invoke inst` >> gvs[trace_step_eq] >>
      PairCases_on `x` >> gvs[] >>
      Cases_on `lookup_function x0 ctx.ctx_functions` >> gvs[] >>
      rename1 `lookup_function x0 ctx.ctx_functions = SOME callee` >>
      Cases_on `eval_operands x1 s` >> gvs[] >>
      rename1 `eval_operands x1 s = SOME args` >>
      Cases_on `setup_callee callee args s` >> gvs[] >>
      `wf_function callee` by metis_tac[lookup_function_MEM, EVERY_MEM] >>
      first_x_assum drule_all >> simp[trace_step_eq]) >>
  gvs[trace_step_eq]
QED

Resume trace_eventual_continuation[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gen_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `MEM v _` mp_tac >> simp[Once trace_block_eq]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  Cases_on `v = TraceVisit p d fn inst s`
  >- suspend "head" >>
  gvs[] >> suspend "tail"
QED

Resume trace_eventual_continuation[head]:
  gvs[] >>
  rpt (qpat_x_assum `!x. _` kall_tac) >>
  qpat_x_assum `visit_edge _ _ _ _ _` mp_tac >>
  simp[Once visit_edge_cases] >> strip_tac >> gvs[]
  >- suspend "head_next"
  >- suspend "head_jump"
  >> suspend "head_callee"
QED

Resume trace_eventual_continuation[head_next]:
  `ev_step orc p d (MAX k (MAX fuel bound)) ctx inst s = OK u`
    by (irule ev_step_OK_fuel >> qexists_tac `k` >> simp[]) >>
  `ALL_DISTINCT (fn_labels fn)` by gvs[wf_function_def] >>
  drule_all ev_next_instruction_lookup >> strip_tac >>
  qexists_tac `MAX k (MAX fuel bound)` >>
  simp[Once trace_block_eq] >> simp[Once trace_block_eq]
QED

Resume trace_eventual_continuation[head_jump]:
  `ev_step orc p d (MAX k (MAX fuel bound)) ctx inst s = OK u`
    by (irule ev_step_OK_fuel >> qexists_tac `k` >> simp[]) >>
  qexists_tac `MAX k (MAX fuel bound)` >> simp[] >>
  disj2_tac >> simp[Once ev_defs]
QED

Resume trace_eventual_continuation[head_callee]:
  `wf_function callee` by metis_tac[lookup_function_MEM, EVERY_MEM] >>
  `ALL_DISTINCT (fn_labels callee)` by gvs[wf_function_def] >>
  qexists_tac `SUC (MAX fuel bound)` >>
  conj_tac >- (simp[MAX_DEF]) >>
  conj_tac >- (simp[MAX_DEF]) >>
  simp[Once trace_block_eq] >> disj1_tac >> irule trace_step_callee_entry >> metis_tac[]
QED

Resume trace_eventual_continuation[tail]:
  qpat_x_assum `MEM v _` mp_tac >>
  simp[Once trace_block_eq] >> strip_tac
  >- suspend "tail_step"
  >> suspend "tail_block"
QED

Resume trace_eventual_continuation[tail_step]:
  first_x_assum drule_all >> disch_then (qspec_then `bound` strip_assume_tac) >>
  qexists_tac `larger` >> simp[Once trace_block_eq]
QED

Resume trace_eventual_continuation[tail_block]:
  Cases_on `ev_step orc p d fuel ctx inst s` >> gvs[] >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
  rename1 `ev_step orc p d fuel ctx inst s = OK mid` >>
  `mid.vs_current_bb = s.vs_current_bb` by metis_tac[ev_step_nonterm_current_bb] >>
  gvs[] >> first_x_assum drule_all >>
  disch_then (qspec_then `bound` strip_assume_tac) >>
  `ev_step orc p d larger ctx inst s = OK mid`
    by (irule ev_step_OK_fuel >> qexists_tac `fuel` >> simp[]) >>
  qexists_tac `larger` >> simp[Once trace_block_eq] >>
  gvs[] >> disj2_tac >> simp[Once ev_defs]
QED

Resume trace_eventual_continuation[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gen_tac >>
  Cases_on `fuel`
  >- (qpat_x_assum `MEM v _` mp_tac >> simp[Once trace_blocks_eq]) >>
  rename1 `MEM v (trace_blocks orc p d (SUC fuel0) ctx fn s)` >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- (qpat_x_assum `MEM v _` mp_tac >> simp[Once trace_blocks_eq]) >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  gvs[] >>
  TRY (qpat_x_assum `MEM v _` mp_tac >> simp[Once trace_blocks_eq] >> NO_TAC) >>
  rename1 `eval_phis s bb.bb_instructions = OK sp` >>
  drule eval_phis_preserves_current_bb >> strip_tac >> gvs[] >>
  qpat_x_assum `MEM v _` mp_tac >> simp[Once trace_blocks_eq] >> strip_tac
  >- suspend "blocks_head"
  >> suspend "blocks_tail"
QED

Resume trace_eventual_continuation[blocks_head]:
  first_x_assum drule_all >>
  disch_then (qspec_then `bound` strip_assume_tac)
  >- suspend "blocks_head_mem"
  >> suspend "blocks_head_exit"
QED

Resume trace_eventual_continuation[blocks_head_mem]:
  qexists_tac `SUC larger` >> simp[Once trace_blocks_eq] >> simp[MAX_DEF]
QED

Resume trace_eventual_continuation[blocks_head_exit]:
  gvs[] >>
  `ALL_DISTINCT (fn_labels fn)` by gvs[wf_function_def] >>
  drule visit_edge_jump_target >> strip_tac >>
  `MEM w (trace_blocks orc p (SUC d) (SUC larger) ctx fn u)`
    by (irule visit_edge_jump_entry >> metis_tac[]) >>
  `ev_block orc p (SUC d) (SUC larger) ctx bb
     (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK u`
    by (irule ev_block_OK_fuel >> qexists_tac `larger` >> simp[]) >>
  qexists_tac `SUC (SUC larger)` >>
  gvs[] >> simp[Once trace_blocks_eq]
QED

Resume trace_eventual_continuation[blocks_tail]:
  Cases_on `ev_block orc p (SUC d) fuel0 ctx bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >> gvs[] >>
  rename1 `ev_block _ _ _ _ _ _ _ = OK mid` >>
  Cases_on `mid.vs_halted` >> gvs[] >>
  first_x_assum drule_all >>
  disch_then (qspec_then `bound` strip_assume_tac) >>
  `ev_block orc p (SUC d) larger ctx bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK mid`
    by (irule ev_block_OK_fuel >> qexists_tac `fuel0` >> simp[]) >>
  qexists_tac `SUC larger` >> simp[Once trace_blocks_eq]
QED

Finalise trace_eventual_continuation

Theorem trace_step_eventual_continuation:
  EVERY wf_function ctx.ctx_functions /\
  MEM v (trace_step orc p d fuel ctx inst s) /\ visit_edge orc ctx v w tag ==>
  !bound. ?larger. fuel <= larger /\ bound <= larger /\
    MEM w (trace_step orc p d larger ctx inst s)
Proof
  metis_tac[cj 1 trace_eventual_continuation]
QED

Theorem trace_block_eventual_continuation:
  EVERY wf_function ctx.ctx_functions /\ wf_function fn /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  MEM v (trace_block orc p d fuel ctx fn bb s) /\ visit_edge orc ctx v w tag ==>
  !bound. ?larger. fuel <= larger /\ bound <= larger /\
    (MEM w (trace_block orc p d larger ctx fn bb s) \/
     ?u. tag = SOME(p,d,fn,u) /\ ev_block orc p d larger ctx bb s = OK u)
Proof
  metis_tac[cj 2 trace_eventual_continuation]
QED

Theorem trace_blocks_eventual_continuation:
  EVERY wf_function ctx.ctx_functions /\ wf_function fn /\
  MEM v (trace_blocks orc p d fuel ctx fn s) /\ visit_edge orc ctx v w tag ==>
  !bound. ?larger. fuel <= larger /\ bound <= larger /\
    MEM w (trace_blocks orc p d larger ctx fn s)
Proof
  metis_tac[cj 3 trace_eventual_continuation]
QED
