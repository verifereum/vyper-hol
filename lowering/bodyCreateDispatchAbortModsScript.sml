(* The first creation instruction can exit without consuming an outcome.
   Its read window must still satisfy the memory and pointer checks. *)
Theory bodyCreateDispatchAbortMods
Ancestors
  builtinCreate compileEnv emitHelper fragExec bodyPtrMakeArrayEmission externalEntryShape
  fragGasEmitCtrl fragGasOriginPtr gasEvents gasCount gasOutcomeFullPostMods
  bodyFullShadowBodyInv bodyPtrDefs ptrDiscipline ptrDisciplineTaintProps
  memSafeRun unitTransformDefs contextCodegenRel codegenRel memLocDefs ptrSafeRun
  venomExecSemantics venomState venomInst venomMemDefs
  exprSimDefs exprLoweringProps loweringStateRelDefs stateRelProj createSizeExit
  vyperCreate vyperInterpreter vyperCallOutcome vyperState vyperStorageFootprint
  words list
Libs
  pairLib

Theorem create_dispatch_fetch[local]:
  compile_create_dispatch codep len amount sop rof sm = (result,sb) /\
  fn_has_code sm sb func /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?out bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst sm.cs_next_id (if IS_SOME sop then CREATE2 else CREATE)
        ([amount;codep;len] ++ (case sop of NONE => [] | SOME p => [p])) [out])
Proof
  `(case sop of NONE => emit_op CREATE [amount;codep;len]
      | SOME p => emit_op CREATE2 [amount;codep;len;p]) =
    emit_op (if IS_SOME sop then CREATE2 else CREATE)
      ([amount;codep;len] ++ (case sop of NONE => [] | SOME p => [p]))` by
    (Cases_on `sop` >> simp[]) >>
  simp[compile_create_dispatch_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_check_create_result optmp rof mid = (result,sb)` >>
  `cs_extends sm mid` by
    (irule (REWRITE_RULE [cs_appends_def] (cj 2 cs_appends_emit_helpers)) >>
     goal_assum (drule_at Any)) >>
  `cs_extends mid sb` by
    (qspecl_then [`optmp`,`rof`,`mid`] mp_tac compile_check_create_result_labels >> simp[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all emit_op_fetch_boundary >> strip_tac >>
  qexistsl_tac [`tmp`,`bb`] >> gvs[]
QED

Theorem create_dispatch_abort_path[local]:
  ((inst.inst_opcode = CREATE /\ inst.inst_operands = [amount;bufop;len]) \/
   (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [amount;bufop;len;salt] /\
    (?sw. eval_operand salt s = SOME sw))) /\
  eval_operand amount s = SOME value /\
  eval_operand bufop s = SOME off /\ eval_operand len s = SOME sz /\
  (sz <> 0w ==> ?p. bufop = Var p /\ ptr_covers G tn p s (w2n sz)) /\
  (sz <> 0w ==> w2n off + w2n sz <= s.vs_alloca_next \/
    (ctx_has_dalloca ctx /\ w2n s.vs_initial_fmp <= w2n off /\
     w2n off + w2n sz <= w2n s.vs_fmp)) /\
  EVERY (\op. op_taint tn op = {}) inst.inst_operands /\
  (!j. w2n off <= j /\ j < w2n off + w2n sz ==> j NOTIN tn.t_mem) /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  stor_taint_ok_at D tn s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ step_inst_base inst s = Abort ab u ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (Abort ab u,G,tn)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `source_memory_read_ranges inst s = [(w2n off,w2n sz)] /\
   source_memory_write_ranges inst s = [] /\
   mem_read_ops inst = SOME <|iao_ofst := bufop; iao_size := SOME len;
                              iao_max_size := SOME len|> /\
   inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS` by
    (qpat_assum `_ \/ _` strip_assume_tac >>
     simp[source_memory_read_ranges_def, source_memory_write_ranges_def,
          memory_range_of_operands_def, mem_read_ops_def]) >>
  `access_ok lo G func inst s` by
    (simp[access_ok_def] >> rpt strip_tac >>
     `sz <> 0w` by fs[] >>
     qpat_assum `sz <> 0w ==> ?p. _` drule >> strip_tac >>
     gvs[ptr_covers_def, eval_operand_def] >> metis_tac[]) >>
  `taint_ok func tn inst s` by
    (irule taint_ok_clean_step >> simp[]) >>
  `ptr_inst_ok D lo 0 ctx func G tn inst s` by
    (qpat_assum `_ \/ _` strip_assume_tac >>
     gvs[ptr_inst_ok_def, stor_taint_ok_at_def, step_inst_non_invoke] >> metis_tac[]) >>
  `mem_safe_step 0 ctx inst s` by
    (qpat_assum `_ \/ _` strip_assume_tac >> Cases_on `sz = 0w` >>
     simp[mem_safe_step_non_invoke, inst_mem_below_frontier_def,
          inst_mem_below_frontiers_def, w2n_eq_0] >> metis_tac[]) >>
  irule exit_inst_origin_ptr >> simp[exit_result_def] >>
  simp[step_inst_non_invoke, mem_safe_step_non_invoke, gas_events_step_def,
       gas_count_step_def]
QED

Theorem create_dispatch_preconsume_mods:
  compile_create_dispatch codep len amount sop rof sm = (result,sb) /\
  fn_has_code sm sb func /\ ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s) /\
  eval_operand codep s = SOME pv /\ eval_operand len s = SOME sz /\
  (sz <> 0w ==> ?p. codep = Var p /\ ptr_covers G tn p s (w2n sz)) /\
  (sz <> 0w ==> w2n pv + w2n sz <= s.vs_alloca_next \/
    (ctx_has_dalloca ctx /\ w2n s.vs_initial_fmp <= w2n pv /\
     w2n pv + w2n sz <= w2n s.vs_fmp)) /\
  (!i. w2n pv <= i /\ i < w2n pv + w2n sz ==> i NOTIN tn.t_mem) /\
  op_taint tn codep = {} /\ op_taint tn len = {} /\
  eval_operand amount s = SOME aw /\ op_taint tn amount = {} /\
  (case sop of NONE => sw = NONE | SOME op =>
     ?w. sw = SOME w /\ eval_operand op s = SOME w /\ op_taint tn op = {}) /\
  (!tail. source (ee with gas_obs := tail) =
    if w2n sz > 2 * max_code_size then
      (INR (Error (RuntimeError "create initcode too large")),ee with gas_obs := tail)
    else
      bind (ignore_bind (check_not_static cx)
        (create_oracle_result sw (w2n aw) initcode rof))
        (read_result cx) (ee with gas_obs := tail)) /\
  (w2n sz > 2 * max_code_size \/ cx.txn.is_static \/ s.vs_outcomes = []) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    source (ee,s,G,tn) Q
    (\H res ee' gt r. expr_exit res r /\ halt_exit H cx ee' res r /\
       (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all create_dispatch_fetch >> strip_tac >>
  qabbrev_tac `inst = mk_inst sm.cs_next_id (if IS_SOME sop then CREATE2 else CREATE)
    ([amount;codep;len] ++ (case sop of NONE => [] | SOME p => [p])) [out]` >>
  `inst.inst_outputs = [out] /\ EVERY (\op. op_taint tn op = {}) inst.inst_operands` by
    (Cases_on `sop` >> gvs[Abbr `inst`,mk_inst_def]) >>
  Q.SUBGOAL_THEN
    `((inst.inst_opcode = CREATE /\ inst.inst_operands = [amount;codep;len]) \/
      (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [amount;codep;len;THE sop] /\
         ?w. eval_operand (THE sop) s = SOME w))` ASSUME_TAC
  >- (Cases_on `sop` >> gvs[Abbr `inst`,mk_inst_def]) >>
  `step_inst_base inst s =
    if s.vs_call_ctx.cc_static then Abort ExHalt_abort (halt_state (set_returndata [] s))
    else exec_create inst s aw pv sz sw` by
    (Cases_on `sop` >> gvs[Abbr `inst`,mk_inst_def,step_inst_base_opcode_eqs,eval_operands_def]) >>
  `ee.outcomes = SOME s.vs_outcomes /\ s.vs_call_ctx.cc_static = cx.txn.is_static` by
    (`valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
       by fs[storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _` (drule_then strip_assume_tac) >>
     fs[stmt_state_rel_def,state_rel_def,call_ctx_rel_def]) >>
  `step_inst_base inst s = Abort ExHalt_abort (halt_state (set_returndata [] s))` by
    (Cases_on `cx.txn.is_static` >> gvs[exec_create_abort_iff]) >>
  qabbrev_tac `msg = if w2n sz > 2 * max_code_size then "create initcode too large"
    else if cx.txn.is_static then "write in static context" else "take_create_outcome"` >>
  `!tail. source (ee with gas_obs := tail) =
    (INR (Error (RuntimeError msg)),ee with gas_obs := tail)` by
    (gen_tac >> qpat_assum `!tail. source _ = _` (fn th => rewrite_tac[th]) >>
     Cases_on `w2n sz > 2 * max_code_size` >> simp[Abbr `msg`] >>
     Cases_on `cx.txn.is_static` >> fs[bind_def,ignore_bind_def,
       create_oracle_result_def,take_create_outcome_exhausted]) >>
  irule gas_outcome_full_mods_exit >> simp[] >>
  qexistsl_tac [`G`,`ee`,`Abort ExHalt_abort (halt_state (set_returndata [] s))`,
                `INR (Error (RuntimeError msg))`,`tn`] >>
  simp[exit_result_def,expr_exit_def,halt_exit_def] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _` (drule_then strip_assume_tac) >>
  `allocas_from lo s /\ stor_taint_ok_at (DF H) tn s` by fs[ghost_inv_at_mods_def] >>
  drule_all create_dispatch_abort_path >> simp[] >> disch_tac >>
  Cases_on `w2n sz > 2 * max_code_size` >- simp[Abbr `msg`] >>
  Cases_on `s.vs_call_ctx.cc_static`
  >- simp[halt_state_def,set_returndata_def] >>
  strip_tac >>
  `MEM func ctx.ctx_functions` by
    (drule stmt_state_rel_alloca_room >> simp[alloca_room_def] >>
     strip_tac >> drule lookup_function_MEM >> simp[]) >>
  drule_all oversized_create_abort_at_cursor >> strip_tac >>
  qpat_assum `inst.inst_opcode = CREATE /\ _ \/ _` strip_assume_tac >>
  gvs[]
QED
