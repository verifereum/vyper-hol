(* Rejected external-call code checks, at an arbitrary allocation floor. *)
Theory bodyFullExtCallPrecheckExit
Ancestors
  exprSimSliceExtcode exprSimAccounts exprSimDefs typedCopyOriginPtrBase extCallCodeCheck
  fragGasSeqPtr fragGasOriginPtr fragGasOrigin fragGasPathPtr
  fragExec emitHelper emitHelperProps exprLoweringProps exprLowering compileEnv
  ptrSafeRun ptrDiscipline memSafeRun instMemFrontier unitTransformDefs codegenRel contextCodegenRel gasEvents gasCount
  accountsRelProps loweringStateRelDefs vyperInterpreter
  venomExecSemantics venomInst venomState finite_map pred_set list

Theorem extcall_extcodesize_checked[local]:
  emit_op EXTCODESIZE [addr] a = (op,b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  eval_operand addr s = SOME aw /\ op_taint tn addr = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ?out t G' tn'. op = Var out /\
    eval_operand op t = SOME (n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)) /\
    op_taint tn' op = {} /\ allocas_from lo t /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >>
  drule_all extcall_extcodesize_exact_edge >>
  disch_then (qspecl_then [`explicit`, `PG`, `G`] strip_assume_tac) >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  `b.cs_current_bb = a.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  qabbrev_tac `inst = mk_inst a.cs_next_id EXTCODESIZE [addr]
    [STRING #"%" (toString a.cs_next_var)]` >>
  qabbrev_tac `w : bytes32 = n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)` >>
  qabbrev_tac `u = update_var (STRING #"%" (toString a.cs_next_var)) w s` >>
  qexistsl_tac [`u with vs_inst_idx := SUC s.vs_inst_idx`,
    `step_prov PG G inst u`, `step_taint inst s u tn`] >>
  conj_tac >- simp[Abbr `u`, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- simp[Abbr `inst`, step_taint_def, set_var_taint_def,
    out_taint_def, op_taint_def, FLOOKUP_UPDATE, mk_inst_def] >>
  conj_tac >- (gvs[Abbr `u`, allocas_from_def, update_var_def] >> metis_tac[]) >>
  simp[Abbr `u`, update_var_def] >> gen_tac >>
  qpat_x_assum `!D lo. _` (qspecl_then [`D`,`lo`] mp_tac) >>
  simp[Abbr `inst`, Abbr `w`, update_var_def] >> strip_tac >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  disch_then (qspec_then `[]` mp_tac) >> simp[] >>
  disch_then irule >>
  irule (cj 1 gas_origin_ptr_path_rules) >> simp[]
QED

Theorem extcall_assert_zero_checked[local]:
  emit_void ASSERT [op] a = ((),b) /\ fn_has_code a b func /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  eval_operand op s = SOME 0w /\ op_taint tn op = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ?t. !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (Abort Revert_abort t,G,tn)
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  `b.cs_current_bb = a.cs_current_bb` by
    gvs[emit_void_def, comp_bind_def, fresh_id_def, emit_def, comp_return_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME (mk_inst a.cs_next_id ASSERT [op] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qmatch_asmsub_abbrev_tac `get_instruction bb _ = SOME inst` >>
  qabbrev_tac `r = revert_state (set_returndata [] s)` >>
  `step_inst_base inst s = Abort Revert_abort r` by
    simp[Abbr `inst`, Abbr `r`, step_ASSERT_revert] >>
  qexists_tac `r` >> gen_tac >>
  irule (cj 3 gas_origin_ptr_path_rules) >> simp[exit_result_def] >>
  rewrite_tac[gas_origin_ptr_edge_def] >> conj_tac
  >- (rewrite_tac[gas_origin_edge_def] >> simp[] >>
      qexistsl_tac [`0`, `inst`] >>
      simp[step_inst_non_invoke, Abbr `inst`, mk_inst_def] >>
      fs[mk_inst_def, step_inst_non_invoke, exit_result_def,
        mem_safe_step_non_invoke, inst_mem_below_frontier_def,
        inst_dload_in_section_def, source_memory_write_ranges_def,
        source_memory_read_ranges_def, gas_events_step_def,
        is_terminator_def]) >>
  rewrite_tac[gas_path_ptr_edge_def] >> simp[] >> qexists_tac `0` >>
  qexists_tac `inst` >>
  simp[Abbr `inst`, mk_inst_def, step_inst_non_invoke, gas_count_step_def,
    ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
    source_memory_write_ranges_def, source_memory_read_ranges_def,
    exit_result_def] >> fs[mk_inst_def]
QED

Theorem extcall_precheck_exit_path:
  (if ret_type = NoneT /\ ~skip then compile_extcodesize_check addr_op
   else comp_return ()) sp = ((),s1) /\
  fn_has_code sp s1 func /\
  t.vs_current_bb = sp.cs_current_bb /\
  t.vs_inst_idx = LENGTH sp.cs_current_insts /\ ~t.vs_halted /\
  stmt_state_rel H ctx func cenv cx ee t /\
  accounts_runtime_well_typed ee.accounts /\
  eval_operand addr_op t = SOME aw /\ w2w aw = target /\
  op_taint tn addr_op = {} /\ allocas_from lo t /\ ~ctx_has_dalloca ctx /\
  ~ext_call_precheck_ok skip ret_type target ee.accounts ==>
  ?r G' tn'. exit_result r /\
    expr_exit (INR (Error (RuntimeError "ExtCall target has no code"))) r /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (t,G,tn) [] (r,G',tn')
Proof
  strip_tac >>
  `ret_type = NoneT /\ ~skip /\ (lookup_account target ee.accounts).code = []` by
    (Cases_on `ret_type` >>
     gvs[ext_call_precheck_ok_def, ext_call_has_code_def, NULL_EQ]) >> gvs[] >>
  `accounts_agree H cx ee.accounts t.vs_accounts` by
    fs[stmt_state_rel_def, state_rel_def, accounts_rel_def] >>
  drule accounts_agree_lookup >> disch_then (qspec_then `w2w aw` assume_tac) >>
  `compile_extcodesize_check addr_op sp = ((),s1)` by simp[] >>
  qpat_x_assum `compile_extcodesize_check _ _ = _` mp_tac >>
  simp[compile_extcodesize_check_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op EXTCODESIZE [addr_op] sp = (sz,sm)` >>
  `cs_extends sp sm /\ cs_extends sm s1` by
    (conj_tac >- metis_tac[emit_op_extends_next_var] >>
     irule cs_extends_emit_inst >>
     qexistsl_tac [`ASSERT`, `[sz]`, `[]`] >>
     fs[emit_void_def, emit_inst_def]) >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all extcall_extcodesize_checked >>
  disch_then (qspecl_then [`explicit`, `PG`, `G`] strip_assume_tac) >>
  gvs[] >>
  drule_all extcall_assert_zero_checked >>
  disch_then (qspecl_then [`explicit`, `PG`, `G'`] strip_assume_tac) >>
  qexistsl_tac [`Abort Revert_abort t''`, `G'`, `tn'`] >>
  simp[expr_exit_def, exit_result_def] >> gen_tac >>
  metis_tac[gas_origin_ptr_path_append, APPEND]
QED
