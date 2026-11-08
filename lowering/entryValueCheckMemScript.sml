(* The rejecting nonpayable check is independent of the appended body. *)
Theory entryValueCheckMem
Ancestors
  fragExecMem fragExec moduleLowering compileEnv emitHelper emitHelperProps
  instMemFrontier venomExecSemantics venomState venomInst list rich_list
  words finite_map entryCompileIntervals exprLoweringProps moduleLoweringProps
  entryDispatchMem

Theorem payable_prefix_mem[local]:
  emit_op CALLVALUE [] sa = (cv,sb) /\
  emit_op ISZERO [cv] sb = (nv,sc) /\
  emit_void ASSERT [nv] sc = ((),sd) /\
  fresh_vars_wrt sa s0 /\
  s0.vs_call_ctx.cc_callvalue <> 0w ==>
  frag_exec_mem ctx sa sd (\s. s = s0) (\t. F)
    (\r. ?t. r = Abort Revert_abort t)
Proof
  strip_tac >>
  drule_all compile_payable_check_ok_or_revert >> strip_tac >> gvs[] >>
  qpat_x_assum `emit_op CALLVALUE _ _ = _` mp_tac >>
  qpat_x_assum `emit_op ISZERO _ _ = _` mp_tac >>
  qpat_x_assum `emit_void ASSERT _ _ = _` mp_tac >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
    fresh_var_def, fresh_id_def, emit_def, comp_return_def] >>
  rpt strip_tac >> gvs[] >> irule frag_exec_mem_run_inst_seq >>
  simp[emitted_insts_def, APPEND_ASSOC, DROP_LENGTH_APPEND,
    mk_inst_def, is_terminator_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[is_terminator_def] >> conj_tac
  >- (irule run_inst_seq_mem_ok_every >> simp[EVERY_DEF] >>
      rpt conj_tac >> gen_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[emitted_insts_def, mk_inst_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[] >> metis_tac[]
QED

Theorem compile_entry_checks_value_revert_mem:
  !m sa sb ctx s0.
    compile_entry_checks m F sa = ((),sb) /\
    fresh_vars_wrt sa s0 /\ s0.vs_call_ctx.cc_callvalue <> 0w ==>
    frag_exec_mem ctx sa sb (\s. s = s0) (\t. F)
      (\r. ?t. r = Abort Revert_abort t)
Proof
  rpt gen_tac >>
  simp[compile_entry_checks_def, comp_bind_def, comp_ignore_bind_def,
    pairTheory.pair_case_eq] >>
  rpt strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  drule_all payable_prefix_mem >> disch_then (qspec_then `ctx` assume_tac) >>
  irule frag_exec_mem_exit_prefix >> goal_assum (drule_at Any) >>
  conj_tac
  >- (imp_res_tac (SRULE [cs_appends_def] cs_appends_emit_helpers) >>
      metis_tac[cs_extends_trans]) >>
  Cases_on `4 < m` >> gvs[comp_bind_def, comp_ignore_bind_def,
    comp_return_def, pairTheory.pair_case_eq] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_emit_helpers) >>
  metis_tac[cs_extends_trans, cs_extends_refl]
QED

Theorem entry_checks_value_revert_mem_safe:
  !m sa sb ctx s0 fn.
    compile_entry_checks m F sa = ((),sb) /\
    fresh_vars_wrt sa s0 /\ s0.vs_call_ctx.cc_callvalue <> 0w /\
    fn_has_code sa sb fn /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    !fuel. mem_safe_run fuel ctx fn s0
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_entry_checks_value_revert_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule frag_exec_mem_complete >>
  disch_then irule >> simp[]
QED

Theorem entry_checks_callvalue_interval[local]:
  compile_entry_checks m F sa = ((),sb) ==>
  ?cv sc. emit_op CALLVALUE [] sa = (cv,sc) /\ cs_extends sc sb
Proof
  simp[compile_entry_checks_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_emit_helpers) >>
  Cases_on `4 < m` >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_emit_helpers) >>
  metis_tac[cs_extends_trans, cs_extends_refl]
QED

Theorem entry_checks_no_phi[local]:
  compile_entry_checks m F sa = ((),sb) /\ sa.cs_current_insts = [] /\
  fn_has_code sa sb fn ==>
  ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
       (!s. eval_phis s bb.bb_instructions = OK s) /\
       phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >> drule entry_checks_callvalue_interval >> strip_tac >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_emit_helpers) >>
  `fn_has_code sa sc fn` by metis_tac[fn_has_code_split] >>
  qpat_x_assum `emit_op CALLVALUE _ _ = _` mp_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def,
       emit_def, comp_return_def] >> strip_tac >> gvs[] >>
  gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
  simp[eval_phis_def, phi_prefix_length_def, mk_inst_def]
QED

Theorem entry_checks_value_revert_mem_safe_blocks:
  compile_entry_checks m F sa = ((),sb) /\ sa.cs_current_insts = [] /\
  fresh_vars_wrt sa s0 /\ s0.vs_call_ctx.cc_callvalue <> 0w /\
  fn_has_code sa sb fn /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = 0 ==>
  !fuel. mem_safe_blocks fuel ctx fn s0
Proof
  strip_tac >> drule_all entry_checks_no_phi >> strip_tac >>
  `s0 with vs_inst_idx := 0 = s0` by simp[venom_state_component_equality] >>
  irule mem_safe_blocks_no_phi >> simp[] >>
  irule entry_checks_value_revert_mem_safe >> simp[] >>
  qexistsl_tac [`m`, `sa`, `sb`] >> simp[]
QED
