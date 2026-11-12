(* Memory-safe optional guard release before internal-return loads. *)
Theory internalReturnUnlockMem
Ancestors
  stmtSimReturn fragExecMem instMemFrontier nonreentrantEquiv transientLockProps
  stmtLowering context compileEnv emitHelper emitHelperProps exprLoweringProps
  venomExecSemantics venomState venomInst memSafeRun list rich_list arithmetic

Theorem compile_return_unlock_frag_mem:
  !cenv sa sb ctx sv.
    compile_return_unlock cenv sa = ((),sb) /\
    sv.vs_inst_idx = LENGTH sa.cs_current_insts /\
    ~sv.vs_call_ctx.cc_static ==>
    frag_exec_mem ctx sa sb (\s. s = sv)
      (\s. s = return_unlock_state cenv sv) (\r. F)
Proof
  rpt gen_tac >> strip_tac >>
  irule frag_exec_mem_run_inst_seq >>
  qabbrev_tac `info = cenv.ce_nonreentrant` >> PairCases_on `info` >>
  Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
  gvs[compile_return_unlock_def, compile_nonreentrant_unlock_def,
      return_unlock_state_def, comp_return_def, emit_void_def,
      comp_bind_def, fresh_id_def, emit_def, emitted_insts_def,
      DROP_LENGTH_APPEND, IS_PREFIX_APPEND] >>
  simp[run_inst_seq_mem_ok_def, below_frontier_no_ranges,
       inst_dload_in_section_other, mk_inst_def, is_terminator_def] >>
  simp[run_inst_seq_def,
       SRULE [mk_inst_def] stmtSimReturnTheory.step_persistent_return_unlock,
       SRULE [mk_inst_def] transientLockPropsTheory.step_TSTORE_lit, ADD1] >>
  simp[venom_state_component_equality]
QED

Theorem return_unlock_alloca_next[simp]:
  (return_unlock_state cenv s).vs_alloca_next = s.vs_alloca_next
Proof
  qabbrev_tac `info = cenv.ce_nonreentrant` >> PairCases_on `info` >>
  Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
  simp[return_unlock_state_def, tstore_def, sstore_def]
QED
