(* Exact optional unlock followed by an internal bare return. *)
Theory bodyIntCallReturnUnlockBare
Ancestors
  bodyIntCallJointContract bodyIntCallSharpReturn bodyIntCallFamStmtReturnStackRun
  bodySim stmtSimReturn stmtSimDefs loweringPosts compileEnv loweringStateRelDefs ctorReturnFrame
  stmtLowering vyperTyping vyperInterpreter gasOutcome gasSummary
  gasSummaryCompose venomExecSemantics venomState fragExec emitHelperProps
  emitHelper exprLoweringProps

Theorem compile_unlock_bare_ret_path:
  compile_return_unlock ce sa = ((),sm) /\
  emit_inst RET [rpc] [] sm = ((),sb) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (?pc. eval_operand rpc s = SOME pc) ==>
  gas_path ctx func s 0
    (IntRet <|iret_values := []; iret_adopt_fmp := NONE|>
      (return_unlock_state ce s))
Proof
  strip_tac >> drule compile_return_unlock_shape >> strip_tac >>
  `?u. run_inst_seq (return_unlock_insts ce sa.cs_next_id) s = OK u /\
     u.vs_current_bb = s.vs_current_bb /\ ~u.vs_halted /\
     eval_operand rpc u = SOME pc /\
     u with vs_inst_idx := s.vs_inst_idx + LENGTH (return_unlock_insts ce sa.cs_next_id) =
       return_unlock_state ce s /\
     EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
       (return_unlock_insts ce sa.cs_next_id) /\
     LENGTH (FILTER (\i. i.inst_opcode = GAS) (return_unlock_insts ce sa.cs_next_id)) = 0` by
    (qabbrev_tac `info = ce.ce_nonreentrant` >> PairCases_on `info` >>
     Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
     gvs[return_unlock_insts_def, return_unlock_state_def,
         run_inst_seq_def, venomExecSemanticsTheory.step_inst_base_def,
         venomExecSemanticsTheory.exec_write2_def, eval_operand_def,
         venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def,
         tstore_def, sstore_def, arithmeticTheory.ADD1] >>
     Cases_on `rpc` >> gvs[eval_operand_def, lookup_var_def,
       venom_state_component_equality]) >>
  qpat_x_assum `_ with vs_inst_idx := _ = _` (SUBST1_TAC o SYM) >>
  qpat_x_assum `LENGTH (FILTER _ _) = 0` (SUBST1_TAC o SYM) >>
  irule emitted_seq_values_ret_path >> simp[] >>
  qexistsl_tac [`[]`, `pc`, `rpc`, `sa`, `sb`, `sm`] >>
  simp[eval_operands_def]
QED

Theorem intcall_bare_return_unlock_producer:
  intcall_stmts_producer fp [Return NONE]
Proof
  simp[intcall_stmts_producer_def] >> rpt strip_tac >>
  `fp.jc_ret_ty = NoneT` by
    gvs[vyperTypeSystemTheory.type_stmt_def, AllCaseEqs()] >>
  `ce.ce_return_pc = SOME (PtrVar fp.jc_rpc 0)` by
    fs[intcall_joint_res_def, intcall_expr_res_def, intcall_frame_ok_def, same_frame_def,
       compile_env_component_equality] >>
  `?sm. compile_return_unlock ce sa = ((),sm) /\
     emit_inst RET [fp.jc_rpc] [] sm = ((),sb)` by
    (qpat_x_assum `stmts_env _ _ _ _ _ = _` mp_tac >>
     simp[stmts_env_def, stmtLoweringTheory.declare_stmt_local_def,
          stmtLoweringTheory.compile_stmt_def, comp_get_def,
          comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
     Cases_on `compile_return_unlock ce sa` >>
     rename1 `compile_return_unlock ce sa = (unit,mid)` >>
     Cases_on `unit` >> simp[] >>
     Cases_on `emit_inst RET [fp.jc_rpc] [] mid` >> simp[] >> metis_tac[]) >>
  `gas_path fp.jc_ctx fp.jc_func s 0
     (IntRet <|iret_values := []; iret_adopt_fmp := NONE|>
       (return_unlock_state ce s))` by
    (irule compile_unlock_bare_ret_path >>
     simp[] >> conj_tac
     >- fs[intcall_joint_res_def, intcall_expr_res_def,
           stmt_state_rel_def, state_rel_def] >>
     qexistsl_tac [`fp.jc_rpc`, `sa`, `sb`, `sm`] >>
     fs[intcall_joint_res_def, intcall_expr_res_def,
        stmt_state_rel_def, state_rel_def]) >>
  `return_unlock_state ce s = return_unlock_state fp.jc_root_ce s` by
    fs[intcall_joint_res_def, intcall_expr_res_def, same_frame_def,
       compile_env_component_equality, return_unlock_state_def] >>
  simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR (ReturnException NoneV)`, `es`,
    `IntRet <|iret_values := []; iret_adopt_fmp := NONE|>
       (return_unlock_state fp.jc_root_ce s)`] >>
  conj_tac
  >- (simp[gas_marked_exec_def, gas_explicit_def,
           fragGasModeTheory.gas_marked_path_def,
           vyperInterpreterTheory.evaluate_def,
           vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
           vyperStateTheory.raise_def] >> metis_tac[]) >>
  simp[exit_result_def, intcall_stmt_exit_def] >> disj2_tac >>
  fs[intcall_joint_res_def, intcall_expr_res_def, intcall_frame_ok_def,
     returns_stack_count_def, vyperValueTheory.evaluate_type_def,
     eval_operand_return_unlock] >>
  simp[intret_q_def] >> qexists_tac `s` >>
  simp[result_rel_def, intret_vals_match_def, state_rel_gas_obs] >>
  irule constructor_exit_state_rel >> qexists_tac `ce` >>
  fs[stmt_state_rel_def, state_rel_gas_obs]
QED
