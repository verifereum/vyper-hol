(* Controlled joint witness for the explicit source GAS read. *)
Theory bodyIntCallGasJoint
Ancestors
  msgGasPost msgGasSim gasOutcome gasSummary fragGasMode fragGasPathMem
  exprSimProps exprSimHypsDefs exprLoweringProps exprLowering
  loweringPosts venomState vyperState vyperInterpreter

Theorem compile_msg_gas_joint_post:
  !ctx func cenv cx env ty ann args es sa sb op s0.
    expr_sim_pre cenv cx env (Builtin ann (Env MsgGas) args) es /\
    lower_value compile_expr cenv ty (Builtin ann (Env MsgGas) args) sa =
      (op, sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_summary_at T (ctx, func) [T]
      (bind (eval_expr cx (Builtin ann (Env MsgGas) args)) (read_result cx))
      (es, s0)
      (\res ee t.
         (?v. res = INL v /\
              expr_post ctx func cenv cx (Builtin ann (Env MsgGas) args)
                es sa sb s0 ee v op t) /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts /\
         t.vs_memory = s0.vs_memory /\
         contract_storage t = contract_storage s0 /\
         contract_transient t = contract_transient s0)
      (\res ee r. F)
Proof
  rpt strip_tac >> drule msg_gas_typed >> strip_tac >> gvs[] >>
  drule lower_value_env >> strip_tac >>
  drule_all compile_msg_gas_mem_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `expr_post ctx func cenv cx (Builtin (env_item_type MsgGas) (Env MsgGas) [])
    es sa sb s0 (es with gas_obs := []) (IntV (&w2n w)) (Var out)
    (update_var out w (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
                               vs_inst_idx := LENGTH sb.cs_current_insts|>))` by
    (irule msg_gas_post_frame >> simp[]) >>
  `gas_explicit [T] s0.vs_gas_readings = [w]`
    by simp[gas_explicit_def] >>
  rewrite_tac[gas_summary_at_def, gas_marked_exec_def, gas_marked_path_def] >>
  qexistsl_tac [`INL (IntV (&w2n w))`, `es`,
    `OK (update_var out w
      (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
                 vs_inst_idx := LENGTH sb.cs_current_insts|>))`] >>
  simp[msg_gas_source] >>
  gvs[update_var_def, contract_storage_def, contract_transient_def]
QED

Theorem compile_msg_gas_joint_outcome:
  !ctx func cenv cx env ty ann args es sa sb op s0.
    expr_sim_pre cenv cx env (Builtin ann (Env MsgGas) args) es /\
    lower_value compile_expr cenv ty (Builtin ann (Env MsgGas) args) sa =
      (op, sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx, func)
      (bind (eval_expr cx (Builtin ann (Env MsgGas) args)) (read_result cx))
      (es, s0)
      (\res ee t.
         (?v. res = INL v /\
              expr_post ctx func cenv cx (Builtin ann (Env MsgGas) args)
                es sa sb s0 ee v op t) /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts /\
         t.vs_memory = s0.vs_memory /\
         contract_storage t = contract_storage s0 /\
         contract_transient t = contract_transient s0)
      (\res ee r. F)
Proof
  rpt strip_tac >> drule_all compile_msg_gas_joint_post >> strip_tac >>
  pure_rewrite_tac[gas_outcome_def] >> qexists_tac `[T]` >> disj1_tac >>
  fs[gas_summary_at_def, gas_marked_exec_def, gas_marked_path_def] >>
  rename1 `expr_post ctx func cenv cx _ es sa sb s0
             (ee with gas_obs := []) v op t` >>
  qexistsl_tac [`INL v`, `ee`, `OK t`] >> simp[] >>
  metis_tac[gas_path_mem_exec]
QED
