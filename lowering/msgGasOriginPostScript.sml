(* The source replay and full post use the same canonical target leaf. *)
Theory msgGasOriginPost
Ancestors
  msgGasOrigin msgGasPost msgGasSim gasExplicitSites fragGasOrigin
  gasSummary gasCount loweringPosts
  gasShadowState gasShadowUnit exprSimProps exprSimHypsDefs exprLoweringProps exprLowering
  compileEnv emitHelper venomState vyperInterpreter vyperState

Theorem compile_msg_gas_origin_prefix:
  expr_sim_pre cenv cx env (Builtin ann (Env MsgGas) args) es /\
  lower_value compile_expr cenv ty (Builtin ann (Env MsgGas) args) sa =
    (op, sb) /\
  compile_env_var GasPrice ta = (shadow_op, tb) /\
  gas_shadow_state sa ta /\ gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code ta tb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?v ee t.
    gas_marked_exec memory (ctx, func)
      (bind (eval_expr cx (Builtin ann (Env MsgGas) args)) (read_result cx))
      (es, s0) [T] (INL v) ee (OK t) /\
    gas_origin_path memory (gas_explicit_sites ctx shadow_ctx)
      ctx func s0 [T] (OK t) /\
    expr_post ctx func cenv cx (Builtin ann (Env MsgGas) args)
      es sa sb s0 (ee with gas_obs := []) v op t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt strip_tac >> drule msg_gas_typed >> strip_tac >> gvs[] >>
  drule lower_value_env >> strip_tac >>
  drule_all compile_msg_gas_origin_path >>
  disch_then (qspec_then `memory` strip_assume_tac) >>
  drule gas_origin_path_erase >> simp[] >> strip_tac >>
  qexistsl_tac [`IntV (&w2n w)`, `es`,
    `update_var out w
      (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
                 vs_inst_idx := LENGTH sb.cs_current_insts|>)`] >>
  conj_tac
  >- fs[gas_marked_exec_def, gas_explicit_def, msg_gas_source] >>
  conj_tac >- simp[] >>
  conj_tac >- (irule msg_gas_post_frame >> simp[]) >>
  simp[update_var_def]
QED
