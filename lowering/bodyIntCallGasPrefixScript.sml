(* Compile-expression bridge for the controlled explicit GAS witness. *)
Theory bodyIntCallGasPrefix
Ancestors
  bodyIntCallGasJoint bodyIntCallArgLifetime exprSimIfExp exprSimLeaves
  msgGasPost msgGasSim exprSimHypsDefs exprLowering exprLoweringProps
  loweringPosts compileEnv gasSummary gasOutcome fragGasMode fragGasPath fragGasPathMem
  venomState vyperInterpreter vyperState

Theorem compile_expr_msg_gas_shape:
  compile_expr cenv ty (Builtin ann (Env MsgGas) args) sa = (vv,sb) ==>
  ?op. compile_env_var MsgGas sa = (op,sb) /\ vv = StackValue ann op
Proof
  simp[compile_expr_env, compile_builtin_dispatch_component_eq, compile_builtin_dispatch_body_def,
       as_stack_val_def] >>
  Cases_on `compile_env_var MsgGas sa` >> simp[as_stack_val_def]
QED

Theorem eval_expr_msg_gas_source:
  eval_expr cx (Builtin (env_item_type MsgGas) (Env MsgGas) [])
    (es with gas_obs := w::tail) =
  (INL (Value (IntV (&w2n w))), es with gas_obs := tail)
Proof
  once_rewrite_tac[evaluate_def] >>
  simp[vyperContextTheory.builtin_args_length_ok_def, bind_def, ignore_bind_def,
       type_check_def, check_def, assert_def, return_def, next_gas_reading_def]
QED

Theorem msg_gas_vv_post_frame:
  compile_env_var MsgGas sa = (Var out,sb) /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 ==>
  vv_post ctx func cenv cx (Builtin (env_item_type MsgGas) (Env MsgGas) [])
    es sa sb s0 (es with gas_obs := []) (Value (IntV (&w2n w)))
    (StackValue (env_item_type MsgGas) (Var out))
    (update_var out w (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
                               vs_inst_idx := LENGTH sb.cs_current_insts|>))
Proof
  strip_tac >> drule_all msg_gas_post_frame >>
  disch_then (qspec_then `w` mp_tac) >>
  disch_then (mp_tac o MATCH_MP vv_post_of_expr_post) >>
  simp[vyperASTTheory.expr_type_def, vyperTypeSystemTheory.env_item_type_def,
       is_word_type_def]
QED

Theorem compile_msg_gas_prefix_outcome:
  expr_sim_pre cenv cx env (Builtin ann (Env MsgGas) args) es /\
  compile_expr cenv (expr_type (Builtin ann (Env MsgGas) args))
    (Builtin ann (Env MsgGas) args) sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  EVERY (\(ty,raw,held,lo).
    vv_holds cenv cx ty raw held es s0 /\
    vv_at cenv cx ty lo sa es raw held s0 /\
    safe_operand sa (vv_operand held)) hs ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_expr cx (Builtin ann (Env MsgGas) args)) (es,s0)
    (\res ee t. ?raw_new. res = INL raw_new /\
      vv_post ctx func cenv cx (Builtin ann (Env MsgGas) args)
        es sa sb s0 ee raw_new vv t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ee = es with <|outcomes := ee.outcomes; gas_obs := ee.gas_obs|> /\
      EVERY (\(ty,raw,held,lo).
        vv_holds cenv cx ty raw held ee t /\
        vv_at cenv cx ty lo sb ee raw held t /\
        safe_operand sb (vv_operand held)) hs)
    (\res ee r. F)
Proof
  strip_tac >> drule msg_gas_typed >> strip_tac >> gvs[] >>
  drule compile_expr_msg_gas_shape >> strip_tac >>
  drule_all compile_msg_gas_mem_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >> gvs[] >>
  qabbrev_tac `tgas = update_var out w
    (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
               vs_inst_idx := LENGTH sb.cs_current_insts|>)` >>
  `vv_post ctx func cenv cx (Builtin (env_item_type MsgGas) (Env MsgGas) [])
    es sa sb s0 (es with gas_obs := []) (Value (IntV (&w2n w)))
    (StackValue (env_item_type MsgGas) (Var out)) tgas` by
    (drule_all msg_gas_vv_post_frame >>
     disch_then (qspec_then `w` mp_tac) >> simp[Abbr `tgas`]) >>
  `EVERY (\(ty,raw,held,lo).
    vv_holds cenv cx ty raw held (es with gas_obs := []) tgas /\
    vv_at cenv cx ty lo sb (es with gas_obs := []) raw held tgas /\
    safe_operand sb (vv_operand held)) hs` by
    (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
       vv_post_deferred_prefix >>
     simp[Abbr `tgas`, update_var_def, contract_storage_def,
          contract_transient_def, immutable_holds_def] >>
     disch_then (qspecl_then [`hs`,`env`] mp_tac) >>
     impl_tac >- (gvs[expr_sim_pre_def, stmt_state_rel_def, state_rel_def,
                       evaluation_state_component_equality]) >>
     simp[]) >>
  pure_rewrite_tac[gas_outcome_def] >> qexists_tac `[T]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def, gas_marked_exec_def, gas_marked_path_def] >>
  qexistsl_tac [`INL (Value (IntV (&w2n w)))`, `es`, `OK tgas`] >>
  simp[gas_explicit_def, eval_expr_msg_gas_source] >>
  simp[Abbr `tgas`, update_var_def, evaluation_state_component_equality] >>
  drule gas_path_mem_exec >> simp[update_var_def]
QED
