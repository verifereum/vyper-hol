(* The value-flag residual returns the word already read by the raw GAS step. *)
Theory s1PrefixBoolChainDefaultValueMarshal
Ancestors
  s1PrefixBoolChainDefaultFirstReplay fragGasOriginPtr exprLowering compileEnv

Theorem bool_chain_default_msggas_value_marshal:
  compile_stage_intcall_args
    (\_ _ _. comp_return (StackValue (env_item_type MsgGas) (Var out))) ce
    [Builtin (env_item_type MsgGas) (Env MsgGas) []] [T] [dt] cg = ([h],cm) /\
  compile_stage_intcall_args
    (\_ _ _. comp_return (StackValue (env_item_type MsgGas) (Var out)))
    (gas_shadow_env T ce)
    [gas_shadow_expr (Builtin (env_item_type MsgGas) (Env MsgGas) [])]
    [T] [dt] sh_cg = ([h],sh_cm) /\
  ~u.vs_halted /\ u.vs_current_bb = cg.cs_current_bb /\
  u.vs_inst_idx = LENGTH cg.cs_current_insts /\ u.vs_gas_readings = ws /\
  eval_operand (Var out) u = SOME w ==>
  h = Var out /\ cm = cg /\ sh_cm = sh_cg /\
  ~u.vs_halted /\ u.vs_current_bb = cm.cs_current_bb /\
  u.vs_inst_idx = LENGTH cm.cs_current_insts /\ u.vs_gas_readings = ws /\
  eval_operand h u = SOME w /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (u,G1,tn1) [] (OK u,G1,tn1))
Proof
  simp[compile_stage_intcall_args_def, comp_bind_def, comp_return_def,
       unwrap_value_def] >>
  strip_tac >> gvs[] >>
  rpt strip_tac >> irule (CONJUNCT1 gas_origin_ptr_path_rules) >> simp[]
QED
