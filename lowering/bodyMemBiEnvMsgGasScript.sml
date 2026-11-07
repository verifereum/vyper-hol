(* Counted environment GAS: allocation history at the actual landing cursor. *)
Theory bodyMemBiEnvMsgGas
Ancestors
  msgGasPost msgGasSim allocaHistory compileEnv venomInst venomState list arithmetic
  gasNormalPrefix gasSummary fragGasMode exprSimMemoryValues exprSimMemoryStack
  bodyMemoryPreds bodyMemoryDefs exprSimHypsDefs exprLoweringProps exprSimProps
  vyperTyping vyperTypeSystem vyperAST valueEncoding exprLowering

Theorem compile_msg_gas_history:
  compile_env_var MsgGas sa = (Var out,sb) /\ fn_has_code sa sb func /\
  alloca_history func s0 /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  alloca_history func
    (update_var out w
      (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
                 vs_inst_idx := LENGTH sb.cs_current_insts|>))
Proof
  strip_tac >> drule_all msg_gas_placement >> strip_tac >>
  gvs[alloca_history_def, update_var_def] >>
  rpt strip_tac >>
  Cases_on `k < LENGTH sa.cs_current_insts`
  >- metis_tac[] >>
  `k = LENGTH sa.cs_current_insts` by decide_tac >>
  gvs[mk_inst_def]
QED

Theorem body_msg_gas_mem_prefix[local]:
  lower_value compile_expr cenv ty
    (Builtin (env_item_type MsgGas) (Env MsgGas) []) sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?v t. gas_value_prefix T (ctx,func,cenv,cx)
    (ty,Builtin (env_item_type MsgGas) (Env MsgGas) [])
    (sa,sb,op) (es,s0) [T] (v,es,t)
Proof
  strip_tac >> drule lower_value_env >> strip_tac >>
  drule_all compile_msg_gas_mem_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >> gvs[] >>
  drule_all msg_gas_post_frame >>
  disch_then (qspec_then `w` assume_tac) >>
  drule_all compile_msg_gas_history >>
  disch_then (qspec_then `w` assume_tac) >>
  qexistsl_tac [`IntV (&w2n w)`,
    `update_var out w (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
                               vs_inst_idx := LENGTH sb.cs_current_insts|>)`] >>
  simp[gas_value_prefix_def, gas_marked_exec_def, gas_explicit_def,
       gas_marked_path_def, msg_gas_source, update_var_def] >>
  gvs[update_var_def]
QED

Theorem body_msg_gas_sim_mem[local]:
  !ctx func cenv cx ty es.
    expr_sim_mem ctx func cenv cx ty
      (Builtin (env_item_type MsgGas) (Env MsgGas) []) es
Proof
  rpt gen_tac >> irule expr_sim_mem_word_values >> reverse conj_tac
  >- simp[expr_type_def, env_item_type_def, is_word_type_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all body_msg_gas_mem_prefix >> strip_tac >>
  qexistsl_tac [`[T]`, `v`, `es`, `t`] >> simp[]
QED

Theorem body_msg_gas_vv_sim_mem[local]:
  !ctx func cenv cx ty es.
    expr_vv_sim_mem ctx func cenv cx ty
      (Builtin (env_item_type MsgGas) (Env MsgGas) []) es
Proof
  rpt gen_tac >>
  `is_word_type (expr_type (Builtin (env_item_type MsgGas) (Env MsgGas) []))` by
    simp[expr_type_def, env_item_type_def, is_word_type_def] >>
  drule_then irule body_expr_vv_sim_mem_stack_word >>
  conj_tac
  >- (gen_tac >> simp[compile_expr_def] >>
      Cases_on `compile_env_var MsgGas sa` >> simp[as_stack_val_def]) >>
  conj_tac >- metis_tac[eval_expr_builtin_value] >>
  irule body_msg_gas_sim_mem
QED

Theorem body_msg_gas_mem_case:
  !cx ann args. body_expr_mem_ok cx (Builtin ann (Env MsgGas) args)
Proof
  rpt gen_tac >> (rpt gen_tac >> match_mp_tac body_expr_mem_ok_intro >>
   conj_tac >- (rpt strip_tac >> gvs[])) >>
  rpt gen_tac >> strip_tac >>
  `args = [] /\ ann = env_item_type MsgGas` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  gvs[] >> metis_tac[body_msg_gas_sim_mem, body_msg_gas_vv_sim_mem]
QED
