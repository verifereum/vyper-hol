(* The explicit msg.gas leaf uses one actual target GAS event. *)
Theory msgGasSim
Ancestors
  gasSummary fragGasPath gasCount gasOracleReplay fragExec
  exprLowering emitHelper compileEnv venomExecSemantics venomExecProofs
  venomInst venomState vyperInterpreter vyperState vyperValue
  vyperTypeSystem list rich_list pair arithmetic

Theorem msg_gas_placement[local]:
  compile_env_var MsgGas sa = (op,sb) /\ fn_has_code sa sb func ==>
  ?out id bb. op = Var out /\
    sb.cs_current_bb = sa.cs_current_bb /\
    LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
    lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) =
      SOME (mk_inst id GAS [] [out])
Proof
  strip_tac >>
  `?out id. op = Var out /\
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++ [mk_inst id GAS [] [out]]`
    by (gvs[compile_env_var_def, emit_op_def, comp_bind_def,
            comp_ignore_bind_def, comp_return_def, fresh_id_def,
            fresh_var_def, emit_def] >> metis_tac[]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qexistsl_tac [`out`, `id`, `bb`] >> simp[] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED

Theorem compile_msg_gas_path:
  compile_env_var MsgGas sa = (op, sb) /\
  fn_has_code sa sb func /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out w.
    op = Var out /\ gas_prefix 1 s0.vs_gas_readings = [w] /\
    sb.cs_current_bb = sa.cs_current_bb /\
    gas_path ctx func s0 1
      (OK (update_var out w
        (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
                   vs_inst_idx := LENGTH sb.cs_current_insts|>)))
Proof
  cheat
QED

Theorem compile_msg_gas_summary:
  compile_env_var MsgGas sa = (op, sb) /\
  fn_has_code sa sb func /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_summary (ctx, func)
    (bind (eval_expr cx (Builtin (env_item_type MsgGas) (Env MsgGas) []))
          (read_result cx)) (es, s0)
    (\res es_end t.
       ?w. res = INL (IntV (&w2n w)) /\
           es_end = (es with gas_obs := []) /\
           eval_operand op t = SOME w /\
           t.vs_current_bb = sb.cs_current_bb /\
           t.vs_inst_idx = LENGTH sb.cs_current_insts /\
           t.vs_gas_readings = DROP 1 s0.vs_gas_readings)
    (\res es_end r. F)
Proof
  cheat
QED
