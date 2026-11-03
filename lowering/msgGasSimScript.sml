(* The explicit msg.gas leaf uses one actual target GAS event. *)
Theory msgGasSim
Ancestors
  gasSummary fragGasPath gasCount gasOracleReplay fragExec
  exprLowering emitHelper compileEnv venomExecSemantics venomExecProofs
  venomInst venomState vyperInterpreter vyperState vyperValue
  vyperTypeSystem list rich_list pair arithmetic

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
