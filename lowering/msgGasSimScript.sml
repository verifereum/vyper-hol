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

Theorem msg_gas_source[local]:
  bind (eval_expr cx (Builtin (env_item_type MsgGas) (Env MsgGas) []))
       (read_result cx) (es with gas_obs := w::tail) =
    (INL (IntV (&w2n w)), es with gas_obs := tail)
Proof
  once_rewrite_tac[evaluate_def] >>
  simp[vyperContextTheory.builtin_args_length_ok_def, bind_def, ignore_bind_def,
       type_check_def, check_def, assert_def, return_def,
       next_gas_reading_def, read_result_def]
QED

Theorem msg_gas_edge[local]:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id GAS [] [out]) ==>
  ?w. gas_prefix 1 s.vs_gas_readings = [w] /\
    gas_path_edge ctx func s 1
      (OK (update_var out w
        (s with <|vs_gas_readings := DROP 1 s.vs_gas_readings;
                   vs_inst_idx := SUC s.vs_inst_idx|>)))
Proof
  strip_tac >>
  `1 = SUC 0` by decide_tac >>
  `?w. gas_prefix 1 s.vs_gas_readings = [w] /\
    step_inst 0 ctx (mk_inst id GAS [] [out]) s =
      OK (update_var out w
        (s with vs_gas_readings := DROP 1 s.vs_gas_readings))`
    by (Cases_on `s.vs_gas_readings`
        >- (qexists_tac `0w` >> conj_tac
            >- (qpat_assum `1 = SUC 0` (fn th => once_rewrite_tac[th]) >>
                simp[gas_prefix_suc, gas_prefix_zero]) >>
            qpat_x_assum `1 = SUC 0` kall_tac >>
        simp[step_inst_non_invoke, mk_inst_def] >>
            simp[step_inst_base_def, exec_gas_def] >>
            gvs[update_var_def, venom_state_component_equality]) >>
        rename1 `s.vs_gas_readings = w::ws` >>
        qexists_tac `w` >> conj_tac
        >- (qpat_assum `1 = SUC 0` (fn th => once_rewrite_tac[th]) >>
            simp[gas_prefix_suc, gas_prefix_zero]) >>
        qpat_x_assum `1 = SUC 0` kall_tac >>
        simp[step_inst_non_invoke, mk_inst_def] >>
        simp[step_inst_base_def, exec_gas_def]) >>
  qpat_x_assum `1 = SUC 0` kall_tac >>
  qexists_tac `w` >> simp[] >>
  rewrite_tac[gas_path_edge_def] >> simp[] >>
  qexists_tac `0:num` >>
  simp[gas_count_step_def, mk_inst_def, is_terminator_def, update_var_def] >>
  gvs[update_var_def]
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
  strip_tac >> drule_all msg_gas_placement >> strip_tac >>
  `?w. gas_prefix 1 s0.vs_gas_readings = [w] /\
    gas_path_edge ctx func s0 1
      (OK (update_var out w
        (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
                   vs_inst_idx := SUC s0.vs_inst_idx|>)))`
    by (irule msg_gas_edge >> metis_tac[]) >>
  qexistsl_tac [`out`, `w`] >> simp[] >>
  drule gas_path_edge_normal >> strip_tac >>
  gvs[] >>
  drule (cj 2 gas_path_rules) >>
  disch_then (qspec_then `0` mp_tac) >>
  simp[gas_path_rules]
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
