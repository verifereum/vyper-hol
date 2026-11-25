(* Replay the raw GAS instruction at the first omitted argument, before packing. *)
Theory s1PrefixBoolChainDefaultFirstReplay
Ancestors
  s1PrefixBoolChainDefaultGasCut msgGasPairedPlacement
  s1PrefixBoolChainDefaultMsgGasStep msgGasSim gasSummary gasOracleReplay

Theorem bool_chain_first_default_msggas_replay:
  compile_stage_intcall_args compile_expr ce
    (Builtin (env_item_type MsgGas) (Env MsgGas) []::rs)
    (flag::fs) (dt::ts) si = (ops,sf) /\
  compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
    (MAP gas_shadow_expr (Builtin (env_item_type MsgGas) (Env MsgGas) []::rs))
    (flag::fs) (dt::ts) sh_si = (ops,sh_sf) /\
  gas_shadow_state si sh_si /\
  fn_has_code si sf func /\ fn_has_code sh_si sh_sf sh_func /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  MEM func ctx.ctx_functions /\ MEM sh_func shadow_ctx.ctx_functions /\
  gas_shadow_function func sh_func /\
  ~s.vs_halted /\ s.vs_current_bb = si.cs_current_bb /\
  s.vs_inst_idx = LENGTH si.cs_current_insts /\ s.vs_gas_readings = w::ws /\
  (!H bb i. valid_horizon cx st0 H es.storage_trace /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME i ==>
    ptr_inst_ok (DF H) lo 0 ctx func G tn i s) ==>
  ?out id cg sh_cg h cm sh_cm hs u G1 tn1.
    compile_env_var MsgGas si = (Var out,cg) /\
    compile_env_var GasPrice sh_si = (Var out,sh_cg) /\
    gas_shadow_state cg sh_cg /\
    fn_has_code si cg func /\ fn_has_code sh_si sh_cg sh_func /\
    compile_stage_intcall_args compile_expr ce
      [Builtin (env_item_type MsgGas) (Env MsgGas) []] [flag] [dt] si = ([h],cm) /\
    compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
      [gas_shadow_expr (Builtin (env_item_type MsgGas) (Env MsgGas) [])]
      [flag] [dt] sh_si = ([h],sh_cm) /\
    compile_stage_intcall_args
      (\_ _ _. comp_return (StackValue (env_item_type MsgGas) (Var out))) ce
      [Builtin (env_item_type MsgGas) (Env MsgGas) []] [flag] [dt] cg = ([h],cm) /\
    compile_stage_intcall_args
      (\_ _ _. comp_return (StackValue (env_item_type MsgGas) (Var out)))
      (gas_shadow_env T ce)
      [gas_shadow_expr (Builtin (env_item_type MsgGas) (Env MsgGas) [])]
      [flag] [dt] sh_cg = ([h],sh_cm) /\
    compile_stage_intcall_args compile_expr ce rs fs ts cm = (hs,sf) /\
    compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
      (MAP gas_shadow_expr rs) fs ts sh_cm = (hs,sh_sf) /\
    ops = h::hs /\ gas_shadow_state cm sh_cm /\
    fn_has_code si cm func /\ fn_has_code cm sf func /\
    fn_has_code sh_si sh_cm sh_func /\ fn_has_code sh_cm sh_sf sh_func /\
    (!tail. bind (eval_expr default_cx (Builtin (env_item_type MsgGas) (Env MsgGas) []))
      (read_result default_cx)
      (es with gas_obs := gas_explicit [T] s.vs_gas_readings ++ tail) =
      (INL (IntV (&w2n w)), es with gas_obs := tail)) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s,G,tn) [T] (OK u,G1,tn1)) /\
    ~u.vs_halted /\ u.vs_current_bb = cg.cs_current_bb /\
    u.vs_inst_idx = LENGTH cg.cs_current_insts /\ u.vs_gas_readings = ws /\
    eval_operand (Var out) u = SOME w /\
    G1 = step_prov PG G (mk_inst id GAS [] [out])
           (update_var out w (s with vs_gas_readings := ws)) /\
    tn1 = step_taint (mk_inst id GAS [] [out]) s
            (update_var out w (s with vs_gas_readings := ws)) tn
Proof
  strip_tac >>
  drule_all bool_chain_default_gas_raw_cut >>
  disch_then (qx_choosel_then [`op`,`cg`,`sh_cg`,`h`,`cm`,`sh_cm`,`hs`] strip_assume_tac) >>
  drule_all msg_gas_paired_placement >>
  disch_then (qx_choosel_then [`out`,`id`,`bb`] strip_assume_tac) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    ptr_inst_ok (DF H) lo 0 ctx func G tn (mk_inst id GAS [] [out]) s` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >> qexists_tac `bb` >> simp[]) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx = SOME (mk_inst id GAS [] [out])` by simp[] >>
  drule_all bool_chain_default_msggas_step >>
  disch_then (qspec_then `PG` (qx_choosel_then [`u`,`G1`,`tn1`] strip_assume_tac)) >>
  qexistsl_tac [`out`,`id`,`cg`,`sh_cg`,`h`,`cm`,`sh_cm`,`hs`,`u`,`G1`,`tn1`] >>
  gvs[gas_explicit_def, gas_prefix_def, msg_gas_source]
QED
