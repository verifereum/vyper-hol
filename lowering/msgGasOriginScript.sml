(* An explicit source gas leaf fixes its actual raw GAS/GASPRICE site. *)
Theory msgGasOrigin
Ancestors
  msgGasPairedPlacement
  fragExec msgGasSim gasExplicitSites gasShadowUnit gasShadowState fragGasOrigin
  gasEvents gasCount gasOracleReplay fragGasMode fragGasPathMem memSafeRun
  unitTransformDefs exprLowering emitHelper compileEnv
  venomInst venomState venomExecSemantics venomExecProofs list rich_list

Theorem msg_gas_canonical_placement:
  compile_env_var MsgGas sa = (op, sb) /\
  compile_env_var GasPrice ta = (shadow_op, tb) /\
  gas_shadow_state sa ta /\ gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code ta tb shadow_func ==>
  ?out id bb. op = Var out /\
    sb.cs_current_bb = sa.cs_current_bb /\
    LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
    lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) =
      SOME (mk_inst id GAS [] [out]) /\
    (func.fn_name,id) IN gas_explicit_sites ctx shadow_ctx
Proof
  metis_tac[msg_gas_paired_placement]
QED

Theorem compile_msg_gas_origin_path:
  compile_env_var MsgGas sa = (op, sb) /\
  compile_env_var GasPrice ta = (shadow_op, tb) /\
  gas_shadow_state sa ta /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code ta tb shadow_func /\
  ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out w.
    op = Var out /\ gas_prefix 1 s0.vs_gas_readings = [w] /\
    sb.cs_current_bb = sa.cs_current_bb /\
    gas_origin_path memory (gas_explicit_sites ctx shadow_ctx) ctx func s0 [T]
      (OK (update_var out w
        (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
                   vs_inst_idx := LENGTH sb.cs_current_insts|>)))
Proof
  strip_tac >> drule_all msg_gas_canonical_placement >> strip_tac >>
  `?w. gas_prefix 1 s0.vs_gas_readings = [w] /\
    gas_path_mem_edge ctx func s0 1
      (OK (update_var out w
        (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
                   vs_inst_idx := SUC s0.vs_inst_idx|>)))` by
    (irule msg_gas_mem_edge >> metis_tac[]) >>
  `lookup_block s0.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb s0.vs_inst_idx = SOME (mk_inst id GAS [] [out])`
    by simp[] >>
  drule_all gas_mem_edge_origin >>
  disch_then (qspecl_then [`memory`, `gas_explicit_sites ctx shadow_ctx`]
    mp_tac) >> simp[] >> strip_tac >>
  `~(update_var out w
      (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
                 vs_inst_idx := SUC s0.vs_inst_idx|>)).vs_halted` by
    simp[update_var_def] >>
  gvs[] >>
  drule (cj 2 gas_origin_path_rules) >>
  disch_then (qspecl_then [`[]`,
    `OK (update_var out w
      (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
                 vs_inst_idx := SUC (LENGTH sa.cs_current_insts)|>))`] mp_tac) >>
  simp[gas_origin_path_rules]
QED
