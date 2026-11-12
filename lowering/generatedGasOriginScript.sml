(* Generated default gas reads keep GAS in the paired shadow compilation. *)
Theory generatedGasOrigin
Ancestors
  msgGasSim gasExplicitSites gasShadowUnit gasShadowState fragGasOrigin
  gasShadowUnitObservations gasEvents gasCount gasOracleReplay fragGasMode
  fragGasPathMem memSafeRun fragExec unitTransformDefs
  exprLowering emitHelper compileEnv venomWf
  venomInst venomState venomExecSemantics venomExecProofs list rich_list

Theorem compile_generated_gas_origin_path:
  emit_op GAS [] sa = (op, sb) /\
  emit_op GAS [] ta = (shadow_op, tb) /\
  gas_shadow_state sa ta /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code ta tb shadow_func /\
  ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out w.
    op = Var out /\ gas_prefix 1 s0.vs_gas_readings = [w] /\
    sb.cs_current_bb = sa.cs_current_bb /\
    (func.fn_name, sa.cs_next_id) NOTIN gas_explicit_sites ctx shadow_ctx /\
    gas_origin_path memory (gas_explicit_sites ctx shadow_ctx) ctx func s0 [F]
      (OK (update_var out w
        (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
                   vs_inst_idx := LENGTH sb.cs_current_insts|>)))
Proof
  strip_tac >>
  `?out bb. op = Var out /\
    sb.cs_current_bb = sa.cs_current_bb /\
    LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
    lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) =
      SOME (mk_inst sa.cs_next_id GAS [] [out]) /\
    out = FST (fresh_var sa)` by
    (irule emit_gas_placement_id >> simp[]) >>
  `?shadow_out shadow_bb. shadow_op = Var shadow_out /\
    lookup_block ta.cs_current_bb shadow_func.fn_blocks = SOME shadow_bb /\
    get_instruction shadow_bb (LENGTH ta.cs_current_insts) =
      SOME (mk_inst ta.cs_next_id GAS [] [shadow_out]) /\
    shadow_out = FST (fresh_var ta)` by
    (drule_all emit_gas_placement_id >> metis_tac[]) >>
  `sa.cs_next_id = ta.cs_next_id /\
   FST (fresh_var sa) = FST (fresh_var ta)` by
    gvs[gas_shadow_state_def, fresh_var_def] >>
  `MEM (mk_inst sa.cs_next_id GAS [] [out]) (fn_insts func)` by
    (irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
     gvs[get_instruction_def] >> metis_tac[EL_MEM]) >>
  `MEM (mk_inst sa.cs_next_id GAS [] [out]) (fn_insts shadow_func)` by
    (irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
     gvs[get_instruction_def] >> metis_tac[EL_MEM]) >>
  `gas_shadow_inst (mk_inst sa.cs_next_id GAS [] [out])
                   (mk_inst sa.cs_next_id GAS [] [out])` by
    simp[gas_shadow_inst_def] >>
  `(mk_inst sa.cs_next_id GAS [] [out]).inst_opcode = GAS` by
    simp[mk_inst_def] >>
  `(func.fn_name, sa.cs_next_id) NOTIN gas_explicit_sites ctx shadow_ctx` by
    (drule_all gas_explicit_sites_classify >> simp[mk_inst_def]) >>
  `?w. gas_prefix 1 s0.vs_gas_readings = [w] /\
    gas_path_mem_edge ctx func s0 1
      (OK (update_var out w
        (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
                   vs_inst_idx := SUC s0.vs_inst_idx|>)))` by
    (irule msg_gas_mem_edge >> metis_tac[]) >>
  `gas_origin_edge memory (gas_explicit_sites ctx shadow_ctx) ctx func s0 [F]
      (OK (update_var out w
        (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
                   vs_inst_idx := SUC s0.vs_inst_idx|>)))` by
    (drule gas_mem_edge_origin >> simp[mk_inst_def] >>
     disch_then (qspecl_then [`memory`, `gas_explicit_sites ctx shadow_ctx`] mp_tac) >>
     gvs[]) >>
  qexistsl_tac [`out`, `w`] >> simp[] >>
  `~(update_var out w
      (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
                 vs_inst_idx := SUC s0.vs_inst_idx|>)).vs_halted` by
    simp[update_var_def] >>
  gvs[] >>
  drule (cj 2 gas_origin_path_rules) >>
  disch_then (qspec_then `[]` mp_tac) >>
  simp[gas_origin_path_rules]
QED
