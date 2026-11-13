(* msg.gas at the joint full judgments: one checked GAS step fixes the
   endpoint, ghost and post at every finite horizon. *)
Theory msgGasFull
Ancestors
  bodySimFull gasOutcomeFull gasOutcomeFullCompose msgGasOrigin msgGasPost
  msgGasSim bodyMemBiEnvMsgGas bodyPtrEnvBuiltinsGas bodyPtrEnvBuiltinsEdges
  decoderGhostFramePtr fragGasSeqPtr fragGasOriginPtr bodyPtrDefs ptrSafeRun
  ptrDiscipline gasShadow gasSummary gasOracleReplay allocaHistory
  exprSimMemDefs exprSimStack exprSimIfExp exprSimProps exprLoweringProps
  loweringPosts exprLowering compileEnv emitHelper vyperStorageTrace
  venomExecSemantics venomInst venomState memSafeRun context
  vyperInterpreter vyperState finite_map pred_set list

(* The checked GAS step and its ghosts, fixed before any horizon: the
   endpoint, provenance and taint do not depend on the dead mask. *)
Theorem msg_gas_full_witness[local]:
  compile_env_var MsgGas sa = (Var out, sb) /\
  compile_env_var GasPrice shadow_sa = (shadow_op, shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?w id.
    gas_prefix 1 s0.vs_gas_readings = [w] /\
    sb.cs_current_bb = sa.cs_current_bb /\
    alloca_history func
      (update_var out w (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
                                  vs_inst_idx := LENGTH sb.cs_current_insts|>)) /\
    !D lo d cx es G0 tn0 PG.
      ghost_inv_at D lo d cenv cx es G0 tn0 s0 ==>
      gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s0,G0,tn0) [T]
        (OK (update_var out w
               (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
                          vs_inst_idx := LENGTH sb.cs_current_insts|>)),
         step_prov PG G0 (mk_inst id GAS [] [out])
           (update_var out w (s0 with vs_gas_readings := DROP 1 s0.vs_gas_readings)),
         step_taint (mk_inst id GAS [] [out]) s0
           (update_var out w (s0 with vs_gas_readings := DROP 1 s0.vs_gas_readings))
           tn0) /\
      ghost_inv_at D lo d cenv cx (es with gas_obs := [])
        (step_prov PG G0 (mk_inst id GAS [] [out])
           (update_var out w (s0 with vs_gas_readings := DROP 1 s0.vs_gas_readings)))
        (step_taint (mk_inst id GAS [] [out]) s0
           (update_var out w (s0 with vs_gas_readings := DROP 1 s0.vs_gas_readings))
           tn0)
        (update_var out w
           (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
                      vs_inst_idx := LENGTH sb.cs_current_insts|>)) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0
        (step_prov PG G0 (mk_inst id GAS [] [out])
           (update_var out w (s0 with vs_gas_readings := DROP 1 s0.vs_gas_readings)))
        (step_taint (mk_inst id GAS [] [out]) s0
           (update_var out w (s0 with vs_gas_readings := DROP 1 s0.vs_gas_readings))
           tn0) /\
      ptr_val_ok cx (env_item_type MsgGas) (IntV (&w2n w)) (Var out)
        (step_prov PG G0 (mk_inst id GAS [] [out])
           (update_var out w (s0 with vs_gas_readings := DROP 1 s0.vs_gas_readings)))
        (step_taint (mk_inst id GAS [] [out]) s0
           (update_var out w (s0 with vs_gas_readings := DROP 1 s0.vs_gas_readings))
           tn0)
        (update_var out w
           (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
                      vs_inst_idx := LENGTH sb.cs_current_insts|>))
Proof
  strip_tac >>
  drule_all msg_gas_canonical_placement >> strip_tac >> gvs[] >>
  `?w. gas_prefix 1 s0.vs_gas_readings = [w] /\
       step_inst_base (mk_inst id GAS [] [out]) s0 =
         OK (update_var out w (s0 with vs_gas_readings := DROP 1 s0.vs_gas_readings))`
    by metis_tac[gas_builtin_base_step] >>
  `~not_fresh_at sa out` by
    (qpat_x_assum `compile_env_var MsgGas _ = _` mp_tac >>
     simp[compile_env_var_def, emit_op_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, fresh_id_def,
          fresh_var_def, emit_def] >> strip_tac >>
     gvs[not_fresh_at_def]) >>
  drule_all compile_msg_gas_history >>
  disch_then (qspec_then `w` assume_tac) >>
  qexistsl_tac [`w`, `id`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `inst = mk_inst id GAS [] [out]` >>
  qabbrev_tac `u = update_var out w (s0 with vs_gas_readings := DROP 1 s0.vs_gas_readings)` >>
  `update_var out w (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
                               vs_inst_idx := LENGTH sb.cs_current_insts|>) =
   u with vs_inst_idx := SUC s0.vs_inst_idx` by
    simp[Abbr `u`, update_var_def] >>
  pop_assum SUBST1_TAC >>
  rpt conj_tac
  >- (`ptr_inst_ok D lo 0 ctx func G0 tn0 inst s0` by
        (simp[Abbr `inst`] >> irule ptr_inst_ok_scalar_builtin_at >>
         gvs[ghost_inv_at_def]) >>
      `gas_origin_ptr_edge (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (s0,G0,tn0)
         (if inst.inst_opcode = GAS then
            [(func.fn_name,inst.inst_id) IN gas_explicit_sites ctx shadow_ctx]
          else [])
         (OK (u with vs_inst_idx := SUC s0.vs_inst_idx),
          step_prov PG G0 inst u, step_taint inst s0 u tn0)` by
        (irule straight_line_origin_ptr_edge >> fs[] >>
         simp[Abbr `inst`, mk_inst_def, is_terminator_def,
              inst_mem_below_frontier_def, source_memory_read_ranges_def,
              source_memory_write_ranges_def, inst_dload_in_section_def]) >>
      `~(u with vs_inst_idx := SUC s0.vs_inst_idx).vs_halted` by
        simp[Abbr `u`, update_var_def] >>
      qpat_x_assum `gas_origin_ptr_edge _ _ _ _` mp_tac >>
      simp[Abbr `inst`, mk_inst_def] >> strip_tac >>
      CONV_TAC (RATOR_CONV (RAND_CONV (REWR_CONV (GSYM APPEND_NIL)))) >>
      irule (cj 2 gas_origin_ptr_path_rules) >>
      goal_assum (drule_at Any) >>
      irule (cj 1 gas_origin_ptr_path_rules) >> simp[])
  >- (drule_all gas_builtin_indexed_ghosts_at >>
      disch_then (qspecl_then [`w`, `SUC s0.vs_inst_idx`, `id`,
        `DROP 1 s0.vs_gas_readings`, `PG`] strip_assume_tac) >>
      `update_var out w (s0 with <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
                                   vs_inst_idx := SUC s0.vs_inst_idx|>) =
       u with vs_inst_idx := SUC s0.vs_inst_idx` by
        simp[Abbr `u`, update_var_def] >>
      gvs[Abbr `inst`] >> fs[ghost_inv_at_def])
  >- (drule_all gas_builtin_indexed_ghosts_at >>
      disch_then (qspecl_then [`w`, `SUC s0.vs_inst_idx`, `id`,
        `DROP 1 s0.vs_gas_readings`, `PG`] strip_assume_tac) >>
      fs[Abbr `inst`, Abbr `u`])
  >> simp[ptr_val_ok_def, env_item_type_def, is_word_type_def, Abbr `inst`] >>
  conj_tac
  >- (irule scalar_builtin_output_clean >> simp[]) >>
  irule scalar_builtin_output_no_prov >> simp[]
QED

Theorem msg_gas_source_frame[local]:
  storage_trace_frame
    (bind (eval_expr cx (Builtin (env_item_type MsgGas) (Env MsgGas) []))
      (read_result cx)) /\
  storage_trace_frame
    (eval_expr cx (Builtin (env_item_type MsgGas) (Env MsgGas) []))
Proof
  conj_tac
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  simp[evaluate_storage_trace_frame]
QED

(* Both posts use the same GAS endpoint and ghost at every horizon. *)
Theorem compile_msg_gas_sim_full:
  expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty (Builtin (env_item_type MsgGas) (Env MsgGas) []) es /\
  expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty (Builtin (env_item_type MsgGas) (Env MsgGas) []) es
Proof
  conj_tac
  >- (rw[expr_sim_full_def] >>
      drule lower_value_env >> strip_tac >>
      qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` mp_tac >>
      simp[gas_shadow_expr_def, gas_shadow_builtin_def] >> strip_tac >>
      drule lower_value_env >> strip_tac >>
      `?out. op = Var out` by
        (qpat_x_assum `compile_env_var MsgGas _ = _` mp_tac >>
         simp[compile_env_var_def, emit_op_def, comp_bind_def,
              comp_ignore_bind_def, comp_return_def, fresh_id_def,
              fresh_var_def, emit_def] >> metis_tac[]) >>
      gvs[] >> drule_all msg_gas_full_witness >> strip_tac >>
      irule gas_outcome_full_initial_domain >>
      simp[msg_gas_source_frame] >> strip_tac >>
      rewrite_tac[gas_outcome_full_def] >>
      qexists_tac `[T]` >> disj2_tac >> disj1_tac >>
      qexistsl_tac [`INL (IntV (&w2n w))`, `es`] >>
      qmatch_goalsub_abbrev_tac `gas_origin_ptr_path _ _ _ (_, G1, tn1)` >>
      qmatch_goalsub_abbrev_tac `OK t` >>
      qexistsl_tac [`OK t`, `G1`, `tn1`] >>
      rpt conj_tac
      >- (gen_tac >> fs[gas_explicit_def, msg_gas_source])
      >- simp[] >>
      rpt strip_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
        (drule_then strip_assume_tac) >>
      qpat_x_assum `!D lo d cx es G0 tn0 PG. _`
        (drule_then (qspec_then `PG` strip_assume_tac)) >>
      drule_all msg_gas_post_frame >>
      disch_then (qspec_then `w` assume_tac) >>
      unabbrev_all_tac >>
      gvs[expr_store_bound_word, expr_type_def, env_item_type_def,
          is_word_type_def, update_var_def]) >>
  rw[expr_vv_sim_full_def] >>
  Cases_on `compile_env_var MsgGas sa` >>
  Cases_on `compile_env_var GasPrice shadow_sa` >>
  gvs[gas_shadow_expr_def, gas_shadow_builtin_def] >>
  qpat_x_assum `compile_expr _ _ _ sa = _` mp_tac >>
  simp[Once compile_expr_def, compile_expr_def,
       compile_builtin_dispatch_body_def, as_stack_val_def] >> strip_tac >>
  qpat_x_assum `compile_expr _ _ _ shadow_sa = _` mp_tac >>
  simp[Once compile_expr_def, compile_expr_def,
       compile_builtin_dispatch_body_def, as_stack_val_def] >> strip_tac >>
  gvs[expr_type_def] >>
  `?out. q = Var out` by
    (qpat_x_assum `compile_env_var MsgGas _ = _` mp_tac >>
     simp[compile_env_var_def, emit_op_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, fresh_id_def,
          fresh_var_def, emit_def] >> metis_tac[]) >>
  gvs[] >> drule_all msg_gas_full_witness >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  simp[msg_gas_source_frame] >> strip_tac >>
  rewrite_tac[gas_outcome_full_def] >>
  qexists_tac `[T]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INL (Value (IntV (&w2n w)))`, `es`] >>
  qmatch_goalsub_abbrev_tac `gas_origin_ptr_path _ _ _ (_, G1, tn1)` >>
  qmatch_goalsub_abbrev_tac `OK t` >>
  qexistsl_tac [`OK t`, `G1`, `tn1`] >>
  rpt conj_tac
  >- (gen_tac >>
      `!s tv s'. eval_expr cx (Builtin (env_item_type MsgGas) (Env MsgGas) []) s =
         (INL tv,s') ==> ?v. tv = Value v` by
        metis_tac[eval_expr_builtin_value] >>
      drule eval_expr_force_value >>
      disch_then (qspecl_then [`es with gas_obs := w::tail`,
        `INL (IntV (&w2n w))`, `es with gas_obs := tail`] mp_tac) >>
      fs[gas_explicit_def, msg_gas_source])
  >- simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!D lo d cx es G0 tn0 PG. _`
    (drule_then (qspec_then `PG` strip_assume_tac)) >>
  drule_all msg_gas_post_frame >>
  disch_then (qspec_then `w` assume_tac) >>
  drule_at (Pos last) vv_post_of_expr_post >>
  simp[post_value_type_def, expr_type_def] >> strip_tac >>
  unabbrev_all_tac >>
  gvs[expr_type_def, vv_store_bound_stack_word, env_item_type_def,
      is_word_type_def, ptr_vv_ok_def, vv_location_def, read_result_def,
      return_def, update_var_def]
QED
