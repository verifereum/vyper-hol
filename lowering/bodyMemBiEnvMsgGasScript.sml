(* Counted environment GAS: allocation history at the actual landing cursor. *)
Theory bodyMemBiEnvMsgGas
Ancestors
  msgGasPost msgGasSim allocaHistory compileEnv venomInst venomState list arithmetic
  gasNormalPrefix gasSummary fragGasMode exprSimMemoryValues exprSimMemoryStack
  bodySimFull msgGasOrigin bodyPtrEnvBuiltinsGas bodyPtrEnvBuiltinsEdges
  fragGasSeqPtr fragGasOriginPtr bodyPtrDefs ptrSafeRun ptrDiscipline
  venomExecSemantics memSafeRun finite_map unitTransformDefs contextCodegenRel codegenRel
  bodyMemoryPreds bodyMemoryDefs exprSimHypsDefs exprLoweringProps exprSimProps
  vyperTyping vyperTypeSystem vyperAST valueEncoding exprLowering emitHelper
  exprSimMemDefs loweringPosts gasOutcomeFull gasShadow exprSimStack exprSimIfExp vyperInterpreter vyperState

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
  rpt gen_tac >> pure_rewrite_tac[body_expr_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `args = [] /\ ann = env_item_type MsgGas` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  gvs[] >> metis_tac[body_msg_gas_sim_mem, body_msg_gas_vv_sim_mem]
QED

Theorem msg_gas_full_post[local]:
  compile_env_var MsgGas sa = (Var out, sb) /\
  compile_env_var GasPrice shadow_sa = (shadow_op, shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
  ghost_inv_at D lo d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?w t G tn.
    gas_prefix 1 s0.vs_gas_readings = [w] /\
    gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s0,G0,tn0) [T] (OK t,G,tn) /\
    expr_post ctx func cenv cx (Builtin (env_item_type MsgGas) (Env MsgGas) [])
      es sa sb s0 (es with gas_obs := []) (IntV (&w2n w)) (Var out) t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at D lo d cenv cx (es with gas_obs := []) G tn t /\
    ptr_val_ok cx (env_item_type MsgGas) (IntV (&w2n w)) (Var out) G tn t /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn
Proof
  strip_tac >> drule_all msg_gas_canonical_placement >> strip_tac >> gvs[] >>
  `?w. gas_prefix 1 s0.vs_gas_readings = [w] /\
       step_inst_base (mk_inst id GAS [] [out]) s0 =
         OK (update_var out w (s0 with vs_gas_readings := DROP 1 s0.vs_gas_readings))`
    by metis_tac[gas_builtin_base_step] >>
  qmatch_asmsub_abbrev_tac `step_inst_base inst s0 = OK u` >>
  qabbrev_tac `t = u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `t = update_var out w (s0 with
    <|vs_gas_readings := DROP 1 s0.vs_gas_readings;
      vs_inst_idx := LENGTH sb.cs_current_insts|>)` by
    simp[Abbr `t`, Abbr `u`, update_var_def] >>
  `gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (s0,G0,tn0) [T]
     (OK t,step_prov PG G0 inst u,step_taint inst s0 u tn0)` by
    suspend "path" >>
  `ghost_inv_at D lo d cenv cx (es with gas_obs := [])
     (step_prov PG G0 inst u) (step_taint inst s0 u tn0) t /\
   ghost_kept_at lo cenv es sa G0 tn0 s0
     (step_prov PG G0 inst u) (step_taint inst s0 u tn0)` by
    suspend "ghosts" >>
  drule_all msg_gas_post_frame >> disch_then (qspec_then `w` assume_tac) >>
  drule_all compile_msg_gas_history >> disch_then (qspec_then `w` assume_tac) >>
  qexistsl_tac [`w`, `t`, `step_prov PG G0 inst u`, `step_taint inst s0 u tn0`] >>
  gvs[Abbr `t`, Abbr `u`, update_var_def] >>
  simp[ptr_val_ok_def, env_item_type_def, is_word_type_def, Abbr `inst`] >>
  conj_tac
  >- (irule scalar_builtin_output_clean >> simp[]) >>
  irule scalar_builtin_output_no_prov >> simp[]
QED

Resume msg_gas_full_post[path]:
  `ptr_inst_ok D lo 0 ctx func G0 tn0 inst s0` by
    (simp[Abbr `inst`] >> irule ptr_inst_ok_scalar_builtin_at >>
     gvs[ghost_inv_at_def]) >>
  `gas_origin_ptr_edge (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (s0,G0,tn0)
     (if inst.inst_opcode = GAS then
       [(func.fn_name,inst.inst_id) IN gas_explicit_sites ctx shadow_ctx] else [])
     (OK (u with vs_inst_idx := SUC s0.vs_inst_idx),
      step_prov PG G0 inst u,step_taint inst s0 u tn0)` by
    (irule straight_line_origin_ptr_edge >> simp[] >>
     simp[Abbr `inst`, mk_inst_def, is_terminator_def,
          inst_mem_below_frontier_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def, inst_dload_in_section_def]) >>
  `t = u with vs_inst_idx := SUC s0.vs_inst_idx` by
    gvs[Abbr `t`, Abbr `u`, update_var_def] >>
  `~t.vs_halted` by simp[Abbr `t`, Abbr `u`, update_var_def] >>
  qpat_x_assum `gas_origin_ptr_edge _ _ _ _` mp_tac >>
  simp[Abbr `inst`, mk_inst_def] >>
  disch_tac >>
  `t = u with vs_inst_idx := SUC (LENGTH sa.cs_current_insts)` by
    simp[Abbr `t`] >>
  qpat_x_assum `t = u with vs_inst_idx := SUC (LENGTH _)` (fn th =>
    RULE_ASSUM_TAC (REWRITE_RULE [GSYM th]) >> rewrite_tac[GSYM th]) >>
  CONV_TAC (RATOR_CONV (RAND_CONV (REWR_CONV (GSYM APPEND_NIL)))) >>
  irule (cj 2 gas_origin_ptr_path_rules) >>
  goal_assum (drule_at Any) >>
  irule (cj 1 gas_origin_ptr_path_rules) >> simp[]
QED

Resume msg_gas_full_post[ghosts]:
  `~not_fresh_at sa out` by
    (qpat_x_assum `compile_env_var MsgGas _ = _` mp_tac >>
     simp[compile_env_var_def, emit_op_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, fresh_id_def,
          fresh_var_def, emit_def] >> strip_tac >>
     gvs[not_fresh_at_def]) >>
  drule_all gas_builtin_indexed_ghosts_at >>
  disch_then (qspecl_then [`w`, `LENGTH sb.cs_current_insts`, `id`,
    `DROP 1 s0.vs_gas_readings`, `PG`] mp_tac) >>
  simp[Abbr `inst`, Abbr `u`, Abbr `t`, update_var_def] >>
  strip_tac >>
  qpat_x_assum `ghost_inv_at _ _ _ _ _ es (step_prov _ _ _ _) _ _` mp_tac >>
  simp[ghost_inv_at_def] >> metis_tac[]
QED

Finalise msg_gas_full_post

(* Both posts must use the same GAS endpoint and ghost. The constructor
   instance needs arbitrary lo; the existing scalar edge and ghost
   helpers specialize lo to zero and cannot be applied as-is. *)
Theorem compile_msg_gas_sim_full:
  expr_sim_full (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty (Builtin (env_item_type MsgGas) (Env MsgGas) []) es /\
  expr_vv_sim_full (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty (Builtin (env_item_type MsgGas) (Env MsgGas) []) es
Proof
  conj_tac
  >- (rw[expr_sim_full_def] >>
      drule lower_value_env >> strip_tac >>
      qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` mp_tac >>
      simp[gasShadowTheory.gas_shadow_expr_def, gas_shadow_builtin_def] >> strip_tac >>
      drule lower_value_env >> strip_tac >>
      `?out. op = Var out` by
        (qpat_x_assum `compile_env_var MsgGas _ = _` mp_tac >>
         simp[compile_env_var_def, emit_op_def, comp_bind_def,
              comp_ignore_bind_def, comp_return_def, fresh_id_def,
              fresh_var_def, emit_def] >> metis_tac[]) >>
      gvs[] >> drule_all msg_gas_full_post >>
      disch_then (qspec_then `PG` strip_assume_tac) >>
      simp[gasOutcomeFullTheory.gas_outcome_full_def] >>
      qexists_tac `[T]` >> disj1_tac >>
      qexistsl_tac [`INL (IntV (&w2n w))`, `es`, `OK t`, `G`, `tn`] >>
      simp[gas_explicit_def, msg_gas_source, expr_store_bound_word,
           expr_type_def, post_value_type_def, env_item_type_def,
           is_word_type_def] >>
      gvs[env_item_type_def, SRULE [env_item_type_def] msg_gas_source]) >>
  rw[expr_vv_sim_full_def] >>
  Cases_on `compile_env_var MsgGas sa` >>
  Cases_on `compile_env_var GasPrice shadow_sa` >>
  gvs[gas_shadow_expr_def, gas_shadow_builtin_def] >>
  qpat_x_assum `compile_expr _ _ _ sa = _` mp_tac >>
  simp[Once compile_expr_def, compile_expr_def, compile_builtin_dispatch_body_def, as_stack_val_def] >> strip_tac >>
  qpat_x_assum `compile_expr _ _ _ shadow_sa = _` mp_tac >>
  simp[Once compile_expr_def, compile_expr_def, compile_builtin_dispatch_body_def, as_stack_val_def] >> strip_tac >>
  gvs[expr_type_def] >>
  `?out. q = Var out` by
    (qpat_x_assum `compile_env_var MsgGas _ = _` mp_tac >>
     simp[compile_env_var_def, emit_op_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, fresh_id_def,
          fresh_var_def, emit_def] >> metis_tac[]) >>
  gvs[] >> drule_all msg_gas_full_post >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  simp[gas_outcome_full_def] >> qexists_tac `[T]` >> disj1_tac >>
  qexistsl_tac [`INL (Value (IntV (&w2n w)))`, `es`, `OK t`, `G`, `tn`] >>
  simp[gas_explicit_def, expr_type_def, vv_store_bound_stack_word,
       env_item_type_def, is_word_type_def, ptr_vv_ok_def] >>
  conj_tac
  >- (gen_tac >>
      `!s tv s'. eval_expr cx (Builtin (BaseT (UintT 256)) (Env MsgGas) []) s =
         (INL tv,s') ==> ?v. tv = Value v` by
        metis_tac[eval_expr_builtin_value] >>
      drule eval_expr_force_value >>
      disch_then (qspecl_then [`es with gas_obs := w::tail`,
        `INL (IntV (&w2n w))`, `es with gas_obs := tail`] mp_tac) >>
      simp[SRULE [env_item_type_def] msg_gas_source]) >>
  conj_tac
  >- (drule_at (Pos last) vv_post_of_expr_post >>
      simp[post_value_type_def, expr_type_def, env_item_type_def,
           is_word_type_def]) >>
  gvs[read_result_def, return_def, env_item_type_def]
QED
