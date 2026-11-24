(* The explicit msg.gas read uses one paired GAS/GASPRICE site. *)
Theory bodyMsgGasCaseMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullShadowBodyInv bodyForRangeScalarFrameMods
  gasOutcomeFullMods gasOutcomeFullPostMods vyperStorageFootprint
  msgGasOrigin msgGasPost msgGasSim bodyMemBiEnvMsgGas bodyPtrEnvBuiltinsGas
  bodyPtrEnvBuiltinsEdges fragGasSeqPtr fragGasOriginPtr exprBodyPreProps
  gasShadowCompile exprSimIfExp exprSimMemDefs exprSimStack exprSimProps gasShadow gasSummary
  allocaHistory gasOracleReplay ptrDiscipline loweringPosts emitHelper
  exprLowering vyperAST vyperTypeSystem vyperContext vyperInterpreter vyperState
  compileEnv loweringStateRelDefs unitTransformDefs contextCodegenRel codegenRel
  memSafeRun decoderGhostFramePtr bodyPtrDefs venomExecSemantics
  context venomState venomInst finite_map pred_set list

Theorem msg_gas_vv_source[local]:
  eval_expr cx (Builtin (env_item_type MsgGas) (Env MsgGas) [])
    (es with gas_obs := w::tail) = (INL (Value (IntV (&w2n w))), es with gas_obs := tail)
Proof
  once_rewrite_tac[evaluate_def] >>
  simp[builtin_args_length_ok_def, bind_def, ignore_bind_def, type_check_def,
       check_def, assert_def, return_def, next_gas_reading_def]
QED

Theorem msg_gas_compile_env[local]:
  compile_expr ce ty (Builtin ann (Env item) []) sa = (vv,sb) ==>
  ?op. compile_env_var item sa = (op,sb) /\ vv = StackValue ann op
Proof
  Cases_on `compile_env_var item sa` >>
  simp[Once compile_expr_def, compile_expr_def, compile_builtin_dispatch_body_def,
       as_stack_val_def, expr_type_def] >> metis_tac[]
QED

Theorem msg_gas_fresh[local]:
  compile_env_var MsgGas sa = (Var out,sb) ==> ~not_fresh_at sa out
Proof
  simp[compile_env_var_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[not_fresh_at_def]
QED

Theorem msg_gas_single_step[local]:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id GAS [] [out]) /\
  (func.fn_name,id) IN explicit /\ ~s.vs_halted /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  step_inst_base (mk_inst id GAS [] [out]) s = OK u /\ ~u.vs_halted ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [T]
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G (mk_inst id GAS [] [out]) u,
     step_taint (mk_inst id GAS [] [out]) s u tn)
Proof
  strip_tac >>
  `ptr_inst_ok D lo 0 ctx func G tn (mk_inst id GAS [] [out]) s` by
    (irule ptr_inst_ok_scalar_builtin_at >> simp[]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn)
     (if (mk_inst id GAS [] [out]).inst_opcode = GAS then
        [(func.fn_name,(mk_inst id GAS [] [out]).inst_id) IN explicit] else [])
     (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
      step_prov PG G (mk_inst id GAS [] [out]) u,
      step_taint (mk_inst id GAS [] [out]) s u tn)` by
    (irule straight_line_origin_ptr_edge >> fs[] >>
     simp[mk_inst_def, is_terminator_def, inst_mem_below_frontier_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def,
          inst_dload_in_section_def, dalloca_no_wrap_def]) >>
  irule (SIMP_RULE std_ss [APPEND_NIL]
    (Q.INST [`right` |-> `[]`] (SPEC_ALL (cj 2 gas_origin_ptr_path_rules)))) >>
  irule_at Any (cj 1 gas_origin_ptr_path_rules) >> gvs[mk_inst_def]
QED

Theorem msg_gas_linked_ghost[local]:
  ghost_inv_at_mods D lo d ce cx es G tn s /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~not_fresh_at sa out ==>
  let i = mk_inst id GAS [] [out];
      u = update_var out w (s with vs_gas_readings := DROP 1 s.vs_gas_readings);
      G' = step_prov PG G i u;
      tn' = step_taint i s u tn
  in ghost_inv_at_mods D lo d ce cx (es with gas_obs := []) G' tn'
       (u with vs_inst_idx := k) /\ ghost_kept_at lo ce es sa G tn s G' tn' /\
     ptr_val_ok cx (env_item_type MsgGas) (IntV (&w2n w)) (Var out) G' tn'
       (u with vs_inst_idx := k)
Proof
  strip_tac >> simp[] >> qmatch_goalsub_abbrev_tac `step_taint i s u tn` >>
  `(step_taint i s u tn).t_mem = tn.t_mem` by
    (irule step_taint_no_memory_effect >>
     simp[Abbr `i`, Abbr `u`, source_memory_write_ranges_def,
          written_taint_def, mk_inst_def, update_var_def]) >>
  conj_tac
  >- (irule ghost_inv_at_mods_exterior_frame >>
      qexistsl_tac [`G`, `es`, `s`, `sa`, `tn`] >>
      `(step_taint i s u tn).t_stor = tn.t_stor /\
       (step_taint i s u tn).t_trans = tn.t_trans /\
       (step_taint i s u tn).t_imm = tn.t_imm` by
        (irule step_taint_nonmemory_frame >> simp[Abbr `i`, mk_inst_def]) >>
      simp[Abbr `u`, update_var_def] >> rpt strip_tac >>
      `x <> out` by metis_tac[] >>
      simp[Abbr `i`, step_prov_other_output, step_taint_other_output,
           mk_inst_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  conj_tac
  >- (fs[Abbr `i`] >> irule single_output_ghost_kept_at >> fs[ghost_kept_at_def]) >>
  simp[ptr_val_ok_def, env_item_type_def, is_word_type_def, Abbr `i`] >>
  conj_tac
  >- (irule scalar_builtin_output_clean >> simp[]) >>
  irule scalar_builtin_output_no_prov >> simp[]
QED

Theorem msg_gas_linked_immutable[local]:
  immutable_frame_mods func ce cx es s /\ local_ptrs_reserved ce sa /\
  ~not_fresh_at sa out ==>
  immutable_frame_mods func ce cx (es with gas_obs := [])
    (update_var out w (s with vs_gas_readings := gs) with vs_inst_idx := k)
Proof
  strip_tac >> irule immutable_frame_mods_exterior_frame >>
  qexistsl_tac [`es`, `s`, `sa`] >> simp[update_var_def] >>
  rpt strip_tac >> `x <> out` by metis_tac[] >>
  simp[lookup_var_def, FLOOKUP_UPDATE]
QED

(* Choose the observed word and the machine endpoint before the horizon. *)
Theorem msg_gas_landing[local]:
  compile_env_var MsgGas sa = (op,sb) /\
  compile_env_var GasPrice sha = (shop,shb) /\
  gas_shadow_state sa sha /\ gas_shadow_function func shfunc /\
  MEM func ctx.ctx_functions /\ MEM shfunc shctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code sha shb shfunc /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s /\ immutable_frame_mods func ce cx es s /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out w t G' tn'. op = Var out /\ gas_explicit [T] s.vs_gas_readings = [w] /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    !H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
        (s,G,tn) [T] (OK t,G',tn') /\
      expr_post H ctx func ce cx (Builtin (env_item_type MsgGas) (Env MsgGas) [])
        es sa sb s (es with gas_obs := []) (IntV (&w2n w)) (Var out) t /\
      immutable_frame_mods func ce cx (es with gas_obs := []) t /\
      ghost_inv_at_mods (DF H) lo d ce cx (es with gas_obs := []) G' tn' t /\
      ptr_val_ok cx (env_item_type MsgGas) (IntV (&w2n w)) (Var out) G' tn' t /\
      ghost_kept_at lo ce es sa G tn s G' tn'
Proof
  strip_tac >> drule_all msg_gas_canonical_placement >> strip_tac >> gvs[] >>
  drule_then assume_tac msg_gas_fresh >>
  strip_assume_tac (Q.INST [`s` |-> `s`,`id` |-> `id`,`out` |-> `out`] gas_builtin_base_step) >>
  `gas_explicit [T] s.vs_gas_readings = [w]` by simp[gas_explicit_def] >>
  qabbrev_tac `u = update_var out w (s with vs_gas_readings := DROP 1 s.vs_gas_readings)` >>
  qabbrev_tac `t = u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  qexistsl_tac [`w`,`t`, `step_prov PG G (mk_inst id GAS [] [out]) u`,
    `step_taint (mk_inst id GAS [] [out]) s u tn`] >>
  `alloca_history func t` by
    (drule_all compile_msg_gas_history >> disch_then (qspec_then `w` mp_tac) >>
     simp[Abbr `t`, Abbr `u`, update_var_def]) >>
  `~u.vs_halted` by simp[Abbr `u`, update_var_def] >>
  `t.vs_current_bb = sa.cs_current_bb /\ t.vs_inst_idx = SUC (LENGTH sa.cs_current_insts) /\
   t.vs_alloca_next = s.vs_alloca_next /\ allocas_below_fmp t = allocas_below_fmp s` by
    simp[Abbr `t`, Abbr `u`, update_var_def, allocas_below_fmp_def] >>
  simp[] >> gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  conj_tac >-
    (`t = u with vs_inst_idx := SUC s.vs_inst_idx` by simp[Abbr `t`] >>
     pop_assum (pure_once_rewrite_tac o single) >>
     irule msg_gas_single_step >> simp[] >> qexists_tac `bb` >> simp[]) >>
  conj_tac >-
    (drule_all msg_gas_post_frame >> disch_then (qspec_then `w` mp_tac) >>
     simp[Abbr `t`, Abbr `u`, update_var_def]) >>
  conj_tac >- (drule_all msg_gas_linked_immutable >> simp[Abbr `t`, Abbr `u`]) >>
  drule_all msg_gas_linked_ghost >>
  simp[Abbr `t`, Abbr `u`]
QED

(* No exempt error is needed: even with no initial oracle entries the
   padded machine reading is replayed by the source with an arbitrary tail. *)
Theorem msg_gas_outcome[local]:
  ~s.vs_halted /\
  (!tail. (SND (source (es with gas_obs := tail))).storage_trace = es.storage_trace) /\
  (!tail. source (es with gas_obs := gas_explicit [T] s.vs_gas_readings ++ tail) =
            (res, es with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [T] (OK t,G',tn') /\
     Q H res (es with gas_obs := []) G' tn' t) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source (es,s,G,tn) Q R
Proof
  strip_tac >> Cases_on `storage_trace_domain cx st0 es.storage_trace`
  >- (rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `[T]` >>
      disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`es`,`OK t`,`G'`,`tn'`] >> simp[]) >>
  irule gas_outcome_full_mods_bad_nil >> simp[]
QED

Theorem msg_gas_trace[local]:
  (SND (eval_expr cx (Builtin (env_item_type MsgGas) (Env MsgGas) [])
    (es with gas_obs := tail))).storage_trace = es.storage_trace /\
  (SND (bind (eval_expr cx (Builtin (env_item_type MsgGas) (Env MsgGas) []))
    (read_result cx) (es with gas_obs := tail))).storage_trace = es.storage_trace
Proof
  Cases_on `tail`
  >- (once_rewrite_tac[evaluate_def] >>
      simp[builtin_args_length_ok_def, bind_def, ignore_bind_def, type_check_def,
           check_def, assert_def, return_def, next_gas_reading_def, raise_def]) >>
  simp[msg_gas_source,msg_gas_vv_source]
QED

Theorem msg_gas_value_sim_mods[local]:
  expr_sim_full_mods (DF,lo,d,ctx,shctx,PG,func,shfunc)
    ce cx ty (Builtin (env_item_type MsgGas) (Env MsgGas) []) es
Proof
  rw[expr_sim_full_mods_def] >>
  drule lower_value_env >> strip_tac >>
  qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[gas_shadow_expr_def, gas_shadow_builtin_def] >> strip_tac >>
  drule lower_value_env >> strip_tac >>
  drule_all msg_gas_landing >> disch_then (qspec_then `PG` strip_assume_tac) >> gvs[] >>
  irule msg_gas_outcome >> simp[msg_gas_trace] >>
  qexistsl_tac [`G'`,`INL (IntV (&w2n w))`,`t`,`tn'`] >>
  simp[msg_gas_trace,msg_gas_source] >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  fs[expr_post_mods_def, expr_store_bound_word, post_value_type_def,
     expr_type_def, env_item_type_def, is_word_type_def]
QED

Theorem msg_gas_vv_sim_mods[local]:
  expr_vv_sim_full_mods (DF,lo,d,ctx,shctx,PG,func,shfunc)
    ce cx ty (Builtin (env_item_type MsgGas) (Env MsgGas) []) es
Proof
  rw[expr_vv_sim_full_mods_def] >>
  drule msg_gas_compile_env >> strip_tac >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[gas_shadow_expr_def, gas_shadow_builtin_def] >>
  disch_then (strip_assume_tac o MATCH_MP msg_gas_compile_env) >>
  drule_all msg_gas_landing >> disch_then (qspec_then `PG` strip_assume_tac) >> gvs[] >>
  irule msg_gas_outcome >> simp[msg_gas_trace] >>
  qexistsl_tac [`G'`,`INL (Value (IntV (&w2n w)))`,`t`,`tn'`] >>
  simp[msg_gas_trace,msg_gas_vv_source] >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule_at (Pos last) vv_post_of_expr_post >>
  simp[post_value_type_def, expr_type_def] >> strip_tac >>
  fs[vv_post_mods_def, vv_post_def, vv_holds_mods_def, vv_place_ptr_mods_def,
     expr_type_def, vv_store_bound_stack_word, env_item_type_def, is_word_type_def,
     ptr_vv_ok_def, ptr_val_ok_def, vv_location_def, read_result_def, return_def] >>
  first_assum ACCEPT_TAC
QED

Theorem body_msg_gas_case_mods:
  !mods exps cx ann args. body_expr_full_ok_mods mods exps cx (Builtin ann (Env MsgGas) args)
Proof
  rw[body_expr_full_ok_mods_def] >>
  drule_then mp_tac expr_body_pre_mods_well_typed >>
  simp[well_typed_expr_def, well_typed_builtin_app_def] >>
  strip_tac >> gvs[msg_gas_value_sim_mods,msg_gas_vv_sim_mods]
QED
