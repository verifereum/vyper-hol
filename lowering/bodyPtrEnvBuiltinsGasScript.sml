(* Explicit msg.gas: one checked GAS edge and the unchanged S1 frame. *)
Theory bodyPtrEnvBuiltinsGas
Ancestors
  bodyPtrEnvBuiltinsScalar bodyPtrEnvBuiltinsEdges bodyPtrDefs bodyPtrPreds
  decoderGhostFramePtr
  msgGasSim msgGasPost fragGasPathPtr fragGasSeqPtr gasSummary
  ptrDiscipline ptrSafeRun emitHelper emitHelperProps exprLoweringProps
  compileEnv exprLowering exprPtrUnwrap exprSimProps stmtFragPtr
  venomInst venomState venomExecSemantics finite_map pred_set list rich_list
  vyperAST vyperTypeSystem vyperValue valueEncoding codegenRel exprSimHypsDefs

Theorem gas_builtin_base_step:
  ?w. gas_prefix 1 s.vs_gas_readings = [w] /\
      step_inst_base (mk_inst id GAS [] [out]) s =
        OK (update_var out w (s with vs_gas_readings := DROP 1 s.vs_gas_readings))
Proof
  Cases_on `s.vs_gas_readings`
  >- (qexists_tac `0w` >>
      simp[gasOracleReplayTheory.gas_prefix_def,
       Once (numLib.num_CONV ``1``), TAKE_def, REPLICATE,
           step_inst_base_opcode_eqs, exec_gas_def, mk_inst_def] >>
      gvs[update_var_def, venom_state_component_equality] >> EVAL_TAC) >>
  qexists_tac `h` >>
  simp[gasOracleReplayTheory.gas_prefix_def,
       Once (numLib.num_CONV ``1``), TAKE_def, REPLICATE,
       step_inst_base_opcode_eqs, exec_gas_def, mk_inst_def] >> EVAL_TAC
QED

Theorem gas_builtin_ghosts:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~not_fresh_at sa out ==>
  !t. t = update_var out w (s with vs_gas_readings := gs) ==>
  ghost_inv d cenv cx es
    (step_prov PG G (mk_inst id GAS [] [out]) t)
    (step_taint (mk_inst id GAS [] [out]) s t tn) t /\
  ghost_kept cenv es sa G tn s
    (step_prov PG G (mk_inst id GAS [] [out]) t)
    (step_taint (mk_inst id GAS [] [out]) s t tn)
Proof
  strip_tac >> gen_tac >> strip_tac >>
  `(step_taint (mk_inst id GAS [] [out]) s t tn).t_mem = tn.t_mem` by
    (irule step_taint_no_memory_effect >>
     simp[source_memory_write_ranges_def, written_taint_def, mk_inst_def] >>
     gvs[update_var_def]) >>
  conj_tac
  >- (irule single_output_ghost_inv >> simp[] >>
      qexists_tac `sa` >> simp[] >>
      gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> IF_CASES_TAC >> gvs[]) >>
  irule single_output_ghost_kept >> simp[ghost_kept_refl]
QED

Theorem ghost_inv_gas_readings[simp]:
  ghost_inv d cenv cx es G tn (s with vs_gas_readings := gs) <=>
  ghost_inv d cenv cx es G tn s
Proof
  Cases_on `d` >- simp[ghost_inv_def, ptr_covers_def, return_buf_ptr_def, stor_taint_ok_def,
                        lookup_var_def] >>
  PairCases_on `x` >>
  simp[ghost_inv_def, ptr_covers_def, return_buf_ptr_def,
       stor_taint_ok_def, lookup_var_def]
QED

Theorem gas_builtin_indexed_ghosts_at:
  ghost_inv_at D lo d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~not_fresh_at sa out ==>
  ghost_inv_at D lo d cenv cx es
    (step_prov PG G (mk_inst id GAS [] [out])
      (update_var out w (s with vs_gas_readings := gs)))
    (step_taint (mk_inst id GAS [] [out]) s
      (update_var out w (s with vs_gas_readings := gs)) tn)
    (update_var out w (s with <|vs_gas_readings := gs; vs_inst_idx := k|>)) /\
  ghost_kept_at lo cenv es sa G tn s
    (step_prov PG G (mk_inst id GAS [] [out])
      (update_var out w (s with vs_gas_readings := gs)))
    (step_taint (mk_inst id GAS [] [out]) s
      (update_var out w (s with vs_gas_readings := gs)) tn)
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `step_prov PG G inst u` >>
  `(step_taint inst s u tn).t_mem = tn.t_mem` by
    (irule step_taint_no_memory_effect >>
     simp[Abbr `inst`, Abbr `u`, source_memory_write_ranges_def,
          written_taint_def, mk_inst_def, update_var_def]) >>
  conj_tac
  >- (irule ghost_inv_at_register_transport >>
      qexistsl_tac [`G`, `s`, `sa`, `tn`] >>
      simp[update_var_def] >>
      `((step_taint inst s u tn).t_stor = tn.t_stor) /\
       ((step_taint inst s u tn).t_trans = tn.t_trans) /\
       ((step_taint inst s u tn).t_imm = tn.t_imm)` by
        (irule step_taint_nonmemory_frame >> simp[Abbr `inst`, mk_inst_def]) >>
      simp[] >> rpt strip_tac >> `x <> out` by metis_tac[] >>
      simp[Abbr `inst`, step_prov_other_output, step_taint_other_output,
           mk_inst_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  unabbrev_all_tac >> irule single_output_ghost_kept_at >>
  simp[ghost_kept_at_def]
QED

Theorem gas_builtin_indexed_ghosts:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~not_fresh_at sa out ==>
  ghost_inv d cenv cx es
    (step_prov PG G (mk_inst id GAS [] [out])
      (update_var out w (s with vs_gas_readings := gs)))
    (step_taint (mk_inst id GAS [] [out]) s
      (update_var out w (s with vs_gas_readings := gs)) tn)
    (update_var out w (s with <|vs_gas_readings := gs; vs_inst_idx := k|>)) /\
  ghost_kept cenv es sa G tn s
    (step_prov PG G (mk_inst id GAS [] [out])
      (update_var out w (s with vs_gas_readings := gs)))
    (step_taint (mk_inst id GAS [] [out]) s
      (update_var out w (s with vs_gas_readings := gs)) tn)
Proof
  pure_rewrite_tac[ghost_inv_cx_dead, ghost_kept_zero] >>
  metis_tac[gas_builtin_indexed_ghosts_at]
QED

Theorem gas_builtin_counted_post:
  compile_env_var MsgGas sa = (op,sb) /\ fn_has_code sa sb fn /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx es G tn s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx fn cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?w G' tn' t.
    gas_prefix 1 s.vs_gas_readings = [w] /\
    gas_path_ptr D 0 ctx fn PG G tn s 1 G' tn' (OK t) /\
    expr_post ctx fn cenv cx (Builtin (env_item_type MsgGas) (Env MsgGas) [])
      es sa sb s (es with gas_obs := []) (IntV (&w2n w)) op t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv d cenv cx (es with gas_obs := []) G' tn' t /\
    ptr_val_ok cx (env_item_type MsgGas) (IntV (&w2n w)) op G' tn' t /\
    ghost_kept cenv es sa G tn s G' tn'
Proof
  strip_tac >>
  `emit_op GAS [] sa = (op,sb)` by gvs[compile_env_var_def] >>
  `op = Var (STRING #"%" (toString sa.cs_next_var)) /\
   sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_id_def, fresh_var_def, emit_def] >>
  `~not_fresh_at sa (STRING #"%" (toString sa.cs_next_var))` by
    simp[not_fresh_at_def] >>
  `?w. gas_prefix 1 s.vs_gas_readings = [w] /\
    step_inst_base (mk_inst sa.cs_next_id GAS []
      [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var)) w
      (s with vs_gas_readings := DROP 1 s.vs_gas_readings))` by
    metis_tac[gas_builtin_base_step] >>
  drule emit_scalar_builtin_counted_suffix >> simp[MEM] >>
  disch_then drule_all >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] assume_tac) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `SUC s.vs_inst_idx = LENGTH sb.cs_current_insts` by simp[] >>
  `expr_post ctx fn cenv cx (Builtin (env_item_type MsgGas) (Env MsgGas) [])
    es sa sb s (es with gas_obs := []) (IntV (&w2n w)) op
    (update_var (STRING #"%" (toString sa.cs_next_var)) w
      (s with <|vs_gas_readings := DROP 1 s.vs_gas_readings;
                 vs_inst_idx := LENGTH sb.cs_current_insts|>))` by
    metis_tac[msg_gas_post_frame] >>
  drule gas_builtin_indexed_ghosts >> disch_then drule_all >>
  disch_then (qspecl_then [`w`, `LENGTH sb.cs_current_insts`, `sa.cs_next_id`,
    `DROP 1 s.vs_gas_readings`, `PG`] strip_assume_tac) >>
  qpat_x_assum `ghost_inv _ _ _ _ _ _ (update_var _ _ _)` mp_tac >>
  `update_var (STRING #"%" (toString sa.cs_next_var)) w
     (s with <|vs_gas_readings := DROP 1 s.vs_gas_readings;
               vs_inst_idx := LENGTH sb.cs_current_insts|>) =
   update_var (STRING #"%" (toString sa.cs_next_var)) w
     (s with vs_gas_readings := DROP 1 s.vs_gas_readings) with
     vs_inst_idx := LENGTH sb.cs_current_insts` by simp[update_var_def] >>
  pop_assum (fn th => rewrite_tac[th, ghost_inv_inst_idx]) >> strip_tac >>
  qpat_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  gvs[update_var_def, ptr_val_ok_def, env_item_type_def, is_word_type_def,
      arithmeticTheory.ADD1, ghost_inv_gas_obs] >>
  conj_tac
  >- (irule scalar_builtin_output_clean >> simp[MEM]) >>
  irule scalar_builtin_output_no_prov >> simp[MEM]
QED

Theorem compile_msg_gas_sim_ptr:
  expr_sim_ptr d ctx PG fn cenv cx ty
    (Builtin (env_item_type MsgGas) (Env MsgGas) []) es
Proof
  rw[expr_sim_ptr_def] >>
  drule lower_value_env >> strip_tac >>
  drule_all gas_builtin_counted_post >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  simp[gas_outcome_ptr_def] >> qexists_tac `[T]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (IntV (&w2n w))`, `es`, `G'`, `tn'`, `OK t`] >>
  simp[gas_explicit_def, msg_gas_source] >>
  gvs[expr_type_def, env_item_type_def, is_word_type_def]
QED

Theorem compile_msg_gas_vv_sim_ptr:
  expr_vv_sim_ptr d ctx PG fn cenv cx ty
    (Builtin (env_item_type MsgGas) (Env MsgGas) []) es
Proof
  irule expr_vv_sim_ptr_stack >> conj_tac
  >- (gen_tac >> simp[compile_expr_def] >>
      Cases_on `compile_env_var MsgGas sa` >> simp[as_stack_val_def]) >>
  conj_tac >- metis_tac[eval_expr_builtin_value] >>
  simp[compile_msg_gas_sim_ptr]
QED

Theorem body_msg_gas_ptr_case:
  body_expr_ptr_ok cx (Builtin ann (Env MsgGas) args)
Proof
  rw[body_expr_ptr_ok_def] >>
  `args = [] /\ ann = env_item_type MsgGas` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  gvs[] >> simp[compile_msg_gas_sim_ptr, compile_msg_gas_vv_sim_ptr]
QED
