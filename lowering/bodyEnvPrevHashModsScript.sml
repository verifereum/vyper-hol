(* The previous-block hash uses NUMBER, SUB and BLOCKHASH, with no writes
   other than the three fresh registers. Keep the linked frame on that run. *)
Theory bodyEnvPrevHashMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullShadowBodyInv
  bodyForRangeScalarFrameMods gasOutcomeFullPostMods
  exprBodyPreProps builtinProps varsExt
  allocaHistoryFragment valueEncoding valueEncodingProofs exprSimProps exprSimWordArgs
  exprLoweringProps loweringPosts stateRelProj exprSimMemDefs bodyPtrDefs
  gasContext gasExplicitSites fragGasSeqPtr emitHelperProps emitHelper
  vyperTypeBuiltins vyperTypeSystem vyperAST vyperValue vyperInterpreter
  vyperContext vyperState loweringStateRelDefs vyperStorageFootprint
  vyperStorageTrace compileEnv exprLowering venomExecSemantics venomInst
  venomState instMemFrontier memSafeRun ptrDiscipline finite_map rich_list
  list fragExecMem loweringSlice fragExec unitTransformDefs contextCodegenRel
  codegenRel ptrSafeRun vyperStorageBackend exprSimUnopProps

Theorem prevhash_seq[local]:
  compile_env_var PrevHash sa = (op,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?G' tn'.
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\
    (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!D lo. allocas_from lo s ==>
      inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s G' tn')
Proof
  strip_tac >>
  gvs[compile_env_var_def, emit_op_def, comp_bind_def, fresh_var_def,
      fresh_id_def, comp_ignore_bind_def, comp_return_def, emit_def,
      emitted_insts_def] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, DROP_LENGTH_APPEND]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> gvs[] >>
  qmatch_goalsub_abbrev_tac `mk_inst iid NUMBER [] [v0]` >>
  qmatch_goalsub_abbrev_tac `mk_inst iid1 SUB _ [v1]` >>
  qmatch_goalsub_abbrev_tac `mk_inst iid2 BLOCKHASH _ [v2]` >>
  qexistsl_tac [`DRESTRICT G (COMPL {v0;v1;v2})`,
    `tn with t_var := tn.t_var |+ (v0,{}) |+ (v1,{}) |+ (v2,{})`] >>
  `!x. not_fresh_at sa x ==> x <> v0 /\ x <> v1 /\ x <> v2` by
    (simp[Abbr `v0`, Abbr `v1`, Abbr `v2`, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_ADD]) >>
  simp[op_prov_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  conj_tac
  >- (irule run_inst_seq_mem_ok_every >>
      simp[MEM, mk_inst_def, inst_dload_in_section_def] >>
      rpt strip_tac >> irule below_frontier_no_ranges >>
      simp[source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  rpt gen_tac >> strip_tac >>
  fs[run_inst_seq_def, step_inst_base_opcode_eqs, exec_read0_def,
     exec_pure2_def, exec_read1_def, mk_inst_def, eval_operands_def,
     eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  suspend "steps"
QED

Resume prevhash_seq[steps]:
  simp[Once inst_seq_ptr_def] >>
  simp[step_inst_base_opcode_eqs, exec_read0_def,
       exec_pure2_def, exec_read1_def, eval_operands_def, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       step_prov_def, out_prov_def, set_prov_def, first_prov_def,
       op_prov_def, step_taint_def, out_taint_def, set_var_taint_def,
       store_taint_def, imm_taint_def, adopt_reset_def] >>
  conj_tac
  >- simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def,
          step_inst_def, step_inst_base_opcode_eqs, exec_read0_def, update_var_def] >>
  simp[mem_taint_def, new_site_bytes_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def, range_bytes_def,
       FLOOKUP_DEF] >>
  simp[Once inst_seq_ptr_def] >>
  simp[step_inst_base_opcode_eqs, exec_pure2_def, eval_operands_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       step_prov_def, out_prov_def, set_prov_def, first_prov_def,
       op_prov_def, FLOOKUP_DRESTRICT, step_taint_def, out_taint_def,
       set_var_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
       op_taint_def] >>
  conj_tac
  >- (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
           source_memory_read_ranges_def, source_memory_write_ranges_def,
           step_inst_def, step_inst_base_opcode_eqs, exec_pure2_def,
           eval_operands_def, eval_operand_def, lookup_var_def,
           FLOOKUP_UPDATE, op_taint_def, update_var_def, allocas_from_def, allocas_below_fmp_def] >>
      fs[allocas_from_def, allocas_below_fmp_def] >> conj_tac
      >- (gen_tac >> Cases_on `op` >> simp[] >> metis_tac[]) >>
      metis_tac[]) >>
  simp[mem_taint_def, new_site_bytes_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def, range_bytes_def,
       FLOOKUP_DEF, SF CONJ_ss] >>
  simp[Once inst_seq_ptr_def] >>
  simp[step_inst_base_opcode_eqs, exec_read1_def, eval_operands_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       step_prov_def, out_prov_def, set_prov_def, first_prov_def,
       op_prov_def, FLOOKUP_DRESTRICT, step_taint_def, out_taint_def,
       set_var_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
       op_taint_def] >> conj_tac
  >- (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
           source_memory_read_ranges_def, source_memory_write_ranges_def,
           step_inst_def, step_inst_base_opcode_eqs, exec_read1_def,
           eval_operands_def, eval_operand_def, lookup_var_def,
           FLOOKUP_UPDATE, op_taint_def, update_var_def, allocas_from_def,
           allocas_below_fmp_def] >>
      fs[allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  simp[inst_seq_ptr_def, mem_taint_def, new_site_bytes_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def, range_bytes_def,
       FLOOKUP_DEF, SF CONJ_ss] >> conj_tac
  >- (AP_TERM_TAC >> simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  simp[taint_component_equality]
QED

Finalise prevhash_seq

Theorem prevhash_source[local]:
  tx_env_ok cx.txn ==>
  !s. bind (eval_expr cx (Builtin (env_item_type PrevHash) (Env PrevHash) []))
      (read_result cx) s =
    (INL (BytesV (word_to_bytes_be (EL 0 cx.txn.block_hashes))),s)
Proof
  strip_tac >> gen_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, get_accounts_def, lift_sum_def,
       builtin_args_length_ok_def, read_result_def, is_self_codesize_def] >>
  simp[Once evaluate_def, bind_def, read_result_def, return_def,
       evaluate_builtin_def, tx_env_ok_evaluate_prevhash]
QED

Theorem prevhash_run[local]:
  compile_env_var PrevHash sa = (op,sb) /\
  call_ctx_rel cx.txn s.vs_call_ctx s.vs_tx_ctx s.vs_block_ctx ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME (HD cx.txn.block_hashes) /\
      t = s with vs_vars := t.vs_vars /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule_then strip_assume_tac compile_prevhash_shape >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  drule_all_then strip_assume_tac compile_prevhash_run >>
  `vars_ext_result (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s))
     (run_inst_seq (emitted_insts sa sb) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >> fs[EVERY_MEM]) >>
  gvs[vars_ext_result_def] >> rename1 `vars_ext tt t` >>
  drule call_ctx_rel_prevhash >> strip_tac >>
  `eval_operand op t = SOME (HD cx.txn.block_hashes)` by
    (fs[vars_ext_def, drop_fresh_def] >>
     qpat_x_assum `t = tt with vs_vars := _` SUBST1_TAC >>
     simp[eval_operand_vars_ext]) >>
  drule_all_then strip_assume_tac compile_prevhash_frame >>
  simp[lookup_var_def]
QED

Theorem prevhash_path[local]:
  compile_env_var PrevHash sa = (op,sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  (!D lo. allocas_from lo s ==>
    inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s G' tn') ==>
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  (!D lo. allocas_from lo s ==>
     gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
       (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn'))
Proof
  strip_tac >> drule_then strip_assume_tac compile_prevhash_shape >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest) /\
   s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND, emitted_insts_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    fs[EVERY_MEM] >>
  conj_tac >- (drule_all alloca_history_run_inst_seq >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  `(ctx_has_dalloca ctx ==>
    !pre i post u. emitted_insts sa sb = pre ++ i::post /\
      run_inst_seq pre s = OK u ==> dalloca_no_wrap i u)` by
    (rpt strip_tac >> irule dalloca_no_wrap_non_dalloca >>
     qpat_assum `EVERY (\i. _ /\ _ /\ _ /\ MEM _ _ /\ _) _`
       mp_tac >> simp[EVERY_APPEND] >> strip_tac >> gvs[]) >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >>
     qpat_assum `EVERY (\i. _ /\ _ /\ _ /\ MEM _ _ /\ _) _`
       (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `i` mp_tac) >> simp[]) >>
  `inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s G' tn'` by simp[] >>
  drule_all run_inst_seq_gas_origin_ptr_path >> simp[]
QED

Theorem prevhash_value_post[local]:
  stmt_state_rel H ctx func cenv cx es t /\
  storage_well_formed_on cx es (FST H) /\
  immutable_frame_mods func cenv cx (es with gas_obs := []) t /\
  eval_operand op t = SOME (HD cx.txn.block_hashes) /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas ==>
  expr_post_mods H ctx func cenv cx
    (Builtin (env_item_type PrevHash) (Env PrevHash) []) es sa sb s
    (es with gas_obs := []) (BytesV (word_to_bytes_be (EL 0 cx.txn.block_hashes))) op t
Proof
  strip_tac >>
  `storage_well_formed_on cx (es with gas_obs := []) (FST H)` by
    (`storage_well_formed_on cx (es with gas_obs := []) (FST H) <=>
      storage_well_formed_on cx es (FST H)` suffices_by simp[] >>
     irule storage_well_formed_on_backends >> simp[]) >>
  simp[expr_post_mods_def, expr_post_def, expr_val_rel_def, expr_val_at_def,
       expr_type_def, env_item_type_def, is_word_type_def, vyperValueTheory.evaluate_type_def,
       post_value_type_def, typed_val_to_w256_def, PAD_RIGHT,
       length_word_to_bytes_be, word_of_bytes_be_to_bytes,
       stmt_state_rel_start_gas_obs, locals_kept_def, pure_frame_def,
       popped_kept_def, vyperEvalScopesProgressTheory.scopes_progress_refl]
QED

Theorem prevhash_value_sim_mods[local]:
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin (env_item_type PrevHash) (Env PrevHash) []) es
Proof
  rewrite_tac[expr_sim_full_mods_def] >> rpt gen_tac >> strip_tac >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (irule gas_outcome_full_mods_bad_nil >> simp[] >>
      rpt gen_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
           assert_def, return_def, raise_def, get_accounts_def, lift_sum_def,
           builtin_args_length_ok_def, read_result_def, is_self_codesize_def] >>
      simp[Once evaluate_def, bind_def, read_result_def, return_def,
           evaluate_builtin_def, evaluate_block_hash_def] >> IF_CASES_TAC >>
      simp[raise_def, return_def, read_result_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _` (drule_then strip_assume_tac) >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  drule stmt_state_rel_state_rel >> disch_then (assume_tac o MATCH_MP state_rel_call_ctx_rel) >>
  `tx_env_ok cx.txn` by fs[call_ctx_rel_def] >>
  drule_then assume_tac lower_value_env >>
  drule_all_then strip_assume_tac prevhash_run >>
  drule_all prevhash_seq >>
  disch_then (qspecl_then [`tn0`,`func`,`PG`,`G0`] strip_assume_tac) >>
  drule_all prevhash_path >>
  disch_then (qspec_then `gas_explicit_sites ctx shadow_ctx` strip_assume_tac) >>
  qabbrev_tac `u = t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  irule gas_outcome_full_mods_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G'`,`es`,`INL (BytesV (word_to_bytes_be (EL 0 cx.txn.block_hashes)))`,
                `u`,`tn'`] >>
  conj_tac >- simp[prevhash_source] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _`
    (drule_then strip_assume_tac) >>
  conj_tac >- (qpat_assum `!D lo. allocas_from _ _ ==> gas_origin_ptr_path _ _ _ _`
      (qspecl_then [`DF H`,`lo`] irule) >> fs[ghost_inv_at_mods_def]) >>
  suspend "post"
QED

Resume prevhash_value_sim_mods[post]:
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s0` by
    fs[Abbr `u`, lookup_var_def] >>
  `stmt_state_rel H ctx func cenv cx es u` by
    (simp[Abbr `u`, stmt_state_rel_inst_idx] >>
     qpat_assum `t = s0 with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
     irule stmt_state_rel_vars_frame >> simp[] >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x t = _`
       (assume_tac o REWRITE_RULE [lookup_var_def]) >>
     fs[local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]) >>
  `u.vs_memory = s0.vs_memory /\ u.vs_data_section = s0.vs_data_section /\
   u.vs_allocas = s0.vs_allocas /\ u.vs_alloca_next = s0.vs_alloca_next /\
   u.vs_call_ctx = s0.vs_call_ctx /\ u.vs_accounts = s0.vs_accounts /\
   u.vs_transient = s0.vs_transient /\ u.vs_immutables = s0.vs_immutables /\
   u.vs_current_bb = s0.vs_current_bb /\ u.vs_fmp = s0.vs_fmp /\
   u.vs_initial_fmp = s0.vs_initial_fmp` by
    (simp[Abbr `u`] >>
     qpat_assum `t = s0 with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `immutable_frame_mods func cenv cx (es with gas_obs := []) u` by
    (irule immutable_frame_mods_exterior_frame >> qexistsl_tac [`es`,`s0`,`sa`] >> simp[]) >>
  `ghost_inv_at_mods (DF H) lo d cenv cx (es with gas_obs := []) G' tn' u` by
    (irule ghost_inv_at_mods_exterior_frame >> qexistsl_tac [`G0`,`es`,`s0`,`sa`,`tn0`] >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_x_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s0` mp_tac >>
     simp[allocas_below_fmp_def] >> metis_tac[]) >>
  drule_then strip_assume_tac compile_prevhash_shape >>
  `eval_operand op u = SOME (HD cx.txn.block_hashes)` by
    simp[Abbr `u`, eval_operand_def, lookup_var_def] >>
  simp[expr_store_bound_def, ptr_val_ok_def, ghost_kept_at_def,
       expr_type_def, env_item_type_def, is_word_type_def] >>
  conj_tac >- (irule (SIMP_RULE (srw_ss()) [env_item_type_def] prevhash_value_post) >> simp[]) >>
  fs[Abbr `u`]
QED

Finalise prevhash_value_sim_mods

Theorem prevhash_sim_mods:
  (!DF lo d ctx sh PG f sf cenv cx ty e es.
    is_word_type (post_value_type cenv e) /\
    expr_sim_full_mods (DF,lo,d,ctx,sh,PG,f,sf) cenv cx ty e es /\
    (!sa. ?a op sb. compile_expr cenv ty e sa = (StackValue a op,sb)) /\
    (!s tv t. eval_expr cx e s = (INL tv,t) ==> ?v. tv = Value v) ==>
    expr_vv_sim_full_mods (DF,lo,d,ctx,sh,PG,f,sf) cenv cx ty e es) ==>
  !DF lo d ctx shadow_ctx PG func shadow_func cenv env cx ty ann args es.
    expr_body_pre_mods mods cenv cx env (Builtin ann (Env PrevHash) args) es ==>
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin ann (Env PrevHash) args) es /\
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin ann (Env PrevHash) args) es
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule expr_body_pre_mods_well_typed >>
  simp[well_typed_expr_def, well_typed_builtin_app_def] >> strip_tac >> gvs[] >>
  conj_asm1_tac >- simp[prevhash_value_sim_mods] >>
  first_assum irule >> simp[expr_type_def, env_item_type_def, is_word_type_def] >>
  reverse conj_tac >- metis_tac[eval_expr_builtin_value] >>
  gen_tac >> simp[compile_expr_def] >>
  Cases_on `compile_env_var PrevHash sa` >> simp[as_stack_val_def]
QED
