(* Joint full simulation of the previous-block hash environment builtin. *)
Theory bodyFullBuiltinEnvPrevHash
Ancestors
  bodyFullBuiltinEnvPrevHashSeq varsExt vyperState vyperValue
  allocaHistoryFragment valueEncoding valueEncodingProofs exprSimUnopProps
  exprSimWordArgs loweringPosts finite_map exprSimMemDefs bodyPtrDefs vyperStorageBackend
  bodyFullExprGeneric bodyFullGhostFrame bodyFullPreds bodySimFull
  gasOutcomeFullCompose fragGasSeqPtr builtinProps exprSimProps exprSimSource
  exprSimHypsDefs exprLowering exprLoweringProps emitHelperProps emitHelper
  vyperTypeBuiltins vyperTypeSystem vyperAST vyperInterpreter vyperContext
  venomExecSemantics venomInst venomState compileEnv list rich_list
  vyperStorageTrace vyperStorageFootprint loweringStateRelDefs

val _ = Parse.hide "body";

Theorem env_prevhash_value_full[local]:
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin (env_item_type PrevHash) (Env PrevHash) []) es
Proof
  rw[expr_sim_full_def] >>
  irule gas_outcome_full_initial_domain >>
  simp[storage_trace_frame_bind, evaluate_storage_trace_frame,
       storage_trace_frame_read_result] >>
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace)
     es.storage_trace` by gvs[storage_trace_domain_def] >>
  `tx_env_ok cx.txn` by
    (first_x_assum drule >> gvs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def]) >>
  drule lower_value_env >> strip_tac >>
  drule compile_prevhash_shape >> strip_tac >>
  `fresh_vars_wrt sa (drop_fresh sa s0)` by simp[fresh_vars_wrt_drop_fresh] >>
  drule_all compile_prevhash_run >> strip_tac >>
  `vars_ext_result (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s0))
     (run_inst_seq (emitted_insts sa sb) s0)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >> fs[EVERY_MEM]) >>
  gvs[vars_ext_result_def] >> rename1 `vars_ext tt t` >>
  drule_all env_prevhash_seq_ghosts >>
  disch_then (qspecl_then [`tn0`, `func`, `es`, `d`, `cx`, `PG`, `G0`] strip_assume_tac) >>
  `(?bb rest. lookup_block s0.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s0.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest) /\
    s0.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    (gvs[fragExecTheory.fn_has_code_def, IS_PREFIX_APPEND, emitted_insts_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G'`, `es`, `INL (BytesV (word_to_bytes_be (EL 0 cx.txn.block_hashes)))`,
    `t with vs_inst_idx := LENGTH sb.cs_current_insts`, `tn'`] >>
  conj_tac
  >- (simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, get_accounts_def, lift_sum_def,
       builtin_args_length_ok_def, read_result_def] >>
      simp[Once evaluate_def, bind_def, read_result_def, return_def,
       evaluate_builtin_def, tx_env_ok_evaluate_prevhash]) >>
  gen_tac >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx es s0 /\
   ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0` by metis_tac[] >>
  `inst_seq_ptr (DF H) lo ctx func PG G0 tn0 (emitted_insts sa sb) s0 G' tn' /\
   ghost_inv_at (DF H) lo d cenv cx es G' tn'
     (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by metis_tac[] >>
  conj_tac
  >- (drule_at (Pat `run_inst_seq _ s0 = OK t`) run_inst_seq_gas_origin_ptr_path >>
      disch_then (qspecl_then [`lo`, `gas_explicit_sites ctx shadow_ctx`, `PG`, `DF H`, `G0`, `tn0`, `G'`, `tn'`, `ctx`, `func`, `bb`] mp_tac) >>
      impl_tac >- (simp[IS_PREFIX_APPEND] >> fs[EVERY_MEM]) >>
      `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
        (simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >>
         fs[EVERY_MEM] >>
         qpat_x_assum `!i. MEM i (emitted_insts sa sb) ==> _`
           (qspec_then `i` mp_tac) >> simp[]) >> simp[]) >>
  `call_ctx_rel cx.txn s0.vs_call_ctx s0.vs_tx_ctx s0.vs_block_ctx` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  drule call_ctx_rel_prevhash >> strip_tac >>
  `eval_operand op t = SOME (HD cx.txn.block_hashes)` by
    (fs[vars_ext_def, drop_fresh_def] >>
     qpat_x_assum `t = tt with vs_vars := _` SUBST1_TAC >>
     simp[eval_operand_vars_ext]) >>
  drule_all compile_prevhash_frame >> strip_tac >>
  `alloca_inv s0` by gvs[stmt_state_rel_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  drule_all alloca_history_run_inst_seq >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx es t` by
    (qpat_x_assum `t = s0 with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
     irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
     simp[lookup_var_def] >> first_x_assum irule >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       expr_store_bound_def, expr_type_def, env_item_type_def, is_word_type_def,
       evaluate_type_def, typed_val_to_w256_def, PAD_RIGHT,
       length_word_to_bytes_be, word_of_bytes_be_to_bytes,
       stmt_state_rel_inst_idx, locals_kept_mem, ptr_val_ok_def,
       post_value_type_def] >>
  `t.vs_memory = s0.vs_memory /\ t.vs_allocas = s0.vs_allocas /\
   t.vs_alloca_next = s0.vs_alloca_next /\ t.vs_current_bb = s0.vs_current_bb` by
    (qpat_x_assum `t = s0 with vs_vars := _` SUBST1_TAC >> simp[]) >>
  `storage_well_formed_on cx es (FST H)` by metis_tac[] >>
  simp[storage_well_formed_on_def, pure_frame_def, locals_kept_mem,
       lookup_var_def] >>
  conj_tac >- (fs[storage_well_formed_on_def] >> rpt gen_tac >> strip_tac >> qpat_x_assum `!b slot tv. MEM (b,slot,tv) (FST H) ==> _` drule >> Cases_on `b` >> simp[get_storage_def]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (fs[ghost_inv_at_def] >> metis_tac[]) >>
  simp[ghost_kept_at_def] >> FAIL_TAC "kept"
QED

Theorem env_prevhash_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    bt = Env PrevHash /\ builtin_args_length_ok bt (LENGTH args) /\
    (builtin_args_length_ok bt (LENGTH args) /\ bt <> Len ==>
     body_exprs_full_ok cx args) /\
    (builtin_args_length_ok bt (LENGTH args) /\ bt = Len ==>
     body_expr_full_ok cx (HD args)) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin a bt args) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  `args = [] /\ a = env_item_type PrevHash` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  gvs[] >> conj_tac >- simp[env_prevhash_value_full] >>
  irule expr_vv_sim_stack_full >>
  simp[expr_type_def, env_item_type_def, is_word_type_def,
       env_prevhash_value_full] >>
  conj_tac
  >- (gen_tac >> simp[compile_expr_def] >>
      Cases_on `compile_env_var PrevHash sa` >> simp[as_stack_val_def]) >>
  metis_tac[eval_expr_builtin_value]
QED
