(* Previous-block hash: lift the existing straight-line execution to memory. *)
Theory bodyMemBiEnvPrevHash
Ancestors
  builtinProps exprSimProps exprSimSource exprLoweringProps exprLowering
  fragGasSeqMem fragExecMem allocaHistoryFragment instMemFrontier
  loweringSlice emitHelperProps compileEnv venomInst venomState
  venomExecSemantics memSafeRun list rich_list finite_map
  varsExt fragExec contextCodegenRel codegenRel
  gasNormalPrefix gasSummary fragGasMode exprSimMemoryValues exprSimMemoryStack
  bodyMemoryPreds bodyMemoryDefs exprSimHypsDefs loweringPosts
  vyperInterpreter vyperState vyperValue vyperContext vyperTypeSystem vyperTyping
  vyperAST valueEncoding valueEncodingProofs exprSimUnopProps

Theorem body_prevhash_counted:
  compile_env_var PrevHash sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s0 0 (OK t) /\
      eval_operand op t = SOME (HD cx.txn.block_hashes) /\
      stmt_state_rel ctx func cenv cx es t /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==> lookup_var z t = SOME w) /\
      t.vs_memory = s0.vs_memory /\ t.vs_allocas = s0.vs_allocas /\
      t.vs_alloca_next = s0.vs_alloca_next /\ alloca_history func t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `call_ctx_rel cx.txn s0.vs_call_ctx s0.vs_tx_ctx s0.vs_block_ctx` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  drule compile_prevhash_shape >> strip_tac >>
  `fresh_vars_wrt sa (drop_fresh sa s0)` by simp[fresh_vars_wrt_drop_fresh] >>
  drule_all compile_prevhash_run >> strip_tac >>
  `(drop_fresh sa s0).vs_block_ctx = s0.vs_block_ctx` by simp[drop_fresh_def] >>
  `vars_ext_result (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s0))
     (run_inst_seq (emitted_insts sa sb) s0)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >> fs[EVERY_MEM]) >>
  gvs[vars_ext_result_def] >> rename1 `vars_ext tt t` >>
  drule call_ctx_rel_prevhash >> strip_tac >>
  `eval_operand op t = SOME (HD cx.txn.block_hashes)` by
    (fs[vars_ext_def] >>
     qpat_x_assum `t = tt with vs_vars := _` SUBST1_TAC >>
     simp[eval_operand_vars_ext]) >>
  drule_all compile_prevhash_frame >> strip_tac >>
  `(?bb rest. lookup_block s0.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s0.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest) /\
    s0.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND, emitted_insts_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s0` by
    (irule run_inst_seq_mem_ok_every >> fs[EVERY_MEM] >>
     rpt gen_tac >> disch_tac >> first_x_assum drule >> strip_tac >>
     gen_tac >> simp[inst_dload_in_section_def] >>
     irule below_frontier_no_ranges >>
     gvs[source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  `alloca_inv s0` by gvs[stmt_state_rel_def] >>
  drule_all alloca_history_run_inst_seq >> strip_tac >>
  `gas_path_mem ctx func s0 0 (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (drule_at (Pat `run_inst_seq _ _ = OK _`) run_inst_seq_gas_path_mem >>
     disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
     impl_tac >- fs[IS_PREFIX_APPEND, EVERY_MEM] >>
     `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
       (simp[FILTER_EQ_NIL] >> fs[EVERY_MEM] >> rpt strip_tac >>
        qpat_x_assum `!i. MEM i _ ==> _ /\ ~is_ext_call_op _ /\ _`
          drule >> rw[] >> gvs[]) >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es t` by
    (qpat_x_assum `t = _ with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
     irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
     simp[lookup_var_def] >> first_x_assum irule >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  fs[stmt_state_rel_inst_idx, eval_operand_def, lookup_var_def] >>
  qpat_x_assum `t = _ with vs_vars := _` SUBST_ALL_TAC >> gvs[]
QED

Theorem body_prevhash_mem_prefix[local]:
  lower_value compile_expr cenv ty
    (Builtin (env_item_type PrevHash) (Env PrevHash) []) sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?v t. gas_value_prefix T (ctx,func,cenv,cx)
    (ty,Builtin (env_item_type PrevHash) (Env PrevHash) [])
    (sa,sb,op) (es,s0) [] (v,es,t)
Proof
  strip_tac >>
  `tx_env_ok cx.txn` by gvs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  `!tail. bind (eval_expr cx (Builtin (env_item_type PrevHash) (Env PrevHash) []))
            (read_result cx) (es with gas_obs := tail) =
          (INL (BytesV (word_to_bytes_be (EL 0 cx.txn.block_hashes))),
           es with gas_obs := tail)` by
    (simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
          assert_def, return_def, raise_def, get_accounts_def, lift_sum_def,
          builtin_args_length_ok_def, read_result_def] >>
     simp[Once evaluate_def, bind_def, read_result_def, return_def,
          evaluate_builtin_def, tx_env_ok_evaluate_prevhash]) >>
  drule lower_value_env >> strip_tac >>
  drule_all body_prevhash_counted >> strip_tac >>
  drule msg_gas_state_frame >>
  disch_then (qspecl_then [`t.vs_gas_readings`, `t.vs_inst_idx`, `[]`] mp_tac) >>
  simp[NoAsms] >> strip_tac >>
  qexistsl_tac [`BytesV (word_to_bytes_be (EL 0 cx.txn.block_hashes))`, `t`] >>
  simp[gas_value_prefix_def, gas_marked_exec_def, gas_marked_path_def,
       gas_explicit_def, expr_post_def, expr_val_rel_def, expr_val_at_def,
       expr_type_def, env_item_type_def, is_word_type_def,
       evaluate_type_def, typed_val_to_w256_def, PAD_RIGHT,
       length_word_to_bytes_be, word_of_bytes_be_to_bytes, locals_kept_mem]
QED

Theorem body_prevhash_sim_mem[local]:
  !ctx func cenv cx ty es.
    expr_sim_mem ctx func cenv cx ty
      (Builtin (env_item_type PrevHash) (Env PrevHash) []) es
Proof
  rpt gen_tac >> irule expr_sim_mem_word_values >> reverse conj_tac
  >- simp[expr_type_def, env_item_type_def, is_word_type_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all body_prevhash_mem_prefix >> strip_tac >>
  qexistsl_tac [`[]`, `v`, `es`, `t`] >> simp[]
QED

Theorem body_prevhash_vv_sim_mem[local]:
  !ctx func cenv cx ty es.
    expr_vv_sim_mem ctx func cenv cx ty
      (Builtin (env_item_type PrevHash) (Env PrevHash) []) es
Proof
  rpt gen_tac >>
  `is_word_type (expr_type (Builtin (env_item_type PrevHash) (Env PrevHash) []))` by
    simp[expr_type_def, env_item_type_def, is_word_type_def] >>
  drule_then irule body_expr_vv_sim_mem_stack_word >>
  conj_tac
  >- (gen_tac >> simp[compile_expr_def] >>
      Cases_on `compile_env_var PrevHash sa` >> simp[as_stack_val_def]) >>
  conj_tac >- metis_tac[eval_expr_builtin_value] >>
  irule body_prevhash_sim_mem
QED

Theorem body_prevhash_mem_case:
  !cx ann args. body_expr_mem_ok cx (Builtin ann (Env PrevHash) args)
Proof
  rpt gen_tac >> pure_rewrite_tac[body_expr_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `args = [] /\ ann = env_item_type PrevHash` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  gvs[] >> metis_tac[body_prevhash_sim_mem, body_prevhash_vv_sim_mem]
QED
