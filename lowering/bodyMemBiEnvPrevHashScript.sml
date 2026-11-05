(* Previous-block hash: lift the existing straight-line execution to memory. *)
Theory bodyMemBiEnvPrevHash
Ancestors
  builtinProps exprSimProps exprSimSource exprLoweringProps exprLowering
  fragGasSeqMem fragExecMem allocaHistoryFragment instMemFrontier
  loweringSlice emitHelperProps compileEnv venomInst venomState
  venomExecSemantics memSafeRun list rich_list finite_map
  varsExt fragExec contextCodegenRel codegenRel

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
