Theory aggregateCountedRenamedStore
Ancestors
  aggregateCountedStoreShapeGeneral exprSimAggregateChildren
  exprSimAbiGasBridge context compileEnv vyperAST venomExecSemantics
  emitHelper emitHelperProps list rich_list fragExec exprLoweringProps
  loweringPosts venomState venomInst venomMemDefs

Theorem aggregate_typed_sarray_start_relabel:
  !ce dst src n su sb L ids.
  compile_copy_sarray_typed ce (Var dst) (BaseT (UintT 256))
    (Var src) (TupleT []) n su = ((),sb) /\
  LENGTH ids = LENGTH su.cs_current_insts ==>
  compile_copy_sarray_typed ce (Var dst) (BaseT (UintT 256))
    (Var src) (TupleT []) n (start_relabel L ids su) =
    ((),start_swap su L ids sb)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, type_memory_bytes_def,
       is_word_type_def] >>
  simp[Once compile_store_memory_typed_def, is_word_type_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_label_def, fresh_var_def, fresh_id_def,
       emit_inst_def, emit_op_def, emit_void_def, emit_def, new_block_def] >>
  strip_tac >> gvs[] >>
  simp[start_relabel_def, start_swap_def, emitted_blocks_def] >>
  simp[Once compile_store_memory_typed_def, type_memory_bytes_def,
       is_word_type_def] >>
  simp[Once compile_store_memory_typed_def, is_word_type_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_label_def, fresh_var_def, fresh_id_def,
       emit_inst_def, emit_op_def, emit_void_def, emit_def, new_block_def] >>
  `SUC (SUC (SUC (LENGTH su.cs_blocks))) - (LENGTH su.cs_blocks + 3) = 0` by decide_tac >>
  simp[] >>
  once_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> REFL_TAC
QED

Theorem aggregate_stmt_state_rel_current_bb:
  stmt_state_rel ctx func ce cx es (s with vs_current_bb := L) <=>
  stmt_state_rel ctx func ce cx es s
Proof
  simp[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def,
       local_region_def, local_backed_def, lookup_var_def, storage_rel_def,
       transient_rel_def, immutables_rel_def, logs_rel_def, call_ctx_rel_def,
       contract_storage_def, contract_transient_def, alloca_inv_def,
       allocas_non_overlapping_def, alloca_next_valid_def, alloca_room_def,
       pending_alloca_size_def, fmp_room_def, immutable_alloca_sep_def,
       immutable_base_zero_alt, accounts_rel_def]
QED

Theorem aggregate_expr_post_start_relabel:
  expr_post ctx func ce cx e es sa (start_relabel L ids su) r es' v op
    (s with vs_current_bb := L) <=>
  expr_post ctx func ce cx e es sa su r es' v op s
Proof
  Cases_on `op` >>
  simp[expr_post_def, aggregate_stmt_state_rel_current_bb,
       expr_val_rel_def, expr_val_at_def, expr_val_own_def,
       start_relabel_def, eval_operand_def, lookup_var_def,
       local_region_def, locals_kept_def]
QED
