Theory aggregateCountedRenamedStore
Ancestors
  aggregateCountedStoreShapeGeneral exprSimAggregateChildren
  exprSimAbiGasBridge context compileEnv loweringStateRelDefs vyperAST venomExecSemantics
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
       local_region_def, locals_kept_def, popped_kept_def]
QED

Theorem aggregate_typed_sarray_start_swap_endpoint:
  compile_copy_sarray_typed ce (Var dst) (BaseT (UintT 256))
    (Var src) (TupleT []) n su = ((),sb) ==>
  (start_swap su L ids sb).cs_current_bb = sb.cs_current_bb /\
  (start_swap su L ids sb).cs_current_insts = sb.cs_current_insts
Proof
  strip_tac >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, type_memory_bytes_def,
       is_word_type_def] >>
  simp[Once compile_store_memory_typed_def, is_word_type_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_label_def, fresh_var_def, fresh_id_def,
       emit_inst_def, emit_op_def, emit_void_def, emit_def, new_block_def] >>
  strip_tac >> gvs[start_swap_def, emitted_blocks_def]
QED

Theorem aggregate_typed_sarray_renamed_body_run:
  compile_copy_sarray_typed ce (Var x) (BaseT (UintT 256))
    (Var src) (TupleT []) n su = ((),sb) /\
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed n) /\
  post_value_type ce e = ArrayT (TupleT []) (Fixed m) /\
  expr_body_pre ce cx env e es /\
  (do res <- eval_expr cx e; read_result cx res od) es = (INL v,es') /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    su r es' v (Var src) s /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  sm.cs_next_var <= su.cs_next_var /\ not_fresh_at su src /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  stmt_state_rel ctx func ce cx es' r /\
  FLOOKUP r.vs_allocas did = SOME (b,k) /\ did < sa.cs_next_id /\
  b <= w2n w /\ w2n w + type_memory_size tv <= b+k /\
  w2n w + type_memory_size tv < dimword (:256) /\
  (!name a len. local_region ce es'.scopes r name a len ==>
    a+len <= w2n w \/ w2n w + type_memory_size tv <= a) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) /\
  ~s.vs_halted /\ s.vs_inst_idx = LENGTH su.cs_current_insts ==>
  !L ids fn'. LENGTH ids = LENGTH su.cs_current_insts /\
    fn_has_code (start_relabel L ids su) (start_swap su L ids sb) fn' ==>
  ?q. val_in_memory tv v (w2n w) q.vs_memory /\
    stmt_state_rel ctx func ce cx es' q /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==> lookup_var z q = SOME a) /\
    (!aid a. FLOOKUP r.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
    (!aid off sz a len.
      FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!name b k. local_region ce es'.scopes r name b k ==>
        off+sz <= b \/ b+k <= off) /\
      off <= a /\ a+len <= off+sz /\
      (a+len <= w2n w \/ w2n w+type_memory_size tv <= a) ==>
      mem_bytes_at a len q.vs_memory = mem_bytes_at a len r.vs_memory) /\
    locals_kept ce es' es' r q /\
    (!fuel rr. run_from fuel ctx fn' q = rr /\ (!err. rr <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn' (s with vs_current_bb := L) = rr)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all aggregate_typed_sarray_start_relabel >> strip_tac >>
  drule aggregate_typed_sarray_start_swap_endpoint >>
  disch_then (qspecl_then [`ids`,`L`] strip_assume_tac) >>
  `compile_store_memory_typed ce (Var x) (expr_type e) (Var src)
     (post_value_type ce e) (start_relabel L ids su) =
     ((),start_swap su L ids sb)` by
    (simp[Once compile_store_memory_typed_def, is_word_type_def,
          is_bytestring_type_def] >> first_x_assum irule) >>
  drule aggregate_store_body_typed_run >>
  simp[aggregate_expr_post_start_relabel] >>
  disch_then irule >>
  simp[aggregate_expr_post_start_relabel, start_relabel_def,
       local_ptrs_reserved_def, not_fresh_at_def, is_word_type_def,
       is_bytestring_type_def] >>
  fs[local_ptrs_reserved_def, not_fresh_at_def] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED
