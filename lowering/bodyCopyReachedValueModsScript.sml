(* A value-only copy reads from the very endpoint selected by the value
   child. The physical type need not be the source annotation's type. *)
Theory bodyCopyReachedValueMods
Ancestors
  bodyLocalCopyPhysicalRhsMods bodyCopyReadPhysicalTypeMods
  bodyFullPostsMods bodyInvSplit vyperStorageFootprint vyperInterpreter
  finite_map compileEnv exprLowering context exprSimMemDefs fragGasOriginPtr
  exprSimHypsDefs bodyPtrDefs words gasContext valueTypingMemoryProps

Theorem local_copy_reached_value_mods:
  compile_expr ce (expr_type e) e a = (vv,sm) /\
  unwrap_value ce vv sm = (op,b) /\ local_ptrs_reserved ce a /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks entry.vs_gas_readings ++ tail) =
    (INL v,ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (entry,Gi,ti) marks (OK s,G,tn) /\
    expr_post_mods H ctx func ce cx e es a b entry ee v op s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  expr_store_bound cx (post_value_type ce e) v op s /\
  ptr_val_ok cx (post_value_type ce e) v op G tn s /\
  (~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G s) /\
  ghost_kept_at lo ce es a Gi ti entry G tn /\
  s.vs_current_bb = b.cs_current_bb /\ s.vs_inst_idx = LENGTH b.cs_current_insts /\
  alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  entry.vs_alloca_next <= s.vs_alloca_next /\
  expr_body_pre_mods mods ce cx env e es /\ ~is_word_type (expr_type e) ==>
  ?pt rt.
    evaluate_type (get_tenv cx) (post_value_type ce e) = SOME pt /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
    value_has_type pt v /\ value_has_type rt v /\
    ~is_word_type (post_value_type ce e) /\
    (post_value_type ce e = lowered_value_type ce e \/
     is_bytestring_type (post_value_type ce e) /\
     is_bytestring_type (lowered_value_type ce e)) /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt /\ val_wf rt v /\
    lower_value compile_expr ce (expr_type e) e a = (op,b) /\
    (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks entry.vs_gas_readings ++ tail) =
      (INL v,ee with gas_obs := tail)) /\
    bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks entry.vs_gas_readings) =
      (INL v,ee with gas_obs := []) /\
    ~s.vs_halted /\ s.vs_current_bb = b.cs_current_bb /\
    s.vs_inst_idx = LENGTH b.cs_current_insts /\
    alloca_history func s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    entry.vs_alloca_next <= s.vs_alloca_next /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (entry,Gi,ti) marks (OK s,G,tn) /\
      expr_post_mods H ctx func ce cx e es a b entry ee v op s /\
      ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
    expr_store_bound cx (post_value_type ce e) v op s /\
    ptr_val_ok cx (post_value_type ce e) v op G tn s /\ ptr_buf_ok ce e op G s /\
    ghost_kept_at lo ce es a Gi ti entry G tn /\
    (!dst cap dw aid chunk. not_fresh_at a dst /\ lookup_var dst entry = SOME dw /\
      ptr_covers Gi ti dst entry cap /\ FLOOKUP entry.vs_allocas aid = SOME chunk ==>
      lookup_var dst s = SOME dw /\ ptr_covers G tn dst s cap /\
      FLOOKUP s.vs_allocas aid = SOME chunk) /\
    ?w. eval_operand op s = SOME w /\ op_taint tn op = {} /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
             val_in_memory rt v (w2n w) mem) /\
      (val_store_size rt v = 0 \/ w2n w + val_store_size rt v <= s.vs_alloca_next) /\
      (0 < type_memory_size rt ==>
        ?src. op = Var src /\ not_fresh_at b src /\ ptr_covers G tn src s (type_memory_size rt))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks entry.vs_gas_readings) =
     (INL v,ee with gas_obs := [])` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac[listTheory.APPEND_NIL] >> disch_then ACCEPT_TAC) >>
  drule_all_then
    (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac (qx_choosel_then [`pt`,`rt`] strip_assume_tac)))
    copy_read_physical_type_gas_obs_mods >>
  `ptr_buf_ok ce e op G s` by first_assum (drule_then ACCEPT_TAC) >>
  drule_all_then strip_assume_tac local_copy_physical_rhs_mods >>
  qexistsl [`pt`,`rt`] >> asm_rewrite_tac[] >>
  qexists_tac `w` >> asm_rewrite_tac[]
QED
