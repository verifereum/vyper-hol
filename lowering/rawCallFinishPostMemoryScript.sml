(* Typed value and capacity postconditions for raw-call finish endpoints. *)
Theory rawCallFinishPostMemory
Ancestors
  exprSimRawCall bodyMemAggregateBounds exprSimMemDefs exprSimVVFrame
  valueEncoding exprSimDefs exprSimProps loweringPosts exprLowering
  vyperInterpreter vyperState compileEnv exprLoweringProps venomState context words finite_map

Theorem raw_call_zero_finish_post_mem:
  expr_type e = (if rev then NoneT else BaseT BoolT) /\
  lowered_value_type ce e = expr_type e /\
  stmt_state_rel ctx func ce cx es' u /\ wb_frame ce es sa s0 u /\
  (if rev then result = Lit 0w
   else expr_val_rel cx (BaseT BoolT) (BoolV success) result u) ==>
  vv_post ctx func ce cx e es sa sb s0 es'
    (Value (if rev then NoneV else BoolV success)) (StackValue ann result) u /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) es'
    (Value (if rev then NoneV else BoolV success)) (StackValue ann result) u
Proof
  strip_tac >>
  qpat_assum `lowered_value_type _ _ = _`
    (assume_tac o MATCH_MP post_value_type_lowered) >>
  Cases_on `rev` >> gvs[]
  >- (conj_tac >- (irule raw_call_none_post >> simp[]) >>
      simp[vv_store_bound_def, is_word_type_def, expr_store_bound_def,
        read_result_def, return_def, vyperValueTheory.evaluate_type_def,
        type_memory_size_def, val_store_size_def]) >>
  conj_tac >- (irule raw_call_bool_post >> simp[]) >>
  irule vv_store_bound_stack_word >> simp[is_word_type_def]
QED

Theorem raw_call_bytes_finish_post_mem:
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  lowered_value_type ce e = expr_type e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic cap))) /\
  cap <= rounded /\ ((cap + 31) DIV 32) * 32 <= rounded /\
  b + (rounded + 32) < dimword (:256) /\
  raw_call_finish_view u =
    raw_call_finish_view (mstore b (n2w (MIN (LENGTH bytes) cap)) t) /\
  mem_bytes_at (b+32) (LENGTH (TAKE cap bytes)) t.vs_memory = TAKE cap bytes /\
  stmt_state_rel ctx func ce cx es' u /\
  eval_operand result u = SOME (n2w b) /\
  FLOOKUP t.vs_allocas aid = SOME (b,rounded+32) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  (!name lb lsz. local_region ce es'.scopes u name lb lsz ==>
    b + (rounded+32) <= lb \/ lb + lsz <= b) /\
  wb_frame ce es sa s0 u ==>
  vv_post ctx func ce cx e es sa sb s0 es' (Value (BytesV (TAKE cap bytes)))
    (LocatedValue (expr_type e) (mk_ptr result LocMemory)) u /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) es'
    (Value (BytesV (TAKE cap bytes)))
    (LocatedValue (expr_type e) (mk_ptr result LocMemory)) u
Proof
  strip_tac >>
  qpat_assum `lowered_value_type _ _ = _`
    (assume_tac o MATCH_MP post_value_type_lowered) >>
  `vv_post ctx func ce cx e es sa sb s0 es' (Value (BytesV (TAKE cap bytes)))
    (LocatedValue (expr_type e) (mk_ptr result LocMemory)) u` by
    (irule raw_call_bytes_post >> simp[] >>
     qexistsl_tac [`aid`,`b`,`rounded`,`t`] >> simp[] >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule aggregate_allocated_result_store_bound_mem >>
  conj_tac >- fs[stmt_state_rel_def] >>
  conj_tac
  >- (qexistsl_tac [`aid`,`b`,`BaseTV (BytesT (Dynamic cap))`,`rounded+32`] >>
      simp[mk_ptr_def, type_memory_size_def, vfmConstantsTheory.word_size_def] >>
      qpat_x_assum `raw_call_finish_view _ = _` mp_tac >>
      simp[raw_call_finish_view_def, venom_state_component_equality, mstore_def]) >>
  simp[] >> metis_tac[]
QED
