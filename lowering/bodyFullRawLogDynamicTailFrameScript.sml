(* RawLog's dynamic tail frame, independent of instruction execution. *)
Theory bodyFullRawLogDynamicTailFrame
Ancestors
  bodySimFull exprSimMemDefs loweringPosts bodyPtrDefs exprLoweringProps
  loweringShapeDefs venomState compileEnv vyperEvent finite_map words list arithmetic

Theorem raw_log_dynamic_tail_post_frame:
  expr_post H ctx func cenv cx data es sa sm s0 ee (BytesV bs) data_op s /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  alloca_history func s /\ alloca_history func u /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  sa.cs_next_var <= sm.cs_next_var /\
  expr_type (Call ann RawLog es_call dflt) = NoneT /\
  post_value_type cenv (Call ann RawLog es_call dflt) = NoneT /\
  expr_has_effect (Call ann RawLog es_call dflt) /\
  (t with vs_vars := s.vs_vars) = s /\
  (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
  ghost_kept_at lo cenv ee sm G tn s G1 tn1 /\ tn1.t_mem = tn.t_mem /\
  (u with <|vs_logs := t.vs_logs; vs_inst_idx := t.vs_inst_idx|>) = t /\
  stmt_state_rel H ctx func cenv cx
    (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) u /\
  storage_well_formed_on cx
    (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) (FST H) /\
  ghost_inv_at D lo d cenv cx
    (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) G1 tn1 u ==>
  expr_post H ctx func cenv cx (Call ann RawLog es_call dflt) es sa sb s0
    (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) NoneV (Lit 0w) u /\
  expr_store_bound cx (expr_type (Call ann RawLog es_call dflt)) NoneV (Lit 0w) u /\
  alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
  ghost_inv_at D lo d cenv cx
    (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vals bs]) G1 tn1 u /\
  ptr_val_ok cx (post_value_type cenv (Call ann RawLog es_call dflt)) NoneV (Lit 0w) G1 tn1 u /\
  (~is_word_type (post_value_type cenv (Call ann RawLog es_call dflt)) ==>
    ptr_buf_ok cenv (Call ann RawLog es_call dflt) (Lit 0w) G1 u) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    metis_tac[not_fresh_at_mono] >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next /\
   (!x. lookup_var x u = lookup_var x t)` by
    (qpat_x_assum `(u with <|vs_logs := _; vs_inst_idx := _|>) = t` mp_tac >>
     qpat_x_assum `(t with vs_vars := _) = s` mp_tac >>
     simp[venom_state_component_equality, lookup_var_def] >> metis_tac[]) >>
  conj_tac >- suspend "post" >>
  conj_tac >- suspend "bound" >>
  conj_tac >- suspend "history" >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "value" >>
  conj_tac >- suspend "buffer" >>
  fs[ghost_kept_at_def] >> metis_tac[]
QED
Resume raw_log_dynamic_tail_post_frame[post]:
  fs[expr_post_def] >>
  simp[expr_val_rel_def, expr_val_at_def, is_word_type_def,
       eval_operand_def, valueEncodingDefsTheory.val_in_memory_def,
       val_footprint_def, valueEncodingTheory.type_memory_size_def,
       valueEncodingDefsTheory.val_wf_def] >>
  fs[locals_kept_def, popped_kept_def] >> metis_tac[]
QED
Resume raw_log_dynamic_tail_post_frame[bound]:
  simp[expr_store_bound_def, exprSimPropsTheory.val_store_size_def,
       valueEncodingTheory.type_memory_size_def]
QED
Resume raw_log_dynamic_tail_post_frame[history]:
  simp[]
QED
Resume raw_log_dynamic_tail_post_frame[value]:
  simp[ptr_val_ok_def, ptr_mem_ok_def, ptrDisciplineTheory.op_taint_def,
       valueEncodingDefsTheory.val_in_memory_def, val_footprint_def,
       valueEncodingTheory.type_memory_size_def]
QED
Resume raw_log_dynamic_tail_post_frame[buffer]:
  simp[is_word_type_def, ptr_buf_ok_def,
       exprLoweringTheory.lowered_value_type_def,
       compileEnvTheory.type_memory_bytes_def]
QED
Finalise raw_log_dynamic_tail_post_frame
