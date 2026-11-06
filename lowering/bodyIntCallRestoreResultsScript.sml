Theory bodyIntCallRestoreResults
Ancestors
  intCallResult exprSimProps valueTypingMemoryProps exprSimHash
  loweringPosts compileEnv vyperState vyperValue vyperTyping
  emitHelper emitHelperProps venomState

(* Located results need ownership even when the type is a machine word. *)
Theorem allocated_value_vv_at:
  evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
  eval_operand p.ptr_operand s = SOME w /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  b <= w2n w /\ w2n w + val_footprint tv v <= b + sz /\
  (!n lb lsz. local_region ce es.scopes s n lb lsz ==>
    b + sz <= lb \/ lb + lsz <= b) ==>
  vv_at ce cx ty sa sb es (Value v) (LocatedValue ty p) s
Proof
  simp[vv_at_def, read_result_def, return_def] >> rpt strip_tac >>
  gvs[] >> disj1_tac >>
  qexistsl_tac [`aid`,`b`,`sz`] >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem allocated_buffer_vv_post:
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\
  stmt_state_rel ctx func ce cx es' s /\
  wb_frame ce es sa s0 s /\
  eval_operand buf.buf_operand s = SOME w /\
  val_in_memory tv v (w2n w) s.vs_memory /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  b <= w2n w /\ w2n w + val_footprint tv v <= b + sz /\
  (!n lb lsz. local_region ce es'.scopes s n lb lsz ==>
    b + sz <= lb \/ lb + lsz <= b) ==>
  vv_post ctx func ce cx e es sa sb s0 es' (Value v)
    (LocatedValue (expr_type e) (base_ptr buf)) s
Proof
  strip_tac >> irule vv_post_frame_intro >> simp[] >> conj_tac
  >- (irule buffer_vv_holds >> goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[]) >>
  irule allocated_value_vv_at >>
  qexistsl_tac [`aid`,`b`,`sz`,`tv`,`w`] >>
  simp[contextTheory.base_ptr_def] >> conj_tac
  >- first_assum ACCEPT_TAC >>
  irule value_has_type_memory_wf >> simp[]
QED

(* A void INVOKE has no result-store suffix: its successor is the call's
   endpoint.  This consumer uses the restored caller frame. *)
Theorem void_invoke_return_post:
  emit_void INVOKE ops si = ((),sb) /\
  expr_type e = NoneT /\ value_has_type NoneTV v /\
  stmt_state_rel ctx func ce cx es' s /\ wb_frame ce es sa s0 s /\
  s.vs_current_bb = si.cs_current_bb /\
  s.vs_inst_idx = SUC (LENGTH si.cs_current_insts) ==>
  vv_post ctx func ce cx e es sa sb s0 es' (Value v)
    (StackValue NoneT (Lit 0w)) s /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `v = NoneV` by fs[value_has_type_def] >> gvs[] >>
  reverse conj_tac
  >- (drule emitted_insts_emit_void >> strip_tac >>
      gvs[emit_void_def, comp_bind_def, fresh_id_def, emit_def]) >>
  irule vv_post_frame_intro >>
  simp[vv_holds_def, vv_at_def, read_result_def, return_def,
    expr_val_rel_def, expr_val_at_def, eval_operand_def,
    evaluate_type_def, is_word_type_def,
    valueEncodingTheory.val_in_memory_def,
    valueEncodingTheory.val_wf_def, val_footprint_def,
    valueEncodingTheory.type_memory_size_def]
QED
