Theory bodyIntCallRestoreResults
Ancestors
  intCallResult exprSimProps valueTypingMemoryProps exprSimHash
  loweringPosts compileEnv loweringStateRelDefs vyperState vyperValue vyperTyping
  emitHelper emitHelperProps venomState venomExecSemantics

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
  expr_has_effect e /\
  post_value_type ce e = expr_type e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\
  stmt_state_rel ctx func ce cx es' s /\
  wb_frame ce es es' sa s0 s /\
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
  strip_tac >> irule vv_post_frame_intro >> simp[] >> rpt conj_tac
  >~ [`vv_holds`] >- (irule buffer_vv_holds >> goal_assum (drule_at Any) >> simp[] >>
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
  expr_has_effect e /\
  emit_void INVOKE ops si = ((),sb) /\
  post_value_type ce e = expr_type e /\
  expr_type e = NoneT /\ value_has_type NoneTV v /\
  stmt_state_rel ctx func ce cx es' s /\ wb_frame ce es es' sa s0 s /\
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
    valueEncodingDefsTheory.val_in_memory_def,
    valueEncodingDefsTheory.val_wf_def, val_footprint_def,
    valueEncodingTheory.type_memory_size_def]
QED

(* Memory returns keep the caller's buffer pointer and allocation map.
   The callee has already filled the buffer; no caller stores follow. *)
Theorem memory_invoke_return_post:
  expr_has_effect e /\
  emit_void INVOKE ops si = ((),sb) /\
  post_value_type ce e = expr_type e /\
  t.vs_current_bb = si.cs_current_bb /\
  t.vs_inst_idx = LENGTH si.cs_current_insts /\
  s = (merge_callee_state t cs with vs_inst_idx := SUC t.vs_inst_idx) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ type_memory_size tv <= buf.buf_size /\
  eval_operand buf.buf_operand t = SOME w /\
  FLOOKUP t.vs_allocas aid = SOME (w2n w,buf.buf_size) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  val_in_memory tv v (w2n w) cs.vs_memory /\
  (!n lb lsz. local_region ce es'.scopes t n lb lsz ==>
     w2n w + buf.buf_size <= lb \/ lb + lsz <= w2n w) /\
  stmt_state_rel ctx func ce cx es' s /\ wb_frame ce es es' sa s0 s ==>
  vv_post ctx func ce cx e es sa sb s0 es' (Value v)
    (LocatedValue (expr_type e) (base_ptr buf)) s /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> reverse conj_tac
  >- (drule emitted_insts_emit_void >> strip_tac >>
      gvs[emit_void_def, comp_bind_def, fresh_id_def, emit_def,
          merge_callee_state_def]) >>
  irule allocated_buffer_vv_post >> simp[] >>
  qexistsl_tac [`aid`,`w2n w`,`buf.buf_size`,`w`] >> simp[] >>
  `val_wf tv v` by (irule value_has_type_memory_wf >> simp[]) >>
  `val_footprint tv v <= buf.buf_size` by
    (drule val_footprint_le >> decide_tac) >>
  simp[merge_callee_state_def] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!n lb lsz. local_region _ _ _ _ _ _ ==> _`
        (qspecl_then [`n`,`lb`,`lsz`] mp_tac) >>
      (impl_tac >-
        (fs[local_region_def, lookup_var_def] >>
         goal_assum (drule_at Any) >> simp[])) >> decide_tac) >>
  Cases_on `buf.buf_operand` >>
  gvs[merge_callee_state_def, eval_operand_def, lookup_var_def]
QED
