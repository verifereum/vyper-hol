(* Control normalization for the target-only dynamic source capture. *)
Theory exprSimSliceCaptureControl
Ancestors
  exprSimSliceCapture exprSimSliceMemory exprSimSliceCompose instIdxIndep

Theorem slice_bytestring_src_zero_code:
  compile_bytestring_src src sm = ((len,data),sc) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\
             ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS)
    (emitted_insts sm sc)
Proof
  strip_tac >> drule slice_bytestring_src_shape >> strip_tac >>
  simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]
QED

Theorem slice_bytestring_capture_outcome_prefix:
  compile_bytestring_src src sm = ((len,data),sc) /\
  ~t.vs_halted /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sc) (DROP t.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq (emitted_insts sm sc) t = OK u /\
  gas_outcome F tops (ctx,func) source
    (ee,u with vs_inst_idx := t.vs_inst_idx + LENGTH (emitted_insts sm sc)) Q R ==>
  gas_outcome F tops (ctx,func) source (ee,t) Q R
Proof
  strip_tac >> irule slice_capture_outcome_prefix >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`emitted_insts sm sc`, `u`] >>
  pure_once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  asm_rewrite_tac[] >> metis_tac[slice_bytestring_src_zero_code]
QED

Theorem slice_capture_post_initial_index:
  expr_post ctx func ce cx e es sa sb (s0 with vs_inst_idx := k) ee v op s <=>
  expr_post ctx func ce cx e es sa sb s0 ee v op s
Proof
  simp[loweringPostsTheory.expr_post_def,
       loweringStateRelDefsTheory.local_region_def, venomStateTheory.lookup_var_def,
       loweringPostsTheory.locals_kept_def]
QED

Theorem slice_capture_value_index:
  expr_val_at ce cx ty sa sb ee v op (u with vs_inst_idx := k) <=>
  expr_val_at ce cx ty sa sb ee v op u
Proof
  simp[loweringPostsTheory.expr_val_at_def, instIdxIndepTheory.eval_op_inst_idx,
       loweringStateRelDefsTheory.local_region_def, venomStateTheory.lookup_var_def]
QED

Theorem slice_bytestring_src_control:
  compile_bytestring_src src sm = ((len,data),sc) ==>
  sc.cs_current_bb = sm.cs_current_bb /\
  sc.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sc
Proof
  simp[builtinBytesTheory.compile_bytestring_src_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def,
       emitHelperTheory.emit_op_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def] >>
  strip_tac >> gvs[] >>
  simp[exprLoweringPropsTheory.emitted_insts_def, rich_listTheory.DROP_APPEND1]
QED

Theorem slice_capture_index_frame:
  compile_bytestring_src src sm = ((len,data),sc) /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  t.vs_current_bb = sm.cs_current_bb /\
  u.vs_current_bb = t.vs_current_bb /\
  stmt_state_rel ctx func ce cx ee u /\
  eval_operand len u = SOME lw /\ eval_operand data u = SOME dw /\
  expr_val_at ce cx ty sa sc ee v src u /\
  (!e sd ee' v' op' r.
    expr_post ctx func ce cx e ee sc sd u ee' v' op' r ==>
    mem_bytes_at addr nbytes r.vs_memory = bs) ==>
  let u' = u with vs_inst_idx := t.vs_inst_idx + LENGTH (emitted_insts sm sc) in
    u'.vs_inst_idx = LENGTH sc.cs_current_insts /\
    u'.vs_current_bb = sc.cs_current_bb /\
    stmt_state_rel ctx func ce cx ee u' /\
    eval_operand len u' = SOME lw /\ eval_operand data u' = SOME dw /\
    expr_val_at ce cx ty sa sc ee v src u' /\
    (!e sd ee' v' op' r.
      expr_post ctx func ce cx e ee sc sd u' ee' v' op' r ==>
      mem_bytes_at addr nbytes r.vs_memory = bs)
Proof
  strip_tac >> drule slice_bytestring_src_control >> strip_tac >>
  simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx,
       instIdxIndepTheory.eval_op_inst_idx, slice_capture_value_index,
       slice_capture_post_initial_index] >>
  qpat_x_assum `sc.cs_current_insts = _` (fn th => rewrite_tac[th]) >>
  simp[] >> metis_tac[]
QED
