(* Fixed-byte source encoding and scratch continuation interface. *)
Theory exprSimSliceFixedAdapter
Ancestors
  exprSimSliceMemory exprSimSliceCaptureControl exprSimSliceOrdinaryFrame
  exprSimSource exprSimHash vyperTypeExprResult vyperTypeExprSoundness vyperTypeInvariants vyperTyping

Theorem slice_source_fixed_view:
  expr_body_pre cenv cx env src es /\
  bind (eval_expr cx src) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
  expr_post ctx func cenv cx src es sa sm s0 ee v src_op t /\
  expr_type src = BaseT (BytesT (Fixed m)) /\ m <= 32 ==>
  expr_sim_inv cenv cx env ee /\
  ?bs w. v = BytesV bs /\ LENGTH bs = m /\
    eval_operand src_op t = SOME w /\
    TAKE (LENGTH bs) (word_to_bytes_be w) = bs
Proof
  strip_tac >>
  `expr_body_pre cenv cx env src (es with gas_obs := gs)` by simp[] >>
  `expr_sim_inv cenv cx env ee /\ expr_result_typed env src (Value v)` by
    metis_tac[exprSimSourceTheory.expr_body_pre_eval] >>
  `env.type_defs = get_tenv cx` by
    fs[exprSimHypsDefsTheory.expr_body_pre_def,
       exprSimHypsDefsTheory.expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  fs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def,
     vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >> gvs[vyperValueTheory.evaluate_type_def,
    vyperTypingTheory.value_has_type_def, AllCaseEqs()] >>
  drule hash_fixed_post_view >> simp[vyperTypingTheory.value_has_type_def]
QED

Theorem slice_fixed_scratch_code:
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; val_op] sm = ((),sb) ==>
  sm.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++
    (emitted_insts sa sm ++ emitted_insts sm sb) /\
  emitted_insts sa sm =
    [mk_inst sa.cs_next_id ALLOCA [Lit 32w]
      [STRING #"%" (toString sa.cs_next_var)]] /\
  EVERY (\i. i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS)
    (emitted_insts sa sm ++ emitted_insts sm sb)
Proof
  simp[contextTheory.compile_alloc_buffer_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  drule emitHelperPropsTheory.emitted_insts_emit_void >> strip_tac >>
  simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def,
       listTheory.APPEND_ASSOC] >>
  fs[emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
     emitHelperTheory.emit_inst_def, compileEnvTheory.comp_bind_def,
     compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.comp_return_def,
     compileEnvTheory.fresh_var_def, compileEnvTheory.fresh_id_def,
     compileEnvTheory.emit_def] >> gvs[]
QED

Theorem slice_fixed_scratch_embedding:
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; val_op] sm = ((),sb) /\
  fn_has_code sa sb func /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
  ?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sm ++ emitted_insts sm sb)
      (DROP s.vs_inst_idx bb.bb_instructions)
Proof
  strip_tac >> drule_all slice_fixed_scratch_code >> strip_tac >>
  fs[fragExecTheory.fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
  conj_tac
  >- (irule fragExecTheory.lookup_block_fn_insts >>
      goal_assum (drule_at Any) >> simp[]) >>
  simp[rich_listTheory.DROP_APPEND1, rich_listTheory.IS_PREFIX_APPEND,
       listTheory.APPEND_ASSOC]
QED

Theorem slice_fixed_scratch_entry:
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; val_op] sm = ((),sb) /\
  eval_operand val_op s = SOME w /\
  (!x. val_op = Var x ==> not_fresh_at sa x) /\ (!l. val_op <> Label l) /\
  LENGTH bs <= 32 /\ TAKE (LENGTH bs) (word_to_bytes_be w) = bs /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u p. run_inst_seq (emitted_insts sa sm ++ emitted_insts sm sb) s = OK u /\
    w2n p + LENGTH bs < dimword (:256) /\
    let u' = u with vs_inst_idx :=
      s.vs_inst_idx + LENGTH (emitted_insts sa sm ++ emitted_insts sm sb) in
      u'.vs_inst_idx = LENGTH sb.cs_current_insts /\
      u'.vs_current_bb = sb.cs_current_bb /\
      stmt_state_rel ctx func cenv cx es u' /\
      eval_operand buf.buf_operand u' = SOME p /\
      eval_operand (Lit (n2w (LENGTH bs))) u' = SOME (n2w (LENGTH bs)) /\
      mem_bytes_at (w2n p) (LENGTH bs) u'.vs_memory = bs /\
      (?x. buf.buf_operand = Var x /\ not_fresh_at sb x) /\
      (!sd se e1 e2 es1 es2 v1 v2 op1 op2 r1 r2.
        local_ptrs_reserved cenv sb /\ sb.cs_next_id <= sd.cs_next_id /\
        MAP FDOM es.scopes = MAP FDOM es1.scopes /\
        expr_post ctx func cenv cx e1 es sb sd u' es1 v1 op1 r1 /\
        expr_post ctx func cenv cx e2 es1 sd se r1 es2 v2 op2 r2 ==>
        mem_bytes_at (w2n p) (LENGTH bs) r2.vs_memory = bs) /\
      (!tops source Q R.
        gas_outcome F tops (ctx,func) source (es,u') Q R ==>
        gas_outcome F tops (ctx,func) source (es,s) Q R)
Proof
  strip_tac >> drule_all slice_fixed_scratch_embedding >> strip_tac >>
  drule_all slice_fixed_scratch_code >> strip_tac >>
  drule_all slice_fixed_scratch_alloc >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sm ++ emitted_insts sm sb)` by
    fs[listTheory.EVERY_MEM] >>
  `t.vs_current_bb = s.vs_current_bb` by
    (drule_all (cj 1 fragExecTheory.exec_block_run_inst_seq) >> simp[]) >>
  `w2n p + LENGTH bs < dimword (:256)` by decide_tac >>
  qexistsl_tac [`t`, `p`] >>
  simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx,
       instIdxIndepTheory.eval_op_inst_idx, venomStateTheory.eval_operand_def] >>
  conj_tac
  >- (rpt strip_tac >>
      fs[slice_capture_post_initial_index] >>
      qpat_x_assum `stmt_state_rel ctx func cenv cx es s` kall_tac >>
      `sa.cs_next_id < sd.cs_next_id` by decide_tac >>
      `!name off sz. local_region cenv es.scopes t name off sz ==>
        w2n p + 32 <= off \/ off + sz <= w2n p` by
        metis_tac[loweringStateRelDefsTheory.regions_disjoint_def,
                  arithmeticTheory.ADD_COMM] >>
      drule_all slice_fixed_payload_two_operands >> simp[]) >>
  rpt strip_tac >> irule exprSimSliceComposeTheory.slice_capture_outcome_prefix >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`emitted_insts sa sm ++ emitted_insts sm sb`, `t`] >>
  simp[] >>
  pure_once_rewrite_tac[arithmeticTheory.ADD_COMM] >> asm_rewrite_tac[] >>
  qpat_x_assum `isPREFIX _ _` mp_tac >> simp[]
QED

Theorem slice_source_fixed_capture_entry:
  expr_body_pre cenv cx env src es /\
  bind (eval_expr cx src) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
  expr_post ctx func cenv cx src es sa sm s0 ee v src_op t /\
  expr_type src = BaseT (BytesT (Fixed m)) /\ m <= 32 /\
  lower_value compile_expr cenv (BaseT (BytesT (Fixed m))) src sa = (src_op,sm) /\
  compile_alloc_buffer 32 sm = (buf,sb) /\
  emit_void MSTORE [buf.buf_operand; src_op] sb = ((),sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  fn_inst_ids_distinct func /\ fn_has_code sm sc func /\ ~t.vs_halted /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?bs u p. v = BytesV bs /\ LENGTH bs = m /\
    expr_sim_inv cenv cx env ee /\
    run_inst_seq (emitted_insts sm sb ++ emitted_insts sb sc) t = OK u /\
    w2n p + LENGTH bs < dimword (:256) /\
    let u' = u with vs_inst_idx :=
      t.vs_inst_idx + LENGTH (emitted_insts sm sb ++ emitted_insts sb sc) in
      u'.vs_inst_idx = LENGTH sc.cs_current_insts /\
      u'.vs_current_bb = sc.cs_current_bb /\
      stmt_state_rel ctx func cenv cx ee u' /\
      eval_operand buf.buf_operand u' = SOME p /\
      eval_operand (Lit (n2w (LENGTH bs))) u' = SOME (n2w (LENGTH bs)) /\
      mem_bytes_at (w2n p) (LENGTH bs) u'.vs_memory = bs /\
      (?x. buf.buf_operand = Var x /\ not_fresh_at sc x) /\
      (!sd se e1 e2 ee1 ee2 v1 v2 op1 op2 r1 r2.
        local_ptrs_reserved cenv sc /\ sc.cs_next_id <= sd.cs_next_id /\
        MAP FDOM ee.scopes = MAP FDOM ee1.scopes /\
        expr_post ctx func cenv cx e1 ee sc sd u' ee1 v1 op1 r1 /\
        expr_post ctx func cenv cx e2 ee1 sd se r1 ee2 v2 op2 r2 ==>
        mem_bytes_at (w2n p) (LENGTH bs) r2.vs_memory = bs) /\
      (!tops source Q R.
        gas_outcome F tops (ctx,func) source (ee,u') Q R ==>
        gas_outcome F tops (ctx,func) source (ee,t) Q R)
Proof
  strip_tac >> drule_all slice_source_fixed_view >> strip_tac >>
  `!z. src_op = Var z ==> not_fresh_at sm z` by
    metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `!l. src_op <> Label l` by
    (drule_all exprSimSliceCaptureTheory.slice_source_operand_not_label >> simp[]) >>
  `stmt_state_rel ctx func cenv cx ee t` by
    fs[loweringPostsTheory.expr_post_def] >>
  `LENGTH bs <= 32` by decide_tac >>
  drule_all slice_fixed_scratch_entry >> strip_tac >>
  qexistsl_tac [`bs`, `u`, `p`] >> gvs[] >>
  first_assum MATCH_ACCEPT_TAC
QED
