(* BLOBHASH suffix at the allocation-aware operand frame. *)
Theory bodyPtrEnvBuiltinsBlobHashRun
Ancestors
  bodyPtrEnvBuiltinsBlobHashFacts bodyPtrEnvBuiltinsOperandCompose
  bodyPtrDefs exprLoweringProps exprLowering compileEnv stmtFragPtr
  venomState venomInst vyperInterpreter vyperValue vyperContext
  vyperTypeSystem list

Theorem operand_blobhash_suffix_run:
  lower_value compile_expr cenv ty e sa = (arg,sm) /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) /\
  expr_post ctx fn cenv cx e es sa sm s0 ee v arg s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  local_ptrs_rel fn cenv es.scopes s0 /\ local_ptrs_reserved cenv sa /\
  emit_op BLOBHASH [arg] sm = (op,sb) /\ fn_has_code sm sb fn /\
  0 <= i /\ i < 2 ** 256 /\
  eval_operand arg s = SOME (typed_val_to_w256 (BaseTV (UintT 256)) (IntV i)) /\
  op_taint tn arg = {} /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx ee G tn s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx fn cenv cx ee s /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    ghost_inv d cenv cx ee G' tn' t /\
    ghost_kept cenv es sa G0 tn0 s0 G' tn' /\
    op_taint tn' op = {} /\ op_prov G' op = NONE /\
    eval_operand op t = SOME (typed_val_to_w256 (BaseTV (BytesT (Fixed 32)))
      (evaluate_blob_hash cx.txn (Num i))) /\
    stmt_state_rel ctx fn cenv cx ee t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas
Proof
  strip_tac >>
  drule_all blobhash_read_typed_step >>
  disch_then (qspecl_then [`STRING #"%" (toString sm.cs_next_var)`,
    `sm.cs_next_id`] assume_tac) >>
  drule_at (Pat `emit_op _ _ _ = _`) operand_scalar_suffix_run >>
  simp[MEM] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G''`, `tn''`, `t`] >> simp[]
QED
