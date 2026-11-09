Theory bodyPtrTypeBuiltinsCastContinuation
Ancestors
  bodyPtrTypeBuiltinsCastPost bodyPtrTypeBuiltinsMemoryInterface
  bodyPtrTypeBuiltinsTransport rawCallBufferPtr exprSimConvertBytes
  exprSimExtract32Post bodyPtrDefs exprLoweringProps venomState
  loweringPosts stmtFragPtr bodyPtrTypeBuiltinsCastOutcome
  bodyPtrSignedConvertSourceFrame exprLowering

Theorem cast_convert_success_post:
  expr_post ctx fn cenv cx e es ca sa s0 ee v (Var src) s /\
  post_value_type cenv e = expr_type e /\
  is_bytestring_type (expr_type e) /\ is_bytestring_type dst /\
  ~is_word_type dst /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  evaluate_type (get_tenv cx) dst = SOME tout /\ value_has_type tv v /\
  convert_result cx (expr_type e) dst v = INL vout /\
  (t with vs_vars := s.vs_vars) = s /\
  (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s) /\
  lookup_var src s = SOME w /\ not_fresh_at sa src /\
  local_ptrs_reserved cenv sa /\
  ca.cs_next_var <= sa.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  ghost_inv d cenv cx ee H th (t with vs_inst_idx := j) /\
  ghost_kept cenv ee sa G tn s H th /\
  ptr_buf_ok cenv e (Var src) G s /\
  type_memory_bytes cenv dst <= type_memory_bytes cenv (lowered_value_type cenv e) /\
  ptr_covers H th src (t with vs_inst_idx := j) sz /\
  type_memory_size tout <= sz /\
  (!m. mem_agree_outside th.t_mem t.vs_memory m ==> val_in_memory tout vout (w2n w) m) ==>
  expr_post ctx fn cenv cx (TypeBuiltin dst Convert dst [e]) es ca sb s0
    (ee with gas_obs := []) vout (Var src) (t with vs_inst_idx := j) /\
  ghost_inv d cenv cx (ee with gas_obs := []) H th (t with vs_inst_idx := j) /\
  ptr_val_ok cx (post_value_type cenv (TypeBuiltin dst Convert dst [e]))
    vout (Var src) H th (t with vs_inst_idx := j) /\
  ptr_buf_ok cenv (TypeBuiltin dst Convert dst [e]) (Var src) H (t with vs_inst_idx := j)
Proof
  strip_tac >>
  `lookup_var src (t with vs_inst_idx := j) = SOME w` by
    (simp[lookup_var_def] >> metis_tac[lookup_var_def]) >>
  conj_tac >- (irule cast_convert_parent_post >> metis_tac[]) >>
  simp[ghost_inv_gas_obs] >> conj_tac
  >- (simp[post_value_type_not_int_call, vyperASTTheory.expr_type_def] >>
      irule ptr_val_ok_from_covers >>
      fs[] >> qexists_tac `sz` >> simp[] >>
      irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `type_memory_size tout` >>
      simp[] >> irule exprSimPropsTheory.val_store_size_le >>
      irule convert_bytestring_wf >> metis_tac[]) >>
  irule convert_outer_buffer_restrict >> simp[] >>
  irule ptr_buf_ok_ghost_kept >>
  qexistsl_tac [`G`,`ee`,`s`,`sa`,`th`,`tn`] >>
  simp[eval_operand_def, lookup_var_def]
QED

Theorem cast_convert_modern_outcome_ptr:
  compile_type_convert (Var src) (ConvBytestringCast n i) sa = (out,sb) /\
  (expr_type e = BaseT (BytesT (Dynamic i)) \/ expr_type e = BaseT (StringT i)) /\
  (dst = BaseT (BytesT (Dynamic n)) \/ dst = BaseT (StringT n)) /\
  ~is_word_type dst /\ post_value_type cenv e = expr_type e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  evaluate_type (get_tenv cx) dst = SOME tout /\ value_has_type tv v /\
  val_in_memory tv v (w2n w) s.vs_memory /\ lookup_var src s = SOME w /\
  not_fresh_at sa src /\ i < dimword(:256) /\ n < dimword(:256) /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ptr_covers G tn src s sz /\ 32 <= sz /\ type_memory_size tout <= sz /\
  (!j. w2n w <= j /\ j < w2n w + 32 ==> j NOTIN tn.t_mem) /\
  ghost_inv d cenv cx ee G tn s /\ local_ptrs_reserved cenv sa /\
  (!p z. cenv.ce_return_buf = SOME (PtrVar (Var p) z) ==> not_fresh_at sa p) /\
  (!p z. cenv.ce_return_pc = SOME (PtrVar (Var p) z) ==> not_fresh_at sa p) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n w) m) /\
  expr_post ctx fn cenv cx e es ca sa s0 ee v (Var src) s /\
  ptr_buf_ok cenv e (Var src) G s /\
  type_memory_bytes cenv dst <= type_memory_bytes cenv (lowered_value_type cenv e) /\
  ghost_kept cenv es ca G0 tn0 s0 G tn /\
  ca.cs_next_var <= sa.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts ==>
  gas_outcome_ptr D tops (ctx,fn) PG
    (\st. (convert_result cx (expr_type e) dst v,st)) (ee,s,G,tn)
    (\res fin H th u. ?vout. res = INL vout /\
      expr_post ctx fn cenv cx (TypeBuiltin dst Convert dst [e]) es ca sb s0 fin vout out u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin H th u /\
      ptr_val_ok cx (post_value_type cenv (TypeBuiltin dst Convert dst [e])) vout out H th u /\
      (~is_word_type (post_value_type cenv (TypeBuiltin dst Convert dst [e])) ==>
        ptr_buf_ok cenv (TypeBuiltin dst Convert dst [e]) out H u) /\
      ghost_kept cenv es ca G0 tn0 s0 H th)
    (\res fin gt r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `is_bytestring_type (expr_type e) /\ is_bytestring_type dst` by
    (fs[compileEnvTheory.is_bytestring_type_def] >> simp[compileEnvTheory.is_bytestring_type_def]) >>
  irule cast_convert_suffix_outcome_ptr >> simp[] >>
  qexistsl_tac [`cenv`,`d`,`i`,`n`,`out`,`sa`,`sb`,`src`,`sz`,`w`] >>
  simp[arithmeticTheory.ADD_COMM] >>
  rpt gen_tac >> strip_tac >>
  `ghost_kept cenv es ca G0 tn0 s0 H th` by
    (irule ghost_kept_readonly_frame >>
     qexistsl_tac [`G`,`not_fresh_at sa`,`tn`] >> simp[] >>
     fs[ghost_kept_def, compileEnvTheory.not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `t.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `(t with vs_vars := _) = s` (fn eq => once_rewrite_tac[GSYM eq]) >> simp[]) >>
  simp[] >>
  drule_all (SRULE [] cast_convert_success_post) >>
  simp[vyperASTTheory.expr_type_def]
QED
