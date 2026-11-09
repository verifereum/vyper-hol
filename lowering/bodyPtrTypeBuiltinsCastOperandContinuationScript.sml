Theory bodyPtrTypeBuiltinsCastOperandContinuation
Ancestors
  bodyPtrTypeBuiltinsCastContinuation bodyPtrTypeBuiltinsMemoryOperandSemantics
  bodyPtrTypeBuiltinsMemoryOperandResources bodyPtrTypeBuiltinsConvertOperandBoundary
  bodyPtrTypeBuiltinsMemoryInterface assignTuplePtrBytesResources
  exprOperandVar valueCopyBytes exprLoweringProps bodyPtrDefs loweringPosts
  compileEnv venomState exprLowering
Libs monadsyntax

Theorem cast_convert_operand_continuation:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert target [e]) (es with gas_obs := gs) /\
  is_bytestring_type (expr_type e) /\ is_bytestring_type target /\ ~is_word_type target /\
  ~((?a f args drv. e = Call a (IntCall f) args drv) /\
    lowered_value_type cenv e <> expr_type e) /\
  (do r <- eval_expr cx e; read_result cx r od) (es with gas_obs := gs) = (INL v,ee) /\
  lower_value compile_expr cenv (expr_type e) e ca = (x,sa) /\
  compile_type_convert x (mk_convert_op (expr_type e) target) sa = (out,sb) /\
  type_memory_bytes cenv target <= type_memory_bytes cenv (lowered_value_type cenv e) /\
  32 <= type_memory_bytes cenv (lowered_value_type cenv e) /\
  (!i. expr_type e = BaseT (BytesT (Dynamic i)) \/ expr_type e = BaseT (StringT i) ==> i < dimword(:256)) /\
  (!n. target = BaseT (BytesT (Dynamic n)) \/ target = BaseT (StringT n) ==> n < dimword(:256)) /\
  expr_post ctx fn cenv cx e es ca sa s0 ee v x s /\
  ptr_val_ok cx (post_value_type cenv e) v x G tn s /\ ptr_buf_ok cenv e x G s /\
  local_ptrs_reserved cenv ca /\ local_ptrs_reserved cenv sa /\ ca.cs_next_var <= sa.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es ca G0 tn0 s0 G tn /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  gas_outcome_ptr D tops (ctx,fn) PG
    (\st. (convert_result cx (expr_type e) target v,st)) (ee,s,G,tn)
    (\res fin H th u. ?vout. res = INL vout /\
      expr_post ctx fn cenv cx (TypeBuiltin target Convert target [e]) es ca sb s0 fin vout out u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin H th u /\
      ptr_val_ok cx (post_value_type cenv (TypeBuiltin target Convert target [e])) vout out H th u /\
      (~is_word_type (post_value_type cenv (TypeBuiltin target Convert target [e])) ==>
        ptr_buf_ok cenv (TypeBuiltin target Convert target [e]) out H u) /\
      ghost_kept cenv es ca G0 tn0 s0 H th)
    (\res fin gt r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all convert_memory_operand_semantics >> strip_tac >>
  `post_value_type cenv e = expr_type e` by metis_tac[convert_operand_post_type] >>
  `~is_word_type (expr_type e)` by metis_tac[is_bytestring_word_type] >>
  drule_all convert_memory_operand_resources >> strip_tac >>
  `not_fresh_at sa src` by metis_tac[compile_lower_value_var] >>
  `!j. w2n a <= j /\ j < w2n a + 32 ==> j NOTIN tn.t_mem` by
    metis_tac[robust_bytestring_header_clean_ptr] >>
  `val_in_memory tv v (w2n a) s.vs_memory` by
    (first_x_assum irule >> simp[bodyPtrDefsTheory.mem_agree_outside_def]) >>
  mp_tac (Q.SPECL [`expr_type e`,`target`] memory_convert_shapes) >>
  simp[] >> disch_then (qx_choose_then `i` (qx_choose_then `n` assume_tac)) >>
  irule (SRULE [] cast_convert_modern_outcome_ptr) >> simp[] >>
  rpt (goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`i`,`n`] >> gvs[]
QED
