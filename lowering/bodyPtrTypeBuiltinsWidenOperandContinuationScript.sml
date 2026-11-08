Theory bodyPtrTypeBuiltinsWidenOperandContinuation
Ancestors
  bodyPtrTypeBuiltinsWidenContinuation bodyPtrTypeBuiltinsMemoryOperandSemantics
  bodyPtrTypeBuiltinsMemoryOperandResources bodyPtrTypeBuiltinsConvertOperandBoundary
  bodyPtrTypeBuiltinsWidenCopyShape exprSimConvertBytes exprLoweringProps
  exprOperandVar exprSimHypsDefs exprSimProps emitHelperProps valueCopyBytes
  loweringPosts bodyPtrDefs compileEnv venomState exprLowering
Libs monadsyntax

Theorem widen_convert_operand_continuation:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert target [e]) (es with gas_obs := gs) /\
  is_bytestring_type (expr_type e) /\ is_bytestring_type target /\ ~is_word_type target /\
  ~((?a f args drv. e = Call a (IntCall f) args drv) /\
    lowered_value_type cenv e <> expr_type e) /\
  (do r <- eval_expr cx e; read_result cx r od) (es with gas_obs := gs) = (INL v,ee) /\
  lower_value compile_expr cenv (expr_type e) e ca = (x,sa) /\
  compile_bytestring_widen_copy (type_memory_bytes cenv target) x
    (type_memory_bytes cenv (lowered_value_type cenv e)) sa = (out,sb) /\
  type_memory_bytes cenv (lowered_value_type cenv e) < type_memory_bytes cenv target /\
  type_memory_bytes cenv target < dimword(:256) /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  expr_post ctx fn cenv cx e es ca sa s0 ee v x s /\
  ptr_val_ok cx (post_value_type cenv e) v x G tn s /\ ptr_buf_ok cenv e x G s /\
  stmt_state_rel ctx fn cenv cx es s0 /\ local_ptrs_rel fn cenv es.scopes s0 /\
  local_ptrs_reserved cenv ca /\ local_ptrs_reserved cenv sa /\
  ca.cs_next_var <= sa.cs_next_var /\ ca.cs_next_id <= sa.cs_next_id /\
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
  `?vout. convert_result cx (expr_type e) target v = INL vout` by
    (irule convert_bytestring_lowered_widen_success >> metis_tac[]) >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee)` by
    metis_tac[] >>
  suspend "outcome"
QED

Resume widen_convert_operand_continuation[outcome]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  irule widen_convert_modern_outcome_ptr >> simp[] >>
  rpt (goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- (qexists_tac `gs` >> simp[]) >>
  qexistsl_tac [`a`,`type_memory_bytes cenv target`,
    `type_memory_bytes cenv (lowered_value_type cenv e)`,`sa`,`ca`,`src`,`expr_type e`] >>
  simp[arithmeticTheory.ADD_COMM] >> gvs[]
QED
Finalise widen_convert_operand_continuation
