Theory bodyPtrTypeBuiltinsBytesWordContinue
Ancestors bodyPtrTypeBuiltinsBytesWordSuccess bodyPtrTypeBuiltinsBytesWordAbort
  bodyPtrTypeBuiltinsBytesWordActual bodyPtrTypeBuiltinsBytesWordInputs
  bodyPtrTypeBuiltinsBytesWordTypes bodyPtrSignedConvertSourceTyping
  fragGasPathPtr bodyPtrDefs exprLowering exprLoweringProps loweringPosts
  compileEnv venomState exprSimDefs

Theorem bytes_word_nonzero_outcome_ptr:
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es /\
  is_bytestring_type (expr_type e) /\ ~is_bytestring_type dst /\
  valid_conversion (expr_type e) dst /\ well_formed_type tenv dst /\
  ~((?b. dst = BaseT (IntT b)) \/ dst = BaseT DecimalT) /\
  lowered_value_type cenv e <> BaseT (BytesT (Dynamic 0)) /\
  lowered_value_type cenv e <> BaseT (StringT 0) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
  compile_type_convert x (mk_convert_op (expr_type e) dst) sa = (out,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  fn_has_code sa sb fn /\
  expr_post ctx fn cenv cx e es ca sa s0 ee v x s /\
  ptr_val_ok cx (expr_type e) v x G tn s /\ ptr_buf_ok cenv e x G s /\
  ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es ca G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sa /\ ca.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
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
  `64 <= type_memory_bytes cenv (lowered_value_type cenv e)` by
    (drule_all body_source_lowered_nonzero_capacity >> simp[]) >>
  drule_all bytes_word_child_memory_inputs >> strip_tac >>
  `eval_operand x s = SOME a` by simp[eval_operand_def] >>
  `convert_result cx (expr_type e) dst v = convert_result cx (expr_type e) dst v` by simp[] >>
  drule_all bytes_word_semantic_run_actual >>
  Cases_on `convert_result cx (expr_type e) dst v` >> simp[] >> strip_tac
  >- (`is_word_type dst` by
        (drule_all bytestring_scalar_unsigned_convert_op >> simp[]) >>
      `expr_val_rel cx dst x' out sf` by
        (simp[expr_val_rel_def] >> goal_assum (drule_at Any) >> simp[]) >>
      drule_all bytes_word_success_post_counted >>
      disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
      simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
      simp[gas_summary_ptr_at_def] >>
      qexistsl_tac [`INL x'`,`ee`,`H`,`th`,
        `OK (sf with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
      gvs[vyperASTTheory.expr_type_def]) >>
  drule_all bytes_word_abort_counted >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INR y`,`ee`,`H`,`th`,`Abort Revert_abort (sf with vs_inst_idx := j)`] >>
  gvs[oneline expr_exit_def, AllCaseEqs(), fragExecTheory.exit_result_def]
QED
