Theory bodyPtrTypeBuiltinsIntegerBytesContinue
Ancestors bodyPtrTypeBuiltinsIntegerBytesRun bodyPtrTypeBuiltinsCheckedArithmetic
  convertScalarEncoding bodyPtrTypeBuiltinsSourceFrame bodyPtrTypeBuiltinsUintContinue
  bodyPtrTypeBuiltinsUintCounted exprSimConvert exprLowering exprLoweringProps
  emitHelper emitHelperProps venomState venomInst venomExecSemantics compileEnv
  bodyPtrDefs fragGasPathPtr ptrDiscipline exprSimDefs exprSimHyps exprSimProps
  exprSimWordArgs loweringPosts instIdxIndep finite_map vyperAST vyperValue
  vyperValueOperation vyperTypeSystem vyperTyping valueEncoding integer_word
  words list rich_list arithmetic fragExec

Theorem scalar_integer_bytes_compile_eq:
  mk_convert_op (BaseT (if si then IntT bi else UintT bi))
    (BaseT (BytesT (Fixed m))) = ConvIntToBytesM si bi m
Proof
  Cases_on `si` >> simp[mk_convert_op_def, is_signed_type_def,
    type_bits_def, is_bytestring_type_def]
QED

Theorem scalar_integer_bytes_typed_actual:
  evaluate_type (get_tenv cx) (BaseT (if si then IntT bi else UintT bi)) = SOME tv /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Fixed m))) = SOME tout /\
  value_has_type tv v /\
  valid_conversion (BaseT (if si then IntT bi else UintT bi)) (BaseT (BytesT (Fixed m))) /\
  compile_type_convert x (mk_convert_op (BaseT (if si then IntT bi else UintT bi))
    (BaseT (BytesT (Fixed m)))) sa = (r,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  eval_operand x ss = SOME (typed_val_to_w256 tv v) ==>
  ?out sf. convert_result cx (BaseT (if si then IntT bi else UintT bi))
      (BaseT (BytesT (Fixed m))) v = INL out /\
    run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand r sf = SOME (typed_val_to_w256 tout out) /\
    (sf with vs_vars := ss.vs_vars) = ss /\
    (!z. not_fresh_at sa z ==> lookup_var z sf = lookup_var z ss)
Proof
  rewrite_tac[scalar_integer_bytes_compile_eq] >>
  Cases_on `si` >> simp[vyperValueTheory.evaluate_type_def, valid_conversion_def] >>
  strip_tac >> Cases_on `v` >>
  gvs[value_has_type_def, AllCaseEqs(), typed_val_to_w256_def, val_to_w256_def] >>
  drule_all integer_bytes_actual_run >> simp[] >> strip_tac >>
  qexistsl_tac [`BytesV (DROP (32-m) (word_to_bytes_be (i2w i:bytes32)))`,`t`] >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes,
       evaluate_convert_def, scalar_word_to_fixed]
QED

Theorem scalar_integer_bytes_compile_frame:
  compile_type_convert x (ConvIntToBytesM si bi m) sa = (r,sb) ==>
  inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
  LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa sb)
Proof
  Cases_on `si` >> Cases_on `m*8 < bi` >>
  simp[compile_type_convert_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >> simp[emitted_insts_def, inst_extends_def] >>
  rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]
QED

Theorem scalar_integer_bytes_counted_success:
  compile_type_convert x (ConvIntToBytesM si bi m) s1 = (op,sb) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts s1 sb) s = OK t /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts s1 sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  local_ptrs_reserved cenv s1 /\ sa.cs_next_var <= s1.cs_next_var /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at s1 p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at s1 p) /\
  ghost_inv d cenv cx es G tn s /\ ghost_kept cenv es0 sa G0 tn0 s0 G tn ==>
  ?H th. gas_path_ptr D 0 ctx func PG G tn s 0 H th
    (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts s1 sb))) /\
    op_prov H op = NONE /\ op_taint th op = {} /\
    ghost_inv d cenv cx es H th
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts s1 sb)) /\
    ghost_kept cenv es0 sa G0 tn0 s0 H th
Proof
  strip_tac >> drule_all convert_int_bytes_counted_certificate >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `t = s with vs_vars := t.vs_vars /\
   (!p. not_fresh_at s1 p ==> lookup_var p t = lookup_var p s)` by
    (drule_all convert_int_bytes_runtime_frame >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `ghost_inv d cenv cx es H th
    (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts s1 sb))` by
    (irule ghost_inv_readonly_frame >>
     qexistsl_tac [`G`,`not_fresh_at s1`,`s`,`tn`] >>
     qpat_x_assum `t = s with vs_vars := _` SUBST_ALL_TAC >>
     fs[local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]) >>
  `ghost_kept cenv es0 sa G0 tn0 s0 H th` by
    (irule ghost_kept_readonly_frame >>
     qexistsl_tac [`G`,`not_fresh_at s1`,`tn`] >> simp[] >>
     fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  qexistsl_tac [`H`,`th`] >> simp[]
QED

Theorem scalar_integer_bytes_continuation:
  expr_post ctx func cenv cx e es sa s1 s0 (ee with gas_obs := []) v1 x t0 /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t0.vs_halted /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert (BaseT (BytesT (Fixed m))) [e]) es /\
  expr_type e = BaseT (if si then IntT bi else UintT bi) /\
  compile_type_convert x (mk_convert_op (expr_type e) (BaseT (BytesT (Fixed m)))) s1 = (op,sb) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v1 /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\
  fn_has_code s1 sb func /\ local_ptrs_reserved cenv s1 /\
  sa.cs_next_var <= s1.cs_next_var /\ ~ctx_has_dalloca ctx /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at s1 p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at s1 p) /\
  ptr_val_ok cx (expr_type e) v1 x G tn t0 /\
  ghost_inv d cenv cx (ee with gas_obs := []) G tn t0 /\
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,func) PG []
    (\vs. (convert_result cx (expr_type e) (BaseT (BytesT (Fixed m))) v1,vs))
    (ee with gas_obs := [],t0,G,tn)
    (\res fin H th ss. ?v. res = INL v /\
      expr_post ctx func cenv cx (TypeBuiltin ann Convert (BaseT (BytesT (Fixed m))) [e])
        es sa sb s0 fin v op ss /\
      ss.vs_current_bb = sb.cs_current_bb /\ ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin H th ss /\
      ptr_val_ok cx (BaseT (BytesT (Fixed m))) v op H th ss /\
      ghost_kept cenv es sa G0 tn0 s0 H th)
    (\res fin gt out. expr_exit res out)
Proof
  strip_tac >>
  drule expr_body_pre_convert >> strip_tac >> gvs[] >>
  `eval_operand x t0 = SOME (typed_val_to_w256 tv v1)` by
    (Cases_on `si` >> fs[expr_post_def, expr_val_rel_def, is_word_type_def]) >>
  `?tout. evaluate_type (get_tenv cx) (BaseT (BytesT (Fixed m))) = SOME tout` by
    (qpat_assum `expr_body_pre _ _ _ (TypeBuiltin _ _ _ _) _`
       (mp_then Any mp_tac expr_body_pre_type_evaluates) >>
     simp[expr_type_def, optionTheory.IS_SOME_EXISTS]) >>
  drule_all scalar_integer_bytes_typed_actual >> strip_tac >>
  fs[scalar_integer_bytes_compile_eq] >>
  drule_all scalar_integer_bytes_compile_frame >> strip_tac >>
  `?bb. lookup_block t0.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts s1 sb) (DROP t0.vs_inst_idx bb.bb_instructions)` by
    (irule fn_code_emitted_prefix >> simp[] >> metis_tac[]) >>
  `op_prov G x = NONE /\ op_taint tn x = {}` by
    (Cases_on `si` >> fs[ptr_val_ok_def, is_word_type_def]) >>
  suspend "success"
QED

Resume scalar_integer_bytes_continuation[success]:
  `m <= 32 /\ tout = BaseTV (BytesT (Fixed m))` by
    (qpat_x_assum `evaluate_type _ (BaseT (BytesT (Fixed m))) = _` mp_tac >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
  qpat_x_assum `tout = _` SUBST_ALL_TAC >>
  drule_all scalar_integer_bytes_counted_success >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  `sf = t0 with vs_vars := sf.vs_vars` by fs[venom_state_component_equality] >>
  `stmt_state_rel ctx func cenv cx (ee with gas_obs := []) sf` by
    (irule stmt_state_rel_readonly_vars_pc >>
     qexistsl_tac [`t0`,`s1`] >> simp[] >> reverse conj_tac
     >- fs[expr_post_def, stmt_state_rel_gas_obs] >>
     qpat_x_assum `sf = t0 with vs_vars := _` SUBST1_TAC >>
     simp[venom_state_component_equality]) >>
  `expr_post ctx func cenv cx
    (TypeBuiltin (BaseT (BytesT (Fixed m))) Convert (BaseT (BytesT (Fixed m))) [e])
    es sa sb s0 (ee with gas_obs := []) out op
      (sf with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule scalar_suffix_expr_post >>
     simp[expr_type_def, is_word_type_def, stmt_state_rel_inst_idx, eval_op_inst_idx] >>
     conj_tac >- fs[stmt_state_rel_gas_obs] >>
     qexistsl_tac [`e`,`s1`,`t0`,`v1`,`x`] >> simp[lookup_var_def] >>
     conj_tac >- (fs[lookup_var_def] >> metis_tac[]) >>
     qpat_x_assum `sf = t0 with vs_vars := _` SUBST1_TAC >> simp[]) >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL out`,`ee`,`H`,`th`,
    `OK (sf with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  gvs[ptr_val_ok_def, is_word_type_def, arithmeticTheory.ADD_COMM] >>
  qpat_x_assum `sf = t0 with vs_vars := _` SUBST_ALL_TAC >>
  gvs[venom_state_component_equality]
QED

Finalise scalar_integer_bytes_continuation
