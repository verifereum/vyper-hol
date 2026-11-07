Theory bodyPtrTypeBuiltinsAddressFixedContinue
Ancestors bodyPtrTypeBuiltinsIntegerBytesContinue bodyPtrTypeBuiltinsIntegerBytesRun convertScalarEncoding
  exprSimConvert exprLowering exprLoweringProps vyperValue vyperValueOperation
  vyperTypeSystem vyperTyping valueEncoding integer_word words list rich_list
  venomState venomExecSemantics compileEnv bodyPtrDefs fragGasPathPtr ptrDiscipline
  bodyPtrTypeBuiltinsSourceFrame bodyPtrTypeBuiltinsUintContinue
  bodyPtrTypeBuiltinsUintCounted exprSimDefs exprSimHyps exprSimProps
  exprSimWordArgs loweringPosts instIdxIndep emitHelperProps finite_map vyperAST fragExec

Theorem scalar_address_fixed_typed_actual:
  evaluate_type (get_tenv cx) (BaseT AddressT) = SOME tv /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Fixed m))) = SOME tout /\
  value_has_type tv v /\
  valid_conversion (BaseT AddressT) (BaseT (BytesT (Fixed m))) /\
  compile_type_convert x (mk_convert_op (BaseT AddressT)
    (BaseT (BytesT (Fixed m)))) sa = (r,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  eval_operand x ss = SOME (typed_val_to_w256 tv v) ==>
  ?out sf. convert_result cx (BaseT AddressT) (BaseT (BytesT (Fixed m))) v = INL out /\
    run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand r sf = SOME (typed_val_to_w256 tout out) /\
    (sf with vs_vars := ss.vs_vars) = ss /\
    (!z. not_fresh_at sa z ==> lookup_var z sf = lookup_var z ss)
Proof
  simp[vyperValueTheory.evaluate_type_def, valid_conversion_def] >> strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def, AllCaseEqs(), mk_convert_op_def,
    is_signed_type_def, type_bits_def, is_bytestring_type_def] >>
  drule_all integer_bytes_actual_run >> simp[] >> strip_tac >>
  qexistsl_tac [`BytesV (PAD_LEFT 0w m l)`,`t`] >>
  simp[convert_result_def, evaluate_convert_from_def, scalar_address_to_fixed]
QED

Theorem scalar_address_fixed_continuation:
  expr_post ctx func cenv cx e es sa s1 s0 (ee with gas_obs := []) v1 x t0 /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t0.vs_halted /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert (BaseT (BytesT (Fixed m))) [e]) es /\
  expr_type e = BaseT AddressT /\
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
  strip_tac >> drule expr_body_pre_convert >> strip_tac >> gvs[] >>
  `eval_operand x t0 = SOME (typed_val_to_w256 tv v1)` by
    fs[expr_post_def, expr_val_rel_def, is_word_type_def] >>
  `?tout. evaluate_type (get_tenv cx) (BaseT (BytesT (Fixed m))) = SOME tout` by
    (qpat_assum `expr_body_pre _ _ _ (TypeBuiltin _ _ _ _) _`
       (mp_then Any mp_tac expr_body_pre_type_evaluates) >>
     simp[expr_type_def, optionTheory.IS_SOME_EXISTS]) >>
  drule_all scalar_address_fixed_typed_actual >> strip_tac >>
  `compile_type_convert x (ConvIntToBytesM F 160 m) s1 = (op,sb)` by
    fs[mk_convert_op_def, is_signed_type_def, type_bits_def, is_bytestring_type_def] >>
  drule_all scalar_integer_bytes_compile_frame >> strip_tac >>
  `?bb. lookup_block t0.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts s1 sb) (DROP t0.vs_inst_idx bb.bb_instructions)` by
    (irule fn_code_emitted_prefix >> simp[] >> metis_tac[]) >>
  `op_prov G x = NONE /\ op_taint tn x = {}` by fs[ptr_val_ok_def, is_word_type_def] >>
  suspend "success"
QED

Resume scalar_address_fixed_continuation[success]:
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

Finalise scalar_address_fixed_continuation
