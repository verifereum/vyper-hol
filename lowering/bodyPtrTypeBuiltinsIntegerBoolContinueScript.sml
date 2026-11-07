(* Integer-to-Bool semantics and pointer continuation. *)
Theory bodyPtrTypeBuiltinsIntegerBoolContinue
Ancestors bodyPtrTypeBuiltinsBoolContinue bodyPtrTypeBuiltinsIntegerContinue
  exprSimArith vyperTyping integer_word valueEncoding exprLowering vyperAST
  vyperValue vyperValueOperation exprSimConvert exprSimDefs exprSimHyps
  bodyPtrTypeBuiltinsBool exprLoweringProps vyperTypeSystem compileEnv
  bodyPtrTypeBuiltinsSourceFrame bodyPtrDefs fragGasPathPtr ptrDiscipline
  venomState emitHelperProps list rich_list finite_map
  bodyPtrTypeBuiltinsUintContinue bodyPtrTypeBuiltinsUintCounted
  exprSimProps exprSimWordArgs loweringPosts instIdxIndep

Theorem scalar_integer_bool_typed_actual:
  evaluate_type (get_tenv cx) (BaseT (if si then IntT bi else UintT bi)) = SOME tv /\
  value_has_type tv v /\
  compile_type_convert x (mk_convert_op (BaseT (if si then IntT bi else UintT bi))
    (BaseT BoolT)) sa = (r,sb) /\
  eval_operand x ss = SOME (typed_val_to_w256 tv v) ==>
  ?out sf.
    convert_result cx (BaseT (if si then IntT bi else UintT bi)) (BaseT BoolT) v = INL out /\
    evaluate_type (get_tenv cx) (BaseT BoolT) = SOME (BaseTV BoolT) /\
    run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand r sf = SOME (typed_val_to_w256 (BaseTV BoolT) out) /\
    (sf with vs_vars := ss.vs_vars) = ss /\
    (!z. not_fresh_at sa z ==> lookup_var z sf = lookup_var z ss)
Proof
  Cases_on `si` >> simp[vyperValueTheory.evaluate_type_def] >> strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def, AllCaseEqs(), mk_convert_op_def,
    is_bytestring_type_def, typed_val_to_w256_def, val_to_w256_def] >>
  drule_all convert_bool_run_actual >> strip_tac >>
  `((i2w i : bytes32) = 0w) <=> i = 0` by
    (mp_tac (Q.SPECL [`bi`,`T`,`i`] i2w_eq_0_within) >>
     mp_tac (Q.SPECL [`bi`,`F`,`i`] i2w_eq_0_within) >>
     simp[within_int_bound_def] >> metis_tac[integer_wordTheory.i2w_0]) >>
  qexistsl_tac [`BoolV (i <> 0)`,`t`] >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes, evaluate_convert_def,
       typed_val_to_w256_def, val_to_w256_def] >>
  Cases_on `i = 0` >> simp[venomExecSemanticsTheory.bool_to_word_def]
QED

Theorem scalar_bool_compile_frame:
  compile_type_convert x ConvToBool sa = (r,sb) ==>
  inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
  LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa sb)
Proof
  simp[compile_type_convert_def, emitHelperTheory.emit_op_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >> simp[emitted_insts_def, inst_extends_def] >>
  rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]
QED

Theorem scalar_bool_counted_success:
  compile_type_convert x ConvToBool s1 = (op,sb) /\
  op_taint tn x = {} /\ ~ctx_has_dalloca ctx /\
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
  strip_tac >> drule_all convert_bool_counted_certificate >>
  disch_then (qspecl_then [`PG`,`G`,`D`] strip_assume_tac) >>
  `t = s with vs_vars := t.vs_vars /\
   (!p. not_fresh_at s1 p ==> lookup_var p t = lookup_var p s)` by
    (drule_all convert_bool_runtime_frame >>
     simp[venomStateTheory.venom_state_component_equality] >> metis_tac[]) >>
  `ghost_inv d cenv cx es H th
    (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts s1 sb))` by
    (irule bodyPtrTypeBuiltinsSourceFrameTheory.ghost_inv_readonly_frame >>
     qexistsl_tac [`G`,`not_fresh_at s1`,`s`,`tn`] >>
     qpat_x_assum `t = s with vs_vars := _` SUBST_ALL_TAC >>
     fs[local_ptrs_reserved_def, venomStateTheory.lookup_var_def] >> metis_tac[]) >>
  `ghost_kept cenv es0 sa G0 tn0 s0 H th` by
    (irule bodyPtrTypeBuiltinsSourceFrameTheory.ghost_kept_readonly_frame >>
     qexistsl_tac [`G`,`not_fresh_at s1`,`tn`] >> simp[] >>
     fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  qexistsl_tac [`H`,`th`] >> simp[]
QED

Theorem scalar_integer_bool_continuation:
  expr_post ctx func cenv cx e es sa s1 s0 (ee with gas_obs := []) v1 x t0 /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t0.vs_halted /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert (BaseT BoolT) [e]) es /\
  expr_type e = BaseT (if si then IntT bi else UintT bi) /\
  compile_type_convert x (mk_convert_op (expr_type e) (BaseT BoolT)) s1 = (op,sb) /\
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
    (\vs. (convert_result cx (expr_type e) (BaseT BoolT) v1,vs))
    (ee with gas_obs := [],t0,G,tn)
    (\res fin H th ss. ?v. res = INL v /\
      expr_post ctx func cenv cx (TypeBuiltin ann Convert (BaseT BoolT) [e])
        es sa sb s0 fin v op ss /\
      ss.vs_current_bb = sb.cs_current_bb /\ ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin H th ss /\
      ptr_val_ok cx (BaseT BoolT) v op H th ss /\
      ghost_kept cenv es sa G0 tn0 s0 H th)
    (\res fin gt out. expr_exit res out)
Proof
  strip_tac >>
  `ann = BaseT BoolT` by (drule expr_body_pre_convert >> simp[]) >> gvs[] >>
  `is_word_type (BaseT (if si then IntT bi else UintT bi))` by
    (Cases_on `si` >> simp[is_word_type_def]) >>
  `eval_operand x t0 = SOME (typed_val_to_w256 tv v1)` by
    fs[expr_post_def, expr_val_rel_def] >>
  drule_all scalar_integer_bool_typed_actual >> strip_tac >>
  `compile_type_convert x ConvToBool s1 = (op,sb)` by
    (Cases_on `si` >> fs[mk_convert_op_def, is_bytestring_type_def]) >>
  drule_all scalar_bool_compile_frame >> strip_tac >>
  `?bb. lookup_block t0.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts s1 sb) (DROP t0.vs_inst_idx bb.bb_instructions)` by
    (irule fn_code_emitted_prefix >> simp[] >> metis_tac[]) >>
  `op_taint tn x = {}` by fs[ptr_val_ok_def] >>
  drule_all scalar_bool_counted_success >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  suspend "post"
QED

Resume scalar_integer_bool_continuation[post]:
  `sf = t0 with vs_vars := sf.vs_vars` by fs[venom_state_component_equality] >>
  `stmt_state_rel ctx func cenv cx (ee with gas_obs := []) sf` by
    (irule stmt_state_rel_readonly_vars_pc >>
     qexistsl_tac [`t0`,`s1`] >> simp[] >> reverse conj_tac
     >- fs[expr_post_def, stmt_state_rel_gas_obs] >>
     qpat_x_assum `sf = t0 with vs_vars := _` SUBST1_TAC >>
     simp[venom_state_component_equality]) >>
  `expr_post ctx func cenv cx
    (TypeBuiltin (BaseT BoolT) Convert (BaseT BoolT) [e])
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

Finalise scalar_integer_bool_continuation
