Theory bodyPtrTypeBuiltinsFixedBoolContinue
Ancestors bodyPtrTypeBuiltinsIntegerBoolContinue bodyPtrTypeBuiltinsBoolContinue
  convertScalarEncoding exprLowering exprLoweringProps exprSimConvert
  vyperValue vyperValueOperation vyperTypeSystem vyperTyping valueEncoding
  bodyPtrTypeBuiltinsSourceFrame bodyPtrTypeBuiltinsUintContinue
  bodyPtrTypeBuiltinsUintCounted bodyPtrDefs fragGasPathPtr ptrDiscipline
  exprSimDefs exprSimHyps exprSimProps exprSimWordArgs loweringPosts instIdxIndep
  venomState venomExecSemantics emitHelperProps compileEnv finite_map
  list rich_list words vyperAST

Theorem scalar_fixed_bool_typed_actual:
  evaluate_type (get_tenv cx) (BaseT (BytesT (Fixed m))) = SOME tv /\
  value_has_type tv v /\
  compile_type_convert x (mk_convert_op (BaseT (BytesT (Fixed m)))
    (BaseT BoolT)) sa = (r,sb) /\
  eval_operand x ss = SOME (typed_val_to_w256 tv v) ==>
  ?out sf.
    convert_result cx (BaseT (BytesT (Fixed m))) (BaseT BoolT) v = INL out /\
    run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand r sf = SOME (typed_val_to_w256 (BaseTV BoolT) out) /\
    (sf with vs_vars := ss.vs_vars) = ss /\
    (!z. not_fresh_at sa z ==> lookup_var z sf = lookup_var z ss)
Proof
  simp[vyperValueTheory.evaluate_type_def] >> strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def, AllCaseEqs(), mk_convert_op_def,
    is_bytestring_type_def, typed_val_to_w256_def, val_to_w256_def] >>
  drule_all convert_bool_run_actual >> strip_tac >>
  `((word_of_bytes_be (PAD_RIGHT 0w 32 l):bytes32) = 0w) <=> EVERY (\b. b = 0w) l` by
    (irule scalar_fixed_zero >> simp[]) >>
  qexistsl_tac [`BoolV (EXISTS (\b. b <> 0w) l)`,`t`] >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes, evaluate_convert_def,
       typed_val_to_w256_def, val_to_w256_def] >>
  simp[combinTheory.o_DEF] >>
  Cases_on `EXISTS (\b. b <> 0w) l` >> simp[]
QED

Theorem scalar_fixed_bool_continuation:
  expr_post ctx func cenv cx e es sa s1 s0 (ee with gas_obs := []) v1 x t0 /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t0.vs_halted /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert (BaseT BoolT) [e]) es /\
  expr_type e = BaseT (BytesT (Fixed m)) /\
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
  `m <= 32` by
    (Cases_on `m <= 32` >> fs[vyperValueTheory.evaluate_type_def]) >>
  `eval_operand x t0 = SOME (typed_val_to_w256 tv v1)` by
    fs[expr_post_def, expr_val_rel_def, is_word_type_def] >>
  drule_all scalar_fixed_bool_typed_actual >> strip_tac >>
  `compile_type_convert x ConvToBool s1 = (op,sb)` by
    fs[mk_convert_op_def, is_bytestring_type_def] >>
  drule_all scalar_bool_compile_frame >> strip_tac >>
  `?bb. lookup_block t0.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts s1 sb) (DROP t0.vs_inst_idx bb.bb_instructions)` by
    (irule fn_code_emitted_prefix >> simp[] >> metis_tac[]) >>
  `op_taint tn x = {}` by fs[ptr_val_ok_def, is_word_type_def] >>
  drule_all scalar_bool_counted_success >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  suspend "post"
QED

Resume scalar_fixed_bool_continuation[post]:
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
     simp[expr_type_def, is_word_type_def, stmt_state_rel_inst_idx, eval_op_inst_idx,
          vyperValueTheory.evaluate_type_def] >>
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

Finalise scalar_fixed_bool_continuation
