Theory bodyPtrTypeBuiltinsFlagUintContinue
Ancestors bodyPtrTypeBuiltinsScalarContinue bodyPtrTypeBuiltinsUintContinue
  convertScalarEncoding exprSimConvert exprLowering exprLoweringProps vyperValue
  vyperValueOperation vyperTypeSystem vyperTyping valueEncoding integer_word integer
  words list venomState compileEnv bodyPtrDefs fragGasPathPtr ptrDiscipline vyperAST
  exprSimDefs exprSimHyps exprSimProps exprSimWordArgs loweringPosts

Theorem scalar_flag_uint_semantic:
  evaluate_type (get_tenv cx) (FlagT name) = SOME tv /\ value_has_type tv v ==>
  ?out. convert_result cx (FlagT name) (BaseT (UintT 256)) v = INL out /\
    typed_val_to_w256 (BaseTV (UintT 256)) out = typed_val_to_w256 tv v
Proof
  simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >> strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  `n < 2 ** 256` by
    (irule arithmeticTheory.LESS_LESS_EQ_TRANS >> qexists_tac `2 ** m` >>
     simp[]) >>
  qexists_tac `IntV (&n)` >>
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def,
       within_int_bound_ineq, scalar_flag_encoding]
QED

Theorem scalar_flag_uint_continuation:
  expr_post ctx func cenv cx e es sa s1 s0 (ee with gas_obs := []) v1 x t0 /\
  t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\ ~t0.vs_halted /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert (BaseT (UintT 256)) [e]) es /\
  expr_type e = FlagT name /\
  compile_type_convert x (mk_convert_op (expr_type e) (BaseT (UintT 256))) s1 = (op,sb) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v1 /\
  sa.cs_next_var <= s1.cs_next_var /\
  ptr_val_ok cx (expr_type e) v1 x G tn t0 /\
  ghost_inv d cenv cx (ee with gas_obs := []) G tn t0 /\
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,func) PG []
    (\vs. (convert_result cx (expr_type e) (BaseT (UintT 256)) v1,vs))
    (ee with gas_obs := [],t0,G,tn)
    (\res fin H th ss. ?v. res = INL v /\
      expr_post ctx func cenv cx (TypeBuiltin ann Convert (BaseT (UintT 256)) [e])
        es sa sb s0 fin v op ss /\
      ss.vs_current_bb = sb.cs_current_bb /\ ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin H th ss /\
      ptr_val_ok cx (BaseT (UintT 256)) v op H th ss /\
      ghost_kept cenv es sa G0 tn0 s0 H th)
    (\res fin gt out. expr_exit res out)
Proof
  strip_tac >>
  `ann = BaseT (UintT 256)` by (drule expr_body_pre_convert >> simp[]) >>
  gvs[] >> drule_all scalar_flag_uint_semantic >> strip_tac >>
  gvs[mk_convert_op_def, is_bytestring_type_def, compile_type_convert_def, comp_return_def] >>
  `eval_operand op t0 = SOME (typed_val_to_w256 (BaseTV (UintT 256)) out)` by
    fs[expr_post_def, expr_val_rel_def, is_word_type_def] >>
  `expr_post ctx func cenv cx
    (TypeBuiltin (BaseT (UintT 256)) Convert (BaseT (UintT 256)) [e])
    es sa s1 s0 (ee with gas_obs := []) out op t0` by
    (irule scalar_suffix_expr_post >> simp[expr_type_def, is_word_type_def,
       vyperValueTheory.evaluate_type_def] >>
     conj_tac >- fs[expr_post_def, stmt_state_rel_gas_obs] >>
     qexistsl_tac [`e`,`s1`,`t0`,`v1`,`op`] >>
     simp[] >> fs[expr_post_def]) >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL out`,`ee`,`G`,`tn`,`OK t0`] >>
  fs[ptr_val_ok_def, is_word_type_def] >> simp[gas_path_ptr_rules]
QED
