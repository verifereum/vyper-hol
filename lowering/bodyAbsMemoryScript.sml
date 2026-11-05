(* Memory-checked abs: the operand's lowering, then compile_builtin_abs. *)
Theory bodyAbsMemory
Ancestors
  bodyUnopFragMemory exprSimMemoryStack exprSimMemDefs exprSimSource
  exprSimUnopProps exprSimUnopCompose exprLoweringProps freshWrites
  exprLowering compileEnv vyperContext vyperTypeSystem vyperTyping vyperValue
  vyperAST vyperInterpreter

Theorem compile_abs_sim_mem:
  expr_type e = BaseT (IntT 256) /\ expr_body_pre cenv cx env e es /\
  expr_sim_mem ctx func cenv cx ty e es ==>
  expr_sim_mem ctx func cenv cx ty (Builtin (BaseT (IntT 256)) Abs [e]) es
Proof
  strip_tac >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ty`, `BaseT (IntT 256)`, `Abs`,
               `e`, `ty`, `compile_builtin_abs`, `es`]
    mp_tac compile_unop_sim_mem >>
  impl_tac >- (
    rpt conj_tac
    >- simp[]
    >- simp[]
    >- simp[builtin_args_length_ok_def]
    >- simp[is_word_type_def]
    >- simp[is_word_type_def]
    >- (rpt strip_tac >> drule lower_value_abs >> simp[])
    >- (rpt gen_tac >> strip_tac >>
        drule expr_body_pre_lower_value_word_shape >> disch_then drule >>
        simp[is_word_type_def])
    >- (rpt gen_tac >> strip_tac >> drule_at Any straight_fresh_cs_extends >>
        simp[straight_fresh_abs])
    >- simp[] >>
    rpt strip_tac >>
    qspecl_then [`cenv`, `cx`, `env`, `e`, `es with gas_obs := gs1`, `v1`, `es1`]
      mp_tac expr_body_pre_word_value >>
    simp[is_word_type_def] >> strip_tac >>
    gvs[vyperValueTheory.evaluate_type_def, compile_abs_frag_mem]) >>
  simp[]
QED

Theorem compile_abs_vv_sim_mem:
  expr_type e = BaseT (IntT 256) /\ expr_body_pre cenv cx env e es /\
  expr_sim_mem ctx func cenv cx ty e es ==>
  expr_vv_sim_mem ctx func cenv cx ty (Builtin (BaseT (IntT 256)) Abs [e]) es
Proof
  strip_tac >> `is_word_type (expr_type (Builtin (BaseT (IntT 256)) Abs [e]))` by
    simp[vyperASTTheory.expr_type_def, is_word_type_def] >>
  drule_then irule body_expr_vv_sim_mem_stack_word >>
  rpt conj_tac
  >~ [`compile_expr`] >- simp[compile_not_abs_stack]
  >~ [`eval_expr`] >- metis_tac[eval_expr_builtin_value] >>
  metis_tac[compile_abs_sim_mem]
QED
