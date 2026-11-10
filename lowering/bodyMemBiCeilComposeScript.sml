(* Counted unary composition for Ceil. *)
Theory bodyMemBiCeilCompose
Ancestors
  bodyMemBiCeilFrag bodyUnopFragMemory exprSimMemoryStack exprSimMemDefs
  exprSimSource exprSimUnopProps exprSimUnopCompose exprLoweringProps freshWrites
  exprSimWordBuiltins exprLowering compileEnv vyperContext vyperTypeSystem
  vyperTyping vyperValue vyperAST vyperInterpreter

Theorem compile_ceil_sim_mem:
  expr_type e = BaseT DecimalT /\ expr_body_pre cenv cx env e es /\
  expr_sim_mem ctx func cenv cx ty e es ==>
  expr_sim_mem ctx func cenv cx ty (Builtin (BaseT (IntT 256)) Ceil [e]) es
Proof
  strip_tac >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ty`, `BaseT (IntT 256)`, `Ceil`,
               `e`, `ty`, `\x. compile_ceil x 10000000000`, `es`]
    mp_tac compile_unop_sim_mem >>
  impl_tac >- (
    rpt conj_tac
    >- simp[]
    >- simp[]
    >- simp[builtin_args_length_ok_def]
    >- simp[is_word_type_def]
    >- simp[is_word_type_def]
    >- (rpt strip_tac >> drule lower_value_ceil >> simp[])
    >- (rpt gen_tac >> strip_tac >>
        drule expr_body_pre_lower_value_word_shape >> disch_then drule >>
        simp[is_word_type_def])
    >- (rpt gen_tac >> strip_tac >> drule_at Any straight_fresh_cs_extends >>
        simp[straight_fresh_ceil])
    >- simp[] >>
    rpt strip_tac >>
    qspecl_then [`cenv`, `cx`, `env`, `e`, `es with gas_obs := gs1`, `v1`, `es1`]
      mp_tac expr_body_pre_word_value >>
    simp[is_word_type_def] >> strip_tac >>
    gvs[evaluate_type_def] >>
    Cases_on `v1` >>
    gvs[value_has_type_def, compile_ceil_frag_mem]) >>
  simp[]
QED

Theorem compile_ceil_vv_sim_mem:
  expr_type e = BaseT DecimalT /\ expr_body_pre cenv cx env e es /\
  expr_sim_mem ctx func cenv cx ty e es ==>
  expr_vv_sim_mem ctx func cenv cx ty (Builtin (BaseT (IntT 256)) Ceil [e]) es
Proof
  strip_tac >>
  `is_word_type (expr_type (Builtin (BaseT (IntT 256)) Ceil [e]))` by
    simp[expr_type_def, is_word_type_def] >>
  drule_then irule body_expr_vv_sim_mem_stack_word >>
  rpt conj_tac
  >~ [`compile_expr`] >- (gen_tac >>
    Cases_on `compile_expr cenv ty (Builtin (BaseT (IntT 256)) Ceil [e]) sa` >>
    drule compile_ceil_stack >> strip_tac >> gvs[] >> metis_tac[])
  >~ [`eval_expr`] >- metis_tac[eval_expr_builtin_value] >>
  metis_tac[compile_ceil_sim_mem]
QED
