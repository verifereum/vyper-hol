(* Memory-checked neg: the operand's lowering, then compile_neg. *)
Theory bodyNegMemory
Ancestors
  bodyUnopFragMemory exprSimMemoryStack exprSimMemDefs exprSimSource
  exprSimUnopProps exprSimUnopCompose exprLoweringProps freshWrites
  exprLowering compileEnv vyperContext vyperTypeSystem vyperTyping vyperValue
  vyperAST vyperInterpreter exprSimHypsDefs arithmeticProps vyperArith

Theorem expr_body_pre_neg:
  expr_body_pre cenv cx env (Builtin ann Neg [e]) es ==>
  ann = expr_type e /\ expr_body_pre cenv cx env e es /\
  is_numeric_type ann /\ ~is_uint_type ann /\
  0 < type_bits ann /\ type_bits ann <= 256 /\ is_word_type ann
Proof
  strip_tac >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule expr_body_pre_builtin_arg >> simp[] >>
     qexistsl_tac [`ann`, `[e]`, `Neg`, `es`] >> simp[]) >>
  `ann = expr_type e /\ is_numeric_type ann /\ ~is_uint_type ann /\
   well_formed_type env.type_defs ann` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  `0 < type_bits ann /\ type_bits ann <= 256 /\ is_word_type ann` by
    (qpat_x_assum `ann = expr_type e` kall_tac >>
     Cases_on `ann` >> gvs[is_numeric_type_def, is_int_type_def, is_uint_type_def] >>
     rename1 `BaseT b` >> Cases_on `b` >>
     gvs[is_numeric_type_def, is_int_type_def, is_uint_type_def, type_bits_def,
         is_word_type_def, well_formed_type_def, evaluate_type_def,
         expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def]) >>
  simp[]
QED

Theorem compile_neg_sim_mem:
  expr_body_pre cenv cx env (Builtin ann Neg [e]) es /\
  expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_sim_mem ctx func cenv cx ty (Builtin ann Neg [e]) es
Proof
  strip_tac >> drule expr_body_pre_neg >> strip_tac >>
  qpat_x_assum `ann = expr_type e` SUBST_ALL_TAC >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ty`, `expr_type e`, `Neg`,
               `e`, `expr_type e`, `\x. compile_neg x (expr_type e)`, `es`]
    mp_tac compile_unop_sim_mem >>
  impl_tac >- (
    rpt conj_tac
    >- simp[]
    >- simp[]
    >- simp[builtin_args_length_ok_def]
    >- gvs[]
    >- gvs[]
    >- (rpt strip_tac >> drule lower_value_neg >> simp[])
    >- (rpt gen_tac >> strip_tac >>
        drule expr_body_pre_lower_value_word_shape >> disch_then drule >> simp[])
    >- (rpt gen_tac >> strip_tac >> drule_at Any straight_fresh_cs_extends >>
        simp[CONV_RULE (DEPTH_CONV ETA_CONV) straight_fresh_neg])
    >- gvs[] >>
    rpt strip_tac >>
    qspecl_then [`cenv`, `cx`, `env`, `e`, `es with gas_obs := gs1`, `v1`, `es1`]
      mp_tac expr_body_pre_word_value >>
    simp[] >> strip_tac >> gvs[] >>
    irule_at Any compile_neg_frag_mem >> gvs[]) >>
  simp[]
QED

Theorem compile_neg_vv_sim_mem:
  expr_body_pre cenv cx env (Builtin ann Neg [e]) es /\
  expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_vv_sim_mem ctx func cenv cx ty (Builtin ann Neg [e]) es
Proof
  strip_tac >> `is_word_type (expr_type (Builtin ann Neg [e]))` by
    (drule expr_body_pre_neg >> strip_tac >>
     gvs[vyperASTTheory.expr_type_def]) >>
  drule_then irule body_expr_vv_sim_mem_stack_word >>
  rpt conj_tac
  >~ [`compile_expr`] >- simp[compile_neg_stack]
  >~ [`eval_expr`] >- metis_tac[eval_expr_builtin_value] >>
  metis_tac[compile_neg_sim_mem]
QED
