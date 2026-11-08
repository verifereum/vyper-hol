Theory augAssignPtrDecimalNumeric
Ancestors augAssignPtrNumericProbe exprSimArith exprBopSimDefs exprLowering
  exprLoweringProps vyperValue valueEncoding loweringSlice list
  vyperValueOperation vyperInterpreter vyperTyping arithmeticProps compileEnv vyperAST vyperContext builtinMath venomExecSemantics
Libs intLib

Theorem decimal_add_sub_mod_numeric_witness:
  MEM bop [Add; Sub; Mod] /\
  within_int_bound (Signed 168) d1 /\ within_int_bound (Signed 168) d2 ==>
  (?v. bop_result cx ann bop tys (DecimalV d1) (DecimalV d2) es = INL v /\
       word_value v /\
       !x y sa sb op ss.
         compile_binop bop x y (BaseT DecimalT) bl el sa = (op,sb) /\
         fresh_vars_wrt sa ss /\
         eval_operand x ss = SOME (val_to_w256 (DecimalV d1)) /\
         eval_operand y ss = SOME (val_to_w256 (DecimalV d2)) ==>
         ?t. run_inst_seq (emitted_insts sa sb) ss = OK t /\
             eval_operand op t = SOME (val_to_w256 v)) \/
  (?m. bop_result cx ann bop tys (DecimalV d1) (DecimalV d2) es =
         INR (Error (RuntimeError m)) /\
       !x y sa sb op ss.
         compile_binop bop x y (BaseT DecimalT) bl el sa = (op,sb) /\
         fresh_vars_wrt sa ss /\
         eval_operand x ss = SOME (val_to_w256 (DecimalV d1)) /\
         eval_operand y ss = SOME (val_to_w256 (DecimalV d2)) ==>
         ?t. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort t)
Proof
  strip_tac >>
  `type_to_int_bound (BaseT (IntT 168)) = SOME (Signed 168) /\
   0 < type_bits (BaseT (IntT 168)) /\ type_bits (BaseT (IntT 168)) <= 256` by
    simp[type_to_int_bound_def, type_bits_def] >>
  Cases_on `bop = Mod` >>
  FIRST
    [qpat_assum `bop = Mod` kall_tac >>
     `MEM bop [Div; Mod]` by simp[] >>
     qpat_assum `within_int_bound _ d1`
       (mp_then (Pat `within_int_bound _ i1`) mp_tac divmod_integer_numeric_witness),
     qpat_assum `bop <> Mod` kall_tac >>
     `MEM bop [Add; Sub; Mul]` by fs[MEM] >>
     qpat_assum `within_int_bound _ d1`
       (mp_then (Pat `within_int_bound _ i1`) mp_tac checked_integer_numeric_witness)] >>
  disch_then drule_all >>
  disch_then (qspecl_then [`tys`, `es`, `el`] mp_tac) >>
  disch_then (qspecl_then [`cx`, `bl`] mp_tac) >>
  `!x y. compile_binop bop x y (BaseT DecimalT) bl el =
         compile_binop bop x y (BaseT (IntT 168)) bl el` by
    (gvs[] >> rpt gen_tac >>
     simp[compile_binop_def, compile_safe_add_def, compile_safe_sub_def,
          compile_safe_mod_def, clamp_and_return_def, compile_clamp_def,
          type_bounds_def, type_bits_def, is_signed_type_def]) >>
  gvs[] >>
  simp[bop_result_def, evaluate_builtin_def, evaluate_binop_def,
       bounded_int_op_def, bounded_decimal_op_def, type_to_int_bound_def,
       int_bound_bits_def] >>
  rpt IF_CASES_TAC >> simp[word_value_def, val_to_w256_def]
QED

Theorem decimal_scaled_word_facts:
  within_int_bound (Signed 168) d1 /\ within_int_bound (Signed 168) d2 ==>
  w2i (i2w d1 : bytes32) = d1 /\ w2i (i2w d2 : bytes32) = d2 /\
  (i2w d1 * n2w 10000000000 : bytes32) = i2w (d1 * 10000000000) /\
  ((i2w d2 = (0w : bytes32)) <=> d2 = 0) /\
  (d2 <> 0 ==>
   safe_sdiv (i2w d1 * n2w 10000000000) (i2w d2) =
     (i2w (d1 * 10000000000) / i2w d2 : bytes32))
Proof
  strip_tac >>
  `w2i (i2w d1 : bytes32) = d1 /\ w2i (i2w d2 : bytes32) = d2` by
    (conj_tac >> irule integer_wordTheory.w2i_i2w >>
     fs[within_int_bound_def, wordsTheory.INT_MIN_def,
        wordsTheory.INT_MAX_def, wordsTheory.dimword_def] >> intLib.ARITH_TAC) >>
  `(i2w d1 * n2w 10000000000 : bytes32) = i2w (d1 * 10000000000)` by
    (qspecl_then [`i2w d1 : bytes32`, `n2w 10000000000 : bytes32`] mp_tac
       integer_wordTheory.word_mul_i2w >>
     asm_rewrite_tac[w2i_decimal_divisor] >>
     disch_then (SUBST1_TAC o SYM) >> REFL_TAC) >>
  `((i2w d2 = (0w : bytes32)) <=> d2 = 0)` by
    (eq_tac >> strip_tac >> simp[integer_wordTheory.i2w_0] >>
     qpat_x_assum `w2i (i2w d2) = d2` (SUBST1_TAC o SYM) >>
     asm_simp_tac std_ss [integer_wordTheory.word_0_w2i]) >>
  simp[] >> strip_tac >> asm_simp_tac std_ss [safe_sdiv_def]
QED

Theorem decimal_mul_div_numeric_witness:
  MEM bop [Mul; Div] /\
  within_int_bound (Signed 168) d1 /\ within_int_bound (Signed 168) d2 ==>
  (?v. bop_result cx ann bop tys (DecimalV d1) (DecimalV d2) es = INL v /\
       word_value v /\
       !x y sa sb op ss.
         compile_binop bop x y (BaseT DecimalT) bl el sa = (op,sb) /\
         fresh_vars_wrt sa ss /\
         eval_operand x ss = SOME (val_to_w256 (DecimalV d1)) /\
         eval_operand y ss = SOME (val_to_w256 (DecimalV d2)) ==>
         ?t. run_inst_seq (emitted_insts sa sb) ss = OK t /\
             eval_operand op t = SOME (val_to_w256 v)) \/
  (?m. bop_result cx ann bop tys (DecimalV d1) (DecimalV d2) es =
         INR (Error (RuntimeError m)) /\
       !x y sa sb op ss.
         compile_binop bop x y (BaseT DecimalT) bl el sa = (op,sb) /\
         fresh_vars_wrt sa ss /\
         eval_operand x ss = SOME (val_to_w256 (DecimalV d1)) /\
         eval_operand y ss = SOME (val_to_w256 (DecimalV d2)) ==>
         ?t. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort t)
Proof
  strip_tac >>
  `in_type_range (BaseT DecimalT) d1 /\ in_type_range (BaseT DecimalT) d2` by
    simp[in_type_range_decimal] >>
  qpat_assum `within_int_bound _ d1`
    (mp_then (Pat `within_int_bound _ d1`) mp_tac decimal_scaled_word_facts) >>
  disch_then drule_all >> strip_tac >>
  gvs[MEM] >>
  simp[bop_result_def, evaluate_builtin_def, evaluate_binop_def,
       decimal_sgn_quot, bounded_decimal_op_def, compile_binop_def,
       is_decimal_type_def, decimal_divisor_def, val_to_w256_def]
  >- (Cases_on `within_int_bound (Signed 168) (d1 * d2 quot 10000000000)` >>
      simp[word_value_def, val_to_w256_def] >> rpt strip_tac >>
      drule_all compile_safe_decimal_mul_run >> gvs[in_type_range_decimal]) >>
  Cases_on `d2 = 0` >> simp[]
  >- (rpt strip_tac >> drule_all compile_safe_decimal_div_run >> gvs[]) >>
  Cases_on `within_int_bound (Signed 168)
              (w2i (i2w (d1 * 10000000000) / i2w d2 : bytes32))` >>
  simp[word_value_def, val_to_w256_def, integer_wordTheory.i2w_w2i] >>
  rpt strip_tac >> drule_all compile_safe_decimal_div_run >>
  gvs[in_type_range_decimal]
QED
