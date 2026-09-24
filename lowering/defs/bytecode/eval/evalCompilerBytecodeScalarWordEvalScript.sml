(* Checked opaque-word accelerators for scalar bytecode parity evaluation. *)

Theory evalCompilerBytecodeScalarWordEval
Ancestors compileVyper integer_word
Libs computeLib wordsLib

(* Keep DecimalT's 168-bit signed bounds opaque as words during pipeline
   evaluation. Their numeric values are exposed only where code generation
   asks for w2n, avoiding enormous set_byte normal forms. *)
Definition scalar_decimal_lo_word_def[nocompute]:
  scalar_decimal_lo_word : bytes32 = i2w (-&(2 ** 167))
End

Definition scalar_decimal_hi_word_def[nocompute]:
  scalar_decimal_hi_word : bytes32 = i2w (&(2 ** 167 - 1))
End

Theorem scalar_decimal_type_bounds_eval:
  type_bounds (BaseT DecimalT) =
    (scalar_decimal_lo_word, scalar_decimal_hi_word)
Proof
  simp[compileEnvTheory.type_bounds_def,
       compileEnvTheory.type_bits_def, compileEnvTheory.is_signed_type_def,
       scalar_decimal_lo_word_def, scalar_decimal_hi_word_def]
QED

Theorem w2n_i2w_neg_bytes32:
  ∀i. i < 0 ∧ -&(dimword (:256)) < i ⇒
    w2n ((i2w i) : bytes32) = Num (i + &(dimword (:256)))
Proof
  rpt strip_tac >>
  `&(w2n ((i2w i) : bytes32)) = i % &(dimword (:256))` by
    simp[integer_wordTheory.w2n_i2w] >>
  `0 < dimword (:256)` by simp[wordsTheory.ZERO_LT_dimword] >>
  `&(dimword (:256)) ≠ (0:int)` by intLib.ARITH_TAC >>
  `0 ≤ i + &(dimword (:256)) ∧
   i + &(dimword (:256)) < &(dimword (:256))` by intLib.ARITH_TAC >>
  `(i + &(dimword (:256))) % &(dimword (:256)) =
   i + &(dimword (:256))` by simp[integerTheory.INT_LESS_MOD] >>
  `(-1 * &(dimword (:256)) + (i + &(dimword (:256)))) %
     &(dimword (:256)) =
   (i + &(dimword (:256))) % &(dimword (:256))` by
    simp[integerTheory.INT_MOD_ADD_MULTIPLES] >>
  `-1 * &(dimword (:256)) + (i + &(dimword (:256))) = i` by
    intLib.ARITH_TAC >>
  `0 ≤ i + &(dimword (:256))` by intLib.ARITH_TAC >>
  `&(w2n ((i2w i) : bytes32)) = i + &(dimword (:256))` by
    metis_tac[] >>
  metis_tac[integerTheory.NUM_OF_INT, integerTheory.INT_INJ]
QED

Theorem w2n_scalar_decimal_lo_word_eval:
  w2n scalar_decimal_lo_word = 2 ** 256 - 2 ** 167
Proof
  PURE_REWRITE_TAC [scalar_decimal_lo_word_def] >>
  `w2n ((i2w (-&(2 ** 167))) : bytes32) =
   Num (-&(2 ** 167) + &(dimword (:256)))` by
    (irule w2n_i2w_neg_bytes32 >>
     simp[wordsTheory.dimword_def] >> EVAL_TAC) >>
  pop_assum SUBST1_TAC >>
  EVAL_TAC
QED

Theorem w2n_scalar_decimal_hi_word_eval:
  w2n scalar_decimal_hi_word = 2 ** 167 - 1
Proof
  PURE_REWRITE_TAC [scalar_decimal_hi_word_def] >> EVAL_TAC
QED

Theorem w2i_scalar_decimal_lo_word_eval[compute]:
  w2i scalar_decimal_lo_word = -&(2 ** 167)
Proof
  PURE_REWRITE_TAC [scalar_decimal_lo_word_def] >>
  irule integer_wordTheory.w2i_i2w >> EVAL_TAC
QED

Theorem w2i_scalar_decimal_hi_word_eval[compute]:
  w2i scalar_decimal_hi_word = &(2 ** 167 - 1)
Proof
  PURE_REWRITE_TAC [scalar_decimal_hi_word_def] >>
  irule integer_wordTheory.w2i_i2w >> EVAL_TAC
QED

Theorem scalar_decimal_lo_word_eq_word[compute]:
  ((scalar_decimal_lo_word : bytes32) = w) =
  (2 ** 256 - 2 ** 167 = w2n w)
Proof
  PURE_REWRITE_TAC [GSYM wordsTheory.w2n_11,
                    w2n_scalar_decimal_lo_word_eval] >> REFL_TAC
QED

Theorem word_eq_scalar_decimal_lo_word[compute]:
  ((w : bytes32) = scalar_decimal_lo_word) =
  (w2n w = 2 ** 256 - 2 ** 167)
Proof
  PURE_REWRITE_TAC [GSYM wordsTheory.w2n_11,
                    w2n_scalar_decimal_lo_word_eval] >> REFL_TAC
QED

Theorem scalar_decimal_hi_word_eq_word[compute]:
  ((scalar_decimal_hi_word : bytes32) = w) =
  (2 ** 167 - 1 = w2n w)
Proof
  PURE_REWRITE_TAC [GSYM wordsTheory.w2n_11,
                    w2n_scalar_decimal_hi_word_eval] >> REFL_TAC
QED

Theorem word_eq_scalar_decimal_hi_word[compute]:
  ((w : bytes32) = scalar_decimal_hi_word) =
  (w2n w = 2 ** 167 - 1)
Proof
  PURE_REWRITE_TAC [GSYM wordsTheory.w2n_11,
                    w2n_scalar_decimal_hi_word_eval] >> REFL_TAC
QED

Definition scalar_int256_min_word_def[nocompute]:
  scalar_int256_min_word : bytes32 = i2w (-&(2 ** 255))
End

Definition scalar_int256_max_word_def[nocompute]:
  scalar_int256_max_word : bytes32 = i2w (&(2 ** 255 - 1))
End

Theorem scalar_int256_type_bounds_eval:
  type_bounds (BaseT (IntT 256)) =
    (scalar_int256_min_word, scalar_int256_max_word)
Proof
  simp[compileEnvTheory.type_bounds_def,
       compileEnvTheory.type_bits_def, compileEnvTheory.is_signed_type_def,
       scalar_int256_min_word_def, scalar_int256_max_word_def]
QED

Theorem w2n_scalar_int256_min_word_eval:
  w2n scalar_int256_min_word = 2 ** 255
Proof
  PURE_REWRITE_TAC [scalar_int256_min_word_def] >>
  `w2n ((i2w (-&(2 ** 255))) : bytes32) =
   Num (-&(2 ** 255) + &(dimword (:256)))` by
    (irule w2n_i2w_neg_bytes32 >>
     simp[wordsTheory.dimword_def] >> EVAL_TAC) >>
  pop_assum SUBST1_TAC >> EVAL_TAC
QED

Theorem w2i_scalar_int256_min_word_eval[compute]:
  w2i scalar_int256_min_word = -&(2 ** 255)
Proof
  PURE_REWRITE_TAC [scalar_int256_min_word_def] >>
  irule integer_wordTheory.w2i_i2w >> EVAL_TAC
QED

Theorem w2n_scalar_int256_max_word_eval[compute]:
  w2n scalar_int256_max_word = 2 ** 255 - 1
Proof
  PURE_REWRITE_TAC [scalar_int256_max_word_def] >> EVAL_TAC
QED

Theorem w2i_scalar_int256_max_word_eval[compute]:
  w2i scalar_int256_max_word = &(2 ** 255 - 1)
Proof
  PURE_REWRITE_TAC [scalar_int256_max_word_def] >>
  irule integer_wordTheory.w2i_i2w >> EVAL_TAC
QED

Theorem scalar_int256_min_word_eq_word[compute]:
  ((scalar_int256_min_word : bytes32) = w) = (2 ** 255 = w2n w)
Proof
  PURE_REWRITE_TAC [GSYM wordsTheory.w2n_11,
                    w2n_scalar_int256_min_word_eval] >> REFL_TAC
QED

Theorem word_eq_scalar_int256_min_word[compute]:
  ((w : bytes32) = scalar_int256_min_word) = (w2n w = 2 ** 255)
Proof
  PURE_REWRITE_TAC [GSYM wordsTheory.w2n_11,
                    w2n_scalar_int256_min_word_eval] >> REFL_TAC
QED

Theorem scalar_int256_max_word_eq_word[compute]:
  ((scalar_int256_max_word : bytes32) = w) = (2 ** 255 - 1 = w2n w)
Proof
  PURE_REWRITE_TAC [GSYM wordsTheory.w2n_11,
                    w2n_scalar_int256_max_word_eval] >> REFL_TAC
QED

Theorem word_eq_scalar_int256_max_word[compute]:
  ((w : bytes32) = scalar_int256_max_word) = (w2n w = 2 ** 255 - 1)
Proof
  PURE_REWRITE_TAC [GSYM wordsTheory.w2n_11,
                    w2n_scalar_int256_max_word_eval] >> REFL_TAC
QED

Theorem scalar_int8_type_bounds_eval:
  type_bounds (BaseT (IntT 8)) = (i2w (-128), i2w 127)
Proof
  simp[compileEnvTheory.type_bounds_def,
       compileEnvTheory.type_bits_def, compileEnvTheory.is_signed_type_def]
QED

Theorem scalar_mk_convert_decimal_to_int256_eval:
  mk_convert_op (BaseT DecimalT) (BaseT (IntT 256)) =
    ConvDecimalToInt 10000000000
      (-&(2 ** 167)) (&(2 ** 167 - 1))
      (-&(2 ** 255)) (&(2 ** 255 - 1)) T
Proof
  simp[exprLoweringTheory.mk_convert_op_def,
       compileEnvTheory.is_bytestring_type_def,
       scalar_decimal_type_bounds_eval,
       scalar_int256_type_bounds_eval,
       w2i_scalar_decimal_lo_word_eval,
       w2i_scalar_decimal_hi_word_eval,
       w2i_scalar_int256_min_word_eval,
       w2i_scalar_int256_max_word_eval]
QED

Theorem scalar_compile_convert_decimal_to_int256_eval:
  ∀v.
    compile_type_convert v
      (ConvDecimalToInt 10000000000
        (-&(2 ** 167)) (&(2 ** 167 - 1))
        (-&(2 ** 255)) (&(2 ** 255 - 1)) T) =
    emit_op SDIV [v; Lit (n2w 10000000000)]
Proof
  simp[exprLoweringTheory.compile_type_convert_def] >>
  simp[FUN_EQ_THM, compileEnvTheory.comp_return_def,
       compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def] >> EVAL_TAC
QED

Theorem scalar_mk_convert_decimal_to_int8_eval:
  mk_convert_op (BaseT DecimalT) (BaseT (IntT 8)) =
    ConvDecimalToInt 10000000000
      (-&(2 ** 167)) (&(2 ** 167 - 1)) (-128) 127 T
Proof
  simp[exprLoweringTheory.mk_convert_op_def,
       compileEnvTheory.is_bytestring_type_def,
       scalar_decimal_type_bounds_eval,
       scalar_int8_type_bounds_eval,
       w2i_scalar_decimal_lo_word_eval,
       w2i_scalar_decimal_hi_word_eval,
       integer_wordTheory.w2i_i2w] >> EVAL_TAC
QED

Theorem scalar_compile_convert_decimal_to_int8_eval:
  ∀v.
    compile_type_convert v
      (ConvDecimalToInt 10000000000
        (-&(2 ** 167)) (&(2 ** 167 - 1)) (-128) 127 T) =
    do too_small <- emit_op SLT [v; Lit (i2w (-1280000000000))];
       ok1 <- emit_op ISZERO [too_small];
       emit_void ASSERT [ok1];
       too_big <- emit_op SGT [v; Lit (i2w 1270000000000)];
       ok2 <- emit_op ISZERO [too_big];
       emit_void ASSERT [ok2];
       emit_op SDIV [v; Lit (n2w 10000000000)]
    od
Proof
  simp[exprLoweringTheory.compile_type_convert_def] >> EVAL_TAC >>
  simp[compileEnvTheory.comp_bind_assoc]
QED

Theorem scalar_dispatch_convert_decimal_literal_to_int8_eval:
  ∀cenv vv_ty ty st.
    compile_type_builtin_dispatch cenv vv_ty ty Convert (BaseT (IntT 8))
      [Literal (BaseT DecimalT) (DecimalL 10000000000)] st =
    as_stack_val vv_ty
      (compile_type_convert (Lit (i2w 10000000000))
        (ConvDecimalToInt 10000000000
          (-&(2 ** 167)) (&(2 ** 167 - 1)) (-128) 127 T) st)
Proof
  simp[exprLoweringTheory.compile_expr_def,
       exprLoweringTheory.lower_value_def,
       exprLoweringTheory.compile_literal_vv_def,
       vyperASTTheory.expr_type_def,
       exprLoweringTheory.unwrap_value_def,
       exprLoweringTheory.as_stack_val_def,
       scalar_mk_convert_decimal_to_int8_eval,
       compileEnvTheory.comp_return_def,
       compileEnvTheory.comp_bind_def]
QED

Theorem scalar_compile_expr_decimal_literal_to_int8_eval:
  ∀cenv ty st.
    compile_expr cenv ty
      (TypeBuiltin (BaseT (IntT 8)) Convert (BaseT (IntT 8))
        [Literal (BaseT DecimalT) (DecimalL 10000000000)]) st =
    as_stack_val (BaseT (IntT 8))
      (compile_type_convert (Lit (i2w 10000000000))
        (ConvDecimalToInt 10000000000
          (-&(2 ** 167)) (&(2 ** 167 - 1)) (-128) 127 T) st)
Proof
  simp[exprLoweringTheory.compile_expr_def,
       vyperASTTheory.expr_type_def,
       scalar_dispatch_convert_decimal_literal_to_int8_eval]
QED

Theorem scalar_mk_convert_int8_to_decimal_eval:
  mk_convert_op (BaseT (IntT 8)) (BaseT DecimalT) =
    ConvIntToDecimal T 8 10000000000
      (-&(2 ** 167)) (&(2 ** 167 - 1))
Proof
  simp[exprLoweringTheory.mk_convert_op_def,
       compileEnvTheory.is_bytestring_type_def,
       scalar_decimal_type_bounds_eval,
       w2i_scalar_decimal_lo_word_eval,
       w2i_scalar_decimal_hi_word_eval]
QED

Theorem scalar_compile_convert_int8_to_decimal_eval:
  ∀v.
    compile_type_convert v
      (ConvIntToDecimal T 8 10000000000
        (-&(2 ** 167)) (&(2 ** 167 - 1))) =
    emit_op MUL [v; Lit (n2w 10000000000)]
Proof
  simp[exprLoweringTheory.compile_type_convert_def] >> EVAL_TAC >>
  simp[FUN_EQ_THM, compileEnvTheory.comp_return_def,
       compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def]
QED

Theorem scalar_dispatch_convert_int8_literal_to_decimal_eval:
  ∀cenv vv_ty ty st.
    compile_type_builtin_dispatch cenv vv_ty ty Convert (BaseT DecimalT)
      [Literal (BaseT (IntT 8)) (IntL 1)] st =
    as_stack_val vv_ty
      (compile_type_convert (Lit (i2w 1))
        (ConvIntToDecimal T 8 10000000000
          (-&(2 ** 167)) (&(2 ** 167 - 1))) st)
Proof
  simp[exprLoweringTheory.compile_expr_def,
       exprLoweringTheory.lower_value_def,
       exprLoweringTheory.compile_literal_vv_def,
       vyperASTTheory.expr_type_def,
       exprLoweringTheory.unwrap_value_def,
       exprLoweringTheory.as_stack_val_def,
       scalar_mk_convert_int8_to_decimal_eval,
       compileEnvTheory.comp_return_def,
       compileEnvTheory.comp_bind_def]
QED

Theorem scalar_compile_expr_int8_literal_to_decimal_eval:
  ∀cenv ty st.
    compile_expr cenv ty
      (TypeBuiltin (BaseT DecimalT) Convert (BaseT DecimalT)
        [Literal (BaseT (IntT 8)) (IntL 1)]) st =
    as_stack_val (BaseT DecimalT)
      (compile_type_convert (Lit (i2w 1))
        (ConvIntToDecimal T 8 10000000000
          (-&(2 ** 167)) (&(2 ** 167 - 1))) st)
Proof
  simp[exprLoweringTheory.compile_expr_def,
       vyperASTTheory.expr_type_def,
       scalar_dispatch_convert_int8_literal_to_decimal_eval]
QED

Theorem scalar_mk_convert_bytes32_to_decimal_eval:
  mk_convert_op (BaseT (BytesT (Fixed 32))) (BaseT DecimalT) =
    ConvBytesMToDecimal 32 10000000000
      (-&(2 ** 167)) (&(2 ** 167 - 1))
Proof
  simp[exprLoweringTheory.mk_convert_op_def,
       compileEnvTheory.is_bytestring_type_def,
       scalar_decimal_type_bounds_eval,
       w2i_scalar_decimal_lo_word_eval,
       w2i_scalar_decimal_hi_word_eval]
QED

Theorem scalar_compile_convert_bytes32_to_decimal_eval:
  ∀v.
    compile_type_convert v
      (ConvBytesMToDecimal 32 10000000000
        (-&(2 ** 167)) (&(2 ** 167 - 1))) =
    do shifted <- emit_op SAR [Lit 0w; v];
       too_small <- emit_op SLT [shifted; Lit scalar_decimal_lo_word];
       ok1 <- emit_op ISZERO [too_small];
       too_big <- emit_op SGT [shifted; Lit scalar_decimal_hi_word];
       ok2 <- emit_op ISZERO [too_big];
       ok <- emit_op AND [ok1; ok2];
       emit_void ASSERT [ok];
       return shifted
    od
Proof
  simp[exprLoweringTheory.compile_type_convert_def,
       scalar_decimal_lo_word_def, scalar_decimal_hi_word_def]
QED
