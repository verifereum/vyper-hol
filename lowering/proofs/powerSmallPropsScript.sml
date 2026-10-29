(* The primitive bases and exponents, on arbitrary operands and states. *)
Theory powerSmallProps
Ancestors
  powerGuardProps powerRunProps powerTypedCounterexample
  exprLowering compileEnv emitHelper emitHelperProps exprLoweringProps
  venomExecSemantics venomState words integer_word integer
  vyperValueOperation vyperValue vyperArith arithmetic
Libs
  wordsLib

Theorem power_bind_return[simp]:
  (do v <- m; return v od) = m
Proof
  simp[FUN_EQ_THM, comp_bind_def, comp_return_def, pairTheory.UNCURRY]
QED

Theorem power_bind_return_left[simp]:
  (do v <- return a; f v od) = f a
Proof
  simp[FUN_EQ_THM, comp_bind_def, comp_return_def]
QED

Theorem power_bind_assoc[simp]:
  (do b <- (do a <- m; f a od); g b od) =
  (do a <- m; b <- f a; g b od)
Proof
  simp[FUN_EQ_THM, comp_bind_def] >> gen_tac >>
  Cases_on `m x` >> simp[]
QED

Theorem compile_safe_pow_primitive_exponent_run:
  compile_safe_pow x y ty NONE (SOME (&n)) st = (op,st') /\
  (n = 0 \/ n = 1) /\ (~is_signed_type ty \/ type_bits ty <> 1) /\
  eval_operand x ss = SOME (i2w a) /\ eval_operand y ss = SOME (n2w n) /\
  fresh_vars_wrt st ss ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
        eval_operand op ss' = SOME (i2w (a ** n))
Proof
  strip_tac >>
  `(do emit_void ASSERT [Lit 1w]; emit_op Exp [x;y] od) st = (op,st')`
    by (qpat_x_assum `compile_safe_pow _ _ _ _ _ _ = _` mp_tac >>
        simp[compile_safe_pow_def] >> gvs[]) >>
  `eval_operand (Lit 1w) ss = SOME 1w` by simp[eval_operand_lit] >>
  drule_all power_assert_exp_run >>
  simp[word_exp_i2w, dimword_def, EVAL ``dimindex (:256)``]
QED

Theorem power_small_in_bound:
  (a = -1 \/ a = 0 \/ a = 1) /\
  (if signed then 1 < bits else 0 < bits) /\
  within_int_bound (if signed then Signed bits else Unsigned bits) a ==>
  within_int_bound (if signed then Signed bits else Unsigned bits) (a ** n)
Proof
  strip_tac >> Cases_on `signed` >> gvs[within_int_bound_def] >>
  Cases_on `EVEN n` >>
  simp[INT_EXP_NEG, INT_EXP, ZERO_EXP, ODD_EVEN, within_int_bound_def] >>
  Cases_on `n = 0` >> simp[]
QED

Theorem compile_safe_pow_small_base_run:
  compile_safe_pow x y ty (SOME a) el st = (op,st') /\
  (a = -1 \/ a = 0 \/ a = 1) /\
  (~is_signed_type ty \/ type_bits ty <> 1) /\
  eval_operand x ss = SOME (i2w a) /\ eval_operand y ss = SOME (i2w e) /\
  (is_signed_type ty ==> within_int_bound (Signed 256) e) /\
  (~is_signed_type ty ==> 0 <= e) /\ Num e < dimword (:256) /\
  fresh_vars_wrt st ss ==>
  (0 <= e ==> ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
                         eval_operand op ss' = SOME (i2w (a ** Num e))) /\
  (e < 0 ==> ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss')
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_signed_type ty`
  >- (fs[] >> (
      qpat_x_assum `compile_safe_pow _ _ _ _ _ _ = _` mp_tac >>
      simp[compile_safe_pow_def] >> strip_tac >>
      `((i2w e : bytes32) < 0w) <=> e < 0` by
        (drule w2i_i2w_within_signed >> simp[WORD_LTi, word_0_w2i]) >>
      drule_all power_nonnegative_exp_run >>
      Cases_on `0 <= e`
      >- (`i2w e = (n2w (Num e) : bytes32)` by
            (simp[GSYM i2w_pos] >> AP_TERM_TAC >> ONCE_REWRITE_TAC[EQ_SYM_EQ] >> simp[]) >>
          simp[word_exp_i2w, INT_NOT_LT] >> metis_tac[]) >>
      simp[INT_NOT_LE] >> metis_tac[])) >>
  fs[] >> qpat_x_assum `compile_safe_pow _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_safe_pow_def] >> strip_tac >>
  `eval_operand (Lit 1w) ss = SOME 1w` by simp[eval_operand_lit] >>
  drule_all power_assert_exp_run >>
  `i2w e = (n2w (Num e) : bytes32)` by (simp[GSYM i2w_pos] >> AP_TERM_TAC >> ONCE_REWRITE_TAC[EQ_SYM_EQ] >> simp[]) >>
  simp[word_exp_i2w, GSYM INT_NOT_LE]
QED
