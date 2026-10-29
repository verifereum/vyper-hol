(* Unsigned checked power: emitted execution agrees with evaluate_binop on
   the literal-exponent >= 2 and literal-base >= 2 branches, including revert
   before EXP on mathematical overflow. Small bases/exponents and signed
   power are not certified here; this is not full expression simulation.
   TOP-LEVEL: compile_safe_pow_unsigned_exponent/base_correct,
   power_uint256_overflow_reverts, and reusable guard/EXP run lemmas.
   No arithmetic simulation admission is used. *)
Theory powerRunProps
Ancestors
  exprLowering exprLoweringProps emitHelper emitHelperProps compileEnv
  venomExecSemantics venomState venomInst words integer_word arithmetic powerBoundProps
  vyperValueOperation vyperValue
Libs
  pairLib wordsLib

val power_word_size = EVAL ``dimindex (:256)``;

Theorem power_unsigned_source_result:
  evaluate_binop (Unsigned bits) tv Exp (IntV (&a)) (IntV (&n)) =
    if a ** n < 2 ** bits then INL (IntV (&(a ** n)))
    else INR (RuntimeError "bounded_int_op bound")
Proof
  simp[evaluate_binop_def, bounded_int_op_def, within_int_bound_def,
       integerTheory.INT_EXP]
QED

(* EVM EXP is the word image of mathematical integer exponentiation when
   the nonnegative exponent is represented without wrapping. *)
Theorem word_exp_i2w:
  !a n. n < dimword (:256) ==>
    word_exp (i2w a : bytes32) (n2w n) = i2w (a ** n)
Proof
  `!n a. (n2w (w2n (i2w a : bytes32) ** n) : bytes32) = i2w (a ** n)` by
    (Induct >> simp[EXP, integerTheory.int_exp, i2w_pos, GSYM word_mul_n2w,
                   GSYM integer_wordTheory.word_i2w_mul]) >>
  simp[word_exp_def]
QED

Theorem step_Exp:
  eval_operand x ss = SOME a /\ eval_operand y ss = SOME b ==>
  step_inst_base (mk_inst id Exp [x; y] [out]) ss =
    OK (update_var out (word_exp a b) ss)
Proof
  rw[step_inst_base_def] >> irule exec_pure2_ok >> rw[]
QED

Theorem emit_op_Exp_correct:
  emit_op Exp [x; y] st = (op, st') /\
  eval_operand x ss = SOME a /\ eval_operand y ss = SOME b /\
  fresh_vars_wrt st ss ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
        eval_operand op ss' = SOME (word_exp a b) /\
        same_blocks st st' /\ fresh_vars_wrt st' ss' /\
        (!op w. eval_operand op ss = SOME w ==> eval_operand op ss' = SOME w) /\
        (!a. a < LENGTH ss.vs_memory ==> EL a ss'.vs_memory = EL a ss.vs_memory) /\
        LENGTH ss'.vs_memory = LENGTH ss.vs_memory
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`Exp`, `word_exp`, `x`, `y`, `a`, `b`,
                  `st`, `op`, `st'`, `ss`] emit_op_pure2_correct) >>
  simp[step_Exp]
QED

Theorem power_upper_check_passes:
  emit_op GT [y; Lit bound] st0 = (above, st1) /\
  emit_op ISZERO [above] st1 = (ok, st2) /\
  emit_void ASSERT [ok] st2 = ((), st3) /\
  eval_operand y ss = SOME b /\ w2n b <= w2n bound /\
  fresh_vars_wrt st0 ss ==>
  ?ss'. run_inst_seq (emitted_insts st0 st3) ss = OK ss' /\
        fresh_vars_wrt st3 ss' /\
        st3.cs_current_insts = st0.cs_current_insts ++ emitted_insts st0 st3 /\
        (!op w. eval_operand op ss = SOME w ==> eval_operand op ss' = SOME w) /\
        same_blocks st0 st3
Proof
  strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) [eval_operand_lit]
    (Q.INST [`op2` |-> `Lit bound`, `v2` |-> `bound`] (SPEC_ALL emit_op_GT_correct))) >>
  disch_then (qx_choose_then `s1` strip_assume_tac) >>
  drule_all emit_op_ISZERO_correct >>
  disch_then (qx_choose_then `s2` strip_assume_tac) >>
  `eval_operand ok s2 = SOME 1w` by gvs[bool_to_word_def] >>
  `(1w : bytes32) <> 0w` by simp[] >>
  drule_all emit_void_ASSERT_ok_full >> strip_tac >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  mp_tac (Q.SPECL [`st0`, `st1`, `st2`, `ss`, `s1`] run_inst_seq_chain) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `run_inst_seq (emitted_insts st0 st2) ss = OK s2` by gvs[] >>
  mp_tac (Q.SPECL [`st0`, `st2`, `st3`, `ss`, `s2`] run_inst_seq_chain) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexists_tac `s2` >> simp[] >> fs[same_blocks_def] >> metis_tac[]
QED

Theorem power_upper_check_reverts:
  emit_op GT [y; Lit bound] st0 = (above, st1) /\
  emit_op ISZERO [above] st1 = (ok, st2) /\
  emit_void ASSERT [ok] st2 = ((), st3) /\
  eval_operand y ss = SOME b /\ w2n bound < w2n b /\
  fresh_vars_wrt st0 ss ==>
  ?ss'. run_inst_seq (emitted_insts st0 st3) ss = Abort Revert_abort ss'
Proof
  strip_tac >>
  drule_all (SIMP_RULE (srw_ss()) [eval_operand_lit]
    (Q.INST [`op2` |-> `Lit bound`, `v2` |-> `bound`] (SPEC_ALL emit_op_GT_correct))) >>
  disch_then (qx_choose_then `s1` strip_assume_tac) >>
  drule_all emit_op_ISZERO_correct >>
  disch_then (qx_choose_then `s2` strip_assume_tac) >>
  `eval_operand ok s2 = SOME 0w` by gvs[bool_to_word_def] >>
  drule_all emit_void_ASSERT_revert >> strip_tac >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  mp_tac (Q.SPECL [`st0`, `st1`, `st2`, `ss`, `s1`] run_inst_seq_chain) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `run_inst_seq (emitted_insts st0 st2) ss = OK s2` by gvs[] >>
  mp_tac (Q.SPECL [`st0`, `st2`, `st3`, `ss`, `s2`] run_inst_seq_chain) >>
  (impl_tac >- simp[]) >> strip_tac >> gvs[]
QED

Theorem power_upper_checked_run:
  (do above <- emit_op GT [checked; Lit bound];
      ok <- emit_op ISZERO [above];
      emit_void ASSERT [ok];
      emit_op Exp [x; y] od) st = (op, st') /\
  eval_operand x ss = SOME a /\ eval_operand y ss = SOME b /\
  eval_operand checked ss = SOME c /\ fresh_vars_wrt st ss ==>
  (w2n c <= w2n bound ==>
   ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
         eval_operand op ss' = SOME (word_exp a b)) /\
  (w2n bound < w2n c ==>
   ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss')
Proof
  strip_tac >>
  gvs[comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op Exp [x; y] st3 = (op, st')` >> conj_tac >> strip_tac
  >- (drule_all power_upper_check_passes >>
      disch_then (qx_choose_then `s3` strip_assume_tac) >>
      `eval_operand x s3 = SOME a /\ eval_operand y s3 = SOME b` by metis_tac[] >>
      drule_all emit_op_Exp_correct >> strip_tac >>
      imp_res_tac emit_op_extends >>
      drule_all run_inst_seq_chain >> strip_tac >> gvs[]) >>
  drule_all power_upper_check_reverts >> strip_tac >>
  imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends st st3` by metis_tac[inst_extends_trans] >>
  drule_all run_inst_seq_abort_extends >> strip_tac >> gvs[]
QED

(* For a literal exponent >= 2, the unsigned guard accepts exactly the
   mathematical powers inside the type, before EVM EXP can wrap. *)
Theorem compile_safe_pow_unsigned_exponent_run:
  compile_safe_pow x y ty NONE (SOME (&n)) st = (op, st') /\
  ~is_signed_type ty /\ type_bits ty <= 256 /\ 2 <= n /\
  a < dimword (:256) /\ n < dimword (:256) /\
  eval_operand x ss = SOME (n2w a) /\ eval_operand y ss = SOME (n2w n) /\
  fresh_vars_wrt st ss ==>
  (a ** n < 2 ** type_bits ty ==>
   ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
         eval_operand op ss' = SOME (n2w (a ** n))) /\
  (~(a ** n < 2 ** type_bits ty) ==>
   ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss')
Proof
  strip_tac >>
  `0 < n /\ n <> 0 /\ n <> 1` by simp[] >>
  `largest_pow_base n (type_bits ty) F < 2 ** type_bits ty` by
    (mp_tac (Q.SPECL [`n`, `type_bits ty`, `F`] largest_pow_base_lt_limit) >> simp[]) >>
  `largest_pow_base n (type_bits ty) F < dimword (:256)` by
    (irule LESS_LESS_EQ_TRANS >> qexists_tac `2 ** type_bits ty` >>
     simp[dimword_def, power_word_size]) >>
  `a <= largest_pow_base n (type_bits ty) F <=> a ** n < 2 ** type_bits ty`
    by simp[largest_pow_base_characterisation] >>
  qpat_x_assum `compile_safe_pow _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_safe_pow_def] >> strip_tac >>
  drule_all power_upper_checked_run >>
  simp[word_exp_def, w2n_n2w]
QED

Theorem compile_safe_pow_unsigned_exponent_correct:
  compile_safe_pow x y ty NONE (SOME (&n)) st = (op, st') /\
  ~is_signed_type ty /\ type_bits ty <= 256 /\ 2 <= n /\
  a < dimword (:256) /\ n < dimword (:256) /\
  eval_operand x ss = SOME (n2w a) /\ eval_operand y ss = SOME (n2w n) /\
  fresh_vars_wrt st ss ==>
  (?r ss'. evaluate_binop (Unsigned (type_bits ty)) tv Exp (IntV (&a)) (IntV (&n)) =
              INL (IntV r) /\
            run_inst_seq (emitted_insts st st') ss = OK ss' /\
            eval_operand op ss' = SOME (i2w r)) \/
  (?m ss'. evaluate_binop (Unsigned (type_bits ty)) tv Exp (IntV (&a)) (IntV (&n)) =
              INR (RuntimeError m) /\
            run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss')
Proof
  strip_tac >> drule_all compile_safe_pow_unsigned_exponent_run >> strip_tac >>
  Cases_on `a ** n < 2 ** type_bits ty` >>
  fs[power_unsigned_source_result, i2w_pos] >> metis_tac[]
QED

(* A literal unsigned base >= 2 permits a dynamic exponent.  The guard
   rejects overflow before EXP, rather than clamping a wrapped result. *)
Theorem compile_safe_pow_unsigned_base_run:
  compile_safe_pow x y ty (SOME (&a)) el st = (op, st') /\
  ~is_signed_type ty /\ type_bits ty <= 256 /\
  2 <= a /\ a < 2 ** type_bits ty /\ n < dimword (:256) /\
  eval_operand x ss = SOME (n2w a) /\ eval_operand y ss = SOME (n2w n) /\
  fresh_vars_wrt st ss ==>
  (a ** n < 2 ** type_bits ty ==>
   ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
         eval_operand op ss' = SOME (n2w (a ** n))) /\
  (~(a ** n < 2 ** type_bits ty) ==>
   ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss')
Proof
  strip_tac >>
  `1 < a /\ a <> 0 /\ a <> 1` by simp[] >>
  `a < dimword (:256)` by
    (irule LESS_LESS_EQ_TRANS >> qexists_tac `2 ** type_bits ty` >>
     simp[dimword_def, power_word_size]) >>
  `largest_pow_exponent a (type_bits ty) F < type_bits ty` by
    (mp_tac (Q.SPECL [`a`, `type_bits ty`, `F`] largest_pow_exponent_lt_bits) >> simp[]) >>
  `largest_pow_exponent a (type_bits ty) F < dimword (:256)` by
    (simp[dimword_def, power_word_size] >> decide_tac) >>
  `n <= largest_pow_exponent a (type_bits ty) F <=>
   a ** n < 2 ** type_bits ty` by
    simp[largest_pow_exponent_characterisation] >>
  qpat_x_assum `compile_safe_pow _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_safe_pow_def] >> strip_tac >>
  drule_all power_upper_checked_run >>
  simp[word_exp_def, w2n_n2w]
QED

Theorem compile_safe_pow_unsigned_base_correct:
  compile_safe_pow x y ty (SOME (&a)) el st = (op, st') /\
  ~is_signed_type ty /\ type_bits ty <= 256 /\
  2 <= a /\ a < 2 ** type_bits ty /\ n < dimword (:256) /\
  eval_operand x ss = SOME (n2w a) /\ eval_operand y ss = SOME (n2w n) /\
  fresh_vars_wrt st ss ==>
  (?r ss'. evaluate_binop (Unsigned (type_bits ty)) tv Exp (IntV (&a)) (IntV (&n)) =
              INL (IntV r) /\
            run_inst_seq (emitted_insts st st') ss = OK ss' /\
            eval_operand op ss' = SOME (i2w r)) \/
  (?m ss'. evaluate_binop (Unsigned (type_bits ty)) tv Exp (IntV (&a)) (IntV (&n)) =
              INR (RuntimeError m) /\
            run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss')
Proof
  strip_tac >> drule_all compile_safe_pow_unsigned_base_run >> strip_tac >>
  Cases_on `a ** n < 2 ** type_bits ty` >>
  fs[power_unsigned_source_result, i2w_pos] >> metis_tac[]
QED

Theorem power_uint256_overflow_reverts:
  (compile_safe_pow x y (BaseT (UintT 256)) NONE (SOME 256) st = (op, st') \/
   compile_safe_pow x y (BaseT (UintT 256)) (SOME 2) NONE st = (op, st')) /\
  eval_operand x ss = SOME 2w /\ eval_operand y ss = SOME 256w /\
  fresh_vars_wrt st ss ==>
  evaluate_binop (Unsigned 256) tv Exp (IntV 2) (IntV 256) =
    INR (RuntimeError "bounded_int_op bound") /\
  ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  simp[compile_safe_pow_def, type_bits_def, is_signed_type_def,
       power_uint256_overflow_bounds, power_unsigned_source_result] >>
  rpt strip_tac >> drule_all power_upper_checked_run >> simp[]
QED
