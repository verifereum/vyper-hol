(* Decimal truncation: actual-state replay precedes typed continuation assembly. *)
Theory bodyPtrTypeBuiltinsDecimalIntegerContinue
Ancestors bodyPtrTypeBuiltinsIntegerDecimalContinue convertScalarDecimalRun
  bodyPtrTypeBuiltinsCheckedArithmetic exprLowering exprLoweringProps
  varsExt freshWrites emitHelper emitHelperProps venomState venomInst
  venomExecSemantics list rich_list words integer integer_word vyperArith compileEnv
  exprSimConvert vyperValue vyperValueOperation valueEncoding arithmeticProps
  vyperDecimalBounds intExtension vyperAST vyperTyping vyperTypeSystem

Theorem scalar_decimal_integer_replay:
  compile_type_convert x (ConvDecimalToInt divisor ilo ihi lo hi so) sa = (r,sb) ==>
  vars_ext_result
    (run_inst_seq (emitted_insts sa sb) (drop_fresh sa ss))
    (run_inst_seq (emitted_insts sa sb) ss)
Proof
  strip_tac >> irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >>
  Cases_on `so` >> Cases_on `ilo < lo * &divisor` >>
  Cases_on `ihi > hi * &divisor` >>
  gvs[compile_type_convert_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def] >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  simp[emitted_insts_def] >>
  rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, is_terminator_def, is_ext_call_op_def]
QED

Theorem scalar_decimal_integer_actual_run:
  compile_type_convert x
    (ConvDecimalToInt 10000000000 (-&(2**167)) (&(2**167)-1) lo hi T) sa = (r,sb) /\
  eval_operand x ss = SOME (i2w i) /\ (!z. x = Var z ==> not_fresh_at sa z) /\
  within_int_bound decimal_bound i /\ lo <= 0 /\ 0 <= hi ==>
  if lo * decimal_scale <= i /\ i <= hi * decimal_scale then
    ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME (i2w (i quot decimal_scale)) /\
      (sf with vs_vars := ss.vs_vars) = ss /\
      (!z. not_fresh_at sa z ==> lookup_var z sf = lookup_var z ss)
  else ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  strip_tac >>
  `eval_operand x (drop_fresh sa ss) = SOME (i2w i)` by simp[eval_operand_drop_fresh] >>
  `fresh_vars_wrt sa (drop_fresh sa ss)` by simp[fresh_vars_wrt_drop_fresh] >>
  Cases_on `lo * decimal_scale <= i /\ i <= hi * decimal_scale` >> simp[]
  >- (fs[] >> drule_all (SRULE [] scalar_decimal_to_int_ok) >> strip_tac >>
      drule scalar_decimal_integer_replay >> disch_then (qspec_then `ss` mp_tac) >>
      simp[vars_ext_result_def] >> strip_tac >> gvs[] >>
      rename1 `run_inst_seq (emitted_insts sa sb) ss = OK actual` >> conj_tac
      >- (fs[vars_ext_def] >>
          qpat_x_assum `actual = _ with vs_vars := _` SUBST1_TAC >>
          simp[eval_operand_vars_ext]) >>
      irule convert_decimal_runtime_frame >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[]) >>
  drule_all scalar_decimal_to_int_abort >> strip_tac >>
  drule scalar_decimal_integer_replay >> disch_then (qspec_then `ss` mp_tac) >>
  simp[vars_ext_result_def] >> metis_tac[]
QED

Theorem scalar_decimal_integer_compile_eq:
  0 < bo /\ bo <= 256 ==>
  mk_convert_op (BaseT DecimalT) (BaseT (if so then IntT bo else UintT bo)) =
    ConvDecimalToInt 10000000000 (-&(2**167)) (&(2**167)-1)
      (if so then -&(2**(bo-1)) else 0)
      (if so then &(2**(bo-1))-1 else if bo = 256 then &(2**167)-1 else &(2**bo)-1) T
Proof
  strip_tac >>
  `w2i (i2w (-&(2 ** 167)):bytes32) = -&(2 ** 167)` by
    (irule w2i_i2w_neg_pow2 >> simp[]) >>
  `w2i (i2w (&(2 ** 167 - 1)):bytes32) = &(2 ** 167 - 1)` by
    (irule w2i_i2w_pow2_sub1 >> simp[]) >>
  `bo - 1 <= 255` by decide_tac >>
  `w2i (i2w (-&(2 ** (bo-1))):bytes32) = -&(2 ** (bo-1))` by
    (irule w2i_i2w_neg_pow2 >> simp[]) >>
  `w2i (i2w (&(2 ** (bo-1)-1)):bytes32) = &(2 ** (bo-1)-1)` by
    (irule w2i_i2w_pow2_sub1 >> simp[]) >>
  fs[] >> Cases_on `so`
  >- (simp[mk_convert_op_def, type_bounds_def, type_bits_def,
        is_signed_type_def, is_bytestring_type_def] >>
      simp[INT_SUB] >> intLib.ARITH_TAC) >>
  Cases_on `bo = 256`
  >- (gvs[mk_convert_op_def, type_bounds_def, type_bits_def,
        is_signed_type_def, is_bytestring_type_def] >> intLib.ARITH_TAC) >>
  `bo <= 255` by decide_tac >>
  `w2i (n2w (2 ** bo-1):bytes32) = &(2 ** bo-1)` by
    (rewrite_tac[GSYM i2w_pos] >> irule w2i_i2w_pow2_sub1 >> simp[]) >>
  simp[mk_convert_op_def, type_bounds_def, type_bits_def,
       is_signed_type_def, is_bytestring_type_def, INT_SUB] >>
  simp[w2i_eq_w2n]
QED

