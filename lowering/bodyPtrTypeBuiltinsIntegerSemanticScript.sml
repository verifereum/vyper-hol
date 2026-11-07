(* Actual-state integer conversion semantics, independent of scalar typing aggregates. *)
Theory bodyPtrTypeBuiltinsIntegerSemantic
Ancestors exprSimConvert exprLowering exprLoweringProps exprSimDefs exprSimHyps
  bodyPtrTypeBuiltinsScalarChecks varsExt freshWrites emitHelper emitHelperProps
  venomState venomExecSemantics venomInst list rich_list finite_map
  vyperValue vyperValueOperation valueEncoding integer_word words vyperAST
  vyperTypeSystem vyperTyping compileEnv arithmetic

Theorem scalar_integer_replay:
  compile_type_convert x (ConvIntToInt si bi so bo) sa = (r,sb) ==>
  vars_ext_result
    (run_inst_seq (emitted_insts sa sb) (drop_fresh sa ss))
    (run_inst_seq (emitted_insts sa sb) ss)
Proof
  strip_tac >> irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >>
  Cases_on `si` >> Cases_on `so` >> Cases_on `bo < bi` >>
  gvs[compile_type_convert_def, compile_int_clamp_def,
      emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  simp[emitted_insts_def] >>
  rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, is_terminator_def, is_ext_call_op_def]
QED

Theorem scalar_integer_actual_run:
  compile_type_convert x (ConvIntToInt si bi so bo) sa = (r,sb) /\
  eval_operand x ss = SOME (i2w i) /\ (!z. x = Var z ==> not_fresh_at sa z) /\
  within_int_bound (if si then Signed bi else Unsigned bi) i /\
  0 < bi /\ bi <= 256 /\ 0 < bo /\ (so ==> 1 < bo) /\ bo <= 256 ==>
  if within_int_bound (if so then Signed bo else Unsigned bo) i then
    ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME (i2w i) /\ (sf with vs_vars := ss.vs_vars) = ss /\
      (!z. not_fresh_at sa z ==> lookup_var z sf = lookup_var z ss)
  else ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  strip_tac >>
  `eval_operand x (drop_fresh sa ss) = SOME (i2w i)` by simp[eval_operand_drop_fresh] >>
  `fresh_vars_wrt sa (drop_fresh sa ss)` by simp[fresh_vars_wrt_drop_fresh] >>
  drule_all convert_int_run >>
  Cases_on `within_int_bound (if so then Signed bo else Unsigned bo) i` >>
  simp[] >> strip_tac >>
  drule scalar_integer_replay >> disch_then (qspec_then `ss` mp_tac) >>
  simp[vars_ext_result_def] >> strip_tac >> gvs[]
  >- (rename1 `run_inst_seq (emitted_insts sa sb) ss = OK actual` >> conj_tac
      >- (fs[vars_ext_def] >>
          qpat_x_assum `actual = _ with vs_vars := _` SUBST1_TAC >>
          simp[eval_operand_vars_ext]) >>
      irule convert_int_runtime_frame >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any)) >> simp[]
QED

Theorem scalar_integer_typed_actual:
  evaluate_type (get_tenv cx) (BaseT (if si then IntT bi else UintT bi)) = SOME tv /\
  evaluate_type (get_tenv cx) (BaseT (if so then IntT bo else UintT bo)) = SOME tout /\
  value_has_type tv v /\
  compile_type_convert x (mk_convert_op (BaseT (if si then IntT bi else UintT bi))
    (BaseT (if so then IntT bo else UintT bo))) sa = (r,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  eval_operand x ss = SOME (typed_val_to_w256 tv v) ==>
  case convert_result cx (BaseT (if si then IntT bi else UintT bi))
    (BaseT (if so then IntT bo else UintT bo)) v of
    INL out => ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME (typed_val_to_w256 tout out) /\
      (sf with vs_vars := ss.vs_vars) = ss /\
      (!z. not_fresh_at sa z ==> lookup_var z sf = lookup_var z ss)
  | INR ex => (?msg. ex = Error (RuntimeError msg)) /\
      ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  Cases_on `si` >> Cases_on `so` >>
  simp[vyperValueTheory.evaluate_type_def] >> strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def, AllCaseEqs(), mk_convert_op_def,
    is_bytestring_type_def, type_bits_def, type_bounds_def, is_signed_type_def,
    typed_val_to_w256_def, val_to_w256_def] >>
  `0 < bi /\ 0 < bo` by decide_tac >>
  drule scalar_integer_actual_run >> simp[] >>
  disch_then (qspecl_then [`ss`,`i`] mp_tac) >> simp[] >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes, evaluate_convert_def,
       typed_val_to_w256_def, val_to_w256_def] >>
  IF_CASES_TAC >> simp[typed_val_to_w256_def, val_to_w256_def, within_int_bound_def]
QED

Theorem scalar_integer_body_actual:
  expr_body_pre cenv cx env (TypeBuiltin ann Convert dst [e]) es /\
  expr_type e = BaseT (if si then IntT bi else UintT bi) /\
  dst = BaseT (if so then IntT bo else UintT bo) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  evaluate_type (get_tenv cx) dst = SOME tout /\ value_has_type tv v1 /\
  compile_type_convert x (mk_convert_op (expr_type e) dst) sa = (r,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  eval_operand x ss = SOME (typed_val_to_w256 tv v1) ==>
  case convert_result cx (expr_type e) dst v1 of
    INL out => ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME (typed_val_to_w256 tout out) /\
      (sf with vs_vars := ss.vs_vars) = ss /\
      (!z. not_fresh_at sa z ==> lookup_var z sf = lookup_var z ss)
  | INR ex => (?msg. ex = Error (RuntimeError msg)) /\
      ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  strip_tac >> gvs[] >> irule scalar_integer_typed_actual >>
  goal_assum (drule_at Any) >> qexistsl_tac [`tv`,`x`] >> simp[]
QED

(* Remaining scalar coverage inventory (semantic / actual / pointer / summary):
   ConvIdentity: ScalarSemantic.scalar_identity_semantic_packet and
     ScalarContinue.scalar_identity_continuation complete the Bool->Int/Uint case.
   ConvToFlag: ScalarSemantic.scalar_flag_semantic_actual and
     ScalarContinue.scalar_flag_continuation complete the Uint256->Flag case.
   ConvBytesToInt: ScalarSemantic.scalar_fixed_int_all_typed_actual and
     ScalarContinue.scalar_fixed_int_continuation complete all fixed lengths/signs.
   ConvBytesMToDecimal: scalar_fixed_decimal_all_typed_actual and the decimal
     continuation in those same theories are complete, including Fixed0.
   ConvIntToInt: this leaf supplies integer-source actual typed semantics;
     ScalarChecks.convert_int_counted_certificate and its abort/filter/frame
     boundaries exist. Full continuation remains; Address/Flag sources that
     dispatch to ConvIntToInt still need their own typed interpretation adapter.
   ConvToBool: BoolContinue.convert_bool_run_actual is an actual word run;
     Bool has counted pointer certificates. Scalar source encoding/convert_result
     adapter and full scalar continuation remain (bytestring continuation is not it).
   Integer-to-Address: IntegerAddressContinue supplies direct-clamp actual replay
     and typed success/revert semantics for both integer signs. Signed sources
     use ConvToAddress; unsigned sources use ConvIntToInt F bi F 160.
     scalar_integer_address_continuation supplies the full counted pointer summary.
     Do not import Outputs (broken aggregate).
   ConvBytesToAddress: BytesRun.scalar_bytes_address_run_ok/abort supply fresh
     semantics; ScalarArithmetic.convert_bytes_address_eq reduces pointer code
     to unsigned160. Actual semantic packet and summary remain.
   ConvBytesMToBytesM: BytesRun.scalar_bytes_narrow_run_ok/abort and Encoding
     supply raw narrow/widen facts; ScalarChecks supplies counted/frame/filter
     boundaries. All-length typed actual semantics and summary remain.
   ConvIntToBytesM: Outputs.scalar_int_bytes_run requires bits<=8*m (no clamp);
     CheckedArithmetic supplies full success/abort counted/filter/frame boundary.
     General typed actual success/abort semantics and full continuation remain.
   ConvIntToDecimal: IntegerDecimalContinue supplies actual typed success/revert
     semantics and scalar_integer_decimal_continuation for both integer signs.
     It reuses DecimalRun and CheckedArithmetic directly, without Outputs.
   ConvDecimalToInt: DecimalIntegerContinue supplies typed actual success/revert
     semantics and scalar_decimal_integer_continuation for all destination widths,
     including the capped Uint256 compiler case. No aggregate imports needed.
   ConvBoolToDecimal: ScalarArithmetic has pointer facts, but valid_conversion
     forbids this pair; discharge by scalar source/destination typing partition.
   int_convert_pair is NOT just integer-to-integer: exprSimConvert defines it
     to include Bool->Int/Uint (identity, completed) and Int/Uint->Bool
     (ToBool adapter/summary outstanding), as well as this leaf's four sign pairs.
   S1 leaf signatures/ancestry inspected: exprSimConvert.convert_int_run,
     convertScalarBytesRun, convertScalarOutputs (Bytes/Props dependencies),
     convertScalarDecimalRun (Checks/Decimal dependencies). Do not import
     convertScalarTyping, convertScalarDispatch or convertScalarBridge to obtain
     an adapter: their aggregate typing route is unavailable in this task tree.
   This inventory records missing work only; it introduces no dispatcher claim. *)
