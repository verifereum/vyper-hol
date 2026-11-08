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

(* Scalar partition inventory (current valid_conversion; dynamic Bytes/String
   sources belong to the separate bytestring continuation family).

   Source -> destination       compiler operation        complete continuation
   Bool -> Int/Uint            Identity                  ScalarContinue.scalar_identity_continuation
   Int/Uint -> Int/Uint         IntToInt                  IntegerContinue.scalar_integer_continuation
   Int/Uint -> Bool            ToBool                    IntegerBoolContinue.scalar_integer_bool_continuation
   Int/Uint -> Address         ToAddress/IntToInt        IntegerAddressContinue.scalar_integer_address_continuation
   Int/Uint -> fixed bytes     IntToBytesM               IntegerBytesContinue.scalar_integer_bytes_continuation
   Int/Uint -> Decimal         IntToDecimal              IntegerDecimalContinue.scalar_integer_decimal_continuation
   Decimal -> Int/Uint         DecimalToInt              DecimalIntegerContinue.scalar_decimal_integer_continuation
   fixed bytes -> Int/Uint     BytesToInt                ScalarContinue.scalar_fixed_int_continuation
   fixed bytes -> Decimal      BytesMToDecimal           ScalarContinue.scalar_fixed_decimal_continuation
   fixed bytes -> Address      BytesToAddress            FixedAddressContinue.scalar_fixed_address_continuation
   fixed bytes -> fixed bytes  BytesMToBytesM            FixedBytesContinue.scalar_fixed_fixed_continuation
   Uint256 -> Flag             ToFlag (cenv dispatch)    ScalarContinue.scalar_flag_continuation

   MISSING typed adapters and full continuations:
   fixed bytes -> Bool: ToBool; BoolContinue.convert_bool_run_actual and
     IntegerBoolContinue.scalar_bool_counted_success are reusable. Need
     typed fixed-word zero iff EVERY zero byte, including Fixed0.
   Address -> Uint: IntToInt F 160 F bits. Address is represented by BytesV
     of length 20, NOT IntV. IntegerSemantic.scalar_integer_actual_run and
     IntegerContinue.scalar_integer_counted_success provide raw/count support;
     need decoding to unsigned160, typed semantic guard and result encoding.
   Address -> fixed bytes: IntToBytesM F 160 m, valid only 20<=m<=32.
     IntegerBytesRun.integer_bytes_actual_run and
     IntegerBytesContinue.scalar_integer_bytes_counted_success apply to code.
     Need evaluate_convert_from's PAD_LEFT address rule (not scalar IntV's DROP).
   Flag -> Uint256: IntToInt F 256 F 256; Flag -> fixed32: IntToBytesM F 256 32.
     Need FlagTV/FlagV typing and n2w encoding adapters and full summaries.
     Encoding.scalar_flag_encoding/scalar_flag_to_bytes32 support them; integer raw/count
     certificates alone do not prove source interpretation.

   Exhaustiveness is by vyperTypeSystem.valid_conversion_def: Bool has ONLY
   Int/Uint destinations, Decimal ONLY Int/Uint; Address ONLY Uint/fixed bytes;
   Flag ONLY Uint256/fixed32. Fixed->fixed excludes equal lengths. Int/Uint to
   fixed requires bits<=8*m; hence no typed narrowing and no m=0 with positive
   integer widths. BoolToDecimal and Bool/Decimal->fixed compiler constructors
   exist but are typing-invalid. No Address->Int or Flag->Int is valid either.
   int_convert_pair includes Bool->Int/Uint and Int/Uint->Bool, all completed.
   This inventory does not claim a complete dispatcher; do not import broken
   convertScalarOutputs/Typing/Dispatch/Bridge aggregates to fill these gaps. *)
