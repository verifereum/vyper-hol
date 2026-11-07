(* Integer to Address keeps semantic Address values distinct from uint words. *)
Theory bodyPtrTypeBuiltinsIntegerAddressContinue
Ancestors bodyPtrTypeBuiltinsFixedAddressContinue bodyPtrTypeBuiltinsIntegerContinue
  bodyPtrTypeBuiltinsIntegerSemantic bodyPtrTypeBuiltinsScalarChecks
  convertScalarBytesRun exprSimConvert exprLowering
  exprLoweringProps compileEnv vyperValue vyperValueOperation vyperTyping
  valueEncoding varsExt freshWrites venomState words integer_word byte rich_list list
  exprSimDefs exprSimHyps exprSimProps exprSimWordArgs loweringPosts
  bodyPtrDefs fragGasPathPtr ptrDiscipline emitHelper emitHelperProps instIdxIndep finite_map
  vyperAST bodyPtrTypeBuiltinsUintCounted bodyPtrTypeBuiltinsUintContinue fragExec
  bodyPtrTypeBuiltinsSourceFrame venomInst venomExecSemantics vyperTypeSystem arithmeticProps

Theorem scalar_integer_address_replay:
  compile_type_convert x ConvToAddress sa = (r,sb) ==>
  vars_ext_result
    (run_inst_seq (emitted_insts sa sb) (drop_fresh sa ss))
    (run_inst_seq (emitted_insts sa sb) ss)
Proof
  strip_tac >> irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >>
  gvs[compile_type_convert_def, compile_int_clamp_def,
      emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  simp[emitted_insts_def] >>
  rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, is_terminator_def, is_ext_call_op_def]
QED

Theorem scalar_integer_address_actual_run:
  compile_type_convert x ConvToAddress sa = (r,sb) /\
  eval_operand x ss = SOME (i2w i) /\ (!z. x = Var z ==> not_fresh_at sa z) /\
  -&(2**255) <= i /\ i < &(2**256) ==>
  if within_int_bound (Unsigned 160) i then
    ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME (i2w i) /\ (sf with vs_vars := ss.vs_vars) = ss /\
      (!z. not_fresh_at sa z ==> lookup_var z sf = lookup_var z ss)
  else ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  strip_tac >>
  `eval_operand x (drop_fresh sa ss) = SOME (i2w i)` by simp[eval_operand_drop_fresh] >>
  `fresh_vars_wrt sa (drop_fresh sa ss)` by simp[fresh_vars_wrt_drop_fresh] >>
  `in_type_range (BaseT (UintT 160)) (&w2n (i2w i:bytes32)) <=>
     within_int_bound (Unsigned 160) i` by
    (`(&w2n (i2w i:bytes32):int) = i % &(2**256)` by
       simp[w2n_i2w, dimword_def] >>
     pure_rewrite_tac[SIMP_RULE (srw_ss()) []
       (Q.SPECL [`F`,`160:num`,`&w2n (i2w i:bytes32)`] scalar_int_range)] >>
     pop_assum SUBST1_TAC >> simp[within_int_bound_ineq] >>
     Cases_on `0 <= i`
     >- (fs[integerTheory.INT_MOD_ID] >> intLib.ARITH_TAC) >>
     `i % &(2**256) = i + &(2**256)` by
       (irule integerTheory.INT_MOD_UNIQUE >> qexists_tac `-1` >>
        fs[] >> intLib.ARITH_TAC) >> fs[] >> intLib.ARITH_TAC) >>
  `compile_int_clamp F 160 x sa = (r,sb)` by fs[compile_type_convert_def, compile_int_clamp_def] >>
  Cases_on `within_int_bound (Unsigned 160) i` >> simp[]
  >- (drule (Q.INST [`sg` |-> `F`, `b` |-> `160:num`] scalar_int_clamp_word_ok) >>
      disch_then (qspec_then `drop_fresh sa ss` mp_tac) >> simp[] >> strip_tac >>
      drule scalar_integer_address_replay >> disch_then (qspec_then `ss` mp_tac) >>
      simp[vars_ext_result_def] >> strip_tac >> gvs[] >>
      rename1 `run_inst_seq (emitted_insts sa sb) ss = OK actual` >> conj_tac
      >- (fs[vars_ext_def] >>
          qpat_x_assum `actual = _ with vs_vars := _` SUBST1_TAC >>
          simp[eval_operand_vars_ext]) >>
      irule convert_address_runtime_frame >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any)) >>
  drule (Q.INST [`sg` |-> `F`, `b` |-> `160:num`] scalar_int_clamp_word_abort) >>
  disch_then (qspec_then `drop_fresh sa ss` mp_tac) >> simp[] >> strip_tac >>
  drule scalar_integer_address_replay >> disch_then (qspec_then `ss` mp_tac) >>
  simp[vars_ext_result_def] >> metis_tac[]
QED


Theorem scalar_integer_address_result_word:
  within_int_bound (Unsigned 160) i ==>
  typed_val_to_w256 (BaseTV AddressT) (AddressV (i2w i)) = i2w i
Proof
  strip_tac >>
  `0 <= i /\ i < &(2**160)` by fs[within_int_bound_ineq] >>
  `i = &Num i` by intLib.ARITH_TAC >>
  `Num i < 2**160` by (fs[] >> intLib.ARITH_TAC) >>
  `Num i < dimword(:256)` by (fs[dimword_def] >> decide_tac) >>
  `w2n (i2w i:bytes32) = Num i` by
    (qpat_x_assum `i = &Num i` SUBST1_TAC >> simp[i2w_pos, w2n_n2w]) >>
  mp_tac (Q.INST [`x` |-> `i2w i:bytes32`]
    bodyPtrTypeBuiltinsAddressContinueTheory.bytes_address_encoding) >> fs[] >>
  `i2w i : 160 word = n2w (Num i)` by
    (`i = &Num i` by intLib.ARITH_TAC >>
     pop_assum SUBST1_TAC >> simp[i2w_pos]) >> simp[]
QED

Theorem scalar_integer_address_typed_actual:
  evaluate_type (get_tenv cx) (BaseT (if si then IntT bi else UintT bi)) = SOME tv /\
  evaluate_type (get_tenv cx) (BaseT AddressT) = SOME tout /\
  value_has_type tv v /\
  compile_type_convert x (mk_convert_op (BaseT (if si then IntT bi else UintT bi))
    (BaseT AddressT)) sa = (r,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  eval_operand x ss = SOME (typed_val_to_w256 tv v) ==>
  case convert_result cx (BaseT (if si then IntT bi else UintT bi)) (BaseT AddressT) v of
    INL out => ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME (typed_val_to_w256 tout out) /\
      (sf with vs_vars := ss.vs_vars) = ss /\
      (!z. not_fresh_at sa z ==> lookup_var z sf = lookup_var z ss)
  | INR ex => (?msg. ex = Error (RuntimeError msg)) /\
      ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  Cases_on `si` >> simp[vyperValueTheory.evaluate_type_def] >> strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def, AllCaseEqs(), mk_convert_op_def,
    is_bytestring_type_def, type_bits_def, type_bounds_def, is_signed_type_def,
    typed_val_to_w256_def, val_to_w256_def]
  >- suspend "signed"
  >> suspend "unsigned"
QED

Resume scalar_integer_address_typed_actual[signed]:
  `within_int_bound (Signed 256) i` by
    (irule (SRULE [] (Q.SPECL [`T`,`bi`,`256:num`,`i`] scalar_int_bound_mono)) >>
     qexists_tac `bi` >> simp[]) >>
  `-&(2**255) <= i /\ i < &(2**256)` by
    (fs[within_int_bound_ineq] >> intLib.ARITH_TAC) >>
  drule_all scalar_integer_address_actual_run >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes, evaluate_convert_def] >>
  Cases_on `within_int_bound (Unsigned 160) i` >>
  simp[scalar_integer_address_result_word]
QED

Resume scalar_integer_address_typed_actual[unsigned]:
  `0 < bi` by decide_tac >>
  `within_int_bound (Unsigned bi) i` by fs[within_int_bound_def] >>
  drule scalar_integer_actual_run >> simp[] >>
  disch_then (qspecl_then [`ss`,`i`] mp_tac) >> simp[] >>
  simp[convert_result_def, evaluate_convert_from_not_address_bytes, evaluate_convert_def] >>
  Cases_on `within_int_bound (Unsigned 160) i` >>
  simp[scalar_integer_address_result_word]
QED

Finalise scalar_integer_address_typed_actual
