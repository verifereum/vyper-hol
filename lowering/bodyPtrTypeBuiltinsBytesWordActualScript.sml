Theory bodyPtrTypeBuiltinsBytesWordActual
Ancestors bodyPtrTypeBuiltinsUintActual bodyPtrTypeBuiltinsBytesWordTypes
  exprSimConvertFromBytes freshWrites varsExt exprSimProps
  exprLowering exprLoweringProps emitHelper emitHelperProps compileEnv loweringStateRelDefs
  venomExecSemantics venomInst venomState finite_map rich_list list

Theorem bytes_word_code_frame:
  (conv = ConvBytestringToBool \/ (?m. conv = ConvBytestringToBytesM m) \/
    (?b n. conv = ConvBytestringToInt F b n)) /\
  compile_type_convert op conv sa = (r,sb) ==>
  EVERY (\i. (fresh_write_op i.inst_opcode \/ i.inst_opcode = MLOAD) /\
             EVERY (\x. ~not_fresh_at sa x) i.inst_outputs)
        (emitted_insts sa sb)
Proof
  strip_tac >> gvs[] >>
  TRY (Cases_on `8*n > b`) >>
  gvs[compile_type_convert_def, load_bytestring_as_word_def, compile_int_clamp_def,
      emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  simp[emitted_insts_def] >>
  rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, fresh_write_op_def, not_fresh_at_def,
       ASCIInumbersTheory.toString_inj] >>
  rpt strip_tac >> decide_tac
QED

Theorem bytes_word_unsigned_code_frame:
  is_bytestring_type src /\ ~is_bytestring_type dst /\ valid_conversion src dst /\
  ~((?b. dst = BaseT (IntT b)) \/ dst = BaseT DecimalT) /\
  compile_type_convert op (mk_convert_op src dst) sa = (r,sb) ==>
  EVERY (\i. (fresh_write_op i.inst_opcode \/ i.inst_opcode = MLOAD) /\
             EVERY (\x. ~not_fresh_at sa x) i.inst_outputs)
        (emitted_insts sa sb)
Proof
  strip_tac >> drule_all bytestring_scalar_type_partition >> strip_tac >>
  gvs[mk_convert_op_def, is_bytestring_type_def] >>
  irule bytes_word_code_frame >> goal_assum (drule_at Any) >> simp[]
QED

Theorem bytes_word_unsigned_replay:
  is_bytestring_type src /\ ~is_bytestring_type dst /\ valid_conversion src dst /\
  ~((?b. dst = BaseT (IntT b)) \/ dst = BaseT DecimalT) /\
  compile_type_convert op (mk_convert_op src dst) sa = (r,sb) ==>
  vars_ext_result
    (run_inst_seq (emitted_insts sa sb) (drop_fresh sa ss))
    (run_inst_seq (emitted_insts sa sb) ss)
Proof
  strip_tac >> drule_all bytes_word_unsigned_code_frame >> disch_tac >>
  irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >>
  gvs[fresh_write_op_def, venomInstTheory.is_terminator_def,
      venomInstTheory.is_ext_call_op_def]
QED

Theorem bytes_word_unsigned_run_frame:
  is_bytestring_type src /\ ~is_bytestring_type dst /\ valid_conversion src dst /\
  ~((?b. dst = BaseT (IntT b)) \/ dst = BaseT DecimalT) /\
  compile_type_convert op (mk_convert_op src dst) sa = (r,sb) /\
  run_inst_seq (emitted_insts sa sb) ss = OK sf ==>
  sf = ss with vs_vars := sf.vs_vars /\
  (!z. not_fresh_at sa z ==> FLOOKUP sf.vs_vars z = FLOOKUP ss.vs_vars z)
Proof
  strip_tac >> drule_all bytes_word_unsigned_code_frame >> strip_tac >>
  drule_all readonly_run_frame >> simp[]
QED

Theorem bytes_word_semantic_run_actual:
  is_bytestring_type src /\ ~is_bytestring_type dst /\ valid_conversion src dst /\
  ~((?b. dst = BaseT (IntT b)) \/ dst = BaseT DecimalT) /\
  well_formed_type tenv dst /\
  evaluate_type (get_tenv cx) src = SOME stv /\ value_has_type stv v /\
  convert_result cx src dst v = res /\
  compile_type_convert op (mk_convert_op src dst) sa = (r,sb) /\
  (!z. op = Var z ==> not_fresh_at sa z) /\ eval_operand op ss = SOME a /\
  w2n a+32 < dimword(:256) /\ val_in_memory stv v (w2n a) ss.vs_memory ==>
  case res of
  | INL vout => ?dtv sf. evaluate_type (get_tenv cx) dst = SOME dtv /\
      run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME (typed_val_to_w256 dtv vout) /\
      sf = ss with vs_vars := sf.vs_vars /\
      (!z w. not_fresh_at sa z /\ lookup_var z ss = SOME w ==>
             lookup_var z sf = SOME w)
  | INR ex => (?m. ex = Error (RuntimeError m)) /\
      ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  strip_tac >>
  `fresh_vars_wrt sa (drop_fresh sa ss)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand op (drop_fresh sa ss) = SOME a` by simp[eval_operand_drop_fresh] >>
  `val_in_memory stv v (w2n a) (drop_fresh sa ss).vs_memory` by
    simp[drop_fresh_def] >>
  drule_all dynamic_scalar_run_exact >>
  Cases_on `res` >> simp[] >> strip_tac
  >- (drule_all bytes_word_unsigned_replay >> disch_then (qspec_then `ss` mp_tac) >>
      simp[vars_ext_result_def] >> strip_tac >>
      rename1 `run_inst_seq (emitted_insts sa sb) ss = OK actual` >>
      `actual = ss with vs_vars := actual.vs_vars /\
       (!z. not_fresh_at sa z ==> FLOOKUP actual.vs_vars z = FLOOKUP ss.vs_vars z)` by
        (irule bytes_word_unsigned_run_frame >>
         goal_assum (drule_at Any) >> metis_tac[]) >>
      qexists_tac `actual` >> simp[] >> conj_tac
      >- (fs[vars_ext_def] >>
          qpat_x_assum `actual = sf with vs_vars := _` SUBST1_TAC >>
          simp[eval_operand_vars_ext]) >>
      rpt strip_tac >> fs[lookup_var_def]) >>
  drule_all bytes_word_unsigned_replay >> disch_then (qspec_then `ss` mp_tac) >>
  simp[vars_ext_result_def] >> metis_tac[]
QED
