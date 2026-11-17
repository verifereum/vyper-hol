(* Shared proof facts for the joint TypeBuiltin constructor ports. *)
Theory typeBuiltinPrereqs
Ancestors
  exprSimConvert exprUnopSimDefs fragGasFresh gasContext gasSummary
  gasOutcome gasStorage vyperStorageTrace vyperStorageFootprint gasSummaryCompose
  gasExemptCert fragGasPath fragGasMode exprWordOperand exprSimSource
  exprSimProps exprSimHypsDefs exprSimDefs exprSimStack loweringPosts
  allocLimits exprSimUnop arithmetic list integer
  words integer_word fragExec varsExt freshWrites
  exprSimOps exprSimArith exprBopLowering loweringSlice exprLowering
  emitHelper emitHelperProps exprLoweringProps arithmeticProps compileEnv
  vyperAST vyperInterpreter vyperState vyperContext vyperValue
  vyperValueOperation vyperArith valueEncoding venomExecSemantics venomInst
  venomState exprSimHyps exprSimOperators vyperTyping vyperTypeSystem
  vyperTypeCallGraph exprSimExtract32Run exprSimHashBoundary exprSimExtract32Read exprSimExtract32Value
  convertScalarOutputs exprSimHash builtinBytes builtinProps valueEncodingDefs
  rich_list exprSimBufferEmptyExec abiEmptySequence loweringHalt exprSimAlloc
  exprSimBuffer exprSimBufferEmpty builtinSimple exprSimBufferStore exprSimLiteralBuffer
  valueEncodingProps exprSimWordArgs loweringStateRelDefs context augAssignPtrScalarClamp
  augAssignPtrScalarEmit augAssignPtrScalarCertificate pred_set

Theorem zero_convert_child_post:
  expr_post H ctx func cenv cx e es sa s1 s0 ee v1 x s /\
  is_word_type ann /\ evaluate_type (get_tenv cx) ann = SOME tv /\
  typed_val_to_w256 tv v = 0w ==>
  expr_post H ctx func cenv cx (TypeBuiltin ann Convert ann [e]) es sa s1 s0
    ee v (Lit 0w) s
Proof
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       expr_type_def, eval_operand_def] >> metis_tac[]
QED

Theorem extract32_tail_run_any:
  extract32_result_base_ok bt /\
  (case bt of UintT k => k <= 256 | IntT k => 0 < k /\ k <= 256 |
    BytesT (Fixed k) => k <= 32 | _ => T) /\
  val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p s.vs_memory /\
  LENGTH bs < dimword(:256) /\ n < dimword(:256) /\
  p+32+LENGTH bs < dimword(:256) /\
  eval_operand len s = SOME (n2w (LENGTH bs)) /\
  eval_operand dp s = SOME (n2w (p+32)) /\ eval_operand off s = SOME (n2w n) /\
  (!z. len = Var z \/ dp = Var z \/ off = Var z ==> not_fresh_at sa z) /\
  compile_extract32_load len dp off sa = (raw,sm) /\
  compile_clamp_basetype raw (BaseT bt) sm = (op,sb) ==>
  case evaluate_extract32 bs n bt of
    INL v => ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME (typed_val_to_w256 (BaseTV bt) v)
  | INR err => ?msg t. err = RuntimeError msg /\
      run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
Proof
  strip_tac >>
  `eval_operand len (drop_fresh sa s) = SOME (n2w (LENGTH bs)) /\
   eval_operand dp (drop_fresh sa s) = SOME (n2w (p+32)) /\
   eval_operand off (drop_fresh sa s) = SOME (n2w n)` by
    metis_tac[eval_operand_drop_fresh] >>
  `val_in_memory (BaseTV (BytesT (Dynamic m))) (BytesV bs) p
     (drop_fresh sa s).vs_memory` by simp[drop_fresh_def] >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  `EVERY (\j. ~is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE /\
     ~is_ext_call_op j.inst_opcode) (emitted_insts sa sb)` by
    (drule_all extract32_tail_straight_noext >> simp[EVERY_MEM]) >>
  `vars_ext_result (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s))
     (run_inst_seq (emitted_insts sa sb) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh]) >>
  Cases_on `evaluate_extract32 bs n bt`
  >- suspend "success" >> suspend "error"
QED

Resume extract32_tail_run_any[success]:
  `?v. run_inst_seq (emitted_insts sa sb) (drop_fresh sa s) = OK v /\
       eval_operand op v = SOME (typed_val_to_w256 (BaseTV bt) x)` by
    (drule_all extract32_tail_success >> metis_tac[]) >>
  gvs[vars_ext_result_def] >>
  gvs[vars_ext_def] >>
  drule eval_operand_vars_ext >> disch_then (qspec_then `op` mp_tac) >> simp[] >>
  metis_tac[]
QED

Resume extract32_tail_run_any[error]:
  `?msg. y = RuntimeError msg` by
    (irule extract32_error_runtime >> goal_assum (drule_at Any) >>
     Cases_on `bt` >> gvs[]) >> gvs[] >>
  `LENGTH bs < dimword(:256) /\ p+32+LENGTH bs < dimword(:256)` by decide_tac >>
  `?v. run_inst_seq (emitted_insts sa sb) (drop_fresh sa s) =
     Abort Revert_abort v` by
    (drule_all extract32_tail_error >> metis_tac[]) >>
  gvs[vars_ext_result_def] >> metis_tac[]
QED

Finalise extract32_tail_run_any

Theorem empty_buffer_compile_prefix:
  !sz header sa sb buf func.
    compile_builtin_empty_complex sz header sa = (buf,sb) /\
    fn_has_code sa sb func ==>
    ?sm p. compile_alloc_buffer sz sa = (buf,sm) /\
      buf.buf_operand = Var p /\ not_fresh_at sm p /\
      (if header then emit_void MSTORE [Var p; Lit 0w]
       else compile_zero_words (Var p) ((sz+31) DIV 32)) sm = ((),sb) /\
      fn_has_code sa sm func /\
      emitted_insts sa sm = [mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]] /\
      emitted_insts sa sb =
        mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p] :: emitted_insts sm sb
Proof
  rpt gen_tac >> strip_tac >>
  `?sm. compile_alloc_buffer sz sa = (buf,sm) /\
    (if header then emit_void MSTORE [buf.buf_operand; Lit 0w]
     else compile_zero_words buf.buf_operand ((sz+31) DIV 32)) sm = ((),sb)` by
    (qpat_x_assum `compile_builtin_empty_complex sz header sa = (buf,sb)` mp_tac >>
     simp[compile_builtin_empty_complex_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> rename1 `compile_alloc_buffer sz sa = (ba,sm)` >>
     simp[] >> Cases_on `header` >>
     simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     pairarg_tac >> rename1 `_ = (u,st)` >> Cases_on `u` >> simp[] >>
     strip_tac >> gvs[] >> qexists_tac `sm` >> simp[]) >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  `inst_extends sm sb /\ sb.cs_blocks = sm.cs_blocks /\
    sb.cs_current_bb = sm.cs_current_bb` by suspend "tail" >>
  qexistsl_tac [`sm`, `STRING #"%" (toString sa.cs_next_var)`] >>
  gvs[] >> rpt conj_tac
  >- suspend "code"
  >- simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  gvs[inst_extends_def] >>
  simp_tac (srw_ss()) [Once emitted_insts_def] >>
  qpat_x_assum `sb.cs_current_insts = _` (fn th => rewrite_tac[th]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >> REFL_TAC
QED
Resume empty_buffer_compile_prefix[tail]:
  Cases_on `header` >> gvs[]
  >- (drule inst_extends_emit_void >> strip_tac >> simp[] >>
      gvs[emit_void_def, fresh_id_def, emit_def, comp_bind_def, comp_return_def]) >>
  metis_tac[abi_empty_zero_words_shape]
QED
Resume empty_buffer_compile_prefix[code]:
  fs[fn_has_code_def, inst_extends_def, emitted_blocks_def] >>
  qpat_x_assum `isPREFIX _ _` mp_tac >>
  rpt (pop_assum kall_tac) >> metis_tac[IS_PREFIX_APPEND, APPEND_ASSOC]
QED
Finalise empty_buffer_compile_prefix

Theorem scalar_clamp_basetype_code:
  compile_clamp_basetype raw typ sa = (result,sb) /\ scalar_available A raw ==>
  scalar_code A (emitted_insts sa sb)
Proof
  strip_tac >> Cases_on `typ` >>
  gvs[compile_clamp_basetype_def, comp_return_def, emitted_insts_refl, scalar_code_def] >>
  Cases_on `b`
  >~ [`compile_clamp_basetype raw (BaseT (UintT n)) sa = _`] >-
    (Cases_on `n < 256` >>
     gvs[compile_clamp_basetype_def, comp_return_def, emitted_insts_refl, scalar_code_def] >>
     drule_all scalar_clamp_and_return_code >> simp[])
  >~ [`compile_clamp_basetype raw (BaseT (IntT n)) sa = _`] >-
    (Cases_on `n < 256` >>
     gvs[compile_clamp_basetype_def, comp_return_def, emitted_insts_refl, scalar_code_def] >>
     drule_all scalar_clamp_and_return_code >> simp[])
  >~ [`compile_clamp_basetype raw (BaseT (BytesT bt)) sa = _`] >-
    (Cases_on `bt` >>
     gvs[compile_clamp_basetype_def, comp_return_def, emitted_insts_refl, scalar_code_def,
         AllCaseEqs()] >> suspend "bytes") >>
  gvs[compile_clamp_basetype_def, comp_return_def, emitted_insts_refl, scalar_code_def] >>
  suspend "address"
QED

Resume scalar_clamp_basetype_code[bytes]:
  Cases_on `n < 32` >> gvs[comp_return_def, emitted_insts_refl, scalar_code_def] >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def,
      emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def] >>
  simp[emitted_insts_def] >> rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND,
       scalar_code_def, scalar_shape_def, scalar_binary_def, scalar_unary_def,
       mk_inst_def, scalar_available_def] >>
  gvs[scalar_available_def]
QED

Resume scalar_clamp_basetype_code[address]:
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def,
      emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def] >>
  simp[emitted_insts_def] >> rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND,
       scalar_code_def, scalar_shape_def, scalar_binary_def, scalar_unary_def,
       mk_inst_def, scalar_available_def] >>
  gvs[scalar_available_def]
QED
Finalise scalar_clamp_basetype_code
