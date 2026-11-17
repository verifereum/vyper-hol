(* Shared proof facts for the joint TypeBuiltin constructor ports. *)
Theory typeBuiltinPrereqs
Ancestors
  exprOpenFirstOperand vyperTypeCallStackSoundness supportedExprTraverse
  bodyMemAssignTopCopyIndex fragExecMem instMemFrontier bodyMemAssignTopCopyFacts fragGasSeqMem
  memSafeRun exprSimWordBuiltins bodyUnopFragMemory exprSimConvertFromBytes fragGasPathMem
  bodyLiteralBufferMemory abiEmptyAllocate allocaFootprint venomMemDefs venomMemProps
  allocaHistoryFragment builtinBytesMemory exprSimMemDefs exprOperandVar vyperTypeConversions
  exprSimBopRestWordLoadPath fragGasSeqAbort unitTransformDefs contextCodegenRel codegenRel
  exprCallbackContracts exprCallBounds finite_map ASCIInumbers
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

Theorem convert_load_bytestring_mem_ok:
  load_bytestring_as_word v opc sa = ((r,k),sb) /\
  (opc = SHR \/ opc = SAR) /\ eval_operand v s = SOME w /\
  (!x. v = Var x ==> not_fresh_at sa x) /\
  alloca_inv s /\ w2n w + 64 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  rpt strip_tac >>
  gvs[load_bytestring_as_word_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  `!j. LENGTH sa.cs_current_insts - (LENGTH sa.cs_current_insts + j) = 0` by decide_tac >>
  simp[emitted_insts_def, DROP_APPEND] >>
  simp[Once run_inst_seq_mem_ok_cons] >>
  simp[below_frontier_MLOAD, mk_inst_def, inst_dload_in_section_def,
       step_inst_base_opcode_eqs, exec_read1_def, eval_operands_def] >>
  `!n z. sa.cs_next_var <= n ==>
     eval_operand v (update_var (STRING #"%" (toString n)) z s) = SOME w` by
    metis_tac[eval_operand_update_not_fresh] >>
  `!n. sa.cs_next_var <= n ==> v <> Var (STRING #"%" (toString n))` by
    (rpt strip_tac >> gvs[loweringStateRelDefsTheory.not_fresh_at_def] >>
     metis_tac[]) >>
  once_rewrite_tac[run_inst_seq_mem_ok_cons] >>
  (conj_tac >- (irule below_frontier_no_ranges >> simp[])) >>
  simp[inst_dload_in_section_def] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq_mem_ok tail` >>
  pure_rewrite_tac[step_inst_base_def] >>
  simp_tac (srw_ss()) [] >>
  pure_rewrite_tac[exec_pure2_def, eval_operands_def] >>
  simp[] >>
  unabbrev_all_tac >>
  simp[Once run_inst_seq_mem_ok_cons, GSYM mk_inst_def,
       below_frontier_MLOAD, eval_operand_def] >>
  (conj_tac >-
    (simp[lookup_var_update_var, update_var_def] >>
     mp_tac (Q.INST [`b` |-> `w`, `n` |-> `2`, `i` |-> `1`]
       topcopy_index_bound) >>
     simp[WORD_MULT_CLAUSES])) >>
  Cases_on `step_inst_base
    (mk_inst (sa.cs_next_id + 2) MLOAD
      [Var (STRING #"%" (toString (sa.cs_next_var + 1)))]
      [STRING #"%" (toString (sa.cs_next_var + 2))])
    (update_var (STRING #"%" (toString (sa.cs_next_var + 1))) (w + 32w)
      (update_var (STRING #"%" (toString sa.cs_next_var)) (mload (w2n w) s) s))` >>
  simp[] >> irule run_inst_seq_mem_ok_every >>
  simp[inst_dload_in_section_def] >> rpt conj_tac >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem convert_load_straight_suffix_mem_ok[local]:
  load_bytestring_as_word x opc sa = ((r,k),sm) /\
  (opc = SHR \/ opc = SAR) /\ straight_fresh f /\ f sm = (op,sb) /\
  eval_operand x s = SOME p /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  alloca_inv s /\ w2n p + 64 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sm) s` by
    (irule convert_load_bytestring_mem_ok >> metis_tac[]) >>
  `sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm` by
    (gvs[load_bytestring_as_word_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
     simp[emitted_insts_def, DROP_APPEND]) >>
  fs[straight_fresh_def] >>
  first_x_assum drule >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  pop_assum SUBST1_TAC >> irule run_inst_seq_mem_ok_append >> simp[] >>
  rpt strip_tac >> irule writes_fresh_mem_ok >> metis_tac[]
QED

Theorem convert_bytestring_scalar_ops_mem_ok:
  (cop = ConvBytestringToBool \/
   (?sg b n. cop = ConvBytestringToInt sg b n) \/
   (?d lo hi n. cop = ConvBytestringToDecimal d lo hi n) \/
   (?m. cop = ConvBytestringToBytesM m)) /\
  compile_type_convert x cop sa = (op,sb) /\
  eval_operand x s = SOME p /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  alloca_inv s /\ w2n p + 64 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> gvs[] >>
  qpat_x_assum `compile_type_convert _ _ _ = _` mp_tac >>
  simp[Once compile_type_convert_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  irule (INST_TYPE [``:'a`` |-> ``:operand``]
    convert_load_straight_suffix_mem_ok) >> simp[] >>
  goal_assum (drule_at (Pat `load_bytestring_as_word _ _ _ = _`)) >>
  qmatch_asmsub_abbrev_tac `suffix cs' = (op,sb)` >>
  qexists_tac `suffix` >> simp[] >>
  simp[Abbr `suffix`] >>
  rpt (FIRST [irule straight_fresh_bind >> conj_tac,
    gen_tac >> BETA_TAC,
    irule straight_fresh_emit_op >> simp[fresh_write_op_def] >> NO_TAC,
    irule straight_fresh_emit_void >> simp[fresh_write_op_def] >> NO_TAC,
    irule straight_fresh_return,
    IF_CASES_TAC,
    CHANGED_TAC (simp[compile_int_clamp_def, comp_ignore_bind_def])])
QED

Theorem convert_dynamic_scalar_mem_ok:
  is_bytestring_type src /\ ~is_bytestring_type dst /\
  valid_conversion src dst /\ well_formed_type tenv dst /\
  compile_type_convert x (mk_convert_op src dst) sa = (op,sb) /\
  eval_operand x s = SOME p /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  alloca_inv s /\ w2n p + 64 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  qpat_x_assum `is_bytestring_type src` mp_tac >>
  Cases_on `src` >> simp[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_bytestring_type_def]
  >- (drule_all dynamic_string_scalar_partition >> strip_tac >> gvs[] >>
      irule convert_bytestring_scalar_ops_mem_ok >>
      simp[] >> metis_tac[dynamic_scalar_convert_ops]) >>
  rename1 `BytesT bd` >> Cases_on `bd` >> simp[is_bytestring_type_def] >>
  drule_all dynamic_bytes_scalar_partition >> strip_tac >> gvs[] >>
  irule convert_bytestring_scalar_ops_mem_ok >> simp[] >>
  metis_tac[dynamic_scalar_convert_ops, dynamic_decimal_convert_op]
QED

Theorem convert_bytestring_cast_mem_ok:
  compile_type_convert v (ConvBytestringCast n k) sa = (op,sb) /\
  eval_operand v s = SOME w /\
  w2n w + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  Cases_on `n < k` >>
  gvs[compile_type_convert_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
      fresh_id_def, emit_def, emitted_insts_def]
  >- (`!j. LENGTH sa.cs_current_insts - (LENGTH sa.cs_current_insts + j) = 0`
        by decide_tac >>
      simp[DROP_APPEND, Once run_inst_seq_mem_ok_cons, mk_inst_def,
           below_frontier_MLOAD, inst_dload_in_section_def,
           step_inst_base_def, exec_read1_def, eval_operands_def] >>
      rewrite_tac[GSYM mk_inst_def] >>
      (conj_tac >- simp[below_frontier_MLOAD]) >>
      irule run_inst_seq_mem_ok_every >>
      simp[inst_dload_in_section_def] >> rpt conj_tac >>
      irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  simp[run_inst_seq_mem_ok_def]
QED

Theorem compile_zero_words_no_gas:
  !n pop sa sb.
    compile_zero_words pop n sa = ((),sb) ==>
    EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  Induct >- simp[compile_zero_words_def, comp_return_def, emitted_insts_def] >>
  rpt gen_tac >>
  simp_tac bool_ss [Once compile_zero_words_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_zero_words pop n sa = (ignored,sm)` >>
  Cases_on `ignored:unit` >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  drule abi_empty_zero_words_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `LENGTH sa.cs_current_insts <= LENGTH sm.cs_current_insts` by
    (fs[inst_extends_def] >> metis_tac[LENGTH_APPEND, LESS_EQ_ADD]) >>
  `LENGTH sa.cs_current_insts - LENGTH sm.cs_current_insts = 0` by decide_tac >>
  `LENGTH sa.cs_current_insts - (LENGTH sm.cs_current_insts + 1) = 0` by decide_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++
    [mk_inst sm.cs_next_id ADD [pop; Lit (n2w (32*n))]
      [STRING #"%" (toString sm.cs_next_var)];
     mk_inst cs''.cs_next_id MSTORE [dst; Lit 0w] []]` by
    simp[emitted_insts_def, DROP_APPEND, LENGTH_APPEND] >>
  asm_rewrite_tac[] >> simp[mk_inst_def]
QED

Theorem compile_zero_words_seq_mem:
  !n pop sa sb s w.
    compile_zero_words pop n sa = ((),sb) /\
    eval_operand pop s = SOME w /\
    (!x. pop = Var x ==> not_fresh_at sa x) /\
    w2n w + 32*n <= s.vs_alloca_next /\
    w2n w + 32*n < dimword (:256) ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    (!t. run_inst_seq (emitted_insts sa sb) s = OK t ==>
      t.vs_alloca_next = s.vs_alloca_next /\ eval_operand pop t = SOME w)
Proof
  Induct >- simp[compile_zero_words_def, comp_return_def,
    emitted_insts_def, run_inst_seq_mem_ok_def, run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_zero_words _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once compile_zero_words_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_zero_words pop n sa = (ignored,sm)` >>
  Cases_on `ignored:unit` >> gvs[] >>
  first_x_assum (qspecl_then [`pop`, `sa`, `sm`, `s`, `w`] mp_tac) >>
  impl_tac >- (simp[] >> decide_tac) >> strip_tac >>
  drule abi_empty_zero_words_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `LENGTH sa.cs_current_insts <= LENGTH sm.cs_current_insts` by
    (fs[inst_extends_def] >> metis_tac[LENGTH_APPEND, LESS_EQ_ADD]) >>
  `LENGTH sa.cs_current_insts - LENGTH sm.cs_current_insts = 0` by decide_tac >>
  `LENGTH sa.cs_current_insts - (LENGTH sm.cs_current_insts + 1) = 0` by decide_tac >>
  `LENGTH sm.cs_current_insts - (LENGTH sm.cs_current_insts + 1) = 0` by decide_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (simp[emitted_insts_def, DROP_APPEND, LENGTH_APPEND, SUB_EQ_0]) >>
  `emitted_insts sm sb =
    [mk_inst sm.cs_next_id ADD [pop; Lit (n2w (32*n))]
       [STRING #"%" (toString sm.cs_next_var)];
     mk_inst cs''.cs_next_id MSTORE [dst; Lit 0w] []]` by
    gvs[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `!t. run_inst_seq (emitted_insts sa sm) s = OK t ==>
     run_inst_seq_mem_ok (emitted_insts sm sb) t /\
     (!u. run_inst_seq (emitted_insts sm sb) t = OK u ==>
       u.vs_alloca_next = s.vs_alloca_next /\ eval_operand pop u = SOME w)` by
    (gen_tac >> disch_tac >>
     first_x_assum drule >> strip_tac >>
     qabbrev_tac `p = STRING #"%" (toString sm.cs_next_var)` >>
     `step_inst_base (mk_inst sm.cs_next_id ADD [pop; Lit (n2w (32*n))] [p]) t =
       OK (update_var p (w + n2w (32*n)) t)` by
       (irule step_ADD >> simp[eval_operand_def]) >>
     `w2n (w + n2w (32*n)) = w2n w + 32*n` by
       (`w2n w + 32*n < dimword (:256)` by decide_tac >>
        `32*n < dimword (:256)` by decide_tac >>
        simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w, LESS_MOD]) >>
     conj_tac
     >- (asm_rewrite_tac[] >>
         simp[run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last,
           below_frontier_MSTORE, eval_operand_def, lookup_var_update_var,
           update_var_def] >>
         simp[mk_inst_def, below_frontier_no_ranges, lookup_var_def,
           FLOOKUP_UPDATE] >> rpt strip_tac >> gvs[] >> decide_tac) >>
     `step_inst_base (mk_inst cs''.cs_next_id MSTORE [Var p; Lit 0w] [])
        (update_var p (w + n2w (32*n)) t) =
        OK (mstore (w2n (w + n2w (32*n))) 0w
          (update_var p (w + n2w (32*n)) t))` by
       (irule step_MSTORE >> simp[eval_operand_def, lookup_var_update_var]) >>
     gen_tac >> disch_tac >>
     `u = mstore (w2n (w + n2w (32*n))) 0w
          (update_var p (w + n2w (32*n)) t)` by
       (qpat_x_assum `run_inst_seq (emitted_insts sm sb) t = OK u` mp_tac >>
        gvs[] >> simp[run_inst_seq_def]) >>
     conj_tac >- simp[mstore_def, update_var_def] >>
     Cases_on `pop` >>
     gvs[eval_operand_def, mstore_def, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE, not_fresh_at_def, Abbr `p`] >>
     NO_TAC) >>
  conj_tac
  >- (qpat_x_assum `emitted_insts sa sb = _` SUBST1_TAC >>
      irule run_inst_seq_mem_ok_append >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      rpt strip_tac >> first_x_assum drule >> gvs[]) >>
  gen_tac >> disch_tac >>
  Cases_on `run_inst_seq (emitted_insts sa sm) s`
  >- (drule run_inst_seq_append >>
      disch_then (qspec_then `emitted_insts sm sb` assume_tac) >>
      gvs[] >> metis_tac[]) >>
  `!u. run_inst_seq (emitted_insts sa sm) s <> OK u` by simp[] >>
  drule run_inst_seq_append_err >>
  disch_then (qspec_then `emitted_insts sm sb` assume_tac) >> gvs[]
QED

Theorem compile_empty_buffer_seq_mem:
  !sz header sa sb buf func cenv cx es s ctx.
    compile_builtin_empty_complex sz header sa = (buf,sb) /\
    stmt_state_rel H ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ sz < dimword (:256) /\
    (if header then 32 <= sz else sz MOD 32 = 0) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    (!t. run_inst_seq (emitted_insts sa sb) s = OK t ==>
      s.vs_alloca_next <= t.vs_alloca_next) /\
    EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  rpt gen_tac >> strip_tac >>
  drule abi_empty_complex_parts >> strip_tac >>
  rename1 `compile_alloc_buffer sz sa = (buf,sm)` >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `emitted_insts sa sm =
    [mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]] /\
   sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
   sm.cs_next_var = sa.cs_next_var + 1` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> strip_tac >> gvs[] >>
     drule emitted_insts_emit_op >> simp[]) >>
  `w2n w + sz <= t.vs_alloca_next` by
    (`alloca_inv t` by fs[stmt_state_rel_def] >>
     fs[alloca_inv_def, alloca_next_valid_def] >> first_x_assum drule >> simp[]) >>
  `s.vs_alloca_next <= t.vs_alloca_next` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa sm) s = OK t` mp_tac >>
     asm_rewrite_tac[run_inst_seq_def] >>
     simp[AllCaseEqs()] >> strip_tac >>
     irule step_inst_alloca_alloca_next_mono >>
     qexistsl_tac [`ARB`, `0`, `mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
       [STRING #"%" (toString sa.cs_next_var)]`] >>
     simp[step_inst_non_invoke, mk_inst_def, is_alloca_op_def]) >>
  `sm.cs_current_insts ++ emitted_insts sm sb = sb.cs_current_insts /\
   run_inst_seq_mem_ok (emitted_insts sm sb) t /\
   (!u. run_inst_seq (emitted_insts sm sb) t = OK u ==>
      u.vs_alloca_next = t.vs_alloca_next) /\
   EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sm sb)` by
    (Cases_on `header` >> fs[]
     >- (drule emitted_insts_emit_void >> strip_tac >>
         `run_inst_seq_mem_ok (emitted_insts sm sb) t` by
           (irule emit_mstore_mem_ok >> goal_assum (drule_at Any) >>
            qexists_tac `Lit 0w` >> simp[] >> decide_tac) >>
         `step_inst_base (mk_inst sm.cs_next_id MSTORE [buf.buf_operand; Lit 0w] []) t =
           OK (mstore (w2n w) 0w t)` by
           (irule step_MSTORE >> simp[eval_operand_def]) >>
         gvs[] >> simp[run_inst_seq_def, mstore_def, mk_inst_def]) >>
     `32 * ((sz+31) DIV 32) = sz` by
       (`sz = (sz DIV 32) * 32` by
          (qspec_then `32` mp_tac DIVISION >> simp[] >>
           disch_then (qspec_then `sz` mp_tac) >> decide_tac) >>
        pop_assum SUBST1_TAC >> simp[ADD_DIV_ADD_DIV]) >>
     drule abi_empty_zero_words_shape >> strip_tac >>
     drule compile_zero_words_no_gas >> strip_tac >>
     drule compile_zero_words_seq_mem >>
     disch_then (qspecl_then [`t`, `w`] mp_tac) >>
     impl_tac >- simp[] >>
     fs[inst_extends_def]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  `!xs. run_inst_seq (emitted_insts sa sm ++ xs) s = run_inst_seq xs t` by
    (gen_tac >> irule run_inst_seq_append >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sm) s` by
    simp[run_inst_seq_mem_ok_last, mk_inst_def, below_frontier_no_ranges] >>
  conj_tac
  >- (qpat_x_assum `emitted_insts sa sb = _` SUBST1_TAC >>
      irule run_inst_seq_mem_ok_append >> simp[] >> rpt strip_tac >> gvs[]) >>
  conj_tac >- (rpt strip_tac >> gvs[] >> res_tac >> simp[]) >>
  asm_rewrite_tac[] >> simp[mk_inst_def]
QED

Theorem extract32_source_post_view:
  expr_post H ctx func cenv cx e es sa sm s0 es' (BytesV bs) op s /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic cap))) /\
  expr_store_bound cx (expr_type e) (BytesV bs) op s ==>
  ?b. eval_operand op s = SOME (n2w b) /\
      mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
      mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
      b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
      b + 32 + LENGTH bs <= s.vs_alloca_next
Proof
  strip_tac >>
  drule hash_dynamic_post_view >>
  disch_then (qspec_then `cap` mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `b` >> simp[] >>
  gvs[expr_store_bound_def, is_word_type_def, val_store_size_def,
      vyperValueTheory.evaluate_type_def, eval_operand_def, w2n_n2w] >>
  qspec_then `LENGTH bs` mp_tac le_word_size_mul >> decide_tac
QED

Theorem extract32_source_snapshot:
  compile_bytestring_src src_op sa = ((len_op,data_op),sm) /\
  (!x. src_op = Var x ==> not_fresh_at sa x) /\
  eval_operand src_op s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w len /\
  b + 32 < dimword (:256) /\ len < dimword (:256) /\
  b + 32 + len <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sm) s /\
  ?t. run_inst_seq (emitted_insts sa sm) s = OK t /\
      eval_operand len_op t = SOME (n2w len) /\
      eval_operand data_op t = SOME (n2w (b + 32)) /\
      w2n (n2w (b + 32):bytes32) + w2n (n2w len:bytes32) <= t.vs_alloca_next /\
      (t with vs_vars := s.vs_vars) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!x. len_op = Var x \/ data_op = Var x ==> not_fresh_at sm x)
Proof
  strip_tac >> conj_tac
  >- (irule compile_bytestring_src_mem_ok >> goal_assum (drule_at Any) >>
      simp[w2n_n2w] >> decide_tac) >>
  Cases_on `emit_op MLOAD [src_op] sa` >> rename1 `_ = (lp,sl)` >>
  Cases_on `emit_op ADD [src_op; Lit 32w] sl` >> rename1 `_ = (dp,sc)` >>
  gvs[compile_bytestring_src_def, comp_bind_def, comp_return_def] >>
  `b < dimword (:256)` by decide_tac >>
  drule_all hash_data_prefix_run >> strip_tac >>
  qexists_tac `t` >> simp[w2n_n2w] >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `t with vs_vars := _ = s`
       (mp_tac o Q.AP_TERM `\u. u.vs_alloca_next`) >> simp[]) >>
  simp[] >> metis_tac[]
QED

Theorem extract32_snapshot_entry_frame:
  stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (t with vs_vars := s.vs_vars) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
  stmt_state_rel H ctx func cenv cx es (t with vs_inst_idx := n)
Proof
  strip_tac >>
  `t = s with vs_vars := t.vs_vars` by
    (qpat_x_assum `t with vs_vars := _ = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx es (s with vs_vars := t.vs_vars)` by
    (irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
     `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
     metis_tac[]) >>
  simp[stmt_state_rel_inst_idx] >> metis_tac[]
QED

Theorem extract32_suffix_word_post:
  stmt_state_rel H ctx func cenv cx es' s /\
  storage_well_formed_on cx es' (FST H) /\ wb_frame cenv es es' sa s0 s /\
  (~expr_has_effect e ==> pure_frame cenv func es sa s0 s) /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  t = s with vs_vars := t.vs_vars /\
  (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
  eval_operand op t = SOME (typed_val_to_w256 (BaseTV bt) v) /\
  expr_type e = BaseT bt /\ is_word_type (BaseT bt) ==>
  vv_post H ctx func cenv cx e es sa sb s0 es' (Value v) (StackValue (BaseT bt) op)
    (t with vs_inst_idx := n) /\
  vv_store_bound cx (BaseT bt) lt es' (Value v) (StackValue (BaseT bt) op)
    (t with vs_inst_idx := n)
Proof
  strip_tac >>
  `(t with vs_vars := s.vs_vars) = s` by
    (qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx es' (t with vs_inst_idx := n)` by
    (irule extract32_snapshot_entry_frame >> goal_assum (drule_at Any) >>
     qexists_tac `sm` >> simp[]) >>
  `wb_frame cenv es es' sa s0 (t with vs_inst_idx := n)` by
    (irule wb_frame_readonly_tail >> goal_assum (drule_at Any) >>
     qexists_tac `s` >> simp[lookup_var_def] >>
     qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >>
     fs[lookup_var_def]) >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `t with vs_vars := s.vs_vars = s`
       (mp_tac o Q.AP_TERM `\z. (z.vs_memory,z.vs_allocas)`) >> simp[]) >>
  `~expr_has_effect e ==> pure_frame cenv func es sa s0 t` by
    metis_tac[pure_frame_state_cong] >>
  conj_tac
  >- (irule vv_post_word_intro >> simp[] >>
      metis_tac[evaluate_type_BaseT_SOME]) >>
  simp[exprSimMemDefsTheory.vv_store_bound_def]
QED

Theorem extract32_load_output_range[local]:
  compile_extract32_load l d off sa = (op,sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. MEM i.inst_opcode [ADD; LT; OR; ISZERO; ASSERT; GT; MLOAD] /\
    !x. MEM x i.inst_outputs ==>
      ?n. sa.cs_next_var <= n /\ n < sb.cs_next_var /\
          x = STRING #"%" (toString n)) (emitted_insts sa sb)
Proof
  simp[compile_extract32_load_def, compile_assert_slice_bounds_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >> simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND, mk_inst_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[arithmeticTheory.LESS_ADD_SUC]
QED

Theorem extract32_clamp_output_range[local]:
  !v ty sa op sb.
  compile_clamp_basetype v ty sa = (op,sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. MEM i.inst_opcode
      [LT; GT; SLT; SGT; EQ; ISZERO; OR; AND; SHR; SHL; SAR;
       SIGNEXTEND; ASSERT] /\
    !x. MEM x i.inst_outputs ==>
      ?n. sa.cs_next_var <= n /\ n < sb.cs_next_var /\
          x = STRING #"%" (toString n)) (emitted_insts sa sb)
Proof
  recInduct compile_clamp_basetype_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[compile_clamp_basetype_def, clamp_and_return_def, compile_clamp_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt IF_CASES_TAC >> rpt strip_tac >>
  gvs[type_bounds_def, is_signed_type_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[arithmeticTheory.LESS_ADD_SUC]
QED

Theorem extract32_suffix_output_range:
  compile_extract32_load l d off sa = (raw,sc) /\
  compile_clamp_basetype raw ty sc = (op,sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. MEM i.inst_opcode
      [ADD; LT; GT; SLT; SGT; EQ; ISZERO; OR; AND; SHR; SHL; SAR;
       SIGNEXTEND; ASSERT; MLOAD] /\
    !x. MEM x i.inst_outputs ==>
      ?n. sa.cs_next_var <= n /\ n < sb.cs_next_var /\
          x = STRING #"%" (toString n))
    (emitted_insts sa sc ++ emitted_insts sc sb)
Proof
  strip_tac >> drule extract32_load_output_range >> strip_tac >>
  drule extract32_clamp_output_range >> strip_tac >>
  simp[EVERY_APPEND, EVERY_MEM] >>
  gvs[EVERY_MEM] >> rpt strip_tac >> res_tac >> gvs[] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Theorem extract32_suffix_readonly_frame:
  compile_extract32_load l d off sa = (raw,sc) /\
  compile_clamp_basetype raw ty sc = (op,sb) /\
  run_inst_seq (emitted_insts sa sc ++ emitted_insts sc sb) s = OK t ==>
  t = s with vs_vars := t.vs_vars /\
  (!x. (!n. sa.cs_next_var <= n /\ n < sb.cs_next_var ==>
              x <> STRING #"%" (toString n)) ==>
       FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  strip_tac >> drule_all extract32_suffix_output_range >> strip_tac >>
  ho_match_mp_tac run_inst_seq_protected_frame >>
  qexists `emitted_insts sa sc ++ emitted_insts sc sb` >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  `MEM i.inst_opcode
      [ADD; LT; GT; SLT; SGT; EQ; ISZERO; OR; AND; SHR; SHL; SAR;
       SIGNEXTEND; ASSERT; MLOAD] /\
   (!x. MEM x i.inst_outputs ==>
     ?n. sa.cs_next_var <= n /\ n < sb.cs_next_var /\
         x = STRING #"%" (toString n))` by
    (qpat_x_assum `EVERY _ _` mp_tac >> pure_rewrite_tac[EVERY_MEM] >>
     disch_then (qspec_then `i` mp_tac) >> simp[]) >>
  Cases_on `i.inst_opcode = MLOAD`
  >- (`MEM i.inst_opcode [MLOAD; SLOAD; TLOAD; ILOAD; DLOAD]` by simp[] >>
      drule_all rest_word_step_load_frame >> strip_tac >> metis_tac[]) >>
  `MEM i.inst_opcode
      [ADD; SUB; MUL; Div; Mod; SDIV; SMOD; Exp; ADDMOD; MULMOD;
       EQ; LT; GT; SLT; SGT; ISZERO; AND; OR; XOR; NOT;
       SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSERT; ASSERT_UNREACHABLE]` by gvs[] >>
  drule_all step_pure_opcode_frame >> strip_tac >> metis_tac[]
QED

Theorem extract32_suffix_lookup_kept:
  compile_extract32_load l d off sa = (raw,sc) /\
  compile_clamp_basetype raw ty sc = (op,sb) /\
  run_inst_seq (emitted_insts sa sc ++ emitted_insts sc sb) s = OK t /\
  not_fresh_at sa x ==>
  lookup_var x t = lookup_var x s
Proof
  strip_tac >> drule_all extract32_suffix_readonly_frame >> strip_tac >>
  simp[lookup_var_def] >> first_x_assum irule >>
  gvs[not_fresh_at_def]
QED

Theorem extract32_clamp_footprint[local]:
  !v ty sa op sb.
    compile_clamp_basetype v ty sa = (op,sb) ==>
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      ~is_ext_call_op i.inst_opcode /\ !s. inst_mem_below_frontier i s /\ inst_dload_in_section i s)
      (emitted_insts sa sb)
Proof
  recInduct compile_clamp_basetype_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[compile_clamp_basetype_def, clamp_and_return_def, compile_clamp_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt IF_CASES_TAC >> rpt strip_tac >>
  gvs[type_bounds_def, is_signed_type_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND] >>
  simp[inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, inst_dload_in_section_def, mk_inst_def, is_terminator_def,
       is_ext_call_op_def]
QED

Theorem extract32_clamp_mem_ok[local]:
  compile_clamp_basetype v ty sa = (op,sb) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> irule run_inst_seq_mem_ok_every >>
  drule extract32_clamp_footprint >> simp[EVERY_MEM] >> metis_tac[]
QED

Theorem extract32_suffix_mem_ok[local]:
  compile_extract32_load l d off sa = (raw,sc) /\
  compile_clamp_basetype raw ty sc = (op,sb) /\
  fresh_vars_wrt sa s /\
  eval_operand l s = SOME len /\ eval_operand d s = SOME data /\
  eval_operand off s = SOME start /\
  w2n data + w2n len <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sc ++ emitted_insts sc sb) s
Proof
  strip_tac >> irule run_inst_seq_mem_ok_append >> conj_tac
  >- (rpt strip_tac >> irule extract32_clamp_mem_ok >> metis_tac[]) >>
  irule compile_extract32_load_mem_ok >> metis_tac[]
QED

Theorem extract32_load_straight_line[local]:
  compile_extract32_load l d off sa = (op,sb) ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      ~is_ext_call_op i.inst_opcode /\
      ((!s. inst_mem_below_frontier i s /\ inst_dload_in_section i s) \/
       ?id addr out. i = mk_inst id MLOAD [addr] [out]))
    (emitted_insts sa sb)
Proof
  strip_tac >>
  Cases_on `compile_assert_slice_bounds off (Lit 32w) l sa` >>
  rename1 `compile_assert_slice_bounds off (Lit 32w) l sa = (u,sc)` >>
  Cases_on `u` >>
  drule builtinBytesMemoryTheory.slice_bounds_shape >> strip_tac >>
  gvs[builtinBytesTheory.compile_extract32_load_def, comp_bind_def,
      comp_ignore_bind_def, emit_op_def, fresh_var_def, fresh_id_def,
      emit_def, comp_return_def] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, is_terminator_def, is_ext_call_op_def,
       inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, inst_dload_in_section_def] >>
  metis_tac[mk_inst_def]
QED

Theorem run_inst_seq_mem_ok_total_vars_ext:
  !code s big.
    vars_ext s big /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
      ~is_ext_call_op i.inst_opcode) code /\
    ((?t. run_inst_seq code s = OK t) \/
     (?a t. run_inst_seq code s = Abort a t)) /\
    run_inst_seq_mem_ok code s /\
    (!i u v. MEM i code /\ vars_ext u v /\
      ((?t. step_inst_base i u = OK t) \/
       (?a t. step_inst_base i u = Abort a t)) /\
      inst_mem_below_frontier i u /\ inst_dload_in_section i u ==>
      inst_mem_below_frontier i v /\ inst_dload_in_section i v) ==>
    run_inst_seq_mem_ok code big
Proof
  Induct >- simp[run_inst_seq_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `vars_ext_result (step_inst_base h s) (step_inst_base h big)` by
    (irule step_inst_base_vars_ext_state >>
     qpat_x_assum `EVERY _ _` mp_tac >> simp[EVERY_DEF]) >>
  Cases_on `step_inst_base h s` >>
  qpat_x_assum `run_inst_seq (h::code) s = _` mp_tac >>
  simp[Once run_inst_seq_def] >> strip_tac >>
  qpat_x_assum `run_inst_seq_mem_ok (h::code) s` mp_tac >>
  qpat_assum `step_inst_base h s = _`
    (fn th => pure_rewrite_tac[run_inst_seq_mem_ok_def, th]) >>
  simp[NoAsms] >> strip_tac >>
  qpat_x_assum `vars_ext_result _ _` mp_tac >>
  pure_rewrite_tac[vars_ext_result_def] >> strip_tac >>
  `inst_mem_below_frontier h big /\ inst_dload_in_section h big` by
    (qpat_x_assum `!i u v. _` irule >>
     simp[NoAsms, MEM] >> qexists_tac `s` >> metis_tac[]) >>
  qpat_assum `step_inst_base h big = _`
    (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `inst_mem_below_frontier h big`
    (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `inst_dload_in_section h big`
    (fn th => pure_rewrite_tac[th]) >>
  simp[NoAsms] >>
  (first_x_assum irule >> conj_tac
  >- (qpat_x_assum `!i u v. _` mp_tac >>
      metis_tac[MEM]) >>
  conj_tac
  >- (qpat_x_assum `EVERY _ (h::code)` mp_tac >>
      simp[NoAsms, EVERY_DEF]) >>
  qexists_tac `v` >> metis_tac[])
QED

Theorem mload_total_vars_ext_frontier:
  vars_ext s big /\
  ((?t. step_inst_base (mk_inst id MLOAD [addr] [out]) s = OK t) \/
   (?a t. step_inst_base (mk_inst id MLOAD [addr] [out]) s = Abort a t)) /\
  inst_mem_below_frontier (mk_inst id MLOAD [addr] [out]) s ==>
  inst_mem_below_frontier (mk_inst id MLOAD [addr] [out]) big /\
  inst_dload_in_section (mk_inst id MLOAD [addr] [out]) big
Proof
  strip_tac >>
  qpat_x_assum `vars_ext s big` (strip_assume_tac o REWRITE_RULE [vars_ext_def]) >>
  qpat_x_assum `big = _` SUBST1_TAC >>
  Cases_on `eval_operand addr s` >>
  gvs[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def,
      below_frontier_MLOAD, eval_operand_vars_ext, inst_dload_in_section_def]
QED

Theorem extract32_suffix_total_mem_transfer[local]:
  compile_extract32_load l d off sa = (raw,sc) /\
  compile_clamp_basetype raw ty sc = (op,sb) /\
  vars_ext s big /\
  ((?t. run_inst_seq (emitted_insts sa sc ++ emitted_insts sc sb) s = OK t) \/
   (?a t. run_inst_seq (emitted_insts sa sc ++ emitted_insts sc sb) s = Abort a t)) /\
  run_inst_seq_mem_ok (emitted_insts sa sc ++ emitted_insts sc sb) s ==>
  run_inst_seq_mem_ok (emitted_insts sa sc ++ emitted_insts sc sb) big
Proof
  strip_tac >> drule extract32_load_straight_line >>
  drule extract32_clamp_footprint >> rpt strip_tac >>
  (irule run_inst_seq_mem_ok_total_vars_ext >> conj_tac
   >- (rpt gen_tac >> strip_tac >>
       fs[EVERY_MEM, MEM_APPEND] >>
       first_x_assum drule >> strip_tac >>
       gvs[] >> metis_tac[mload_total_vars_ext_frontier]) >>
   conj_tac
   >- (fs[EVERY_MEM, MEM_APPEND] >> metis_tac[]) >>
   qexists_tac `s` >> metis_tac[])
QED

Theorem extract32_suffix_separated_mem_ok:
  compile_extract32_load l d off sa = (raw,sc) /\
  compile_clamp_basetype raw ty sc = (op,sb) /\
  (!x. l = Var x \/ d = Var x \/ off = Var x ==> not_fresh_at sa x) /\
  eval_operand l s = SOME len /\ eval_operand d s = SOME data /\
  eval_operand off s = SOME start /\
  w2n data + w2n len <= s.vs_alloca_next /\
  ((?t. run_inst_seq (emitted_insts sa sc ++ emitted_insts sc sb)
          (drop_fresh sa s) = OK t) \/
   (?a t. run_inst_seq (emitted_insts sa sc ++ emitted_insts sc sb)
          (drop_fresh sa s) = Abort a t)) ==>
  run_inst_seq_mem_ok (emitted_insts sa sc ++ emitted_insts sc sb) s
Proof
  strip_tac >>
  `eval_operand l (drop_fresh sa s) = SOME len /\
   eval_operand d (drop_fresh sa s) = SOME data /\
   eval_operand off (drop_fresh sa s) = SOME start` by
    simp[eval_operand_drop_fresh] >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  `w2n data + w2n len <= (drop_fresh sa s).vs_alloca_next` by
    simp[drop_fresh_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sc ++ emitted_insts sc sb)
     (drop_fresh sa s)` by
    (irule extract32_suffix_mem_ok >> metis_tac[]) >>
  (irule extract32_suffix_total_mem_transfer >> conj_tac
   >- metis_tac[] >>
   qexists_tac `drop_fresh sa s` >> simp[vars_ext_drop_fresh] >> metis_tac[])
QED

Theorem extract32_compile_equations:
  compile_expr cenv ty (TypeBuiltin ann Extract32 ret [src;off]) sa = (vv,sb) ==>
  ?src_op s1 len data s2 off_op s3 raw s4 op.
    lower_value compile_expr cenv (expr_type src) src sa = (src_op,s1) /\
    compile_bytestring_src src_op s1 = ((len,data),s2) /\
    lower_value compile_expr cenv ty off s2 = (off_op,s3) /\
    compile_extract32_load len data off_op s3 = (raw,s4) /\
    compile_clamp_basetype raw ret s4 = (op,sb) /\
    vv = StackValue ann op
Proof
  simp[exprSimHypsTheory.compile_expr_type_builtin_dispatch,
       Once exprLoweringTheory.compile_expr_def,
       exprLoweringTheory.compile_type_builtin_dispatch_body_def] >>
  `!e aty. MEM e [src;off] ==>
     lower_value (expr_child_callback
       (cenv_defaults_size cenv + (expr_size off + (expr_size src + 2))) compile_expr)
       cenv aty e = lower_value compile_expr cenv aty e` by
    (rpt strip_tac >> irule lower_value_callback_contract >>
     irule expr_child_callback_agrees >> simp[] >> gvs[] >> simp[]) >>
  simp[] >>
  Cases_on `lower_value compile_expr cenv (expr_type src) src sa` >>
  rename1 `_ = (src_op,s1)` >>
  Cases_on `compile_bytestring_src src_op s1` >>
  rename1 `_ = (ld,s2)` >> PairCases_on `ld` >>
  Cases_on `lower_value compile_expr cenv ty off s2` >>
  rename1 `_ = (off_op,s3)` >>
  Cases_on `compile_extract32_load ld0 ld1 off_op s3` >>
  rename1 `_ = (raw,s4)` >>
  Cases_on `compile_clamp_basetype raw ret s4` >>
  simp[as_stack_val_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem extract32_compile_cuts:
  lower_value compile_expr cenv (expr_type src) src sa = (src_op,s1) /\
  compile_bytestring_src src_op s1 = ((len,data),s2) /\
  lower_value compile_expr cenv ty off s2 = (off_op,s3) /\
  compile_extract32_load len data off_op s3 = (raw,s4) /\
  compile_clamp_basetype raw ret s4 = (op,sb) /\
  fn_has_code sa sb func ==>
  ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\
  ci_mono s3 s4 /\ ci_mono s4 sb /\
  fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
  fn_has_code s2 s3 func /\ fn_has_code s3 s4 func /\
  fn_has_code s4 sb func /\ fn_has_code s1 sb func /\
  fn_has_code s2 sb func /\ fn_has_code s3 sb func
Proof
  strip_tac >>
  `ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\
   ci_mono s3 s4 /\ ci_mono s4 sb` by
    metis_tac[ci_mono_lower_value_compile_expr, ci_mono_compile_bytestring_src,
              ci_mono_compile_extract32_load, ci_mono_compile_clamp_basetype, pairTheory.SND] >>
  simp[] >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 s3 /\
   cs_extends s3 s4 /\ cs_extends s4 sb` by fs[ci_mono_def] >>
  `cs_extends s3 sb` by metis_tac[cs_extends_trans] >>
  `cs_extends s2 sb` by metis_tac[cs_extends_trans] >>
  `cs_extends s1 sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code s1 s2 func /\ fn_has_code s2 sb func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code s2 s3 func /\ fn_has_code s3 sb func` by
    metis_tac[fn_has_code_split] >>
  metis_tac[fn_has_code_split]
QED

Theorem extract32_offset_body_pre:
  expr_body_pre cenv cx env (TypeBuiltin ann Extract32 ret [src;off]) es /\
  bind (eval_expr cx src) (read_result cx) es = (INL v,ee) ==>
  expr_body_pre cenv cx env off ee
Proof
  strip_tac >>
  `expr_body_pre cenv cx env src es` by
    (irule expr_body_pre_type_builtin_head >> metis_tac[]) >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) exprSimSourceTheory.expr_body_pre_eval) >> strip_tac >>
  gvs[expr_body_pre_def, well_typed_expr_def, byte_widths_expr_def,
      alloc_limits_expr_def, int_calls_expr_def,
      supportedExprTraverseTheory.supported_expr_exists_def,
      supportedExprTraverseTheory.expr_has_evm_run_thm] >>
  metis_tac[call_evaluation_safe_append_right]
QED
