Theory bodyPtrTypeBuiltinsCastExecution
Ancestors bodyPtrTypeBuiltinsCast exprLowering exprLoweringProps
  emitHelperProps compileEnv venomExecSemantics venomState venomInst
  words list finite_map arithmetic exprSimConvert vyperValueOperation
  vyperValue vyperTyping valueEncoding valueEncodingDefs compileEnv

Theorem cast_sequence_actual:
  eval_operand x s = SOME w /\ mload (w2n w) s = n2w len /\
  len < dimword(:256) /\ n < dimword(:256) ==>
  if len <= n then
    ?t. run_inst_seq
      [mk_inst id MLOAD [x] [a]; mk_inst (id+1) GT [Var a;Lit (n2w n)] [b];
       mk_inst (id+2) ISZERO [Var b] [c]; mk_inst (id+3) ASSERT [Var c] []] s = OK t /\
      (t with vs_vars := s.vs_vars) = s /\
      (!p. p <> a /\ p <> b /\ p <> c ==> lookup_var p t = lookup_var p s)
  else ?t. run_inst_seq
      [mk_inst id MLOAD [x] [a]; mk_inst (id+1) GT [Var a;Lit (n2w n)] [b];
       mk_inst (id+2) ISZERO [Var b] [c]; mk_inst (id+3) ASSERT [Var c] []] s =
      Abort Revert_abort t
Proof
  strip_tac >>
  `step_inst_base (mk_inst id MLOAD [x] [a]) s =
    OK (update_var a (n2w len) s)` by (drule step_MLOAD >> simp[]) >>
  rewrite_tac[run_inst_seq_def] >> asm_rewrite_tac[] >>
  pure_rewrite_tac[step_inst_base_def, mk_inst_def, instruction_accfupds,
    instruction_accessors, combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, exec_pure1_def, eval_operand_def, eval_operand_update_var,
       w2n_n2w, LESS_MOD] >>
  Cases_on `len <= n` >> gvs[bool_to_word_def] >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       revert_state_def, set_returndata_def]
QED

Theorem cast_compile_actual:
  compile_type_convert (Var src) (ConvBytestringCast n i) sa = (out,sb) /\
  lookup_var src s = SOME w /\ mload (w2n w) s = n2w len /\
  not_fresh_at sa src /\ len <= i /\ i < dimword(:256) /\ n < dimword(:256) ==>
  out = Var src /\
  if len <= n then
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      (t with vs_vars := s.vs_vars) = s /\
      (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s)
  else ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
Proof
  strip_tac >> drule convert_cast_emitted_shape >> strip_tac >> simp[] >>
  Cases_on `n < i` >> gvs[]
  >- (`eval_operand (Var src) s = SOME w` by simp[eval_operand_def] >>
      `len < dimword(:256)` by decide_tac >>
      `n < dimword(:256)` by decide_tac >>
      drule_all cast_sequence_actual >>
      disch_then (qspecl_then [`sa.cs_next_id`,`c`,`b`,`a`] mp_tac) >>
      Cases_on `len <= n` >> simp[] >> strip_tac >>
      goal_assum (drule_at Any) >> metis_tac[]) >>
  `len <= n` by decide_tac >> simp[emitted_insts_refl, run_inst_seq_def]
QED

Theorem cast_typed_header_outcome:
  (tsrc = BaseT (BytesT (Dynamic i)) \/ tsrc = BaseT (StringT i)) /\
  (tdst = BaseT (BytesT (Dynamic n)) \/ tdst = BaseT (StringT n)) /\
  evaluate_type (get_tenv cx) tsrc = SOME tv /\ value_has_type tv v /\
  val_in_memory tv v off s.vs_memory ==>
  ?len. len <= i /\ mload off s = n2w len /\
    (if len <= n then ?v'. convert_result cx tsrc tdst v = INL v'
     else ?msg. convert_result cx tsrc tdst v = INR (Error (RuntimeError msg)))
Proof
  strip_tac >> gvs[evaluate_type_def] >> Cases_on `v` >>
  gvs[value_has_type_def, val_in_memory_def, mload_def,
      convert_result_def, evaluate_convert_from_def, evaluate_convert_def] >>
  rename1 `LENGTH payload <= i` >> qexists_tac `LENGTH payload` >>
  fs[GSYM mem_word_at_def] >> Cases_on `LENGTH payload <= n` >> simp[]
QED

Theorem cast_compile_typed_outcome:
  compile_type_convert (Var src) (ConvBytestringCast n i) sa = (out,sb) /\
  (tsrc = BaseT (BytesT (Dynamic i)) \/ tsrc = BaseT (StringT i)) /\
  (tdst = BaseT (BytesT (Dynamic n)) \/ tdst = BaseT (StringT n)) /\
  evaluate_type (get_tenv cx) tsrc = SOME tv /\ value_has_type tv v /\
  val_in_memory tv v (w2n w) s.vs_memory /\ lookup_var src s = SOME w /\
  not_fresh_at sa src /\ i < dimword(:256) /\ n < dimword(:256) ==>
  out = Var src /\
  case convert_result cx tsrc tdst v of
    INL v' => ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      (t with vs_vars := s.vs_vars) = s /\
      (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s)
  | INR ex => ?msg t. ex = Error (RuntimeError msg) /\
      run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
Proof
  strip_tac >>
  qpat_assum `val_in_memory _ _ _ _`
    (mp_then Any mp_tac cast_typed_header_outcome) >>
  disch_then (qspecl_then [`tsrc`,`tdst`,`n`,`i`,`cx`] mp_tac) >>
  simp[] >> strip_tac >>
  drule_all cast_compile_actual >>
  Cases_on `len <= n` >> gvs[] >> metis_tac[]
QED
