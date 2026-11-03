(* Shared conversion simulation for dynamic Bytes and String results. *)
Theory exprSimConvertBytes
Ancestors
  exprSimConvert exprSimHyps exprSim exprLowering compileEnv
  exprSimAlloc exprSimBuffer exprSimBufferStore exprSimLiteralBuffer exprSimHash
  exprOperandVar valueEncoding valueEncodingProofs
  vyperTypeSystem vyperValueOperation vyperValue vyperInterpreter
  fragExec freshWrites loweringSlice venomExecSemantics venomState
  words list integer_word valueCopyBytes abiDecoderString

(* Exhaustive checker boundary for dynamic bytestring results. *)
Theorem valid_conversion_to_bytestring:
  !src dst.
    valid_conversion src dst /\ is_bytestring_type dst ==>
    is_bytestring_type src
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `dst` >> gvs[is_bytestring_type_def] >>
  rename1 `BaseT d` >> Cases_on `d` >> gvs[is_bytestring_type_def] >>
  FIRST [rename1 `BytesT bd` >> Cases_on `bd`, all_tac] >>
  gvs[is_bytestring_type_def] >>
  Cases_on `src` >> gvs[valid_conversion_def] >>
  rename1 `BaseT b` >> Cases_on `b` >> gvs[valid_conversion_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >> gvs[valid_conversion_def]
QED

Theorem mk_convert_op_to_bytestring:
  (!i n.
    mk_convert_op (BaseT (BytesT (Dynamic i))) (BaseT (BytesT (Dynamic n))) =
      ConvBytestringCast n i /\
    mk_convert_op (BaseT (BytesT (Dynamic i))) (BaseT (StringT n)) =
      ConvBytestringCast n i /\
    mk_convert_op (BaseT (StringT i)) (BaseT (BytesT (Dynamic n))) =
      ConvBytestringCast n i /\
    mk_convert_op (BaseT (StringT i)) (BaseT (StringT n)) =
      ConvBytestringCast n i)
Proof
  simp[mk_convert_op_def, is_bytestring_type_def]
QED

(* These equations include the empty-payload and failed-capacity cases. *)
Theorem convert_result_bytes_to_bytestring:
  (!cx src bs n.
    convert_result cx src (BaseT (BytesT (Dynamic n))) (BytesV bs) =
      if LENGTH bs <= n then INL (BytesV bs)
      else INR (Error (RuntimeError "convert BytesV bound"))) /\
  (!cx src bs n.
    convert_result cx src (BaseT (StringT n)) (BytesV bs) =
      if LENGTH bs <= n then INL (StringV (MAP (CHR o w2n) bs))
      else INR (Error (RuntimeError "convert bytes string")))
Proof
  rw[convert_result_def, evaluate_convert_from_def, evaluate_convert_def]
QED

Theorem convert_result_string_to_bytestring:
  (!cx src s n.
    convert_result cx src (BaseT (BytesT (Dynamic n))) (StringV s) =
      if LENGTH s <= n then INL (BytesV (MAP (n2w o ORD) s))
      else INR (Error (RuntimeError "convert string bytes"))) /\
  (!cx src s n.
    convert_result cx src (BaseT (StringT n)) (StringV s) =
      if LENGTH s <= n then INL (StringV s)
      else INR (Error (RuntimeError "convert string string bound")))
Proof
  rw[convert_result_def, evaluate_convert_from_def, evaluate_convert_def]
QED

Theorem convert_result_int_to_bytestring:
  !cx src i n.
    32 <= n ==>
    convert_result cx src (BaseT (BytesT (Dynamic n))) (IntV i) =
      INL (BytesV (word_to_bytes_be ((i2w i):bytes32)))
Proof
  rw[convert_result_def, evaluate_convert_from_def, evaluate_convert_def]
QED

Theorem compile_convert_bytestring_shape:
  !cenv ty ann t e1 sa.
    is_bytestring_type t ==>
    compile_expr cenv ty (TypeBuiltin ann Convert t [e1]) sa =
      let (x, s1) = lower_value compile_expr cenv (expr_type e1) e1 sa in
      as_stack_val ann (compile_type_convert x (mk_convert_op (expr_type e1) t) s1)
Proof
  rpt strip_tac >> drule is_bytestring_word_type >> strip_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def] >>
  simp[Once (CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)),
       compile_type_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[exprBopLoweringTheory.lower_value_child_call, vyperASTTheory.expr_size_def,
       listTheory.list_size_def, vyperASTTheory.expr_type_def] >>
  Cases_on `t` >> gvs[is_bytestring_type_def]
QED

Theorem lower_value_convert_bytestring[local]:
  !cenv ty ann t e1 sa op sb.
    lower_value compile_expr cenv ty (TypeBuiltin ann Convert t [e1]) sa =
      (op,sb) /\ is_bytestring_type t ==>
    ?x s1.
      lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
      compile_type_convert x (mk_convert_op (expr_type e1) t) s1 = (op,sb)
Proof
  rpt strip_tac >> drule is_bytestring_word_type >> strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[Once lower_value_def, comp_bind_def] >>
  simp[compile_convert_bytestring_shape] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[as_stack_val_pair, unwrap_value_def, comp_return_def]
QED

Theorem bytestring_type_cases[local]:
  !t. is_bytestring_type t <=>
    (?n. t = BaseT (BytesT (Dynamic n))) \/ (?n. t = BaseT (StringT n))
Proof
  Cases >> simp[is_bytestring_type_def] >>
  rename1 `BaseT b` >> Cases_on `b` >> simp[is_bytestring_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >> simp[is_bytestring_type_def]
QED

(* Dynamic casts retain the payload and its actual rounded footprint. *)
Theorem convert_bytestring_memory:
  !cx src dst tv1 tv2 v v' off mem.
    is_bytestring_type src /\ is_bytestring_type dst /\
    evaluate_type (get_tenv cx) src = SOME tv1 /\
    evaluate_type (get_tenv cx) dst = SOME tv2 /\
    value_has_type tv1 v /\ convert_result cx src dst v = INL v' ==>
    (val_in_memory tv2 v' off mem <=> val_in_memory tv1 v off mem) /\
    val_footprint tv2 v' = val_footprint tv1 v
Proof
  rpt gen_tac >> strip_tac >>
  gvs[bytestring_type_cases, evaluate_type_def] >>
  Cases_on `v` >>
  gvs[vyperTypingTheory.value_has_type_def,
      convert_result_bytes_to_bytestring, convert_result_string_to_bytestring,
      AllCaseEqs(), val_in_memory_def, val_footprint_def,
      abi_decoder_string_bytes_roundtrip]
QED

Theorem convert_bytestring_typed:
  !cx src dst tv1 tv2 v v'.
    is_bytestring_type src /\ is_bytestring_type dst /\
    evaluate_type (get_tenv cx) src = SOME tv1 /\
    evaluate_type (get_tenv cx) dst = SOME tv2 /\
    value_has_type tv1 v /\ convert_result cx src dst v = INL v' ==>
    value_has_type tv2 v'
Proof
  rpt gen_tac >> strip_tac >>
  gvs[bytestring_type_cases, evaluate_type_def] >>
  Cases_on `v` >>
  gvs[vyperTypingTheory.value_has_type_def,
      convert_result_bytes_to_bytestring, convert_result_string_to_bytestring,
      AllCaseEqs()]
QED

Theorem convert_bytestring_wf:
  !cx src dst tv1 tv2 v v'.
    is_bytestring_type src /\ is_bytestring_type dst /\
    evaluate_type (get_tenv cx) src = SOME tv1 /\
    evaluate_type (get_tenv cx) dst = SOME tv2 /\
    value_has_type tv1 v /\ convert_result cx src dst v = INL v' ==>
    val_wf tv2 v'
Proof
  rpt strip_tac >> irule valueTypingMemoryPropsTheory.value_has_type_memory_wf >>
  drule_all convert_bytestring_typed >> simp[]
QED

Theorem convert_bytestring_val_rel:
  !cx src dst tv1 tv2 v v' op s.
    is_bytestring_type src /\ is_bytestring_type dst /\
    evaluate_type (get_tenv cx) src = SOME tv1 /\
    evaluate_type (get_tenv cx) dst = SOME tv2 /\
    value_has_type tv1 v /\ convert_result cx src dst v = INL v' /\
    expr_val_rel cx src v op s ==>
    expr_val_rel cx dst v' op s
Proof
  rpt strip_tac >>
  drule_all convert_bytestring_memory >> strip_tac >>
  gvs[expr_val_rel_def, is_bytestring_word_type] >>
  qexists `w` >> simp[]
QED

Theorem convert_bytestring_val_at:
  !cenv cx src dst tv1 tv2 v v' sa sb es op s.
    is_bytestring_type src /\ is_bytestring_type dst /\
    evaluate_type (get_tenv cx) src = SOME tv1 /\
    evaluate_type (get_tenv cx) dst = SOME tv2 /\
    value_has_type tv1 v /\ convert_result cx src dst v = INL v' /\
    expr_val_at cenv cx src sa sb es v op s ==>
    expr_val_at cenv cx dst sa sb es v' op s
Proof
  rpt strip_tac >>
  drule_all convert_bytestring_memory >> strip_tac >>
  drule_all convert_bytestring_wf >> strip_tac >>
  gvs[expr_val_at_def, is_bytestring_word_type] >>
  gvs[bytestring_type_cases, dynarray_type_def] >> metis_tac[]
QED

Theorem convert_bytestring_footprint_small:
  !n bs.
    LENGTH bs <= 32 ==>
    val_footprint (BaseTV (BytesT (Dynamic n))) (BytesV bs) <= 64 /\
    val_footprint (BaseTV (StringT n)) (StringV (MAP (CHR o w2n) bs)) <= 64
Proof
  rpt strip_tac >>
  `(LENGTH bs + 31) DIV 32 < 2` by simp[arithmeticTheory.DIV_LT_X] >>
  simp[val_footprint_def, vfmConstantsTheory.word_size_def] >> decide_tac
QED

Theorem convert_fixed_bytes_payload:
  !m bs.
    LENGTH bs <= 32 ==>
    TAKE (LENGTH bs)
      (word_to_bytes_be (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs))) = bs
Proof
  rpt strip_tac >> simp[typed_val_to_w256_def] >>
  qspec_then `PAD_RIGHT (0w:word8) 32 bs` mp_tac
    TAKE_word_to_bytes_be_word_of_bytes_be >>
  simp[PAD_RIGHT, byteTheory.LENGTH_word_to_bytes_aux,
       byteTheory.word_to_bytes_be_def, byteTheory.word_to_bytes_def,
       TAKE_LENGTH_TOO_LONG] >>
  disch_then (mp_tac o Q.AP_TERM `TAKE (LENGTH bs)`) >>
  simp[listTheory.TAKE_APPEND1]
QED

Theorem convert_mem_word_prefix:
  !off mem n.
    n <= 32 ==>
    mem_bytes_at off n mem = TAKE n (word_to_bytes_be (mem_word_at off mem))
Proof
  rpt strip_tac >>
  qspecl_then [`off`, `n`, `32 - n`, `mem`] mp_tac
    mem_bytes_at_split_padded >>
  simp[arithmeticTheory.SUB_ADD, mem_bytes_at_word,
       GSYM byteTheory.word_to_bytes_be_def] >>
  disch_then (mp_tac o Q.AP_TERM `TAKE n`) >>
  simp[listTheory.TAKE_APPEND1, LENGTH_mem_bytes_at_proof]
QED

Theorem convert_word_payload_memory:
  !n bs off mem w.
    LENGTH bs <= 32 /\
    mem_word_at off mem = n2w (LENGTH bs) /\
    mem_word_at (off + 32) mem = w /\
    TAKE (LENGTH bs) (word_to_bytes_be w) = bs ==>
    val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) off mem /\
    val_in_memory (BaseTV (StringT n)) (StringV (MAP (CHR o w2n) bs)) off mem
Proof
  rpt strip_tac >>
  `mem_bytes_at (off + 32) (LENGTH bs) mem = bs` by
    (simp[convert_mem_word_prefix]) >>
  gvs[val_in_memory_def, abi_decoder_string_bytes_roundtrip]
QED

Theorem convert_fixed_bytes_memory:
  !m n bs off mem.
    LENGTH bs <= 32 /\
    mem_word_at off mem = n2w (LENGTH bs) /\
    mem_word_at (off + 32) mem =
      typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs) ==>
    val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) off mem /\
    val_in_memory (BaseTV (StringT n)) (StringV (MAP (CHR o w2n) bs)) off mem
Proof
  rpt gen_tac >> strip_tac >>
  irule convert_word_payload_memory >>
  simp[convert_fixed_bytes_payload] >> metis_tac[]
QED

Theorem convert_integer_bytes_memory:
  !n i off mem.
    mem_word_at off mem = 32w /\
    mem_word_at (off + 32) mem = (i2w i:bytes32) ==>
    val_in_memory (BaseTV (BytesT (Dynamic n)))
      (BytesV (word_to_bytes_be (i2w i:bytes32))) off mem /\
    val_footprint (BaseTV (BytesT (Dynamic n)))
      (BytesV (word_to_bytes_be (i2w i:bytes32))) <= 64
Proof
  rpt strip_tac
  >- (simp[val_in_memory_def, convert_mem_word_prefix,
            byteTheory.word_to_bytes_be_def, byteTheory.word_to_bytes_def,
            byteTheory.LENGTH_word_to_bytes_aux]) >>
  irule (cj 1 convert_bytestring_footprint_small) >>
  simp[byteTheory.word_to_bytes_be_def, byteTheory.word_to_bytes_def,
       byteTheory.LENGTH_word_to_bytes_aux]
QED

Theorem convert_bytes_capacity:
  !tenv n tv.
    evaluate_type tenv (BaseT (BytesT (Dynamic n))) = SOME tv ==>
    n < dimword (:256)
Proof
  simp[evaluate_type_def, AllCaseEqs()]
QED

Theorem convert_string_capacity:
  !tenv n tv.
    evaluate_type tenv (BaseT (StringT n)) = SOME tv ==>
    n < dimword (:256)
Proof
  simp[evaluate_type_def, AllCaseEqs()]
QED

Theorem convert_bytes_header:
  !tenv n tv bs off s.
    evaluate_type tenv (BaseT (BytesT (Dynamic n))) = SOME tv /\
    value_has_type tv (BytesV bs) /\
    val_in_memory tv (BytesV bs) off s.vs_memory ==>
    mload off s = n2w (LENGTH bs) /\ LENGTH bs <= n /\
    LENGTH bs < dimword (:256)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs(),
      vyperTypingTheory.value_has_type_def, val_in_memory_def,
      valueEncodingPropsTheory.mem_word_at_eq_mload] >> decide_tac
QED

Theorem convert_string_header:
  !tenv n tv str off s.
    evaluate_type tenv (BaseT (StringT n)) = SOME tv /\
    value_has_type tv (StringV str) /\
    val_in_memory tv (StringV str) off s.vs_memory ==>
    mload off s = n2w (LENGTH str) /\ LENGTH str <= n /\
    LENGTH str < dimword (:256)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs(),
      vyperTypingTheory.value_has_type_def, val_in_memory_def,
      valueEncodingPropsTheory.mem_word_at_eq_mload] >> decide_tac
QED

Theorem convert_mload_run:
  !x sa y sb ss p.
    emit_op MLOAD [x] sa = (y,sb) /\ eval_operand x ss = SOME p ==>
    run_inst_seq (emitted_insts sa sb) ss =
      OK (update_var (STRING #"%" (toString sa.cs_next_var))
            (mload (w2n p) ss) ss)
Proof
  rpt gen_tac >> strip_tac >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  `step_inst_base
     (mk_inst sa.cs_next_id MLOAD [x] [STRING #"%" (toString sa.cs_next_var)]) ss =
   OK (update_var (STRING #"%" (toString sa.cs_next_var))
         (mload (w2n p) ss) ss)` by
    (irule emitHelperPropsTheory.step_MLOAD >> simp[]) >>
  simp[exprLoweringPropsTheory.run_inst_seq_def]
QED

Theorem convert_mload_frame:
  !x sa y sb ss p.
    emit_op MLOAD [x] sa = (y,sb) /\ eval_operand x ss = SOME p /\
    fresh_vars_wrt sa ss ==>
    ?tt.
      run_inst_seq (emitted_insts sa sb) ss = OK tt /\
      eval_operand y tt = SOME (mload (w2n p) ss) /\
      same_blocks sa sb /\ fresh_vars_wrt sb tt /\
      tt = ss with vs_vars := tt.vs_vars /\
      (!op w. eval_operand op ss = SOME w ==> eval_operand op tt = SOME w) /\
      (!z. not_fresh_at sa z ==> lookup_var z tt = lookup_var z ss)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all emitHelperPropsTheory.emit_op_MLOAD_correct >> strip_tac >>
  drule_all convert_mload_run >> strip_tac >> gvs[] >>
  conj_tac >- simp[update_var_def] >>
  rpt strip_tac >>
  `z <> STRING #"%" (toString sa.cs_next_var)` by
    (strip_tac >> gvs[not_fresh_at_def]) >>
  simp[emitHelperPropsTheory.lookup_var_update_var]
QED

Theorem convert_cast_narrow_shape:
  !x n i sa op sb.
    n < i /\ compile_type_convert x (ConvBytestringCast n i) sa = (op,sb) ==>
    ?len s1 gt s2 ok s3.
      emit_op MLOAD [x] sa = (len,s1) /\
      emit_op GT [len; Lit (n2w n)] s1 = (gt,s2) /\
      emit_op ISZERO [gt] s2 = (ok,s3) /\
      emit_void ASSERT [ok] s3 = ((),sb) /\ op = x
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_type_convert_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt (goal_assum $ drule_at Any) >> simp[]
QED

Theorem convert_cast_check_straight:
  !len n.
    straight_fresh
      (do gt <- emit_op GT [len; Lit (n2w n)];
          ok <- emit_op ISZERO [gt];
          emit_void ASSERT [ok]
       od)
Proof
  rpt gen_tac >> match_mp_tac straight_fresh_bind >> conj_tac
  >- (irule straight_fresh_emit_op >> simp[fresh_write_op_def]) >>
  gen_tac >> BETA_TAC >> match_mp_tac straight_fresh_bind >> conj_tac
  >- (irule straight_fresh_emit_op >> simp[fresh_write_op_def]) >>
  gen_tac >> BETA_TAC >> irule straight_fresh_emit_void >> simp[fresh_write_op_def]
QED

Theorem convert_cast_check_insts:
  !len n L i j k gt ok s.
    eval_operand len s = SOME (n2w L) /\
    L < dimword (:256) /\ n < dimword (:256) ==>
    let tt = update_var ok (bool_to_word (L <= n))
               (update_var gt (bool_to_word (n < L)) s) in
    run_inst_seq
      [mk_inst i GT [len; Lit (n2w n)] [gt];
       mk_inst j ISZERO [Var gt] [ok];
       mk_inst k ASSERT [Var ok] []] s =
      if L <= n then OK tt
      else Abort Revert_abort (revert_state (set_returndata [] tt))
Proof
  rpt gen_tac >> strip_tac >> simp[LET_THM] >>
  `step_inst_base (mk_inst i GT [len; Lit (n2w n)] [gt]) s =
     OK (update_var gt (bool_to_word (n < L)) s)` by
    (`step_inst_base (mk_inst i GT [len; Lit (n2w n)] [gt]) s =
       OK (update_var gt
         (bool_to_word (w2n (n2w L : bytes32) > w2n (n2w n : bytes32))) s)` by
       (irule emitHelperPropsTheory.step_GT >> simp[eval_operand_def]) >>
     gvs[w2n_n2w, arithmeticTheory.GREATER_DEF]) >>
  `step_inst_base (mk_inst j ISZERO [Var gt] [ok])
     (update_var gt (bool_to_word (n < L)) s) =
     OK (update_var ok (bool_to_word (L <= n))
          (update_var gt (bool_to_word (n < L)) s))` by
    (`step_inst_base (mk_inst j ISZERO [Var gt] [ok])
        (update_var gt (bool_to_word (n < L)) s) =
      OK (update_var ok (bool_to_word (bool_to_word (n < L) = 0w))
        (update_var gt (bool_to_word (n < L)) s))` by
       (irule emitHelperPropsTheory.step_ISZERO >>
        simp[eval_operand_def, emitHelperPropsTheory.lookup_var_update_var]) >>
     Cases_on `n < L` >>
     gvs[venomExecSemanticsTheory.bool_to_word_def]) >>
  Cases_on `L <= n` >>
  gvs[venomExecSemanticsTheory.bool_to_word_def] >>
  simp[exprLoweringPropsTheory.run_inst_seq_def,
       emitHelperPropsTheory.assert_ok, emitHelperPropsTheory.assert_revert,
       eval_operand_def, emitHelperPropsTheory.lookup_var_update_var] >>
  `step_inst_base (mk_inst k ASSERT [Var ok] [])
     (update_var ok 0w (update_var gt 1w s)) =
   Abort Revert_abort
     (revert_state (set_returndata [] (update_var ok 0w (update_var gt 1w s))))` by
    (irule emitHelperPropsTheory.step_ASSERT_revert >>
     simp[eval_operand_def, emitHelperPropsTheory.lookup_var_update_var]) >>
  simp[]
QED

Theorem convert_cast_check_run:
  !len n L sa gt s1 ok s2 sb s.
    emit_op GT [len; Lit (n2w n)] sa = (gt,s1) /\
    emit_op ISZERO [gt] s1 = (ok,s2) /\
    emit_void ASSERT [ok] s2 = ((),sb) /\
    eval_operand len s = SOME (n2w L) /\
    L < dimword (:256) /\ n < dimword (:256) ==>
    let tt = update_var (STRING #"%" (toString (sa.cs_next_var + 1)))
               (bool_to_word (L <= n))
               (update_var (STRING #"%" (toString sa.cs_next_var))
                 (bool_to_word (n < L)) s) in
    run_inst_seq (emitted_insts sa sb) s =
      if L <= n then OK tt
      else Abort Revert_abort (revert_state (set_returndata [] tt))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[emitHelperTheory.emit_void_def, emitHelperTheory.emit_op_def,
      emitHelperTheory.emit_inst_def, comp_bind_def, comp_ignore_bind_def,
      fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  simp[exprLoweringPropsTheory.emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND] >>
  drule_all convert_cast_check_insts >>
  simp[LET_THM]
QED

Theorem convert_cast_narrow_run:
  !x n i sa op sb s p L.
    n < i /\ compile_type_convert x (ConvBytestringCast n i) sa = (op,sb) /\
    eval_operand x s = SOME p /\ mload (w2n p) s = n2w L /\
    L < dimword (:256) /\ n < dimword (:256) ==>
    let tt = update_var (STRING #"%" (toString (sa.cs_next_var + 2)))
               (bool_to_word (L <= n))
             (update_var (STRING #"%" (toString (sa.cs_next_var + 1)))
               (bool_to_word (n < L))
             (update_var (STRING #"%" (toString sa.cs_next_var)) (n2w L) s)) in
    run_inst_seq (emitted_insts sa sb) s =
      if L <= n then OK tt
      else Abort Revert_abort (revert_state (set_returndata [] tt))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all convert_cast_narrow_shape >> strip_tac >>
  gvs[emitHelperTheory.emit_void_def, emitHelperTheory.emit_op_def,
      emitHelperTheory.emit_inst_def, comp_bind_def, comp_ignore_bind_def,
      fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  simp[exprLoweringPropsTheory.emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND] >>
  qpat_x_assum `compile_type_convert _ _ _ = _` kall_tac >>
  rename1 `eval_operand x s = SOME p` >>
  `step_inst_base
      (mk_inst sa.cs_next_id MLOAD [x] [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var)) (n2w L) s)` by
    (drule emitHelperPropsTheory.step_MLOAD >> simp[]) >>
  simp[Once exprLoweringPropsTheory.run_inst_seq_def] >>
  `eval_operand (Var (STRING #"%" (toString sa.cs_next_var)))
      (update_var (STRING #"%" (toString sa.cs_next_var)) (n2w L) s) =
    SOME (n2w L)` by
    simp[eval_operand_def, emitHelperPropsTheory.lookup_var_update_var] >>
  drule_all convert_cast_check_insts >> simp[LET_THM]
QED

Theorem convert_cast_success_frame:
  !x n i sa op sb s p L.
    compile_type_convert x (ConvBytestringCast n i) sa = (op,sb) /\
    fresh_vars_wrt sa s /\ eval_operand x s = SOME p /\
    mload (w2n p) s = n2w L /\ L <= i /\ L <= n /\
    i < dimword (:256) /\ n < dimword (:256) ==>
    ?tt.
      run_inst_seq (emitted_insts sa sb) s = OK tt /\
      op = x /\ same_blocks sa sb /\ fresh_vars_wrt sb tt /\
      tt = s with vs_vars := tt.vs_vars /\
      (!z. not_fresh_at sa z ==> lookup_var z tt = lookup_var z s)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `n < i`
  >- (
    `L < dimword (:256)` by decide_tac >>
    drule_all convert_cast_narrow_run >> simp[LET_THM] >> strip_tac >>
    qpat_x_assum `compile_type_convert _ _ _ = _` mp_tac >>
    simp[compile_type_convert_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, emitHelperTheory.emit_void_def, emitHelperTheory.emit_op_def,
         emitHelperTheory.emit_inst_def, fresh_id_def, fresh_var_def, emit_def] >>
    strip_tac >> gvs[] >>
    qpat_x_assum `run_inst_seq _ _ = _` kall_tac >>
    simp[exprLoweringPropsTheory.same_blocks_def, update_var_def] >>
    conj_tac
    >- (gvs[fresh_vars_wrt_def] >> rpt strip_tac >>
        first_x_assum drule >> simp[]) >>
    rpt strip_tac >>
    `z <> STRING #"%" (toString sa.cs_next_var) /\
     z <> STRING #"%" (toString (sa.cs_next_var + 1)) /\
     z <> STRING #"%" (toString (sa.cs_next_var + 2))` by
      (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_ADD]) >>
    simp[lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  gvs[compile_type_convert_def, comp_return_def,
      exprLoweringPropsTheory.emitted_insts_def,
      exprLoweringPropsTheory.run_inst_seq_def, exprLoweringPropsTheory.same_blocks_def]
QED

Theorem convert_readonly_operand_frame:
  !sa s tt.
    fresh_vars_wrt sa s /\ tt = s with vs_vars := tt.vs_vars /\
    (!z. not_fresh_at sa z ==> lookup_var z tt = lookup_var z s) ==>
    !x w. eval_operand x s = SOME w ==> eval_operand x tt = SOME w
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `!z. x = Var z ==> not_fresh_at sa z` by
    (match_mp_tac exprSimWordBuiltinsTheory.fresh_vars_wrt_not_fresh_at >>
     goal_assum $ drule_at Any >> simp[]) >>
  Cases_on `x` >> gvs[eval_operand_def] >>
  qpat_x_assum `tt = _` (fn th => once_rewrite_tac[th]) >>
  simp[eval_operand_def]
QED

Theorem convert_cast_abort_run:
  !x n i sa op sb s p L.
    compile_type_convert x (ConvBytestringCast n i) sa = (op,sb) /\
    eval_operand x s = SOME p /\ mload (w2n p) s = n2w L /\
    L <= i /\ n < L /\ i < dimword (:256) /\ n < dimword (:256) ==>
    ?tt. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort tt
Proof
  rpt gen_tac >> strip_tac >>
  `n < i /\ L < dimword (:256) /\ ~(L <= n)` by decide_tac >>
  drule_all convert_cast_narrow_run >> simp[LET_THM] >>
  strip_tac >> goal_assum $ drule_at Any
QED

Theorem convert_cast_static_frame:
  !x n i sa op sb.
    compile_type_convert x (ConvBytestringCast n i) sa = (op,sb) ==>
    same_blocks sa sb /\
    isPREFIX sa.cs_current_insts sb.cs_current_insts /\
    sa.cs_next_var <= sb.cs_next_var /\ op = x /\
    EVERY (\ins. ins.inst_opcode <> INVOKE /\ ~is_terminator ins.inst_opcode /\
                 ~is_ext_call_op ins.inst_opcode) (emitted_insts sa sb)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `n < i` >>
  gvs[compile_type_convert_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emitHelperTheory.emit_void_def, emitHelperTheory.emit_op_def,
      emitHelperTheory.emit_inst_def, fresh_id_def, fresh_var_def, emit_def,
      exprLoweringPropsTheory.same_blocks_def] >>
  simp[rich_listTheory.IS_PREFIX_APPEND, exprLoweringPropsTheory.emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND, venomInstTheory.mk_inst_def] >>
  simp[venomInstTheory.is_terminator_def, venomInstTheory.is_ext_call_op_def]
QED

Theorem convert_readonly_embed:
  !sa s0 ss tt.
    ss = (drop_fresh sa s0) with vs_vars := ss.vs_vars /\
    (!z. not_fresh_at sa z ==>
         lookup_var z ss = lookup_var z (drop_fresh sa s0)) /\
    vars_ext ss tt ==>
    tt = s0 with vs_vars := tt.vs_vars /\
    (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
           lookup_var z tt = SOME w)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (gvs[varsExtTheory.vars_ext_def] >>
      qpat_x_assum `tt = _` (fn th => once_rewrite_tac[th]) >>
      qpat_x_assum `ss = _` (fn th => once_rewrite_tac[th]) >>
      simp[varsExtTheory.drop_fresh_def]) >>
  rpt gen_tac >> strip_tac >>
  `lookup_var z (drop_fresh sa s0) = SOME w` by
    simp[varsExtTheory.lookup_var_drop_fresh] >>
  `lookup_var z ss = SOME w` by metis_tac[] >>
  gvs[lookup_var_def, varsExtTheory.vars_ext_def] >>
  metis_tac[finite_mapTheory.FLOOKUP_SUBMAP]
QED

Theorem convert_readonly_state_frame:
  !ctx func cenv cx es sa s tt.
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
    tt = s with vs_vars := tt.vs_vars /\
    (!z w. not_fresh_at sa z /\ lookup_var z s = SOME w ==>
           lookup_var z tt = SOME w) ==>
    stmt_state_rel ctx func cenv cx es tt
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `tt = _` (fn th => once_rewrite_tac[th]) >>
  irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
  fs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
  first_x_assum drule_all >> strip_tac >>
  `not_fresh_at sa p` by
    (fs[local_ptrs_reserved_def] >> res_tac) >>
  qpat_x_assum `!z w. _ ==> lookup_var _ _ = _` drule >> simp[lookup_var_def]
QED

Theorem convert_readonly_frag:
  !ctx func cenv cx es sa sb op w P A R s0.
    same_blocks sa sb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts /\
    EVERY (\ins. ins.inst_opcode <> INVOKE /\ ~is_terminator ins.inst_opcode /\
                 ~is_ext_call_op ins.inst_opcode) (emitted_insts sa sb) /\
    local_ptrs_reserved cenv sa /\
    (!ss. P ss ==> P (drop_fresh sa ss)) /\
    (!ss. fresh_vars_wrt sa ss /\ P ss ==>
       (?tt. run_inst_seq (emitted_insts sa sb) ss = OK tt /\
             eval_operand op tt = SOME w /\
             tt = ss with vs_vars := tt.vs_vars /\
             (!z. not_fresh_at sa z ==> lookup_var z tt = lookup_var z ss)) \/
       (?a tt. run_inst_seq (emitted_insts sa sb) ss = Abort a tt /\ A a)) /\
    (!a ss. A a ==> R (Abort a ss)) ==>
    frag_exec ctx sa sb
      (\ss. ss = s0 /\ stmt_state_rel ctx func cenv cx es ss /\ P ss)
      (\ss. stmt_state_rel ctx func cenv cx es ss /\ eval_operand op ss = SOME w /\
            (!z v. not_fresh_at sa z /\ lookup_var z s0 = SOME v ==>
                   lookup_var z ss = SOME v) /\
            ss.vs_allocas = s0.vs_allocas /\ ss.vs_memory = s0.vs_memory) R
Proof
  rpt gen_tac >> strip_tac >>
  irule varsExtTheory.frag_exec_run_inst_seq_drop_fresh >>
  gvs[exprLoweringPropsTheory.same_blocks_def] >> rpt strip_tac >>
  `P (drop_fresh sa s0)` by metis_tac[] >>
  `fresh_vars_wrt sa (drop_fresh sa s0)` by
    simp[varsExtTheory.fresh_vars_wrt_drop_fresh] >>
  qpat_x_assum `!ss. fresh_vars_wrt _ _ /\ _ ==> _` drule_all >>
  strip_tac
  >- (disj1_tac >> goal_assum $ drule_at Any >> rpt strip_tac >>
      drule_all convert_readonly_embed >> strip_tac >>
      `stmt_state_rel ctx func cenv cx es t` by
        (irule convert_readonly_state_frame >> goal_assum $ drule_at Any >> simp[]) >>
      `eval_operand op t = SOME w` by
        (qpat_x_assum `t = _` kall_tac >>
         qpat_x_assum `tt = _` kall_tac >>
         fs[varsExtTheory.vars_ext_def] >>
         qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >>
         simp[varsExtTheory.eval_operand_vars_ext]) >>
      simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx] >>
      qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >>
      simp[lookup_var_def] >> metis_tac[lookup_var_def]) >>
  disj2_tac >> goal_assum $ drule_at Any >> simp[]
QED

Theorem convert_readonly_frag_success:
  !ctx func cenv cx es sa sb op w P A R s0 B.
    same_blocks sa sb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts /\
    EVERY (\ins. ins.inst_opcode <> INVOKE /\ ~is_terminator ins.inst_opcode /\
                 ~is_ext_call_op ins.inst_opcode) (emitted_insts sa sb) /\
    local_ptrs_reserved cenv sa /\
    (!ss. P ss ==> P (drop_fresh sa ss)) /\
    (!ss. fresh_vars_wrt sa ss /\ P ss ==>
       (?tt. B /\ run_inst_seq (emitted_insts sa sb) ss = OK tt /\
             eval_operand op tt = SOME w /\
             tt = ss with vs_vars := tt.vs_vars /\
             (!z. not_fresh_at sa z ==> lookup_var z tt = lookup_var z ss)) \/
       (?a tt. run_inst_seq (emitted_insts sa sb) ss = Abort a tt /\ A a)) /\
    (!a ss. A a ==> R (Abort a ss)) ==>
    frag_exec ctx sa sb
      (\ss. ss = s0 /\ stmt_state_rel ctx func cenv cx es ss /\ P ss)
      (\ss. B /\ stmt_state_rel ctx func cenv cx es ss /\ eval_operand op ss = SOME w /\
            (!z v. not_fresh_at sa z /\ lookup_var z s0 = SOME v ==>
                   lookup_var z ss = SOME v) /\
            ss.vs_allocas = s0.vs_allocas /\ ss.vs_memory = s0.vs_memory) R
Proof
  rpt gen_tac >> strip_tac >>
  irule varsExtTheory.frag_exec_run_inst_seq_drop_fresh >>
  gvs[exprLoweringPropsTheory.same_blocks_def] >> rpt strip_tac >>
  `P (drop_fresh sa s0)` by metis_tac[] >>
  `fresh_vars_wrt sa (drop_fresh sa s0)` by
    simp[varsExtTheory.fresh_vars_wrt_drop_fresh] >>
  qpat_x_assum `!ss. fresh_vars_wrt _ _ /\ _ ==> _` drule_all >>
  strip_tac
  >- (disj1_tac >> goal_assum $ drule_at Any >> rpt strip_tac >>
      drule_all convert_readonly_embed >> strip_tac >>
      `stmt_state_rel ctx func cenv cx es t` by
        (irule convert_readonly_state_frame >> goal_assum $ drule_at Any >> simp[]) >>
      `eval_operand op t = SOME w` by
        (qpat_x_assum `t = _` kall_tac >>
         qpat_x_assum `tt = _` kall_tac >>
         fs[varsExtTheory.vars_ext_def] >>
         qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >>
         simp[varsExtTheory.eval_operand_vars_ext]) >>
      simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx] >>
      qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >>
      simp[lookup_var_def] >> metis_tac[lookup_var_def]) >>
  disj2_tac >> goal_assum $ drule_at Any >> simp[]
QED

Theorem convert_cast_frag:
  !ctx func cenv cx es sa sb x op n i p L R s0.
    compile_type_convert x (ConvBytestringCast n i) sa = (op,sb) /\
    (!z. x = Var z ==> not_fresh_at sa z) /\ local_ptrs_reserved cenv sa /\
    L <= i /\ i < dimword (:256) /\ n < dimword (:256) /\
    (!ss. n < L ==> R (Abort Revert_abort ss)) ==>
    frag_exec ctx sa sb
      (\ss. ss = s0 /\ stmt_state_rel ctx func cenv cx es ss /\
            (eval_operand x ss = SOME p /\ mload (w2n p) ss = n2w L))
      (\ss. stmt_state_rel ctx func cenv cx es ss /\ eval_operand op ss = SOME p /\
            (!z v. not_fresh_at sa z /\ lookup_var z s0 = SOME v ==>
                   lookup_var z ss = SOME v) /\
            ss.vs_allocas = s0.vs_allocas /\ ss.vs_memory = s0.vs_memory) R
Proof
  rpt gen_tac >> strip_tac >> drule convert_cast_static_frame >> strip_tac >>
  ho_match_mp_tac convert_readonly_frag >>
  qexists_tac `\a. a = Revert_abort /\ n < L` >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      fs[freshWritesTheory.eval_operand_drop_fresh,
         varsExtTheory.drop_fresh_def, mload_def]) >>
  rpt gen_tac >> strip_tac >> Cases_on `L <= n`
  >- (disj1_tac >> drule_all convert_cast_success_frame >> strip_tac >>
      drule_all convert_readonly_operand_frame >> strip_tac >>
      goal_assum $ drule_at Any >> simp[]) >>
  disj2_tac >> `n < L` by decide_tac >>
  drule_all convert_cast_abort_run >> simp[]
QED

Theorem convert_cast_frag_success:
  !ctx func cenv cx es sa sb x op n i p L R s0.
    compile_type_convert x (ConvBytestringCast n i) sa = (op,sb) /\
    (!z. x = Var z ==> not_fresh_at sa z) /\ local_ptrs_reserved cenv sa /\
    L <= i /\ i < dimword (:256) /\ n < dimword (:256) /\
    (!ss. n < L ==> R (Abort Revert_abort ss)) ==>
    frag_exec ctx sa sb
      (\ss. ss = s0 /\ stmt_state_rel ctx func cenv cx es ss /\
            (eval_operand x ss = SOME p /\ mload (w2n p) ss = n2w L))
      (\ss. L <= n /\ stmt_state_rel ctx func cenv cx es ss /\
            eval_operand op ss = SOME p /\
            (!z v. not_fresh_at sa z /\ lookup_var z s0 = SOME v ==>
                   lookup_var z ss = SOME v) /\
            ss.vs_allocas = s0.vs_allocas /\ ss.vs_memory = s0.vs_memory) R
Proof
  rpt gen_tac >> strip_tac >> drule convert_cast_static_frame >> strip_tac >>
  ho_match_mp_tac convert_readonly_frag_success >>
  qexists_tac `\a. a = Revert_abort /\ n < L` >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      fs[freshWritesTheory.eval_operand_drop_fresh,
         varsExtTheory.drop_fresh_def, mload_def]) >>
  rpt gen_tac >> strip_tac >> Cases_on `L <= n`
  >- (disj1_tac >> drule_all convert_cast_success_frame >> strip_tac >>
      drule_all convert_readonly_operand_frame >> strip_tac >>
      goal_assum $ drule_at Any >> simp[]) >>
  disj2_tac >> `n < L` by decide_tac >>
  drule_all convert_cast_abort_run >> simp[]
QED

Theorem convert_wb_frame_trans:
  !ctx func cenv cx es es1 sa sm s0 s1 s2.
    wb_frame cenv es sa s0 s1 /\ wb_frame cenv es1 sm s1 s2 /\
    stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id ==>
    wb_frame cenv es sa s0 s2
Proof
  rpt gen_tac >> strip_tac >>
  `locals_kept cenv es s0 s2` by
    (irule exprSimOpsTheory.locals_kept_trans >>
     qexistsl_tac [`es1`, `sa`, `s1`] >>
     gvs[exprSimWordArgsTheory.wb_frame_def]) >>
  gvs[exprSimWordArgsTheory.wb_frame_def] >> conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sm x` by
        (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
      metis_tac[]) >>
  rpt strip_tac >>
  `FLOOKUP s1.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
  `aid < sm.cs_next_id` by decide_tac >>
  `!n b sz'. local_region cenv es1.scopes s1 n b sz' ==>
     off + sz <= b \/ b + sz' <= off` by
    (rpt strip_tac >>
     `local_region cenv es.scopes s0 n b sz'` by
       (irule exprSimOpsTheory.local_region_frame >>
        conj_tac >- (qexists_tac `func` >>
          gvs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def]) >>
        qexistsl_tac [`sa`, `es1.scopes`, `s1`] >> simp[]) >>
     metis_tac[]) >>
  metis_tac[]
QED

Theorem convert_buffer_expr_post:
  !ctx func cenv cx e es es' sa sb s0 tt v tv op p sz.
    ~is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    val_wf tv v /\ val_in_memory tv v (w2n p) tt.vs_memory /\
    stmt_state_rel ctx func cenv cx es' tt /\ eval_operand op tt = SOME p /\
    FLOOKUP tt.vs_allocas sa.cs_next_id = SOME (w2n p,sz) /\
    sa.cs_next_id < sb.cs_next_id /\ val_footprint tv v <= sz /\
    (!name lb lsz. local_region cenv es'.scopes tt name lb lsz ==>
       w2n p + sz <= lb \/ lb + lsz <= w2n p) /\
    wb_frame cenv es sa s0 tt ==>
    expr_post ctx func cenv cx e es sa sb s0 es' v op tt
Proof
  rpt gen_tac >> strip_tac >>
  gvs[expr_post_def, expr_val_rel_def, expr_val_at_def,
      exprSimWordArgsTheory.wb_frame_def] >>
  reverse conj_tac >- metis_tac[] >>
  disj1_tac >> qexistsl_tac [`sa.cs_next_id`, `w2n p`, `sz`] >>
  simp[] >> metis_tac[]
QED

Theorem convert_expr_post_compose:
  !ctx func cenv cx e e1 es es1 sa sm sb s0 s1 tt v1 x v op.
    expr_post ctx func cenv cx e1 es sa sm s0 es1 v1 x s1 /\
    expr_post ctx func cenv cx e es1 sm sb s1 es1 v op tt /\
    stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id ==>
    expr_post ctx func cenv cx e es sa sb s0 es1 v op tt
Proof
  rpt gen_tac >> strip_tac >>
  `wb_frame cenv es sa s0 s1` by
    (gvs[expr_post_def, exprSimWordArgsTheory.wb_frame_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv es1 sm s1 tt` by
    (gvs[expr_post_def, exprSimWordArgsTheory.wb_frame_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all convert_wb_frame_trans >> strip_tac >>
  gvs[expr_post_def, exprSimWordArgsTheory.wb_frame_def] >>
  reverse conj_tac >- (first_assum ACCEPT_TAC) >>
  irule expr_val_at_start_mono >> goal_assum (drule_at Any) >> simp[]
QED

Theorem convert_readonly_val_at:
  !func cenv cx ty sa sm sb es v x op s tt p.
    expr_val_at cenv cx ty sa sm es v x s /\
    eval_operand x s = SOME p /\ eval_operand op tt = SOME p /\
    tt.vs_allocas = s.vs_allocas /\ sm.cs_next_id <= sb.cs_next_id /\
    local_ptrs_rel func cenv es.scopes s /\ local_ptrs_reserved cenv sm /\
    (!z w. not_fresh_at sm z /\ lookup_var z s = SOME w ==>
      lookup_var z tt = SOME w) ==>
    expr_val_at cenv cx ty sa sb es v op tt
Proof
  rpt gen_tac >> strip_tac >>
  `!n b sz. local_region cenv es.scopes tt n b sz <=>
             local_region cenv es.scopes s n b sz` by
    (rpt gen_tac >> eq_tac
     >- (strip_tac >> irule exprSimOpsTheory.local_region_frame >>
         conj_tac >- (qexists_tac `func` >> simp[]) >>
         qexistsl_tac [`sm`, `es.scopes`, `tt`] >> simp[]) >>
     strip_tac >> irule exprSimOpsTheory.local_region_frame_fwd >>
     qexistsl_tac [`s`, `sm`, `es.scopes`] >> simp[]) >>
  gvs[expr_val_at_def] >> rpt strip_tac >>
  qpat_x_assum `!tv. _ ==> _` drule_all >> strip_tac >>
  gvs[]
  >- (disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
      first_assum ACCEPT_TAC) >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`n`, `b`, `sz`] >> simp[]
QED

Theorem convert_readonly_expr_post:
  !ctx func cenv cx e es es1 sa sm sb s0 s tt v x op p.
    expr_post ctx func cenv cx e es sa sm s0 es1 v x s /\
    stmt_state_rel ctx func cenv cx es1 tt /\
    eval_operand x s = SOME p /\ eval_operand op tt = SOME p /\
    tt.vs_allocas = s.vs_allocas /\ tt.vs_memory = s.vs_memory /\
    sm.cs_next_id <= sb.cs_next_id /\ sa.cs_next_var <= sm.cs_next_var /\
    local_ptrs_reserved cenv sm /\
    (!z w. not_fresh_at sm z /\ lookup_var z s = SOME w ==>
      lookup_var z tt = SOME w) ==>
    expr_post ctx func cenv cx e es sa sb s0 es1 v op tt
Proof
  rpt gen_tac >> strip_tac >>
  `local_ptrs_rel func cenv es1.scopes s` by
    gvs[expr_post_def, exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def] >>
  `expr_val_at cenv cx (expr_type e) sa sb es1 v op tt` by
    (irule convert_readonly_val_at >> goal_assum (drule_at Any) >>
     gvs[expr_post_def] >> metis_tac[]) >>
  `expr_val_rel cx (expr_type e) v op tt` by
    (gvs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  gvs[expr_post_def] >> conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sm x'` by
        (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
      metis_tac[]) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  irule locals_kept_mem_tail >>
  qexists_tac `s` >> simp[]
QED

Theorem convert_bytestring_expr_post:
  !ctx func cenv cx e e1 es es1 sa sb s0 tt tv1 tv2 v v' op.
    is_bytestring_type (expr_type e1) /\ is_bytestring_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv2 /\
    value_has_type tv1 v /\
    convert_result cx (expr_type e1) (expr_type e) v = INL v' /\
    expr_post ctx func cenv cx e1 es sa sb s0 es1 v op tt ==>
    expr_post ctx func cenv cx e es sa sb s0 es1 v' op tt
Proof
  rpt gen_tac >> strip_tac >>
  `expr_val_rel cx (expr_type e) v' op tt` by
    (irule convert_bytestring_val_rel >>
     goal_assum (drule_at Any) >> gvs[expr_post_def] >> metis_tac[]) >>
  `expr_val_at cenv cx (expr_type e) sa sb es1 v' op tt` by
    (irule convert_bytestring_val_at >>
     goal_assum (drule_at Any) >> gvs[expr_post_def] >> metis_tac[]) >>
  gvs[expr_post_def] >> first_assum ACCEPT_TAC
QED

Theorem convert_cast_grows[local]:
  !x n i sa op sb.
    compile_type_convert x (ConvBytestringCast n i) sa = (op,sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id
Proof
  rpt gen_tac >> strip_tac >>
  drule convert_cast_static_frame >> strip_tac >>
  conj_tac
  >- (irule cs_extends_same_block >>
      gvs[exprLoweringPropsTheory.same_blocks_def]) >>
  simp[] >> Cases_on `n < i` >>
  gvs[compile_type_convert_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emitHelperTheory.emit_void_def, emitHelperTheory.emit_op_def,
      emitHelperTheory.emit_inst_def, fresh_id_def, fresh_var_def, emit_def]
QED

Theorem convert_bytestring_suffix_grows:
  !src dst x sa op sb.
    valid_conversion src dst /\ is_bytestring_type dst /\
    compile_type_convert x (mk_convert_op src dst) sa = (op,sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id
Proof
  rpt gen_tac >> strip_tac >>
  drule_all valid_conversion_to_bytestring >> strip_tac >>
  gvs[bytestring_type_cases, mk_convert_op_to_bytestring] >>
  metis_tac[convert_cast_grows]
QED

Theorem convert_operand_typed[local]:
  !cenv cx env t e1 es v es1.
    expr_body_pre cenv cx env (TypeBuiltin t Convert t [e1]) es /\
    (do r <- eval_expr cx e1; read_result cx r od) es = (INL v,es1) ==>
    ?tv1 tv2.
      evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
      evaluate_type (get_tenv cx) t = SOME tv2 /\ value_has_type tv1 v
Proof
  rpt gen_tac >> strip_tac >>
  drule expr_body_pre_convert >> strip_tac >> gvs[] >>
  drule_all expr_body_pre_eval >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `IS_SOME (evaluate_type (get_tenv cx) t)` by
    (qpat_assum `expr_body_pre _ _ _ (TypeBuiltin _ _ _ _) _`
       (mp_then Any mp_tac expr_body_pre_type_evaluates) >>
     simp[vyperASTTheory.expr_type_def]) >>
  gvs[vyperTypeExprResultTheory.expr_result_typed_def,
      vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
      vyperTypeInvariantsTheory.value_result_typed_def] >>
  Cases_on `evaluate_type (get_tenv cx) t` >> gvs[]
QED

Theorem convert_dynamic_view[local]:
  !cx src dst tv1 tv2 v x s i n.
    ((src = BaseT (BytesT (Dynamic i))) \/ src = BaseT (StringT i)) /\
    ((dst = BaseT (BytesT (Dynamic n))) \/ dst = BaseT (StringT n)) /\
    evaluate_type (get_tenv cx) src = SOME tv1 /\
    evaluate_type (get_tenv cx) dst = SOME tv2 /\
    value_has_type tv1 v /\ expr_val_rel cx src v x s ==>
    ?p L. eval_operand x s = SOME p /\ mload (w2n p) s = n2w L /\
      L <= i /\ i < dimword (:256) /\ n < dimword (:256) /\
      (L <= n ==> ?v'. convert_result cx src dst v = INL v') /\
      (n < L ==> ?msg. convert_result cx src dst v = INR (Error (RuntimeError msg)))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[expr_val_rel_def, evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >>
  gvs[vyperTypingTheory.value_has_type_def, is_word_type_def,
      convert_result_bytes_to_bytestring, convert_result_string_to_bytestring,
      val_in_memory_def, valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  rename1 `LENGTH payload <= i` >>
  qexists_tac `LENGTH payload` >> simp[] >> decide_tac
QED

Theorem convert_dynamic_cont[local]:
  !ctx func cenv cx e e1 es es1 sa sm sb s0 s v x op tv1 tv2 i n.
    ((expr_type e1 = BaseT (BytesT (Dynamic i))) \/
      expr_type e1 = BaseT (StringT i)) /\
    ((expr_type e = BaseT (BytesT (Dynamic n))) \/
      expr_type e = BaseT (StringT n)) /\
    evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv2 /\
    value_has_type tv1 v /\
    expr_post ctx func cenv cx e1 es sa sm s0 es1 v x s /\
    compile_type_convert x (ConvBytestringCast n i) sm = (op,sb) /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    (!z. x = Var z ==> not_fresh_at sm z) ==>
    frag_exec ctx sm sb (\ss. ss = s)
      (\tt. ?v'. convert_result cx (expr_type e1) (expr_type e) v = INL v' /\
        expr_post ctx func cenv cx e es sa sb s0 es1 v' op tt)
      (expr_exit (convert_result cx (expr_type e1) (expr_type e) v))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_val_rel cx (expr_type e1) v x s` by gvs[expr_post_def] >>
  drule_all convert_dynamic_view >> strip_tac >>
  drule convert_cast_grows >> strip_tac >>
  `!ss. n < L ==> expr_exit (convert_result cx (expr_type e1) (expr_type e) v)
      (Abort Revert_abort ss)` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >> simp[expr_exit_def]) >>
  drule_all convert_cast_frag_success >>
  disch_then (qspecl_then [`ctx`, `func`, `cx`, `es1`] mp_tac) >>
  disch_then (qspecl_then [`p`, `s`] mp_tac) >>
  disch_then (mp_then Any irule frag_exec_weaken) >>
  simp[] >> conj_tac
  >- gvs[expr_post_def] >>
  rpt gen_tac >> strip_tac >>
  `?v'. convert_result cx (expr_type e1) (expr_type e) v = INL v'` by
    (first_x_assum irule >> simp[]) >>
  qexists_tac `v'` >> simp[] >>
  irule convert_bytestring_expr_post >>
  conj_tac >- (gvs[is_bytestring_type_def]) >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`e1`, `tv1`, `v`] >>
  simp[] >> conj_tac >- gvs[is_bytestring_type_def] >>
  irule convert_readonly_expr_post >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`s`, `sm`, `x`] >> simp[]
QED

Theorem convert_bytestring_cont[local]:
  !ctx func cenv cx e e1 es es1 sa sm sb s0 s v x op tv1 tv2.
    valid_conversion (expr_type e1) (expr_type e) /\
    is_bytestring_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv2 /\
    value_has_type tv1 v /\
    expr_post ctx func cenv cx e1 es sa sm s0 es1 v x s /\
    compile_type_convert x (mk_convert_op (expr_type e1) (expr_type e)) sm = (op,sb) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\ MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    (!z. x = Var z ==> not_fresh_at sm z) ==>
    frag_exec ctx sm sb (\ss. ss = s)
      (\tt. ?v'. convert_result cx (expr_type e1) (expr_type e) v = INL v' /\
        expr_post ctx func cenv cx e es sa sb s0 es1 v' op tt)
      (expr_exit (convert_result cx (expr_type e1) (expr_type e) v))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all valid_conversion_to_bytestring >> strip_tac >>
  gvs[bytestring_type_cases, mk_convert_op_to_bytestring] >>
  qpat_assum `expr_type e1 = _` (fn th => pure_rewrite_tac [GSYM th]) >>
  qpat_assum `expr_type e = _` (fn th => pure_rewrite_tac [GSYM th]) >>
  irule convert_dynamic_cont >> goal_assum (drule_at Any) >>
  simp[] >> qexists_tac `x` >> simp[]
QED

Theorem convert_operand_run[local]:
  !ctx func cenv cx ty e es sa sm x r es'.
    expr_sim ctx func cenv cx ty e es /\
    lower_value compile_expr cenv ty e sa = (x,sm) /\
    (do result <- eval_expr cx e; read_result cx result od) es = (r,es') /\
    expr_res_ok r /\ fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa ==>
    !s0. frag_exec ctx sa sm
      (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. ?v. r = INL v /\ expr_post ctx func cenv cx e es sa sm s0 es' v x s)
      (expr_exit r)
Proof
  simp[expr_sim_def] >> rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem compile_convert_bytestring_frag_sim[local]:
  !ctx func cenv cx env ty t e1 es.
    expr_body_pre cenv cx env (TypeBuiltin t Convert t [e1]) es /\
    is_bytestring_type t /\
    expr_sim ctx func cenv cx (expr_type e1) e1 es ==>
    expr_sim ctx func cenv cx ty (TypeBuiltin t Convert t [e1]) es
Proof
  rpt gen_tac >> strip_tac >>
  drule expr_body_pre_convert >> strip_tac >> gvs[] >>
  simp[expr_sim_def] >> rpt gen_tac >> strip_tac >>
  reverse (Cases_on `stmt_state_rel ctx func cenv cx es s0`)
  >- (irule frag_exec_conseq >>
      qexistsl_tac [`\s. F`, `\s. F`, `\r. F`] >>
      simp[frag_exec_false_pre]) >>
  `!n. t <> FlagT n` by (Cases_on `t` >> gvs[is_bytestring_type_def]) >>
  drule_all lower_value_convert_bytestring >> strip_tac >>
  drule (cj 2 exprLoweringPropsTheory.compile_expr_grows) >> strip_tac >>
  drule_all convert_bytestring_suffix_grows >> strip_tac >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `local_ptrs_reserved cenv s1` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!z. x = Var z ==> not_fresh_at s1 z` by
    (metis_tac[exprOperandVarTheory.compile_lower_value_var]) >>
  drule_all eval_expr_convert_cases >> strip_tac
  >- (gvs[] >> drule_all convert_operand_run >>
      disch_then (qspec_then `s0` mp_tac) >>
      disch_then (mp_then Any mp_tac frag_exec_weaken) >>
      simp[] >> disch_tac >>
      irule frag_exec_exit_prefix >> qexists_tac `s1` >> simp[]) >>
  `expr_res_ok (INL v1)` by simp[expr_res_ok_def] >>
  drule_all convert_operand_run >>
  disch_then (qspec_then `s0` mp_tac) >>
  disch_then (mp_then Any mp_tac frag_exec_pre_exit_c) >>
  disch_then (qspecl_then
    [`\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s`, `expr_exit res`] mp_tac) >>
  simp[] >> disch_then (mp_then Any irule frag_exec_then) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  drule_all convert_operand_typed >> strip_tac >>
  drule exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom >> strip_tac >>
  irule (Q.SPECL [`ctx`, `func`, `cenv`, `cx`, `TypeBuiltin t Convert t [e1]`]
    convert_bytestring_cont |> SRULE [vyperASTTheory.expr_type_def]) >>
  goal_assum (drule_at Any) >> simp[] >> qexists_tac `x` >> simp[]
QED

Theorem compile_convert_to_bytestring_case:
  !nocalls ctx func cenv cx ann t e1.
    exprs_case nocalls ctx func cenv cx [e1] /\
    is_bytestring_type t ==>
    expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann Convert t [e1])
Proof
  rw[expr_vv_case_def] >> drule expr_body_pre_convert >> strip_tac >>
  gvs[exprs_case_def] >>
  `expr_sim ctx func cenv cx (expr_type e1) e1 es` by
    (irule expr_sim_case_apply >> conj_tac >- (qexists_tac `env` >> simp[]) >>
     qexists_tac `nocalls` >> simp[] >>
     metis_tac[int_calls_type_builtin_arg, listTheory.MEM]) >>
  irule expr_vv_sim_stack >> rpt conj_tac
  >- simp[compile_convert_stack]
  >- metis_tac[eval_expr_type_builtin_value] >>
  irule compile_convert_bytestring_frag_sim >> simp[] >>
  qexists_tac `env` >> simp[]
QED
