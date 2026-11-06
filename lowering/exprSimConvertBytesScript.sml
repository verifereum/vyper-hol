(* Shared conversion simulation for dynamic Bytes and String results. *)
Theory exprSimConvertBytes
Ancestors
  exprSimHypsDefs exprSimSource
  exprBopSimProps
  exprSimDefs exprSimProps exprSimStack loweringPosts
  exprSimConvert exprSimHyps  exprLowering exprLoweringProps compileEnv
  exprSimAlloc exprSimBuffer exprSimBufferStore exprSimLiteralBuffer exprSimHash
  exprOperandVar valueEncoding valueEncodingProofs
  vyperTypeSystem vyperValueOperation vyperValue vyperInterpreter vyperState
  gasSummary gasOutcome gasSummaryCompose gasExemptCert fragGasPath gasContext
  fragExec fragGasSeq fragGasSeqAbort fragGasMode freshWrites loweringSlice venomExecSemantics venomState
  words list integer_word valueCopyBytes abiDecoderString
Libs
  intLib

Theorem bytestring_read_lowered_footprint:
  !cenv e env cx es v es' tv.
    expr_body_pre cenv cx env e es /\
    (!a f args d. e = Call a (IntCall f) args d ==>
       lowered_value_type cenv e = expr_type e) /\
    is_bytestring_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') ==>
    val_footprint tv v <= type_memory_bytes cenv (lowered_value_type cenv e)
Proof
  rpt strip_tac >>
  drule_all memory_rhs_read_lowered_typed_unwidened >> strip_tac >>
  drule_all memory_rhs_read_annotation_typed >> strip_tac >>
  `is_bytestring_type (lowered_value_type cenv e)` by
    metis_tac[lowered_value_type_bytestring] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_body_pre_def, expr_sim_inv_def,
        vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
  `type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size tv'` by
    metis_tac[expr_sim_inv_memory_size, expr_body_pre_def] >>
  simp[] >> irule bytestring_val_footprint_le >> metis_tac[]
QED

(* Dynamic bytestring results require a dynamic bytestring source. *)
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
  rename1 `BaseT b` >> Cases_on `b` >>
  gvs[valid_conversion_def, is_bytestring_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[valid_conversion_def, is_bytestring_type_def]
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
      if is_bytestring_type (expr_type e1) /\
         type_memory_bytes cenv (lowered_value_type cenv e1) <
         type_memory_bytes cenv t
      then as_stack_val ann (compile_bytestring_widen_copy
             (type_memory_bytes cenv t) x
             (type_memory_bytes cenv (lowered_value_type cenv e1)) s1)
      else as_stack_val ann
             (compile_type_convert x (mk_convert_op (expr_type e1) t) s1)
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
      (if is_bytestring_type (expr_type e1) /\
          type_memory_bytes cenv (lowered_value_type cenv e1) <
          type_memory_bytes cenv t
       then compile_bytestring_widen_copy (type_memory_bytes cenv t) x
              (type_memory_bytes cenv (lowered_value_type cenv e1)) s1
       else compile_type_convert x (mk_convert_op (expr_type e1) t) s1) =
        (op,sb)
Proof
  rpt strip_tac >> drule is_bytestring_word_type >> strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[Once lower_value_def, comp_bind_def] >>
  simp[compile_convert_bytestring_shape] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `is_bytestring_type (expr_type e1) /\
    type_memory_bytes cenv (lowered_value_type cenv e1) < type_memory_bytes cenv t` >>
  gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  gvs[exprBopLoweringTheory.as_stack_val_pair, unwrap_value_def, comp_return_def,
      pairTheory.PAIR_FST_SND_EQ]
QED

Theorem convert_widen_copy_parts:
  !d x k sm op sb.
    compile_bytestring_widen_copy d x k sm = (op,sb) /\ 0 < k ==>
    ?buf mid. compile_alloc_buffer d sm = (buf,mid) /\
      op = buf.buf_operand /\
      emit_void MCOPY [buf.buf_operand; x; Lit (n2w k)] mid = ((),sb)
Proof
  rpt gen_tac >> Cases_on `k` >> simp[] >>
  simp[compile_bytestring_widen_copy_def, contextTheory.compile_copy_memory_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem convert_widen_copy_code:
  !d x k sm op sb func.
    compile_bytestring_widen_copy d x k sm = (op,sb) /\ 0 < k /\
    fn_has_code sm sb func ==>
    ?buf mid inst p.
      compile_alloc_buffer d sm = (buf,mid) /\ op = buf.buf_operand /\
      buf.buf_operand = Var p /\ ~not_fresh_at sm p /\
      emit_void MCOPY [Var p; x; Lit (n2w k)] mid = ((),sb) /\
      ci_mono sm mid /\ ci_mono mid sb /\
      fn_has_code sm mid func /\ fn_has_code mid sb func /\
      MEM inst (fn_insts func) /\ inst.inst_id = sm.cs_next_id /\
      inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p]
Proof
  rpt strip_tac >> drule_all convert_widen_copy_parts >> strip_tac >>
  `ci_mono sm mid` by
    (qspecl_then [`d`, `sm`] mp_tac ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono mid sb` by
    (qspecl_then [`MCOPY`, `[buf.buf_operand; x; Lit (n2w k)]`, `mid`]
       mp_tac ci_mono_emit_void >> simp[]) >>
  `fn_has_code sm mid func /\ fn_has_code mid sb func` by
    (irule fn_has_code_split >> gvs[ci_mono_def]) >>
  drule_all buffer_alloc_code >> strip_tac >>
  `emit_op ALLOCA [Lit (n2w d)] sm = (buf.buf_operand,mid)` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> strip_tac >> gvs[]) >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  qexistsl_tac [`buf`, `mid`,
    `mk_inst sm.cs_next_id ALLOCA [Lit (n2w d)]
       [STRING #"%" (toString sm.cs_next_var)]`,
    `STRING #"%" (toString sm.cs_next_var)`] >>
  gvs[venomInstTheory.mk_inst_def, not_fresh_at_def]
QED

Theorem convert_widen_copy_opcodes[local]:
  !d x k sm op sb.
    compile_bytestring_widen_copy d x k sm = (op,sb) /\ 0 < k ==>
    same_blocks sm sb /\ isPREFIX sm.cs_current_insts sb.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               ~is_terminator i.inst_opcode) (emitted_insts sm sb)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all convert_widen_copy_parts >> strip_tac >>
  gvs[contextTheory.compile_alloc_buffer_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def,
      emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
      emitHelperTheory.emit_inst_def, fresh_id_def, fresh_var_def, emit_def,
      same_blocks_def, emitted_insts_def] >>
  simp[rich_listTheory.IS_PREFIX_APPEND] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND, venomInstTheory.mk_inst_def,
       venomInstTheory.is_terminator_def]
QED

Theorem convert_widen_copy_run_path[local]:
  !d x k sm op sb func s t ctx.
    compile_bytestring_widen_copy d x k sm = (op,sb) /\ 0 < k /\
    fn_has_code sm sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts /\
    run_inst_seq (emitted_insts sm sb) s = OK t ==>
    gas_marked_path F ctx func s 0
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all convert_widen_copy_opcodes >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sm sb)
          (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, same_blocks_def, rich_listTheory.IS_PREFIX_APPEND,
         emitted_insts_def] >> simp[DROP_APPEND]) >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sb)) = 0` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `EVERY _ _` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then drule >> simp[]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts sm sb) =
     LENGTH sb.cs_current_insts` by
    (gvs[rich_listTheory.IS_PREFIX_APPEND, emitted_insts_def]) >>
  simp[gas_marked_path_def] >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) tuple_run_inst_seq_gas_path >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  simp[] >> disch_then irule >> fs[EVERY_MEM]
QED

Theorem bytestring_type_cases[local]:
  !t. is_bytestring_type t <=>
    (?n. t = BaseT (BytesT (Dynamic n))) \/ (?n. t = BaseT (StringT n))
Proof
  Cases >> simp[is_bytestring_type_def] >>
  rename1 `BaseT b` >> Cases_on `b` >> simp[is_bytestring_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >> simp[is_bytestring_type_def]
QED

Theorem bytestring_memory_bytes_aligned:
  !cenv t. is_bytestring_type t ==> type_memory_bytes cenv t MOD 32 = 0
Proof
  simp[bytestring_type_cases] >> rpt strip_tac >>
  simp[type_memory_bytes_def, arithmeticTheory.MOD_PLUS]
QED

Theorem bytestring_widen_length_bound:
  !len sz n.
    sz MOD 32 = 0 /\ len + 32 <= sz /\
    sz < 32 * ((n + 31) DIV 32) + 32 ==> len <= n
Proof
  rpt gen_tac >>
  qspec_then `32` mp_tac arithmeticTheory.DIVISION >> simp[] >>
  disch_then (fn th => map_every (fn q => qspec_then q mp_tac th)
    [`sz`, `n + 31`]) >>
  map_every (fn (tm,v) => Q.SPEC_TAC (tm,v))
    [(`(n + 31) MOD 32`, `r`), (`(n + 31) DIV 32`, `q`),
     (`sz MOD 32`, `srem`), (`sz DIV 32`, `squot`)] >> intLib.COOPER_TAC
QED

Theorem convert_bytestring_widen_success:
  !cx cenv src dst tv1 tv2 v srcsz.
    is_bytestring_type src /\ is_bytestring_type dst /\
    evaluate_type (get_tenv cx) src = SOME tv1 /\
    evaluate_type (get_tenv cx) dst = SOME tv2 /\
    value_has_type tv1 v /\ val_footprint tv1 v <= srcsz /\
    srcsz MOD 32 = 0 /\ srcsz < type_memory_bytes cenv dst ==>
    ?v'. convert_result cx src dst v = INL v'
Proof
  rpt gen_tac >> strip_tac >>
  gvs[bytestring_type_cases, evaluate_type_def] >>
  Cases_on `v` >>
  gvs[vyperTypingTheory.value_has_type_def, val_footprint_def,
      type_memory_bytes_def,
      convert_result_bytes_to_bytestring, convert_result_string_to_bytestring] >>
  irule bytestring_widen_length_bound >> metis_tac[]
QED

Theorem convert_bytestring_lowered_widen_success:
  !cx cenv src dst lowered tv1 tv2 v.
    is_bytestring_type src /\ is_bytestring_type dst /\
    is_bytestring_type lowered /\
    evaluate_type (get_tenv cx) src = SOME tv1 /\
    evaluate_type (get_tenv cx) dst = SOME tv2 /\
    value_has_type tv1 v /\
    val_footprint tv1 v <= type_memory_bytes cenv lowered /\
    type_memory_bytes cenv lowered < type_memory_bytes cenv dst ==>
    ?v'. convert_result cx src dst v = INL v'
Proof
  rpt strip_tac >> irule convert_bytestring_widen_success >>
  metis_tac[bytestring_memory_bytes_aligned]
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
  gvs[bytestring_type_cases] >>
  imp_res_tac vyperTypeValuesTheory.evaluate_type_BaseT_cases >> gvs[] >>
  metis_tac[local_val_at_base, arithmeticTheory.LESS_EQ_REFL]
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

Theorem convert_cast_run_frame[local]:
  !x n i sa op sb s p L.
    compile_type_convert x (ConvBytestringCast n i) sa = (op,sb) /\
    eval_operand x s = SOME p /\ mload (w2n p) s = n2w L /\
    L <= i /\ L <= n /\ i < dimword (:256) /\ n < dimword (:256) ==>
    ?tt. run_inst_seq (emitted_insts sa sb) s = OK tt /\
      tt = s with vs_vars := tt.vs_vars /\
      (!z. not_fresh_at sa z ==> lookup_var z tt = lookup_var z s)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `n < i`
  >- (`L < dimword (:256)` by decide_tac >>
      drule_all convert_cast_narrow_run >> simp[LET_THM] >> strip_tac >>
      qpat_x_assum `compile_type_convert _ _ _ = _` mp_tac >>
      simp[compile_type_convert_def, comp_bind_def, comp_ignore_bind_def,
           comp_return_def, emitHelperTheory.emit_void_def, emitHelperTheory.emit_op_def,
           emitHelperTheory.emit_inst_def, fresh_id_def, fresh_var_def, emit_def] >>
      strip_tac >> gvs[] >>
      qpat_x_assum `run_inst_seq _ _ = _` kall_tac >>
      simp[update_var_def] >> rpt strip_tac >>
      `z <> STRING #"%" (toString sa.cs_next_var) /\
       z <> STRING #"%" (toString (sa.cs_next_var + 1)) /\
       z <> STRING #"%" (toString (sa.cs_next_var + 2))` by
        (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_ADD]) >>
      simp[lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  gvs[compile_type_convert_def, comp_return_def,
      emitted_insts_def, run_inst_seq_def]
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
                 ~is_ext_call_op ins.inst_opcode) (emitted_insts sa sb) /\
    EVERY (\ins. ins.inst_opcode <> GAS) (emitted_insts sa sb)
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
  irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac
  >~ [`cenv.ce_imm_alloca = SOME (Var p)`]
  >- (`not_fresh_at sa p` by
        (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
      `lookup_var p s = SOME 0w` by
        fs[exprLoweringPropsTheory.stmt_state_rel_def, immutable_base_zero_def,
           eval_operand_def, lookup_var_def] >>
      qpat_x_assum `!z w. _ ==> lookup_var _ _ = _`
        (qspecl_then [`p`, `0w`] mp_tac) >>
      simp[lookup_var_def]) >>
  fs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
  first_x_assum drule_all >> strip_tac >>
  `not_fresh_at sa p` by
    (fs[local_ptrs_reserved_def] >> res_tac) >>
  qpat_x_assum `!z w. _ ==> lookup_var _ _ = _` drule >> simp[lookup_var_def]
QED

Theorem convert_cast_counted[local]:
  !ctx func cenv cx es sa sb op x p L n i s.
    compile_type_convert x (ConvBytestringCast n i) sa = (op,sb) /\
    fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
    (!z. x = Var z ==> not_fresh_at sa z) /\
    stmt_state_rel ctx func cenv cx es s /\ eval_operand x s = SOME p /\
    mload (w2n p) s = n2w L /\ L <= i /\
    i < dimword (:256) /\ n < dimword (:256) /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    (?t. gas_marked_path F ctx func s 0 (OK t) /\ L <= n /\
       stmt_state_rel ctx func cenv cx es t /\ eval_operand op t = SOME p /\
       t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
       (!z w. not_fresh_at sa z /\ lookup_var z s = SOME w ==>
              lookup_var z t = SOME w) /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts) \/
    (?t. gas_marked_path F ctx func s 0 (Abort Revert_abort t) /\ n < L)
Proof
  rpt gen_tac >> strip_tac >>
  drule convert_cast_static_frame >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sa sb)
          (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, same_blocks_def, rich_listTheory.IS_PREFIX_APPEND,
         emitted_insts_def] >> simp[DROP_APPEND]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
              ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    fs[EVERY_MEM] >>
  Cases_on `L <= n`
  >- suspend "success"
  >> disj2_tac >>
  `n < L` by decide_tac >>
  drule_all convert_cast_abort_run >> strip_tac >>
  drule_all run_inst_seq_abort_zero_path >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[] >>
  strip_tac >> goal_assum (drule_at Any) >> simp[]
QED

Resume convert_cast_counted[success]:
  disj1_tac >> drule_all convert_cast_run_frame >> strip_tac >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = 0` by
    simp[FILTER_EQ_NIL, EVERY_MEM] >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) =
     LENGTH sb.cs_current_insts` by
    gvs[rich_listTheory.IS_PREFIX_APPEND, emitted_insts_def] >>
  drule_at (Pat `run_inst_seq _ _ = OK _`) tuple_run_inst_seq_gas_path >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  simp[] >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es tt` by
    (irule convert_readonly_state_frame >> qexistsl_tac [`s`, `sa`] >> simp[]) >>
  `eval_operand x tt = SOME p` by
    (Cases_on `x` >> gvs[eval_operand_def] >>
     qpat_x_assum `tt = _` (fn th => once_rewrite_tac[th]) >>
     simp[eval_operand_def]) >>
  qexists_tac `tt with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[gas_marked_path_def, stmt_state_rel_inst_idx] >>
  conj_tac
  >- (first_x_assum irule >> fs[EVERY_MEM]) >>
  qpat_x_assum `tt = _` (fn th => once_rewrite_tac[th]) >>
  simp[lookup_var_def, same_blocks_def] >>
  fs[same_blocks_def, lookup_var_def]
QED

Finalise convert_cast_counted

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
    wb_frame cenv es es sa s0 s1 /\ wb_frame cenv es1 es1 sm s1 s2 /\
    stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id ==>
    wb_frame cenv es es sa s0 s2
Proof
  rpt gen_tac >> strip_tac >>
  `locals_kept cenv es es s0 s2` by
    (irule exprBopSimPropsTheory.locals_kept_trans >>
     qexistsl_tac [`es1`, `sa`, `s1`] >>
     gvs[loweringPostsTheory.wb_frame_def]) >>
  gvs[loweringPostsTheory.wb_frame_def] >> conj_tac
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
       (irule exprSimPropsTheory.local_region_frame >>
        conj_tac >- (qexists_tac `func` >>
          gvs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def]) >>
        qexistsl_tac [`sa`, `es1.scopes`, `s1`] >> simp[]) >>
     metis_tac[]) >>
  metis_tac[]
QED

Theorem convert_buffer_expr_post:
  !ctx func cenv cx e es es' sa sb s0 tt v tv op p sz.
    ~is_word_type (expr_type e) /\
    post_value_type cenv e = expr_type e /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    val_wf tv v /\ val_in_memory tv v (w2n p) tt.vs_memory /\
    stmt_state_rel ctx func cenv cx es' tt /\ eval_operand op tt = SOME p /\
    FLOOKUP tt.vs_allocas sa.cs_next_id = SOME (w2n p,sz) /\
    sa.cs_next_id < sb.cs_next_id /\ val_footprint tv v <= sz /\
    (!name lb lsz. local_region cenv es'.scopes tt name lb lsz ==>
       w2n p + sz <= lb \/ lb + lsz <= w2n p) /\
    wb_frame cenv es es' sa s0 tt ==>
    expr_post ctx func cenv cx e es sa sb s0 es' v op tt
Proof
  rpt gen_tac >> strip_tac >>
  gvs[expr_post_def, expr_val_rel_def, expr_val_at_def,
      loweringPostsTheory.wb_frame_def] >>
  reverse conj_tac >- metis_tac[] >>
  disj1_tac >> qexistsl_tac [`sa.cs_next_id`, `w2n p`, `sz`] >>
  simp[] >> metis_tac[]
QED

Theorem convert_widen_copy_run[local]:
  !ctx func cenv cx es sm sb s x op p d k e v tv.
    compile_bytestring_widen_copy d x k sm = (op,sb) /\
    0 < k /\ k <= d /\ d < dimword (:256) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
    (!z. x = Var z ==> not_fresh_at sm z) /\ eval_operand x s = SOME p /\
    ~is_word_type (expr_type e) /\ post_value_type cenv e = expr_type e /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    val_wf tv v /\ val_in_memory tv v (w2n p) s.vs_memory /\
    val_footprint tv v <= k ==>
    ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
        expr_post ctx func cenv cx e es sm sb s es v op t
Proof
  rpt gen_tac >> strip_tac >>
  drule_all convert_widen_copy_code >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  drule_all hash_alloc_buffer_labels >> strip_tac >>
  `eval_operand x t = SOME p` by
    (Cases_on `x` >> gvs[eval_operand_def]) >>
  `run_inst_seq (emitted_insts mid sb) t =
     OK (mcopy (w2n w) (w2n p) (w2n (n2w k:256 word)) t)` by
    (irule buffer_emit_mcopy_run >>
     qexistsl_tac [`buf.buf_operand`, `x`, `Lit (n2w k)`] >>
     gvs[eval_operand_def]) >>
  `emitted_insts sm sb = emitted_insts sm mid ++ emitted_insts mid sb` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     qpat_x_assum `emit_void MCOPY _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     gvs[contextTheory.compile_alloc_buffer_def, comp_bind_def, comp_return_def,
         comp_ignore_bind_def, emitHelperTheory.emit_op_def,
         emitHelperTheory.emit_void_def, emitHelperTheory.emit_inst_def,
         fresh_id_def, fresh_var_def, emit_def, emitted_insts_def,
         rich_listTheory.DROP_LENGTH_APPEND] >>
     simp[DROP_APPEND]) >>
  qpat_assum `run_inst_seq (emitted_insts sm mid) s = OK t`
    (mp_then Any mp_tac run_inst_seq_append) >>
  disch_then (qspec_then `emitted_insts mid sb` assume_tac) >>
  qexists_tac `mcopy (w2n w) (w2n p) k t` >>
  `k < dimword (:256)` by decide_tac >>
  simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  suspend "owned_post"
QED

Resume convert_widen_copy_run[owned_post]:
  `not_local_ptr cenv es.scopes p'` by
    (irule exprSimOperandsTheory.fresh_not_local_ptr >>
     goal_assum (drule_at Any) >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es (mcopy (w2n w) (w2n p) k t)` by
    (irule stmt_state_rel_mcopy_alloca >> simp[] >>
     qexistsl_tac [`d`, `inst`, `p'`] >> simp[]) >>
  `val_in_memory tv v (w2n w) (mcopy (w2n w) (w2n p) k t).vs_memory` by
    (irule buffer_mcopy_encoding >> simp[]) >>
  `(mcopy (w2n w) (w2n p) k t).vs_allocas = t.vs_allocas` by
    simp[venomExecSemanticsTheory.mcopy_def,
         venomStateTheory.write_memory_with_expansion_def] >>
  irule convert_buffer_expr_post >>
  `sm.cs_next_id < sb.cs_next_id` by gvs[ci_mono_def] >>
  qpat_assum `post_value_type _ _ = _` (fn th => simp[th]) >> conj_tac
  >- (conj_tac
      >- (rpt strip_tac >>
          qpat_assum `stmt_state_rel _ _ _ _ _ (mcopy _ _ _ _)`
            (mp_then Any mp_tac exprSimOperandsTheory.alloca_clear_of_locals) >>
          disch_then (qspec_then `inst` mp_tac) >>
          simp[] >> disch_then drule_all >> simp[]) >>
      simp[venomExecSemanticsTheory.mcopy_def,
           venomStateTheory.write_memory_with_expansion_def,
           eval_operand_def, venomStateTheory.lookup_var_def] >>
      gvs[eval_operand_def, venomStateTheory.lookup_var_def]) >>
  simp[wb_frame_def] >> rpt conj_tac
  >- (simp[venomExecSemanticsTheory.mcopy_def,
           venomStateTheory.write_memory_with_expansion_def,
           venomStateTheory.lookup_var_def] >>
      metis_tac[venomStateTheory.lookup_var_def])
  >- (rpt strip_tac >>
      qpat_x_assum `!aid b len. _` drule_all >>
      simp[regions_disjoint_def] >> strip_tac >>
      (irule EQ_TRANS >> qexists_tac `mem_bytes_at off sz t.vs_memory` >>
       conj_tac >- (irule buffer_mcopy_exterior >> decide_tac) >> simp[])) >>
  irule locals_kept_regions >> rpt strip_tac >>
  `local_region cenv es.scopes t n b sz` by
    (irule exprSimPropsTheory.local_region_frame_fwd >>
     qexistsl_tac [`s`, `sm`, `es.scopes`] >> simp[]) >>
  qpat_x_assum `!name b len. _` drule >>
  simp[regions_disjoint_def] >> strip_tac >>
  (irule EQ_TRANS >> qexists_tac `mem_bytes_at b sz t.vs_memory` >>
   conj_tac >- (irule buffer_mcopy_exterior >> decide_tac) >> simp[])
QED

Finalise convert_widen_copy_run

Theorem convert_widen_copy_owned:
  !ctx func cenv cx es sm sb s e v tv x op p d k.
    compile_bytestring_widen_copy d x k sm = (op,sb) /\
    0 < k /\ k <= d /\ d < dimword (:256) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
    (!z. x = Var z ==> not_fresh_at sm z) /\
    eval_operand x s = SOME p /\ ~is_word_type (expr_type e) /\
    post_value_type cenv e = expr_type e /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    val_wf tv v /\ val_in_memory tv v (w2n p) s.vs_memory /\
    val_footprint tv v <= k /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
        expr_post ctx func cenv cx e es sm sb s es v op t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  drule_all convert_widen_copy_run >> strip_tac >>
  drule_all convert_widen_copy_run_path >> strip_tac >>
  drule_all convert_widen_copy_opcodes >> strip_tac >>
  `t.vs_current_bb = s.vs_current_bb` by
    (irule (SRULE [] run_inst_seq_preserves_field) >>
     qexists_tac `emitted_insts sm sb` >> simp[] >> rpt strip_tac >>
     `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by
       (qpat_x_assum `EVERY _ _` (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
        disch_then drule >> simp[]) >>
     `step_inst 0 ctx i ss1 = OK ss2` by simp[step_inst_non_invoke] >>
     drule_all venomInstProofsTheory.step_preserves_control_flow >> simp[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[same_blocks_def] >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       stmt_state_rel_inst_idx, lookup_var_def, local_region_def,
       locals_kept_def, eval_operand_def] >>
  strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
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
  `wb_frame cenv es es1 sa s0 s1` by
    (gvs[expr_post_def, loweringPostsTheory.wb_frame_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv es1 es1 sm s1 tt` by
    (gvs[expr_post_def, loweringPostsTheory.wb_frame_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all convert_wb_frame_trans >> strip_tac >>
  gvs[expr_post_def, loweringPostsTheory.wb_frame_def] >>
  conj_tac
  >- (irule expr_val_at_start_mono >> goal_assum (drule_at Any) >> simp[]) >>
  reverse conj_tac >- (first_assum ACCEPT_TAC) >>
  strip_tac >> irule expr_val_own_start_mono >>
  goal_assum (drule_at Any) >> simp[]
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
     >- (strip_tac >> irule exprSimPropsTheory.local_region_frame >>
         conj_tac >- (qexists_tac `func` >> simp[]) >>
         qexistsl_tac [`sm`, `es.scopes`, `tt`] >> simp[]) >>
     strip_tac >> irule exprSimPropsTheory.local_region_frame_fwd >>
     qexistsl_tac [`s`, `sm`, `es.scopes`] >> simp[]) >>
  gvs[expr_val_at_def] >> rpt strip_tac >>
  qpat_x_assum `!tv. _ ==> _` drule_all >> strip_tac >>
  gvs[]
  >- (disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
      first_assum ACCEPT_TAC) >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`n`, `b`, `sz`] >> simp[]
QED

Theorem convert_readonly_val_own:
  !func cenv cx ty sa sm sb es v x op s tt p.
    expr_val_own cenv cx ty sa sm es v x s /\
    eval_operand x s = SOME p /\ eval_operand op tt = SOME p /\
    tt.vs_allocas = s.vs_allocas /\ sm.cs_next_id <= sb.cs_next_id /\
    local_ptrs_rel func cenv es.scopes s /\ local_ptrs_reserved cenv sm /\
    (!z w. not_fresh_at sm z /\ lookup_var z s = SOME w ==>
      lookup_var z tt = SOME w) ==>
    expr_val_own cenv cx ty sa sb es v op tt
Proof
  rpt gen_tac >> strip_tac >>
  `!n b sz. local_region cenv es.scopes tt n b sz <=>
             local_region cenv es.scopes s n b sz` by
    (rpt gen_tac >> eq_tac
     >- (strip_tac >> irule exprSimPropsTheory.local_region_frame >>
         conj_tac >- (qexists_tac `func` >> simp[]) >>
         qexistsl_tac [`sm`, `es.scopes`, `tt`] >> simp[]) >>
     strip_tac >> irule exprSimPropsTheory.local_region_frame_fwd >>
     qexistsl_tac [`s`, `sm`, `es.scopes`] >> simp[]) >>
  gvs[expr_val_own_def] >> rpt strip_tac >>
  qpat_x_assum `!tv. _ ==> _` drule_all >> strip_tac >> gvs[] >>
  disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
  first_assum ACCEPT_TAC
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
  `expr_val_at cenv cx (post_value_type cenv e) sa sb es1 v op tt` by
    (irule convert_readonly_val_at >> goal_assum (drule_at Any) >>
     gvs[expr_post_def] >> metis_tac[]) >>
  `expr_val_rel cx (post_value_type cenv e) v op tt` by
    (gvs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  `post_value_type cenv e <> expr_type e ==>
   expr_val_own cenv cx (post_value_type cenv e) sa sb es1 v op tt` by
    (strip_tac >> irule convert_readonly_val_own >>
     goal_assum (drule_at Any) >> gvs[expr_post_def] >> metis_tac[]) >>
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

Theorem convert_bytestring_operand_facts[local]:
  expr_body_pre cenv cx env (TypeBuiltin t Convert t [e1]) es /\
  is_bytestring_type t /\
  (!a f args d. e1 = Call a (IntCall f) args d ==>
     lowered_value_type cenv e1 = expr_type e1) /\
  (do r <- eval_expr cx e1; read_result cx r od)
    (es with gas_obs := gs) = (INL v,ee) ==>
  ?tv1 tv2.
    evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
    evaluate_type (get_tenv cx) t = SOME tv2 /\ value_has_type tv1 v /\
    val_footprint tv1 v <= type_memory_bytes cenv (lowered_value_type cenv e1) /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes
Proof
  strip_tac >>
  `expr_body_pre cenv cx env (TypeBuiltin t Convert t [e1])
     (es with gas_obs := gs)` by simp[] >>
  drule_all convert_operand_typed >> strip_tac >>
  drule expr_body_pre_convert >> strip_tac >> gvs[] >>
  `is_bytestring_type (expr_type e1)` by
    metis_tac[valid_conversion_to_bytestring] >>
  conj_tac
  >- (irule bytestring_read_lowered_footprint >>
      conj_tac >- metis_tac[] >> simp[] >>
      qexistsl_tac [`cx`, `env`, `es with gas_obs := gs`, `ee`] >> simp[]) >>
  drule bop_value_scopes_dom >> simp[]
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

Theorem convert_widen_cont:
  !ctx func cenv cx e e1 es es1 sa sm sb s0 s v x op tv1 tv2.
    is_bytestring_type (expr_type e1) /\ is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type cenv e1) /\
    evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv2 /\
    value_has_type tv1 v /\
    val_footprint tv1 v <= type_memory_bytes cenv (lowered_value_type cenv e1) /\
    type_memory_bytes cenv (lowered_value_type cenv e1) <
      type_memory_bytes cenv (expr_type e) /\
    type_memory_bytes cenv (expr_type e) < dimword (:256) /\
    expr_post ctx func cenv cx e1 es sa sm s0 es1 v x s /\
    compile_bytestring_widen_copy (type_memory_bytes cenv (expr_type e)) x
      (type_memory_bytes cenv (lowered_value_type cenv e1)) sm = (op,sb) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\ MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    (!z. x = Var z ==> not_fresh_at sm z) /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?tt v'. gas_marked_path F ctx func s 0 (OK tt) /\
      convert_result cx (expr_type e1) (expr_type e) v = INL v' /\
      expr_post ctx func cenv cx e es sa sb s0 es1 v' op tt /\
      tt.vs_current_bb = sb.cs_current_bb /\
      tt.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  drule_all convert_bytestring_lowered_widen_success >> strip_tac >>
  drule_all convert_bytestring_wf >> strip_tac >>
  `?p. eval_operand x s = SOME p /\
       val_in_memory tv1 v (w2n p) s.vs_memory` by
    (gvs[expr_post_def, expr_val_rel_def] >>
     `~is_word_type (expr_type e1)` by
       gvs[bytestring_type_cases, is_word_type_def] >> metis_tac[]) >>
  drule_all convert_bytestring_memory >>
  disch_then (qspecl_then [`w2n p`, `s.vs_memory`] strip_assume_tac) >>
  `~is_word_type (expr_type e)` by
    gvs[bytestring_type_cases, is_word_type_def] >>
  `0 < type_memory_bytes cenv (lowered_value_type cenv e1)` by
    metis_tac[valueCopyBytesTheory.bytestring_memory_bytes_positive] >>
  `stmt_state_rel ctx func cenv cx es1 s` by gvs[expr_post_def] >>
  `type_memory_bytes cenv (lowered_value_type cenv e1) <=
     type_memory_bytes cenv (expr_type e)` by decide_tac >>
  `val_in_memory tv2 v' (w2n p) s.vs_memory` by metis_tac[] >>
  `val_footprint tv2 v' <= type_memory_bytes cenv (lowered_value_type cenv e1)` by simp[] >>
  `post_value_type cenv e = expr_type e` by simp[] >>
  drule_all convert_widen_copy_owned >> strip_tac >>
  qexistsl_tac [`t`, `v'`] >> simp[] >>
  qpat_assum `expr_post _ _ _ _ e1 _ _ _ _ _ _ _ _`
    (mp_then Any mp_tac convert_expr_post_compose) >>
  disch_then drule_all >> simp[]
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
  `post_value_type cenv e1 = expr_type e1` by
    (irule post_value_type_bytestring >> gvs[is_bytestring_type_def]) >>
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

Theorem convert_dynamic_counted_cont[local]:
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
    fn_has_code sm sb func /\ local_ptrs_reserved cenv sm /\
    sa.cs_next_var <= sm.cs_next_var /\
    (!z. x = Var z ==> not_fresh_at sm z) /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    (?tt v'. gas_marked_path F ctx func s 0 (OK tt) /\
      convert_result cx (expr_type e1) (expr_type e) v = INL v' /\
      expr_post ctx func cenv cx e es sa sb s0 es1 v' op tt /\
      tt.vs_current_bb = sb.cs_current_bb /\
      tt.vs_inst_idx = LENGTH sb.cs_current_insts) \/
    (?tt. gas_marked_path F ctx func s 0 (Abort Revert_abort tt) /\
      expr_exit (convert_result cx (expr_type e1) (expr_type e) v)
        (Abort Revert_abort tt))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `post_value_type cenv e1 = expr_type e1` by
    (irule post_value_type_bytestring >> gvs[is_bytestring_type_def]) >>
  `expr_val_rel cx (expr_type e1) v x s /\
   stmt_state_rel ctx func cenv cx es1 s` by gvs[expr_post_def] >>
  drule_all convert_dynamic_view >> strip_tac >>
  drule convert_cast_grows >> strip_tac >>
  drule_all convert_cast_counted >> strip_tac
  >- suspend "success" >>
  disj2_tac >> goal_assum (drule_at Any) >>
  first_x_assum drule >> strip_tac >> simp[expr_exit_def]
QED

Resume convert_dynamic_counted_cont[success]:
  disj1_tac >>
  `?v'. convert_result cx (expr_type e1) (expr_type e) v = INL v'` by
    (first_x_assum irule >> simp[]) >>
  qexistsl_tac [`t`, `v'`] >> simp[] >>
  irule convert_bytestring_expr_post >>
  conj_tac >- gvs[is_bytestring_type_def] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`e1`, `tv1`, `v`] >>
  simp[] >> conj_tac >- gvs[is_bytestring_type_def] >>
  irule convert_readonly_expr_post >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`s`, `sm`, `x`] >> simp[]
QED

Finalise convert_dynamic_counted_cont

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

Theorem convert_bytestring_counted_cont[local]:
  !ctx func cenv cx e e1 es es1 sa sm sb s0 s v x op tv1 tv2.
    valid_conversion (expr_type e1) (expr_type e) /\
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type cenv e1) /\
    evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv2 /\
    value_has_type tv1 v /\
    val_footprint tv1 v <= type_memory_bytes cenv (lowered_value_type cenv e1) /\
    type_memory_bytes cenv (expr_type e) < dimword (:256) /\
    expr_post ctx func cenv cx e1 es sa sm s0 es1 v x s /\
    (if type_memory_bytes cenv (lowered_value_type cenv e1) <
        type_memory_bytes cenv (expr_type e) then
       compile_bytestring_widen_copy (type_memory_bytes cenv (expr_type e)) x
         (type_memory_bytes cenv (lowered_value_type cenv e1)) sm
     else compile_type_convert x (mk_convert_op (expr_type e1) (expr_type e)) sm) = (op,sb) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\ MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    (!z. x = Var z ==> not_fresh_at sm z) /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    (?tt v'. gas_marked_path F ctx func s 0 (OK tt) /\
      convert_result cx (expr_type e1) (expr_type e) v = INL v' /\
      expr_post ctx func cenv cx e es sa sb s0 es1 v' op tt /\
      tt.vs_current_bb = sb.cs_current_bb /\
      tt.vs_inst_idx = LENGTH sb.cs_current_insts) \/
    (?tt. gas_marked_path F ctx func s 0 (Abort Revert_abort tt) /\
      expr_exit (convert_result cx (expr_type e1) (expr_type e) v)
        (Abort Revert_abort tt))
Proof
  rpt gen_tac >> strip_tac >>
  `is_bytestring_type (expr_type e1)` by
    metis_tac[valid_conversion_to_bytestring] >>
  Cases_on `type_memory_bytes cenv (lowered_value_type cenv e1) <
              type_memory_bytes cenv (expr_type e)`
  >- (gvs[] >> drule_all convert_widen_cont >> metis_tac[]) >>
  gvs[] >>
  drule_all valid_conversion_to_bytestring >> strip_tac >>
  gvs[bytestring_type_cases, mk_convert_op_to_bytestring] >>
  qpat_assum `expr_type e1 = _` (fn th => pure_rewrite_tac [GSYM th]) >>
  qpat_assum `expr_type e = _` (fn th => pure_rewrite_tac [GSYM th]) >>
  irule convert_dynamic_counted_cont >> goal_assum (drule_at Any) >>
  simp[] >> qexistsl_tac [`sm`, `x`] >> simp[]
QED

Theorem convert_bytestring_continuation_summary[local]:
  valid_conversion (expr_type e1) (expr_type e) /\
  is_bytestring_type (expr_type e) /\
  is_bytestring_type (lowered_value_type cenv e1) /\
  evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv2 /\
  value_has_type tv1 v /\
  val_footprint tv1 v <= type_memory_bytes cenv (lowered_value_type cenv e1) /\
  type_memory_bytes cenv (expr_type e) < dimword (:256) /\
  expr_post ctx func cenv cx e1 es sa sm s0 (ee with gas_obs := []) v x s /\
  (if type_memory_bytes cenv (lowered_value_type cenv e1) <
      type_memory_bytes cenv (expr_type e) then
     compile_bytestring_widen_copy (type_memory_bytes cenv (expr_type e)) x
       (type_memory_bytes cenv (lowered_value_type cenv e1)) sm
   else compile_type_convert x (mk_convert_op (expr_type e1) (expr_type e)) sm) = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!z. x = Var z ==> not_fresh_at sm z) /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  expr_res_ok (convert_result cx (expr_type e1) (expr_type e) v) ==>
  gas_summary_at F (ctx,func) []
    (\vs. (convert_result cx (expr_type e1) (expr_type e) v,vs))
    (ee with gas_obs := [],s)
    (\res fin tt. ?v'. res = INL v' /\
      expr_post ctx func cenv cx e es sa sb s0 fin v' op tt /\
      tt.vs_current_bb = sb.cs_current_bb /\
      tt.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res fin r. expr_exit res r)
Proof
  strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM (ee with gas_obs := []).scopes` by simp[] >>
  drule_all convert_bytestring_counted_cont >> strip_tac
  >- (simp[gas_summary_at_def] >>
      qexistsl_tac [`INL v'`, `ee`, `OK tt`] >>
      simp[gas_marked_exec_def]) >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`convert_result cx (expr_type e1) (expr_type e) v`,
               `ee`, `Abort Revert_abort tt`] >>
  simp[gas_marked_exec_def, exit_result_def]
QED

Theorem compile_convert_bytestring_frag_sim[local]:
  !ctx func cenv cx env ty t e1 es.
    expr_body_pre cenv cx env (TypeBuiltin t Convert t [e1]) es /\
    is_bytestring_type t /\
    (!a f args d. e1 = Call a (IntCall f) args d ==>
       lowered_value_type cenv e1 = expr_type e1) /\
    expr_sim ctx func cenv cx (expr_type e1) e1 es ==>
    expr_sim ctx func cenv cx ty (TypeBuiltin t Convert t [e1]) es
Proof
  rpt gen_tac >> strip_tac >>
  drule expr_body_pre_convert >> strip_tac >> gvs[] >>
  simp[expr_sim_def] >> rpt gen_tac >> strip_tac >>
  `!n. t <> FlagT n` by (Cases_on `t` >> gvs[is_bytestring_type_def]) >>
  drule_all lower_value_convert_bytestring >> strip_tac >>
  drule (cj 2 exprLoweringPropsTheory.compile_expr_grows) >> strip_tac >>
  `is_bytestring_type (expr_type e1)` by
    metis_tac[valid_conversion_to_bytestring] >>
  `is_bytestring_type (lowered_value_type cenv e1)` by
    metis_tac[lowered_value_type_bytestring] >>
  `cs_extends s1 sb /\ s1.cs_next_var <= sb.cs_next_var /\
   s1.cs_next_id <= sb.cs_next_id` by
    (Cases_on `type_memory_bytes cenv (lowered_value_type cenv e1) < type_memory_bytes cenv t`
     >- (gvs[] >>
         `0 < type_memory_bytes cenv (lowered_value_type cenv e1)` by
           metis_tac[bytestring_memory_bytes_positive] >>
         drule_all convert_widen_copy_parts >> strip_tac >>
         `ci_mono s1 mid` by
           metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
         `ci_mono mid sb` by
           metis_tac[ci_mono_emit_void, pairTheory.SND] >>
         gvs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
     gvs[] >> metis_tac[convert_bytestring_suffix_grows]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `local_ptrs_reserved cenv s1` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!z. x = Var z ==> not_fresh_at s1 z` by
    (metis_tac[exprOperandVarTheory.compile_lower_value_var]) >>
  `gas_admissible (bind (eval_expr cx e1) (read_result cx)) expr_res_ok es` by
    (irule convert_operand_admissible >> metis_tac[]) >>
  qpat_x_assum `expr_sim _ _ _ _ _ e1 _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `x`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- suspend "counted" >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule convert_exempt_cert >> simp[]
QED

Resume compile_convert_bytestring_frag_sim[counted]:
  qexists_tac `marks` >> disj1_tac >>
  rewrite_tac[eval_expr_convert_action] >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_summary_at_def]) >>
  strip_tac
  >- suspend "normal" >>
  Cases_on `res` >- gvs[] >>
  simp[gas_summary_at_def] >> qexistsl_tac [`INR y`, `es_end`, `r`] >>
  simp[] >> conj_tac
  >- (irule gas_marked_exec_bind_exception >> simp[]) >>
  gvs[]
QED

Resume compile_convert_bytestring_frag_sim[normal]:
  gvs[] >>
  `bind (eval_expr cx e1) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v, es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `!a f args d. e1 = Call a (IntCall f) args d ==>
     lowered_value_type cenv e1 = expr_type e1` by metis_tac[] >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) convert_bytestring_operand_facts) >> strip_tac >>
  `~t'.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `expr_res_ok (convert_result cx (expr_type e1) t v)` by
    (qpat_x_assum
       `gas_admissible (bind (eval_expr cx (TypeBuiltin _ _ _ _)) _) _ es`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
     rewrite_tac[eval_expr_convert_action] >>
     simp[bind_def] >> disch_then irule >> simp[]) >>
  `type_memory_bytes cenv t < dimword (:256)` by
    (`~is_word_type t` by gvs[bytestring_type_cases, is_word_type_def] >>
     `alloc_limits_expr cenv (TypeBuiltin t Convert t [e1])` by
       gvs[expr_body_pre_def] >>
     gvs[allocLimitsTheory.alloc_limits_expr_def,
         allocLimitsTheory.type_alloc_ok_def, vyperASTTheory.expr_type_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  `MAP FDOM es.scopes = MAP FDOM es_end.scopes` by fs[] >>
  drule_all (Q.INST [`e` |-> `TypeBuiltin t Convert t [e1]`]
    convert_bytestring_continuation_summary |> REWRITE_RULE [vyperASTTheory.expr_type_def]) >>
  rewrite_tac[gas_summary_at_def] >> strip_tac >>
  qexistsl_tac [`res`, `es_end'`, `r`] >>
  (conj_tac
   >- (irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
              |> REWRITE_RULE [APPEND_NIL]) >>
       qexistsl_tac [`es_end`, `t'`, `v`] >> gvs[]) >>
   gvs[])
QED

Finalise compile_convert_bytestring_frag_sim

Theorem compile_convert_to_bytestring_case:
  !nocalls ctx func cenv cx ann t e1.
    exprs_case nocalls ctx func cenv cx [e1] /\
    is_bytestring_type t /\
    (!a f args d. e1 = Call a (IntCall f) args d ==>
       lowered_value_type cenv e1 = expr_type e1) ==>
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
