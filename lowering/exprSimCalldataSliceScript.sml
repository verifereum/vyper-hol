(*
 * Expression simulation: slice(msg.data, start, n) (#636, Builtins row 1)
 *
 * The builtin CalldataSlice n.  The lowering allocates an output buffer of
 * 32 + 32 * word_size n bytes (compile_slice_out_buf), asserts
 * start + n <= CALLDATASIZE without wrapping (compile_assert_slice_bounds),
 * copies the bytes with CALLDATACOPY and stores the length n in the
 * buffer's first word.  The source raises where n = 0 or start + n
 * overflows (evaluate_calldata_slice), and where start + n is past the
 * calldata (evaluate_slice).  expr_body_pre's alloc_limits_expr keeps the
 * buffer below 2 ** 64 bytes, as Python's allocator does.
 *
 * TOP-LEVEL:
 *   compile_calldata_slice_call_case — expr_vv_case of CalldataSlice n
 *
 * Also exported: bytes_buffer_write_encoding, bytes_buffer_write_state_rel,
 *   bytes_buffer_write_frame (a bytes value written into a fresh buffer);
 *   mstore_equal_memory, write_memory_with_expansion_equal_memory;
 *   vv_at_start_mono, vv_post_prefix_frame;
 *   compile_unary_builtin_rel_vv_sim (a unary builtin whose counted suffix
 *   also has the entry state relation).
 *)

Theory exprSimCalldataSlice
Ancestors
  exprSimHashBoundary
  exprSimVVFrame
  exprSimSource
  exprSimUnwrapProps
  exprSimProps
  exprSimHypsDefs
  exprSimDefs
  loweringPosts
  exprSimAlloc
  allocLimits
  list fragExec loweringSlice builtinBytes  exprSimHyps exprBopLowering
  exprSimOperators vyperEvalExprPreservesScopesDom
  exprLowering exprLoweringProps builtinSimple emitHelper compileEnv loweringStateRelDefs
  valueEncoding valueEncodingDefs venomExecSemantics venomInst venomState vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeSystem
  vyperTypeInvariants vyperTyping vyperValueOperation vyperValue
  exprSimWordBuiltins exprSimWordArgs emitHelperProps freshWrites
  exprSimPrecompiles exprSimHash valueEncodingProps valueCopy exprSimLiteralBuffer
  loweringHalt valueTypingMemoryProps
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext fragGasPath

Theorem calldata_slice_typing:
  well_typed_expr env (Builtin ann (CalldataSlice n) args) ==>
  ?e. args = [e] /\ expr_type e = BaseT (UintT 256) /\
      ann = BaseT (BytesT (Dynamic n)) /\ 0 < n /\ n < 2 ** 256
Proof
  simp[Once well_typed_expr_def, well_typed_builtin_app_def] >>
  strip_tac >> Cases_on `args` >> gvs[] >>
  rename1 `MAP expr_type rest = []` >> Cases_on `rest` >> gvs[]
QED

Theorem names_builtin_calldata_slice:
  !args. ~names_builtin (CalldataSlice n) args
Proof
  `!bt args. names_builtin bt args ==> bt <> CalldataSlice n` suffices_by
    metis_tac[] >>
  ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]
QED

Theorem compile_calldata_slice_parts:
  !cenv ty ann n e sa.
    compile_expr cenv ty (Builtin ann (CalldataSlice n) [e]) sa =
    let (start_op, sb) = lower_value compile_expr cenv (expr_type e) e sa in
    as_ptr_val ann LocMemory
      (compile_slice_calldata start_op (Lit (n2w n))
        (type_memory_bytes cenv ann) sb)
Proof
  rpt gen_tac >>
  simp[compile_expr_builtin_dispatch, names_builtin_calldata_slice] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[lower_value_child_call, vyperASTTheory.expr_size_def, list_size_def]
QED

Theorem evaluate_calldata_slice_uint:
  evaluate_calldata_slice bs (IntV &start) n =
  if n = 0 \/ 2 ** 256 <= start + n then
    INR (RuntimeError "calldata slice overflow")
  else if start + n <= LENGTH bs then
    INL (BytesV (TAKE n (DROP start bs)))
  else INR (RuntimeError "evaluate_slice range")
Proof
  simp[evaluate_calldata_slice_def, evaluate_slice_def, dest_NumV_def,
       compatible_bound_def]
QED

Theorem eval_calldata_slice_cases:
  eval_expr cx (Builtin ann (CalldataSlice n) [e]) es = (res, es') ==>
  (?exc. eval_exprs cx [e] es = (INR exc, es') /\ res = INR exc) \/
  ?vs. eval_exprs cx [e] es = (INL vs, es') /\
       res = (case vs of
         [v] => (case evaluate_calldata_slice cx.txn.calldata v n of
                   INL out => INL (Value out)
                 | INR err => INR (Error err))
       | _ => INR (Error (TypeError "builtin")))
Proof
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def] >>
  Cases_on `eval_exprs cx [e] es` >> rename1 `_ = (rr,es1)` >>
  Cases_on `rr` >> simp[get_accounts_def, bind_def, return_def,
                         builtin_args_length_ok_def] >>
  rename1 `eval_exprs cx [e] es = (INL vs,es1)` >>
  simp[evaluate_builtin_def, lift_sum_def, bind_def, return_def, raise_def] >>
  Cases_on `vs` >> simp[raise_def] >>
  rename1 `eval_exprs cx [e] es = (INL (v::rest),es1)` >>
  Cases_on `rest` >> simp[raise_def] >>
  Cases_on `evaluate_calldata_slice cx.txn.calldata v n` >>
  simp[return_def, raise_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem slice_bounds_mod:
  a < modulus /\ n < modulus /\ limit < modulus ==>
  ((a + n) MOD modulus < a \/ limit < (a + n) MOD modulus <=>
   modulus <= a + n \/ limit < a + n)
Proof
  strip_tac >> Cases_on `a + n < modulus`
  >- simp[arithmeticTheory.LESS_MOD] >>
  `a + n < 2 * modulus` by decide_tac >>
  `(a + n) MOD modulus = a + n - modulus` by
    (irule arithmeticTheory.MOD_UNIQUE >> qexists_tac `1` >> simp[] >> decide_tac) >>
  simp[] >> decide_tac
QED

Theorem slice_bounds_word:
  a < 2 ** 256 /\ n < 2 ** 256 /\ limit < 2 ** 256 ==>
  (((n2w a + n2w n):bytes32) <+ n2w a \/
    (n2w limit:bytes32) <+ n2w a + n2w n <=>
   2 ** 256 <= a + n \/ limit < a + n)
Proof
  strip_tac >> fs[] >>
  simp[wordsTheory.WORD_LO, wordsTheory.word_add_n2w,
       wordsTheory.w2n_n2w, wordsTheory.dimword_def] >>
  irule slice_bounds_mod >> simp[]
QED

Theorem slice_bounds_shape:
  compile_assert_slice_bounds a n limit sa = ((), sb) ==>
  sb.cs_next_var = sa.cs_next_var + 5 /\
  sb.cs_next_id = sa.cs_next_id + 6 /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id ADD [a; n]
       [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (sa.cs_next_id + 1) LT
       [Var (STRING #"%" (toString sa.cs_next_var)); a]
       [STRING #"%" (toString (sa.cs_next_var + 1))];
     mk_inst (sa.cs_next_id + 2) GT
       [Var (STRING #"%" (toString sa.cs_next_var)); limit]
       [STRING #"%" (toString (sa.cs_next_var + 2))];
     mk_inst (sa.cs_next_id + 3) OR
       [Var (STRING #"%" (toString (sa.cs_next_var + 1)));
        Var (STRING #"%" (toString (sa.cs_next_var + 2)))]
       [STRING #"%" (toString (sa.cs_next_var + 3))];
     mk_inst (sa.cs_next_id + 4) ISZERO
       [Var (STRING #"%" (toString (sa.cs_next_var + 3)))]
       [STRING #"%" (toString (sa.cs_next_var + 4))];
     mk_inst (sa.cs_next_id + 5) ASSERT
       [Var (STRING #"%" (toString (sa.cs_next_var + 4)))] []]
Proof
  simp[compile_assert_slice_bounds_def, comp_bind_def, comp_ignore_bind_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1, same_blocks_def]
QED

Theorem slice_bounds_run:
  compile_assert_slice_bounds a n limit sa = ((), sb) /\
  eval_operand a s = SOME wa /\ eval_operand n s = SOME wn /\
  eval_operand limit s = SOME wl /\
  (!z. a = Var z ==> not_fresh_at sa z) /\
  (!z. n = Var z ==> not_fresh_at sa z) /\
  (!z. limit = Var z ==> not_fresh_at sa z) ==>
  if wa + wn <+ wa \/ wl <+ wa + wn then
    ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
  else ?t. run_inst_seq (emitted_insts sa sb) s = OK t
Proof
  strip_tac >> drule slice_bounds_shape >> strip_tac >>
  `!j w ss. sa.cs_next_var <= j ==>
      eval_operand a (update_var (STRING #"%" (toString j)) w ss) = eval_operand a ss` by
    (rpt strip_tac >> irule eval_operand_update_not_fresh >>
     qexists_tac `sa` >> simp[]) >>
  `!j w ss. sa.cs_next_var <= j ==>
      eval_operand limit (update_var (STRING #"%" (toString j)) w ss) = eval_operand limit ss` by
    (rpt strip_tac >> irule eval_operand_update_not_fresh >>
     qexists_tac `sa` >> simp[]) >>
  Cases_on `wa + wn <+ wa` >> Cases_on `wl <+ wa + wn` >>
  gvs[wordsTheory.WORD_LO] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, exec_pure1_def, bool_to_word_def,
       eval_operand_def, lookup_var_update_var, wordsTheory.WORD_OR_CLAUSES]
QED

Theorem slice_bounds_writes_fresh[local]:
  compile_assert_slice_bounds a n limit sa = ((), sb) ==>
  writes_fresh sa (emitted_insts sa sb)
Proof
  strip_tac >> drule slice_bounds_shape >> strip_tac >>
  simp[writes_fresh_def, fresh_write_op_def, mk_inst_def, not_fresh_at_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem slice_bounds_run_frame:
  compile_assert_slice_bounds a n limit sa = ((), sb) /\
  eval_operand a s = SOME wa /\ eval_operand n s = SOME wn /\
  eval_operand limit s = SOME wl /\
  (!z. a = Var z ==> not_fresh_at sa z) /\
  (!z. n = Var z ==> not_fresh_at sa z) /\
  (!z. limit = Var z ==> not_fresh_at sa z) ==>
  if wa + wn <+ wa \/ wl <+ wa + wn then
    ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
  else ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
           t = s with vs_vars := t.vs_vars /\
           !x. not_fresh_at sa x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x
Proof
  strip_tac >> drule_all slice_bounds_run >>
  Cases_on `wa + wn <+ wa \/ wl <+ wa + wn` >> simp[] >> strip_tac >>
  drule slice_bounds_writes_fresh >> strip_tac >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  qexists_tac `t` >> simp[]
QED

Theorem bytes_buffer_write_encoding:
  !base data bound s. val_in_memory (BaseTV (BytesT (Dynamic bound))) (BytesV data) base
    (mstore base (n2w (LENGTH data))
      (write_memory_with_expansion (base + 32) data s)).vs_memory
Proof
  rpt gen_tac >> simp[val_in_memory_def, mstore_mem_word_at_same] >>
  simp[mstore_mem_bytes_at_disjoint, hash_write_memory_read_self]
QED

Theorem calldata_slice_no_padding:
  a + n <= LENGTH bs ==>
  TAKE n (DROP a bs ++ REPLICATE n z) = TAKE n (DROP a bs)
Proof
  strip_tac >> irule rich_listTheory.TAKE_APPEND1 >> simp[]
QED

Theorem bytes_buffer_write_frame:
  !p data s a len.
  a + len <= p \/ p + 32 + LENGTH data <= a ==>
  mem_bytes_at a len
    (mstore p (n2w (LENGTH data))
      (write_memory_with_expansion (p + 32) data s)).vs_memory =
  mem_bytes_at a len s.vs_memory
Proof
  rpt strip_tac >>
  `a + len <= p \/ p + 32 <= a` by decide_tac >>
  simp[mstore_mem_bytes_at_disjoint] >>
  irule mem_bytes_at_write_disjoint >> decide_tac
QED

Theorem bytes_buffer_write_state_rel:
  !func cenv cx es s p data sz ctx.
  stmt_state_rel ctx func cenv cx es s /\ 32 + LENGTH data <= sz /\
  (!name b len. local_region cenv es.scopes s name b len ==>
     b + len <= p \/ p + sz <= b) /\
  immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es
    (mstore p (n2w (LENGTH data))
      (write_memory_with_expansion (p + 32) data s)) ==>
  stmt_state_rel ctx func cenv cx es
    (mstore p (n2w (LENGTH data))
      (write_memory_with_expansion (p + 32) data s))
Proof
  rpt strip_tac >>
  `local_ptrs_rel func cenv es.scopes
     (mstore p (n2w (LENGTH data))
       (write_memory_with_expansion (p + 32) data s))` by
    (irule localPtrsPropsTheory.local_ptrs_rel_mem_agree >> qexists_tac `s` >>
     rpt conj_tac
     >~ [`local_ptrs_rel _ _ _ _`]
     >- gvs[stmt_state_rel_def, state_rel_def]
     >~ [`mem_bytes_at _ _ _ = mem_bytes_at _ _ _`]
     >- (rpt strip_tac >> sym_tac >> irule bytes_buffer_write_frame >>
         first_x_assum drule >> decide_tac) >>
     simp_tac (srw_ss()) [mstore_def, write_memory_with_expansion_def, lookup_var_def, LET_THM] >>
     rpt strip_tac >> gvs[]) >>
  `immutable_base_zero cenv
     (mstore p (n2w (LENGTH data))
       (write_memory_with_expansion (p + 32) data s))` by
    (irule immutable_base_zero_frame >> qexists_tac `s` >>
     simp[mstore_def, write_memory_with_expansion_def, lookup_var_def, LET_THM] >>
     gvs[stmt_state_rel_def]) >>
  qpat_x_assum `stmt_state_rel ctx _ _ _ _ _` mp_tac >>
  rewrite_tac[Once stmt_state_rel_def] >> strip_tac >>
  rewrite_tac[stmt_state_rel_def] >> conj_tac
  >- (irule state_rel_frame >> simp[] >> qexistsl_tac [`es`, `s`] >>
      asm_simp_tac (srw_ss()) [mstore_def, write_memory_with_expansion_def, LET_THM]) >>
  conj_tac
  >- (irule localPtrsPropsTheory.alloca_inv_fields >> qexists_tac `s` >>
      asm_simp_tac (srw_ss()) [mstore_def, write_memory_with_expansion_def, LET_THM]) >>
  conj_tac
  >- (irule alloca_room_fields >> qexists_tac `s` >>
      asm_simp_tac (srw_ss()) [mstore_def, write_memory_with_expansion_def, LET_THM]) >>
  conj_tac
  >- (irule fmp_room_fields >> qexists_tac `s` >>
      asm_simp_tac (srw_ss()) [mstore_def, write_memory_with_expansion_def, LET_THM]) >>
  simp[] >>
  qpat_x_assum `immutable_base_zero cenv (mstore _ _ _)` kall_tac >>
  qpat_x_assum `immutables_rel _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `local_ptrs_rel _ _ _ _` kall_tac >>
  qpat_x_assum `state_rel _ _ _ _ _` kall_tac >>
  full_simp_tac (srw_ss()) [mstore_def, write_memory_with_expansion_def,
      LET_THM, immutable_alloca_sep_def, local_region_def, lookup_var_def] >>
  metis_tac[]
QED

Theorem calldata_copy_step:
  !dst off count s wd wa wn iid.
  eval_operand dst s = SOME wd /\ eval_operand off s = SOME wa /\
  eval_operand count s = SOME wn /\
  w2n wa + w2n wn <= LENGTH s.vs_call_ctx.cc_calldata ==>
  step_inst_base (mk_inst iid CALLDATACOPY [dst; off; count] []) s =
  OK (write_memory_with_expansion (w2n wd)
       (TAKE (w2n wn) (DROP (w2n wa) s.vs_call_ctx.cc_calldata)) s)
Proof
  rpt strip_tac >> simp[step_inst_base_opcode_eqs, mk_inst_def,
                       calldata_slice_no_padding]
QED

Theorem calldata_slice_write_encoding:
  !a n bs p bound s. a + n <= LENGTH bs ==>
  val_in_memory (BaseTV (BytesT (Dynamic bound)))
    (BytesV (TAKE n (DROP a bs))) p
    (mstore p (n2w n)
      (write_memory_with_expansion (p + 32) (TAKE n (DROP a bs)) s)).vs_memory
Proof
  rpt strip_tac >>
  `LENGTH (TAKE n (DROP a bs)) = n` by simp[LENGTH_TAKE_EQ] >>
  metis_tac[bytes_buffer_write_encoding]
QED

Theorem slice_calldata_parts:
  !start_op length_op sz sa ptr sb.
  compile_slice_calldata start_op length_op sz sa = (ptr, sb) ==>
  ?buf sm data s1 len s2 s3 s4.
    compile_alloc_buffer sz sa = (buf, sm) /\ ptr = buf.buf_operand /\
    emit_op ADD [ptr; Lit 32w] sm = (data, s1) /\
    emit_op CALLDATASIZE [] s1 = (len, s2) /\
    compile_assert_slice_bounds start_op length_op len s2 = ((), s3) /\
    emit_void CALLDATACOPY [data; start_op; length_op] s3 = ((), s4) /\
    emit_void MSTORE [ptr; length_op] s4 = ((), sb)
Proof
  rpt gen_tac >> simp[compile_slice_calldata_def, compile_slice_out_buf_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt (goal_assum $ drule_at Any) >> simp[]
QED

Theorem slice_calldata_copy_store_run:
  !dst src num_op buf_op sa sm sb s wd wa wn wp.
  emit_void CALLDATACOPY [dst; src; num_op] sa = ((),sm) /\
  emit_void MSTORE [buf_op; num_op] sm = ((),sb) /\
  eval_operand dst s = SOME wd /\ eval_operand src s = SOME wa /\
  eval_operand num_op s = SOME wn /\ eval_operand buf_op s = SOME wp /\
  w2n wa + w2n wn <= LENGTH s.vs_call_ctx.cc_calldata ==>
  run_inst_seq (emitted_insts sa sb) s =
    OK (mstore (w2n wp) wn
      (write_memory_with_expansion (w2n wd)
        (TAKE (w2n wn) (DROP (w2n wa) s.vs_call_ctx.cc_calldata)) s))
Proof
  rpt strip_tac >>
  qpat_x_assum `emit_void CALLDATACOPY _ _ = _` mp_tac >>
  qpat_x_assum `emit_void MSTORE _ _ = _` mp_tac >>
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, emit_def, comp_return_def] >> rpt strip_tac >> gvs[] >>
  `!iid. step_inst_base (mk_inst iid CALLDATACOPY [dst; src; num_op] []) s =
    OK (write_memory_with_expansion (w2n wd)
      (TAKE (w2n wn) (DROP (w2n wa) s.vs_call_ctx.cc_calldata)) s)` by
    (gen_tac >> irule calldata_copy_step >> simp[]) >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1, run_inst_seq_def] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def,
       write_memory_with_expansion_def, write_memory_def, eval_operand_def]
QED

Theorem slice_calldata_address_size_run[local]:
  !buf_op data_op len_op sa sm sb s w.
  emit_op ADD [buf_op; Lit 32w] sa = (data_op,sm) /\
  emit_op CALLDATASIZE [] sm = (len_op,sb) /\
  eval_operand buf_op s = SOME w ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\ sb.cs_next_var = sa.cs_next_var + 2 /\
  sb.cs_next_id = sa.cs_next_id + 2 /\
  (?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand data_op t = SOME (w + 32w) /\
    eval_operand len_op t = SOME (n2w (LENGTH s.vs_call_ctx.cc_calldata)) /\
    t = s with vs_vars := t.vs_vars /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!x. data_op = Var x ==> not_fresh_at sb x) /\
    (!x. len_op = Var x ==> not_fresh_at sb x))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
      emit_def, comp_return_def] >>
  simp[emitted_insts_def, same_blocks_def, rich_listTheory.DROP_APPEND1,
       run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, exec_read0_def, eval_operand_def, bind_outputs_def] >>
  simp[lookup_var_update_var, update_var_def, not_fresh_at_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem slice_calldata_shape:
  !op num_op sz sa buf_op sb.
  compile_slice_calldata op num_op sz sa = (buf_op,sb) ==>
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  sb.cs_next_id = sa.cs_next_id + 11 /\
  sb.cs_next_var = sa.cs_next_var + 8 /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
       [STRING #"%" (toString sa.cs_next_var)]) (emitted_insts sa sb) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  rpt gen_tac >>
  simp[compile_slice_calldata_def, compile_slice_out_buf_def,
       contextTheory.compile_alloc_buffer_def, compile_assert_slice_bounds_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  simp[same_blocks_def, emitted_insts_def, rich_listTheory.DROP_APPEND1,
       mk_inst_def, is_terminator_def]
QED

Theorem mstore_equal_memory:
  !t s off value. t.vs_memory = s.vs_memory ==>
    mstore off value t = t with vs_memory := (mstore off value s).vs_memory
Proof
  rpt strip_tac >> simp[mstore_def]
QED

Theorem write_memory_with_expansion_equal_memory:
  !t s off bytes. t.vs_memory = s.vs_memory ==>
    write_memory_with_expansion off bytes t =
      t with vs_memory := (write_memory_with_expansion off bytes s).vs_memory
Proof
  rpt strip_tac >> simp[write_memory_with_expansion_def]
QED

Theorem slice_calldata_after_alloc_run:
  !buf_op op data_op len_op sa s1 s2 s3 s4 sb s w a n.
  emit_op ADD [buf_op; Lit 32w] sa = (data_op,s1) /\
  emit_op CALLDATASIZE [] s1 = (len_op,s2) /\
  compile_assert_slice_bounds op (Lit (n2w n)) len_op s2 = ((),s3) /\
  emit_void CALLDATACOPY [data_op; op; Lit (n2w n)] s3 = ((),s4) /\
  emit_void MSTORE [buf_op; Lit (n2w n)] s4 = ((),sb) /\
  eval_operand buf_op s = SOME w /\ eval_operand op s = SOME (n2w a) /\
  (!x. buf_op = Var x ==> not_fresh_at sa x) /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  0 < n /\ n < dimword (:256) /\ a < dimword (:256) /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  w2n w + 32 + 32 * word_size n < dimword (:256) ==>
  if dimword (:256) <= a+n \/ LENGTH s.vs_call_ctx.cc_calldata < a+n then
    ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
  else ?t.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    t.vs_memory = (mstore (w2n w) (n2w n)
      (write_memory_with_expansion (w2n w + 32)
        (TAKE n (DROP a s.vs_call_ctx.cc_calldata)) s)).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    eval_operand buf_op t = SOME w
Proof
  rpt gen_tac >> strip_tac >>
  drule_all slice_calldata_address_size_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa s2) s = OK u` >>
  `eval_operand op u = SOME (n2w a)` by
    (`eval_operand op u = eval_operand op s` suffices_by simp[] >>
     irule literal_operand_frame >> conj_tac
     >- (qexists_tac `sa` >> simp[]) >>
     qpat_x_assum `u = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
  `!x. op = Var x ==> not_fresh_at s2 x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `eval_operand (Lit (n2w n)) u = SOME (n2w n)` by simp[eval_operand_def] >>
  `!x. Lit (n2w n) = Var x ==> not_fresh_at s2 x` by simp[] >>
  `emitted_insts sa sb = emitted_insts sa s2 ++
     emitted_insts s2 s3 ++ emitted_insts s3 sb` by
    (drule (cj 3 slice_bounds_shape) >> disch_tac >>
     `sb.cs_current_insts = s3.cs_current_insts ++ emitted_insts s3 sb` by
       (qpat_x_assum `emit_void CALLDATACOPY _ _ = _` mp_tac >>
        qpat_x_assum `emit_void MSTORE _ _ = _` mp_tac >>
        simp[NoAsms, emit_void_def, comp_bind_def, comp_ignore_bind_def,
             fresh_id_def, emit_def, comp_return_def] >> rpt strip_tac >>
        qpat_x_assum `s2.cs_current_insts = _` kall_tac >>
        qpat_x_assum `s3.cs_current_insts = _` kall_tac >> gvs[] >>
        simp[NoAsms, emitted_insts_def, rich_listTheory.DROP_APPEND1]) >>
     `emitted_insts s2 sb = emitted_insts s2 s3 ++ emitted_insts s3 sb` by
       (irule emitted_insts_append >> simp[]) >>
     `sb.cs_current_insts = s2.cs_current_insts ++ emitted_insts s2 sb` by
       asm_rewrite_tac [APPEND_ASSOC] >>
     `emitted_insts sa sb = emitted_insts sa s2 ++ emitted_insts s2 sb` by
       (irule emitted_insts_append >> simp[]) >> simp[]) >>
  `(n2w a + n2w n <+ (n2w a:bytes32) \/
      n2w (LENGTH s.vs_call_ctx.cc_calldata) <+ (n2w a + n2w n:bytes32)) =
    (dimword (:256) <= a+n \/ LENGTH s.vs_call_ctx.cc_calldata < a+n)` by
    (mp_tac (Q.INST [`a` |-> `a`, `n` |-> `n`,
       `limit` |-> `LENGTH s.vs_call_ctx.cc_calldata`] slice_bounds_word) >>
     gvs[wordsTheory.dimword_def]) >>
  drule_all slice_bounds_run_frame >> simp[] >>
  Cases_on `dimword (:256) <= a+n \/ LENGTH s.vs_call_ctx.cc_calldata < a+n` >>
  simp[] >> strip_tac
  >- (qexists_tac `t` >> asm_rewrite_tac[] >>
      rewrite_tac[GSYM APPEND_ASSOC] >>
      qpat_assum `run_inst_seq _ s = OK u`
        (mp_then Any (qspec_then `emitted_insts s2 s3 ++ emitted_insts s3 sb`
           SUBST1_TAC) run_inst_seq_append) >>
      `!v. run_inst_seq (emitted_insts s2 s3) u <> OK v` by simp[] >>
      drule run_inst_seq_append_err >>
      disch_then (qspec_then `emitted_insts s3 sb` SUBST1_TAC) >> simp[]) >>
  qpat_x_assum `s2.cs_current_insts = _` kall_tac >>
  qpat_x_assum `same_blocks sa s2` kall_tac >>
  qpat_x_assum `s2.cs_next_id = _` kall_tac >>
  qpat_x_assum `_ <+ _ \/ _ <+ _ <=> _` kall_tac >>
  `!x. not_fresh_at s2 x ==> lookup_var x t = lookup_var x u` by
    simp[lookup_var_def] >>
  `eval_operand data_op t = SOME (w + 32w) /\
   eval_operand op t = SOME (n2w a)` by
    (conj_tac >>
     `!operand. (!x. operand = Var x ==> not_fresh_at s2 x) ==>
        eval_operand operand t = eval_operand operand u` by
       (rpt strip_tac >> irule literal_operand_frame >> conj_tac
        >- (qexists_tac `s2` >> simp[]) >>
        qpat_x_assum `t = u with vs_vars := _` SUBST1_TAC >> simp[]) >>
     simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at s2 x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
    (rpt strip_tac >> metis_tac[]) >>
  `t = s with vs_vars := t.vs_vars` by
    (qpat_x_assum `t = u with vs_vars := _` SUBST1_TAC >>
     qpat_x_assum `u = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
  `eval_operand buf_op t = SOME w` by
    (`eval_operand buf_op t = eval_operand buf_op s` suffices_by simp[] >>
     irule literal_operand_frame >> conj_tac
     >- (qexists_tac `sa` >> simp[]) >>
     qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
  `w2n (n2w a:bytes32) + w2n (n2w n:bytes32) <=
     LENGTH t.vs_call_ctx.cc_calldata` by
    (qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >>
     gvs[wordsTheory.w2n_n2w]) >>
  `eval_operand (Lit (n2w n)) t = SOME (n2w n)` by simp[eval_operand_def] >>
  drule_all slice_calldata_copy_store_run >> disch_tac >>
  qpat_x_assum `emit_op ADD _ _ = _` kall_tac >>
  qpat_x_assum `emit_op CALLDATASIZE _ _ = _` kall_tac >>
  qpat_x_assum `compile_assert_slice_bounds _ _ _ _ = _` kall_tac >>
  qpat_x_assum `emit_void CALLDATACOPY _ _ = _` kall_tac >>
  qpat_x_assum `emit_void MSTORE _ _ = _` kall_tac >>
  `w2n (w + 32w) = w2n w + 32` by
    (`w2n w + w2n (32w:bytes32) < dimword (:256)` by (simp[] >> decide_tac) >>
     drule wordsTheory.w2n_add_2 >> simp[]) >>

  qmatch_asmsub_abbrev_tac `run_inst_seq (emitted_insts s3 sb) t = OK result` >>
  qexists_tac `result` >> conj_tac
  >- (rewrite_tac[GSYM APPEND_ASSOC] >>
      qpat_assum `run_inst_seq _ s = OK u`
        (mp_then Any (qspec_then `emitted_insts s2 s3 ++ emitted_insts s3 sb`
          SUBST1_TAC) run_inst_seq_append) >>
      qpat_assum `run_inst_seq _ u = OK t`
        (mp_then Any (qspec_then `emitted_insts s3 sb` SUBST1_TAC)
          run_inst_seq_append) >> simp[]) >>
  `t.vs_memory = s.vs_memory /\
   t.vs_call_ctx = s.vs_call_ctx` by
    (qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
  qmatch_goalsub_abbrev_tac `result.vs_memory = reference.vs_memory` >>
  `result = t with vs_memory := reference.vs_memory` by
    (simp[Abbr `result`, Abbr `reference`, wordsTheory.w2n_n2w,
          IgnAsm `t = s with vs_vars := _`, IgnAsm `t = u with vs_vars := _`,
          IgnAsm `u = s with vs_vars := _`] >>
     drule write_memory_with_expansion_equal_memory >>
     disch_then (qspecl_then [`w2n w + 32`,
       `TAKE n (DROP a s.vs_call_ctx.cc_calldata)`] SUBST1_TAC) >>
     qmatch_goalsub_abbrev_tac `mstore _ _ (t with vs_memory := copied.vs_memory)` >>
     `(t with vs_memory := copied.vs_memory).vs_memory = copied.vs_memory` by simp[] >>
     drule mstore_equal_memory >>
     disch_then (qspecl_then [`w2n w`, `n2w n`] SUBST1_TAC) >>
     simp[NoAsms]) >>
  qpat_x_assum `result = t with vs_memory := _` SUBST1_TAC >>
  simp[IgnAsm `t = s with vs_vars := _`, IgnAsm `t = u with vs_vars := _`,
       IgnAsm `u = s with vs_vars := _`, lookup_var_def] >>
  conj_tac
  >- (qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >> simp[NoAsms]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x t = _` drule >>
      simp[lookup_var_def] >>
      qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x u = _` drule >>
      simp[lookup_var_def]) >>
  Cases_on `buf_op` >> gvs[eval_operand_def, lookup_var_def]
QED


Theorem slice_calldata_run:
  !op n sa ptr sb func cenv cx es s a ctx.
  compile_slice_calldata op (Lit (n2w n)) (32 + 32 * word_size n) sa = (ptr,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
  context_well_typed cx /\ 0 < n /\ n < dimword (:256) /\ a < dimword (:256) /\
  32 + 32 * word_size n < 2 ** 64 /\
  eval_operand op s = SOME (n2w a) /\
  (!x. op = Var x ==> not_fresh_at sa x) ==>
  if dimword (:256) <= a+n \/ LENGTH cx.txn.calldata < a+n then
    ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
  else ?t w. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\ eval_operand ptr t = SOME w /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,32 + 32 * word_size n) /\
    val_in_memory (BaseTV (BytesT (Dynamic n)))
      (BytesV (TAKE n (DROP a cx.txn.calldata))) (w2n w) t.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len. FLOOKUP s.vs_allocas aid = SOME (b,len) /\ aid < sa.cs_next_id ==>
       mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    locals_kept cenv es s t /\
    (!nm lb len. local_region cenv es.scopes t nm lb len ==>
       regions_disjoint (w2n w) (32 + 32 * word_size n) lb len)
Proof
  rpt gen_tac >> strip_tac >>
  drule slice_calldata_shape >> strip_tac >>
  drule slice_calldata_parts >> strip_tac >> gvs[] >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (32 + 32 * word_size n))]
       [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    (gvs[fn_has_code_def, same_blocks_def, rich_listTheory.IS_PREFIX_APPEND] >>
     irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
     simp[MEM_APPEND] >> metis_tac[MEM_APPEND]) >>
  `32 + 32 * word_size n < dimword (:256)` by
    (gvs[wordsTheory.dimword_def] >> decide_tac) >>
  gvs[] >> drule_all literal_alloc_buffer_run >> strip_tac >>
  `(cenv.ce_is_ctor ==> !name tv v off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
       SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name =
       SOME (tv,v) ==>
     regions_disjoint off (type_memory_size tv) (w2n w)
       (32 * word_size n + 32))` by
    (rpt strip_tac >>
     qpat_assum `stmt_state_rel ctx func cenv cx es t` mp_tac >>
     pure_rewrite_tac[stmt_state_rel_def, immutable_alloca_sep_def] >> strip_tac >>
     qpat_x_assum `cenv.ce_is_ctor ==> _` drule >>
     disch_then drule_all >> strip_tac >>
     qpat_x_assum `!inst b sz. MEM inst _ /\ _ ==> _`
       (qspec_then `mk_inst sa.cs_next_id ALLOCA
         [Lit (n2w (32 * word_size n + 32))]
         [STRING #"%" (toString sa.cs_next_var)]` mp_tac) >>
     simp[mk_inst_def]) >>
  `t.vs_call_ctx.cc_calldata = cx.txn.calldata /\
   LENGTH t.vs_call_ctx.cc_calldata < dimword (:256)` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ t` mp_tac >>
     qpat_x_assum `context_well_typed cx` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     gvs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def,
         context_well_typed_def, wordsTheory.dimword_def]) >>
  `t.vs_labels = s.vs_labels` by
    (drule compile_alloc_buffer_insts >> strip_tac >>
     qspecl_then [`sa.cs_next_id`,`n2w (32 * word_size n + 32)`,
       `STRING #"%" (toString sa.cs_next_var)`,`s`] strip_assume_tac
       step_alloca_frame >>
     gvs[emitted_insts_def, rich_listTheory.DROP_APPEND1, run_inst_seq_def]) >>
  `eval_operand op t = SOME (n2w a)` by
    (Cases_on `op` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `sa.cs_next_var <= sm.cs_next_var /\
   sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
     strip_tac >> gvs[] >>
     simp[emitted_insts_def, rich_listTheory.DROP_APPEND1]) >>
  `!x. op = Var x ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at sm x` by simp[] >>
  `w2n w + 32 + 32 * word_size n < dimword (:256)` by decide_tac >>
  `sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb` by
    (drule (cj 3 slice_bounds_shape) >> disch_tac >>
     qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     qpat_x_assum `emit_op CALLDATASIZE _ _ = _` mp_tac >>
     qpat_x_assum `emit_void CALLDATACOPY _ _ = _` mp_tac >>
     qpat_x_assum `emit_void MSTORE _ _ = _` mp_tac >>
     qpat_x_assum `s3.cs_current_insts = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[NoAsms, emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
          fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
     rpt strip_tac >> gvs[] >>
     qmatch_goalsub_abbrev_tac `emitted_insts middle s3` >>
     qabbrev_tac `segment = emitted_insts middle s3` >>
     qpat_x_assum `s3.cs_current_insts = _` kall_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[NoAsms, emitted_insts_def] >>
     rewrite_tac[GSYM APPEND_ASSOC] >>
     simp[NoAsms, rich_listTheory.DROP_APPEND1]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  drule_all slice_calldata_after_alloc_run >>
  qpat_x_assum `compile_slice_calldata _ _ _ _ = _` kall_tac >>
  qpat_x_assum `fn_has_code _ _ _` kall_tac >>
  qpat_x_assum `fn_inst_ids_distinct _` kall_tac >>
  qpat_x_assum `EVERY _ _` kall_tac >>
  qpat_x_assum `same_blocks _ _` kall_tac >>
  qpat_x_assum `sb.cs_next_id = _` kall_tac >>
  qpat_x_assum `sb.cs_next_var = _` kall_tac >>
  qpat_x_assum `MEM _ (emitted_insts _ _)` kall_tac >>
  qpat_x_assum `MEM _ (fn_insts _)` kall_tac >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` kall_tac >>
  qpat_x_assum `emit_op ADD _ _ = _` kall_tac >>
  qpat_x_assum `emit_op CALLDATASIZE _ _ = _` kall_tac >>
  qpat_x_assum `compile_assert_slice_bounds _ _ _ _ = _` kall_tac >>
  qpat_x_assum `emit_void CALLDATACOPY _ _ = _` kall_tac >>
  qpat_x_assum `emit_void MSTORE _ _ = _` kall_tac >>
  simp[] >>
  Cases_on `dimword (:256) <= a+n \/ LENGTH cx.txn.calldata < a+n` >>
  simp[] >> strip_tac
  >- (rename1 `run_inst_seq (emitted_insts sm sb) t = Abort _ t_abort` >>
      qexists_tac `t_abort` >> asm_rewrite_tac[] >>
      qpat_assum `run_inst_seq _ s = OK t`
        (mp_then Any (qspec_then `emitted_insts sm sb` SUBST1_TAC)
          run_inst_seq_append) >> simp[]) >>
  rename1 `run_inst_seq (emitted_insts sm sb) t = OK u` >>
  `u.vs_allocas = t.vs_allocas` by
    (qpat_assum `_ with <|vs_memory := _; vs_vars := _|> = t`
       (mp_tac o AP_TERM ``\z. z.vs_allocas``) >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    (rpt strip_tac >>
     `not_fresh_at sm x` by
       (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     qpat_x_assum `!x. not_fresh_at sm x ==> _` drule >>
     qpat_x_assum `!x. not_fresh_at sa x ==> _` drule >> simp[]) >>
  qexistsl_tac [`u`,`w`] >> conj_tac
  >- (asm_rewrite_tac[] >>
      qpat_assum `run_inst_seq _ s = OK t`
        (mp_then Any (qspec_then `emitted_insts sm sb` SUBST1_TAC)
          run_inst_seq_append) >> simp[]) >>
  `LENGTH (TAKE n (DROP a cx.txn.calldata)) = n` by
    (simp[LENGTH_TAKE_EQ] >> decide_tac) >>
  `n <= 32 * word_size n` by simp[word_size_capacity] >>
  `!b len. b + len <= w2n w \/ w2n w + 32 + n <= b ==>
      mem_bytes_at b len u.vs_memory = mem_bytes_at b len t.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `u.vs_memory = _` (fn th => once_rewrite_tac[th]) >>
     `n2w n = n2w (LENGTH (TAKE n (DROP a cx.txn.calldata))):bytes32` by simp[] >>
     pop_assum SUBST1_TAC >> irule bytes_buffer_write_frame >> simp[]) >>
  conj_tac
  >- (irule literal_state_memory_frame >> qexists_tac `t` >>
      simp[IgnAsm `u.vs_memory = _`] >>
      conj_tac
      >- (rpt strip_tac >>
          qpat_assum `!b len. _ ==> mem_bytes_at _ _ u.vs_memory = _` mp_tac >>
          simp[IgnAsm `u.vs_memory = _`] >> disch_then irule >>
          qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _` drule >>
          simp[regions_disjoint_def] >> decide_tac) >>
      `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x t` by
        (rpt strip_tac >>
         `not_fresh_at sm x` by
           (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
         simp[]) >>
      rpt conj_tac
      >- (rpt strip_tac >>
          fs[local_ptrs_reserved_def] >>
          qpat_x_assum `!n1 n2 p sz1 sz2. _` drule >> strip_tac >> simp[])
      >- (rpt strip_tac >> drule_all local_ptrs_reserved_imm_base >> strip_tac >>
          qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x t` irule >>
          first_assum ACCEPT_TAC)
      >- (qpat_assum `u.vs_memory = _` (fn th => once_rewrite_tac[th]) >>
          simp[immutableMemoryFrameTheory.immutable_mstore_capacity,
               immutableMemoryFrameTheory.immutable_write_memory_capacity] >>
          decide_tac) >>
      rpt strip_tac >>
      `regions_disjoint off (type_memory_size tv) (w2n w)
         (32 * word_size n + 32)` by metis_tac[] >>
      qpat_assum `!b len. _ ==> mem_bytes_at _ _ u.vs_memory = _`
        (qspec_then `off` mp_tac) >>
      disch_then (qspec_then `type_memory_size tv` mp_tac) >>
      simp[regions_disjoint_def] >>
      impl_tac >- (fs[regions_disjoint_def] >> decide_tac) >> simp[]) >>
  simp[] >> conj_tac
  >- (asm_rewrite_tac[] >> irule calldata_slice_write_encoding >> decide_tac) >>
  conj_tac
  >- (rpt strip_tac >>
      `b + len <= w2n w \/ w2n w + 32 + n <= b` by
        (qpat_x_assum `!aid b len. _ ==> regions_disjoint _ _ _ _` drule >>
         simp[regions_disjoint_def] >> decide_tac) >>
      metis_tac[]) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      `local_region cenv es.scopes t nm lb len` by
        (irule exprSimPropsTheory.local_region_frame >> conj_tac
         >- (qexists_tac `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
         qexistsl [`sa`, `es.scopes`, `u`] >> simp[] >>
         rpt strip_tac >>
         qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x u = _` drule >>
         qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x t = _` drule >> simp[]) >>
      qpat_x_assum `!name b len. local_region _ _ t _ _ _ ==> _` drule >>
      pure_rewrite_tac[regions_disjoint_def] >> decide_tac) >>
  irule locals_kept_regions >> rpt strip_tac >>
  rename1 `local_region cenv es.scopes s nm b sz` >>
  `local_region cenv es.scopes t nm b sz` by
    (irule exprSimPropsTheory.local_region_frame_fwd >>
     qexistsl [`s`, `sa`, `es.scopes`] >> simp[]) >>
  `b + sz <= w2n w \/ w2n w + 32 + n <= b` by
    (qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _` drule >>
     simp[regions_disjoint_def] >> decide_tac) >>
  metis_tac[]
QED

Theorem slice_calldata_vv_post:
  !func cenv cx e es sa sb s t p a n w ctx.
  expr_type e = BaseT (BytesT (Dynamic n)) /\ p.ptr_location = LocMemory /\
  eval_operand p.ptr_operand t = SOME w /\ a+n <= LENGTH cx.txn.calldata /\
  stmt_state_rel ctx func cenv cx es t /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,32 + 32 * word_size n) /\
  sa.cs_next_id < sb.cs_next_id /\
  val_in_memory (BaseTV (BytesT (Dynamic n)))
    (BytesV (TAKE n (DROP a cx.txn.calldata))) (w2n w) t.vs_memory /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry) /\
  (!aid b len. FLOOKUP s.vs_allocas aid = SOME (b,len) /\ aid < sa.cs_next_id ==>
    mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
  (!nm lb len. local_region cenv es.scopes t nm lb len ==>
     regions_disjoint (w2n w) (32 + 32 * word_size n) lb len) /\
  locals_kept cenv es s t ==>
  !k. vv_post ctx func cenv cx e es sa sb s es
    (Value (BytesV (TAKE n (DROP a cx.txn.calldata))))
    (LocatedValue (expr_type e) p) (t with vs_inst_idx := k)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_bytestring >> simp[is_bytestring_type_def]) >>
  `LENGTH (TAKE n (DROP a cx.txn.calldata)) = n` by simp[LENGTH_TAKE_EQ] >>
  `n <= 32 * word_size n` by simp[word_size_capacity] >>
  `eval_operand p.ptr_operand (t with vs_inst_idx := k) = SOME w` by
    (Cases_on `p.ptr_operand` >> gvs[eval_operand_def, lookup_var_def]) >>
  simp[vv_post_def, stmt_state_rel_inst_idx, vv_holds_def, vv_at_def,
       read_result_def, return_def, evaluate_type_def, is_word_type_def,
       eval_operand_def, lookup_var_def, val_wf_def, val_footprint_def,
       locals_kept_inst_idx] >>
  conj_tac
  >- (strip_tac >> conj_tac
      >- simp[type_memory_size_def, word_size_capacity] >>
      disj1_tac >> qexistsl_tac [`sa.cs_next_id`,`w2n w`,`32 + 32 * word_size n`] >>
      simp[] >> rpt strip_tac >>
      qpat_x_assum `!nm lb len. local_region _ _ t _ _ _ ==> _` drule >>
      simp[regions_disjoint_def] >> decide_tac) >>
  rpt strip_tac >> first_x_assum irule >> qexists_tac `aid` >> simp[]
QED

Theorem slice_calldata_frag[local]:
  !ctx func cenv cx e es sa sb op p n a s0 res.
  compile_slice_calldata op (Lit (n2w n)) (32 + 32 * word_size n) sa =
    (p.ptr_operand,sb) /\ p.ptr_location = LocMemory /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ context_well_typed cx /\
  0 < n /\ n < 2 ** 256 /\ a < 2 ** 256 /\
  32 + 32 * word_size n < 2 ** 64 /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  res = (case evaluate_calldata_slice cx.txn.calldata (IntV &a) n of
           INL v => INL (Value v) | INR err => INR (Error err)) ==>
  frag_exec ctx sa sb
    (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\
         eval_operand op s = SOME (n2w a))
    (\t. ?tv. res = INL tv /\ vv_post ctx func cenv cx e es sa sb s0 es tv
           (LocatedValue (expr_type e) p) t)
    (expr_exit res)
Proof
  rpt gen_tac >> strip_tac >>
  drule slice_calldata_shape >> strip_tac >>
  gvs[same_blocks_def] >>
  irule frag_exec_run_inst_seq >>
  simp[rich_listTheory.IS_PREFIX_APPEND] >>
  rpt strip_tac >> gvs[] >>
  drule_all (SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss)
    [wordsTheory.dimword_def] slice_calldata_run) >>
  Cases_on `dimword (:256) <= a+n \/ LENGTH cx.txn.calldata < a+n` >>
  gns[wordsTheory.dimword_def] >> strip_tac
  >- (disj2_tac >> qexistsl_tac [`Revert_abort`,`t`] >> simp[] >>
      Cases_on `dimword (:256) <= a+n` >>
      fs[wordsTheory.dimword_def] >>
      simp[CONV_RULE numLib.REDUCE_CONV
        evaluate_calldata_slice_uint, expr_exit_def]) >>
  disj1_tac >> qexists_tac `t` >> simp[] >>
  `a+n <= LENGTH cx.txn.calldata` by decide_tac >>
  simp[evaluate_calldata_slice_uint] >>
  qpat_x_assum `expr_type e = _` (assume_tac o GSYM) >>
  asm_rewrite_tac[] >>
  `t = t with vs_inst_idx := t.vs_inst_idx` by
    simp[venom_state_component_equality] >>
  pop_assum (fn th => ONCE_REWRITE_TAC [th]) >>
  irule slice_calldata_vv_post >> simp[] >> metis_tac[]
QED

Theorem slice_calldata_path[local]:
  !ctx func cenv cx e es sa sb op p n a s0 bres.
  compile_slice_calldata op (Lit (n2w n)) (32 + 32 * word_size n) sa =
    (p.ptr_operand,sb) /\ p.ptr_location = LocMemory /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ context_well_typed cx /\
  0 < n /\ n < 2 ** 256 /\ a < 2 ** 256 /\
  32 + 32 * word_size n < 2 ** 64 /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  bres = (case evaluate_calldata_slice cx.txn.calldata (IntV &a) n of
           INL v => INL v | INR err => INR (Error err)) /\
  stmt_state_rel ctx func cenv cx es s0 /\ eval_operand op s0 = SOME (n2w a) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?m r. gas_marked_path F ctx func s0 m r /\
    ((?u. r = OK u /\
          (?rv. bres = INL rv /\ vv_post ctx func cenv cx e es sa sb s0 es
             (Value rv) (LocatedValue (expr_type e) p) u) /\
          u.vs_current_bb = sb.cs_current_bb /\
          u.vs_inst_idx = LENGTH sb.cs_current_insts) \/
     (exit_result r /\ expr_exit bres r))
Proof
  rpt gen_tac >> strip_tac >>
  drule slice_calldata_shape >> strip_tac >>
  qspecl_then [`ctx`, `func`, `sa`, `sb`, `s0`,
    `\u. ?rv. bres = INL rv /\ vv_post ctx func cenv cx e es sa sb s0 es
            (Value rv) (LocatedValue (expr_type e) p) u`, `expr_exit bres`]
    mp_tac run_inst_seq_gas_path >>
  BETA_TAC >> reverse impl_tac >- (disch_then ACCEPT_TAC) >>
  reverse (rpt conj_tac)
  >- (gvs[same_blocks_def] >>
  drule_all (SIMP_RULE (srw_ss() ++ numSimps.ARITH_ss)
    [wordsTheory.dimword_def] slice_calldata_run) >>
  Cases_on `dimword (:256) <= a+n \/ LENGTH cx.txn.calldata < a+n` >>
  gns[wordsTheory.dimword_def] >> strip_tac
  >- (disj2_tac >> qexistsl_tac [`Revert_abort`,`t`] >> simp[] >>
      Cases_on `dimword (:256) <= a+n` >>
      fs[wordsTheory.dimword_def] >>
      simp[CONV_RULE numLib.REDUCE_CONV
        evaluate_calldata_slice_uint, expr_exit_def]) >>
  disj1_tac >> qexists_tac `t` >> simp[] >>
  `a+n <= LENGTH cx.txn.calldata` by decide_tac >>
  simp[evaluate_calldata_slice_uint] >>
  qpat_x_assum `expr_type e = _` (assume_tac o GSYM) >>
  asm_rewrite_tac[] >>
  `t = t with vs_inst_idx := t.vs_inst_idx` by
    simp[venom_state_component_equality] >>
  pop_assum (fn th => ONCE_REWRITE_TAC [th]) >>
  irule slice_calldata_vv_post >> simp[] >> metis_tac[]) >>
  gvs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem vv_at_start_mono:
  sa.cs_next_id <= sm.cs_next_id /\
  vv_at cenv cx ty sm sb es tv vv u ==>
  vv_at cenv cx ty sa sb es tv vv u
Proof
  Cases_on `vv` >> simp[vv_at_def, expr_val_at_def] >>
  rpt strip_tac >> gvs[]
  >>~- ([`FLOOKUP u.vs_allocas aid = SOME (b,sz)`],
        disj1_tac >> qexistsl [`aid`, `b`, `sz`] >> simp[] >>
        first_assum ACCEPT_TAC)
  >>~- ([`local_region cenv es.scopes u n b sz`],
        disj2_tac >> disj1_tac >> qexistsl [`n`, `b`, `sz`] >> simp[])
  >> metis_tac[]
QED

Theorem vv_own_start_mono:
  sa.cs_next_id <= sm.cs_next_id /\
  vv_own cenv cx ty sm sb es tv vv u ==>
  vv_own cenv cx ty sa sb es tv vv u
Proof
  Cases_on `vv` >> simp[vv_own_def, expr_val_own_def] >>
  rpt strip_tac >> gvs[]
  >>~- ([`FLOOKUP u.vs_allocas aid = SOME (b,sz)`],
        disj1_tac >> qexistsl [`aid`, `b`, `sz`] >> simp[] >>
        first_assum ACCEPT_TAC)
  >> metis_tac[]
QED

Theorem vv_post_prefix_frame:
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  wb_frame cenv es sa s0 t /\
  vv_post ctx func cenv cx e es1 sm sb t es2 tv vv u ==>
  vv_post ctx func cenv cx e es sa sb s0 es2 tv vv u
Proof
  simp[vv_post_def, GSYM wb_frame_def] >> rpt strip_tac
  >- metis_tac[vv_at_start_mono]
  >- metis_tac[vv_own_start_mono] >>
  metis_tac[wb_frame_trans]
QED

Theorem slice_expr_exit_INR_cast[local]:
  expr_exit (INR exc : value + exception) r ==>
  expr_exit (INR exc : eval_result + exception) r
Proof
  Cases_on `exc` >> Cases_on `r` >> simp[expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]
QED

(* compile_typed_unary_builtin_vv_sim (exprSimHash) whose suffix also has
   the entry state relation. *)
(* Unary composition keeps the complete argument postcondition available to
   the suffix, including the footprint and protected-allocation frame. The
   suffix is an actual counted target path from every operand endpoint. *)
Theorem compile_unary_builtin_rel_vv_sim:
  expr_body_pre cenv cx env (Builtin ann bt [e]) es /\
  expr_sim ctx func cenv cx (expr_type e) e es /\ expr_type e = BaseT bty /\
  ~precompile_builtin bt /\ bt <> Len /\ builtin_args_length_ok bt 1 /\
  (!sa sb vv. compile_expr cenv ty (Builtin ann bt [e]) sa = (vv,sb) ==>
    ?x sm. lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
      code x sm = (vv,sb)) /\
  (!x. cs_appends (code x)) /\
  (!sa sm sb x vv s0 v gs es' s.
    lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
    code x sm = (vv,sb) /\ fn_has_code sm sb func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    local_ptrs_reserved cenv sm /\
    bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
      (INL v,es') /\
    value_has_type (BaseTV bty) v /\ expr_sim_inv cenv cx env es' /\
    expr_res_ok (builtin_result cx es'.accounts ann bt [expr_type e] [v]) /\
    stmt_state_rel ctx func cenv cx es s0 /\
    expr_post ctx func cenv cx e es sa sm s0 es' v x s /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?n r. gas_marked_path F ctx func s n r /\
      ((?t rv. r = OK t /\
          builtin_result cx es'.accounts ann bt [expr_type e] [v] = INL rv /\
          vv_post ctx func cenv cx (Builtin ann bt [e]) es sa sb s0 es'
            (Value rv) vv t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts) \/
       (exit_result r /\
        expr_exit (builtin_result cx es'.accounts ann bt [expr_type e] [v]) r))) ==>
  expr_vv_sim ctx func cenv cx ty (Builtin ann bt [e]) es
Proof
  strip_tac >> rewrite_tac[expr_vv_sim_def] >> rpt strip_tac >>
  `!n. bt <> Slice n` by
    (rpt strip_tac >> gvs[builtin_args_length_ok_def]) >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >>
     disch_then irule >> gvs[expr_body_pre_def]) >>
  qpat_x_assum `!sa sb vv. _` drule >> strip_tac >>
  `cs_appends (code x)` by simp[] >>
  drule_all hash_unary_suffix_cut >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  `eval_expr cx (Builtin ann bt [e]) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v es. ((case builtin_result cx es.accounts ann bt [expr_type e] [v] of
                 INL w => INL (Value w) | INR exc => INR exc), es))` by
    (irule eval_expr_unary_builtin_action >> simp[]) >>
  qpat_x_assum `gas_admissible (eval_expr _ _) _ _`
    (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
  asm_rewrite_tac[] >> strip_tac >>
  irule expr_sim_suffix >>
  first_assum (irule_at (Pat `expr_sim _ _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> irule slice_expr_exit_INR_cast >> simp[]) >>
  rpt strip_tac >>
  drule_at (Pat `bind _ _ _ = _`)
    (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_base_result) >>
  disch_then (qspecl_then [`env`, `cenv`] mp_tac) >>
  simp[] >> strip_tac >>
  `expr_res_ok (builtin_result cx ee.accounts ann bt [expr_type e] [v])` by
    (qpat_x_assum `!gs res ee. _` (qspec_then `gs` mp_tac) >> simp[bind_def] >>
     Cases_on `builtin_result cx ee.accounts ann bt [expr_type e] [v]` >>
     gvs[expr_vv_res_ok_def, expr_res_ok_def]) >>
  qpat_x_assum `!sa sm sb x vv s0 v gs es' s. _` drule_all >> strip_tac >>
  `ee with gas_obs := [] = ee` by
    simp[evaluation_state_component_equality] >>
  qexists_tac `REPLICATE n F` >>
  rewrite_tac[gas_summary_at_def, gas_marked_exec_def] >>
  qexistsl_tac [`case builtin_result cx ee.accounts ann bt [expr_type e] [v] of
                   INL w => INL (Value w) | INR exc => INR exc`, `ee`, `r`] >>
  simp[expr_exit_success_map] >>
  Cases_on `builtin_result cx ee.accounts ann bt [expr_type e] [v]` >> gvs[]
QED

Theorem compile_calldata_slice_call_case:
  !nocalls ctx func cenv cx ann n args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann (CalldataSlice n) args)
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[expr_vv_case_def] >>
  rpt gen_tac >> strip_tac >>
  `well_typed_expr env (Builtin ann (CalldataSlice n) args)` by
    gvs[expr_body_pre_def] >>
  drule calldata_slice_typing >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env e es /\
   expr_sim ctx func cenv cx (expr_type e) e es` by
    metis_tac[unop_operand_sim] >>
  `!sa sb vv.
     compile_expr cenv ty (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e])
       sa = (vv,sb) ==>
     ?x sm. lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
       as_ptr_val (BaseT (BytesT (Dynamic n))) LocMemory
         (compile_slice_calldata x (Lit (n2w n))
            (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) sm) = (vv,sb)` by
    (rpt strip_tac >> qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
     simp[compile_calldata_slice_parts] >> pairarg_tac >> gvs[]) >>
  `!x. cs_appends (\sm. as_ptr_val (BaseT (BytesT (Dynamic n))) LocMemory
         (compile_slice_calldata x (Lit (n2w n))
            (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) sm))` by
    (rw[cs_appends_def] >>
     qpat_x_assum `as_ptr_val _ _ _ = _` mp_tac >>
     qmatch_goalsub_abbrev_tac `as_ptr_val _ _ cc` >>
     Cases_on `cc` >> fs[markerTheory.Abbrev_def, as_ptr_val_def] >>
     strip_tac >> qpat_x_assum `(_,_) = _` (assume_tac o SYM) >>
     drule slice_calldata_shape >> strip_tac >>
     gvs[cs_extends_def, same_blocks_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `!tys acc a. builtin_result cx acc (BaseT (BytesT (Dynamic n)))
       (CalldataSlice n) tys [IntV (&a)] =
     (case evaluate_calldata_slice cx.txn.calldata (IntV (&a)) n of
        INL v => INL v | INR err => INR (Error err))` by
    simp[builtin_result_def, evaluate_builtin_def] >>
  irule (Q.INST [`ann` |-> `BaseT (BytesT (Dynamic n))`,
                 `bt` |-> `CalldataSlice n`,
                 `bty` |-> `UintT 256`,
                 `code` |-> `\x sm. as_ptr_val (BaseT (BytesT (Dynamic n)))
                    LocMemory (compile_slice_calldata x (Lit (n2w n))
                      (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) sm)`]
           (SPEC_ALL compile_unary_builtin_rel_vv_sim)) >>
  BETA_TAC >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (simp[builtin_args_length_ok_def, precompile_builtin_def] >> NO_TAC) >>
  qexists_tac `env` >> BETA_TAC >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (simp[builtin_args_length_ok_def, precompile_builtin_def] >> NO_TAC) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `as_ptr_val _ _ _ = _` mp_tac >>
  Cases_on `compile_slice_calldata x (Lit (n2w n))
    (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) sm` >>
  simp[as_ptr_val_def] >> strip_tac >>
  rename1 `compile_slice_calldata _ _ _ sm = (out,sb')` >>
  `sb' = sb` by gvs[] >> pop_assum SUBST_ALL_TAC >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  `?a. v = IntV (&a) /\ a < 2 ** 256` by
    (Cases_on `v` >> gvs[value_has_type_def] >>
     `?m. i = &m` by (qexists_tac `Num i` >> intLib.COOPER_TAC) >>
     gvs[]) >>
  qpat_x_assum `v = IntV _` SUBST_ALL_TAC >>
  qpat_x_assum `LocatedValue _ _ = vv` (SUBST_ALL_TAC o SYM) >>
  `stmt_state_rel ctx func cenv cx es' s` by metis_tac[expr_post_state] >>
  `eval_operand x s = SOME (n2w a)` by
    (drule expr_post_word_operand >>
     simp[evaluate_type_def, is_word_type_def, word_value_def, val_to_w256_def,
          integer_wordTheory.i2w_pos]) >>
  `wb_frame cenv es sa s0 s` by metis_tac[expr_post_frame] >>
  `MAP FDOM es.scopes = MAP FDOM es'.scopes` by
    (qpat_x_assum `bind _ _ (es with gas_obs := gs) = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
     imp_res_tac read_result_state >> gvs[] >>
     drule eval_expr_preserves_scopes_dom >> simp[]) >>
  asm_rewrite_tac[] >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`,
    `Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]`, `es'`,
    `sm`, `sb`, `x`, `mk_ptr out LocMemory`, `n`, `a`, `s`,
    `case evaluate_calldata_slice cx.txn.calldata (IntV (&a)) n of
       INL v => INL v | INR err => INR (Error err)`] mp_tac slice_calldata_path >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      TRY (gvs[contextTheory.mk_ptr_def, vyperASTTheory.expr_type_def,
               type_memory_bytes_def] >> NO_TAC) >>
      TRY (fs[expr_body_pre_def, expr_sim_inv_def] >> NO_TAC) >>
      TRY (fs[expr_body_pre_def, alloc_limits_expr_def] >> NO_TAC) >>
      TRY (qpat_x_assum `compile_slice_calldata _ _ _ _ = _` mp_tac >>
           simp[contextTheory.mk_ptr_def, type_memory_bytes_def,
                vfmConstantsTheory.word_size_def] >> NO_TAC) >>
      fs[expr_body_pre_def, alloc_limits_expr_def, type_alloc_ok_def,
         is_word_type_def, type_memory_bytes_def,
         vfmConstantsTheory.word_size_def]) >>
  strip_tac >> qexistsl_tac [`m`, `r`] >>
  asm_simp_tac (srw_ss()) [vyperASTTheory.expr_type_def] >>
  gvs[vyperASTTheory.expr_type_def] >>
  irule vv_post_prefix_frame >>
  first_assum (irule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[]
QED
