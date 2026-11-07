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
  exprLowering exprLoweringProps builtinSimple emitHelper compileEnv
  valueEncoding venomExecSemantics venomInst venomState vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeSystem
  vyperTypeInvariants vyperTyping vyperValueOperation vyperValue
  exprSimWordBuiltins exprSimWordArgs emitHelperProps freshWrites
  exprSimPrecompiles exprSimHash valueEncodingProps valueCopy exprSimLiteralBuffer
  loweringHalt valueTypingMemoryProps
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext fragGasPath

Theorem calldata_slice_typing[local]:
  well_typed_expr env (Builtin ann (CalldataSlice n) args) ==>
  ?e. args = [e] /\ expr_type e = BaseT (UintT 256) /\
      ann = BaseT (BytesT (Dynamic n)) /\ 0 < n /\ n < 2 ** 256
Proof
  cheat
QED

Theorem names_builtin_calldata_slice[local]:
  !args. ~names_builtin (CalldataSlice n) args
Proof
  cheat
QED

Theorem compile_calldata_slice_parts[local]:
  !cenv ty ann n e sa.
    compile_expr cenv ty (Builtin ann (CalldataSlice n) [e]) sa =
    let (start_op, sb) = lower_value compile_expr cenv (expr_type e) e sa in
    as_ptr_val ann LocMemory
      (compile_slice_calldata start_op (Lit (n2w n))
        (type_memory_bytes cenv ann) sb)
Proof
  cheat
QED

Theorem evaluate_calldata_slice_uint[local]:
  evaluate_calldata_slice bs (IntV &start) n =
  if n = 0 \/ 2 ** 256 <= start + n then
    INR (RuntimeError "calldata slice overflow")
  else if start + n <= LENGTH bs then
    INL (BytesV (TAKE n (DROP start bs)))
  else INR (RuntimeError "evaluate_slice range")
Proof
  cheat
QED

Theorem eval_calldata_slice_cases[local]:
  eval_expr cx (Builtin ann (CalldataSlice n) [e]) es = (res, es') ==>
  (?exc. eval_exprs cx [e] es = (INR exc, es') /\ res = INR exc) \/
  ?vs. eval_exprs cx [e] es = (INL vs, es') /\
       res = (case vs of
         [v] => (case evaluate_calldata_slice cx.txn.calldata v n of
                   INL out => INL (Value out)
                 | INR err => INR (Error err))
       | _ => INR (Error (TypeError "builtin")))
Proof
  cheat
QED

Theorem slice_bounds_mod[local]:
  a < modulus /\ n < modulus /\ limit < modulus ==>
  ((a + n) MOD modulus < a \/ limit < (a + n) MOD modulus <=>
   modulus <= a + n \/ limit < a + n)
Proof
  cheat
QED

Theorem slice_bounds_word[local]:
  a < 2 ** 256 /\ n < 2 ** 256 /\ limit < 2 ** 256 ==>
  (((n2w a + n2w n):bytes32) <+ n2w a \/
    (n2w limit:bytes32) <+ n2w a + n2w n <=>
   2 ** 256 <= a + n \/ limit < a + n)
Proof
  cheat
QED

Theorem slice_bounds_shape[local]:
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
  cheat
QED

Theorem slice_bounds_run[local]:
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
  cheat
QED

Theorem slice_bounds_writes_fresh[local]:
  compile_assert_slice_bounds a n limit sa = ((), sb) ==>
  writes_fresh sa (emitted_insts sa sb)
Proof
  cheat
QED

Theorem slice_bounds_run_frame[local]:
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
  cheat
QED

Theorem bytes_buffer_write_encoding:
  !base data bound s. val_in_memory (BaseTV (BytesT (Dynamic bound))) (BytesV data) base
    (mstore base (n2w (LENGTH data))
      (write_memory_with_expansion (base + 32) data s)).vs_memory
Proof
  cheat
QED

Theorem calldata_slice_no_padding[local]:
  a + n <= LENGTH bs ==>
  TAKE n (DROP a bs ++ REPLICATE n z) = TAKE n (DROP a bs)
Proof
  cheat
QED

Theorem bytes_buffer_write_frame:
  !p data s a len.
  a + len <= p \/ p + 32 + LENGTH data <= a ==>
  mem_bytes_at a len
    (mstore p (n2w (LENGTH data))
      (write_memory_with_expansion (p + 32) data s)).vs_memory =
  mem_bytes_at a len s.vs_memory
Proof
  cheat
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
  cheat
QED

Theorem calldata_copy_step[local]:
  !dst off count s wd wa wn iid.
  eval_operand dst s = SOME wd /\ eval_operand off s = SOME wa /\
  eval_operand count s = SOME wn /\
  w2n wa + w2n wn <= LENGTH s.vs_call_ctx.cc_calldata ==>
  step_inst_base (mk_inst iid CALLDATACOPY [dst; off; count] []) s =
  OK (write_memory_with_expansion (w2n wd)
       (TAKE (w2n wn) (DROP (w2n wa) s.vs_call_ctx.cc_calldata)) s)
Proof
  cheat
QED

Theorem calldata_slice_write_encoding[local]:
  !a n bs p bound s. a + n <= LENGTH bs ==>
  val_in_memory (BaseTV (BytesT (Dynamic bound)))
    (BytesV (TAKE n (DROP a bs))) p
    (mstore p (n2w n)
      (write_memory_with_expansion (p + 32) (TAKE n (DROP a bs)) s)).vs_memory
Proof
  cheat
QED

Theorem slice_calldata_parts[local]:
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
  cheat
QED

Theorem slice_calldata_copy_store_run[local]:
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
  cheat
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
  cheat
QED

Theorem slice_calldata_shape[local]:
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
  cheat
QED

Theorem mstore_equal_memory:
  !t s off value. t.vs_memory = s.vs_memory ==>
    mstore off value t = t with vs_memory := (mstore off value s).vs_memory
Proof
  cheat
QED

Theorem write_memory_with_expansion_equal_memory:
  !t s off bytes. t.vs_memory = s.vs_memory ==>
    write_memory_with_expansion off bytes t =
      t with vs_memory := (write_memory_with_expansion off bytes s).vs_memory
Proof
  cheat
QED

Theorem slice_calldata_after_alloc_run[local]:
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
  cheat
QED


Theorem slice_calldata_run[local]:
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
  cheat
QED

Theorem slice_calldata_vv_post[local]:
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
  cheat
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
  cheat
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
  cheat
QED

Theorem vv_at_start_mono:
  sa.cs_next_id <= sm.cs_next_id /\
  vv_at cenv cx ty sm sb es tv vv u ==>
  vv_at cenv cx ty sa sb es tv vv u
Proof
  cheat
QED

Theorem vv_own_start_mono:
  sa.cs_next_id <= sm.cs_next_id /\
  vv_own cenv cx ty sm sb es tv vv u ==>
  vv_own cenv cx ty sa sb es tv vv u
Proof
  cheat
QED

Theorem vv_post_prefix_frame:
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  wb_frame cenv es sa s0 t /\
  vv_post ctx func cenv cx e es1 sm sb t es2 tv vv u ==>
  vv_post ctx func cenv cx e es sa sb s0 es2 tv vv u
Proof
  cheat
QED

Theorem slice_expr_exit_INR_cast[local]:
  expr_exit (INR exc : value + exception) r ==>
  expr_exit (INR exc : eval_result + exception) r
Proof
  cheat
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
  cheat
QED

Theorem compile_calldata_slice_call_case:
  !nocalls ctx func cenv cx ann n args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann (CalldataSlice n) args)
Proof
  cheat
QED
