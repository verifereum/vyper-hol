(* Shared conversion simulation for dynamic Bytes and String results. *)
Theory exprSimConvertBytes
Ancestors
  exprBopSimProps
  exprSimDefs exprSimProps exprSimStack loweringPosts
  exprSimConvert exprSimHyps  exprLowering exprLoweringProps compileEnv
  exprSimAlloc exprSimBuffer exprSimBufferStore exprSimLiteralBuffer exprSimHash
  exprOperandVar valueEncoding valueEncodingProofs
  vyperTypeSystem vyperValueOperation vyperValue vyperInterpreter
  fragExec freshWrites loweringSlice venomExecSemantics venomState
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
  cheat
QED

(* Dynamic bytestring results require a dynamic bytestring source. *)
Theorem valid_conversion_to_bytestring:
  !src dst.
    valid_conversion src dst /\ is_bytestring_type dst ==>
    is_bytestring_type src
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

Theorem convert_result_int_to_bytestring:
  !cx src i n.
    32 <= n ==>
    convert_result cx src (BaseT (BytesT (Dynamic n))) (IntV i) =
      INL (BytesV (word_to_bytes_be ((i2w i):bytes32)))
Proof
  cheat
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
  cheat
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
  cheat
QED

Theorem convert_widen_copy_parts:
  !d x k sm op sb.
    compile_bytestring_widen_copy d x k sm = (op,sb) /\ 0 < k ==>
    ?buf mid. compile_alloc_buffer d sm = (buf,mid) /\
      op = buf.buf_operand /\
      emit_void MCOPY [buf.buf_operand; x; Lit (n2w k)] mid = ((),sb)
Proof
  cheat
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
  cheat
QED

Theorem bytestring_type_cases[local]:
  !t. is_bytestring_type t <=>
    (?n. t = BaseT (BytesT (Dynamic n))) \/ (?n. t = BaseT (StringT n))
Proof
  cheat
QED

Theorem bytestring_memory_bytes_aligned:
  !cenv t. is_bytestring_type t ==> type_memory_bytes cenv t MOD 32 = 0
Proof
  cheat
QED

Theorem bytestring_widen_length_bound:
  !len sz n.
    sz MOD 32 = 0 /\ len + 32 <= sz /\
    sz < 32 * ((n + 31) DIV 32) + 32 ==> len <= n
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

Theorem convert_bytestring_typed:
  !cx src dst tv1 tv2 v v'.
    is_bytestring_type src /\ is_bytestring_type dst /\
    evaluate_type (get_tenv cx) src = SOME tv1 /\
    evaluate_type (get_tenv cx) dst = SOME tv2 /\
    value_has_type tv1 v /\ convert_result cx src dst v = INL v' ==>
    value_has_type tv2 v'
Proof
  cheat
QED

Theorem convert_bytestring_wf:
  !cx src dst tv1 tv2 v v'.
    is_bytestring_type src /\ is_bytestring_type dst /\
    evaluate_type (get_tenv cx) src = SOME tv1 /\
    evaluate_type (get_tenv cx) dst = SOME tv2 /\
    value_has_type tv1 v /\ convert_result cx src dst v = INL v' ==>
    val_wf tv2 v'
Proof
  cheat
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
  cheat
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
  cheat
QED

Theorem convert_bytestring_footprint_small:
  !n bs.
    LENGTH bs <= 32 ==>
    val_footprint (BaseTV (BytesT (Dynamic n))) (BytesV bs) <= 64 /\
    val_footprint (BaseTV (StringT n)) (StringV (MAP (CHR o w2n) bs)) <= 64
Proof
  cheat
QED

Theorem convert_fixed_bytes_payload:
  !m bs.
    LENGTH bs <= 32 ==>
    TAKE (LENGTH bs)
      (word_to_bytes_be (typed_val_to_w256 (BaseTV (BytesT (Fixed m))) (BytesV bs))) = bs
Proof
  cheat
QED

Theorem convert_mem_word_prefix:
  !off mem n.
    n <= 32 ==>
    mem_bytes_at off n mem = TAKE n (word_to_bytes_be (mem_word_at off mem))
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

Theorem convert_bytes_capacity:
  !tenv n tv.
    evaluate_type tenv (BaseT (BytesT (Dynamic n))) = SOME tv ==>
    n < dimword (:256)
Proof
  cheat
QED

Theorem convert_string_capacity:
  !tenv n tv.
    evaluate_type tenv (BaseT (StringT n)) = SOME tv ==>
    n < dimword (:256)
Proof
  cheat
QED

Theorem convert_bytes_header:
  !tenv n tv bs off s.
    evaluate_type tenv (BaseT (BytesT (Dynamic n))) = SOME tv /\
    value_has_type tv (BytesV bs) /\
    val_in_memory tv (BytesV bs) off s.vs_memory ==>
    mload off s = n2w (LENGTH bs) /\ LENGTH bs <= n /\
    LENGTH bs < dimword (:256)
Proof
  cheat
QED

Theorem convert_string_header:
  !tenv n tv str off s.
    evaluate_type tenv (BaseT (StringT n)) = SOME tv /\
    value_has_type tv (StringV str) /\
    val_in_memory tv (StringV str) off s.vs_memory ==>
    mload off s = n2w (LENGTH str) /\ LENGTH str <= n /\
    LENGTH str < dimword (:256)
Proof
  cheat
QED

Theorem convert_mload_run:
  !x sa y sb ss p.
    emit_op MLOAD [x] sa = (y,sb) /\ eval_operand x ss = SOME p ==>
    run_inst_seq (emitted_insts sa sb) ss =
      OK (update_var (STRING #"%" (toString sa.cs_next_var))
            (mload (w2n p) ss) ss)
Proof
  cheat
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
  cheat
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
  cheat
QED

Theorem convert_cast_check_straight:
  !len n.
    straight_fresh
      (do gt <- emit_op GT [len; Lit (n2w n)];
          ok <- emit_op ISZERO [gt];
          emit_void ASSERT [ok]
       od)
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

Theorem convert_readonly_operand_frame:
  !sa s tt.
    fresh_vars_wrt sa s /\ tt = s with vs_vars := tt.vs_vars /\
    (!z. not_fresh_at sa z ==> lookup_var z tt = lookup_var z s) ==>
    !x w. eval_operand x s = SOME w ==> eval_operand x tt = SOME w
Proof
  cheat
QED

Theorem convert_cast_abort_run:
  !x n i sa op sb s p L.
    compile_type_convert x (ConvBytestringCast n i) sa = (op,sb) /\
    eval_operand x s = SOME p /\ mload (w2n p) s = n2w L /\
    L <= i /\ n < L /\ i < dimword (:256) /\ n < dimword (:256) ==>
    ?tt. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort tt
Proof
  cheat
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
  cheat
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
  cheat
QED

Theorem convert_readonly_state_frame:
  !ctx func cenv cx es sa s tt.
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
    tt = s with vs_vars := tt.vs_vars /\
    (!z w. not_fresh_at sa z /\ lookup_var z s = SOME w ==>
           lookup_var z tt = SOME w) ==>
    stmt_state_rel ctx func cenv cx es tt
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

Theorem convert_wb_frame_trans:
  !ctx func cenv cx es es1 sa sm s0 s1 s2.
    wb_frame cenv es sa s0 s1 /\ wb_frame cenv es1 sm s1 s2 /\
    stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id ==>
    wb_frame cenv es sa s0 s2
Proof
  cheat
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
  cheat
QED

Theorem convert_widen_copy_owned:
  !ctx func cenv cx es sm sb s e v tv x op p d k.
    compile_bytestring_widen_copy d x k sm = (op,sb) /\
    0 < k /\ k <= d /\ d < dimword (:256) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
    (!z. x = Var z ==> not_fresh_at sm z) /\
    eval_operand x s = SOME p /\ ~is_word_type (expr_type e) /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    val_wf tv v /\ val_in_memory tv v (w2n p) s.vs_memory /\
    val_footprint tv v <= k ==>
    frag_exec ctx sm sb (\t. t = s)
      (\t. expr_post ctx func cenv cx e es sm sb s es v op t) (\r. F)
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

Theorem convert_cast_grows[local]:
  !x n i sa op sb.
    compile_type_convert x (ConvBytestringCast n i) sa = (op,sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id
Proof
  cheat
QED

Theorem convert_bytestring_suffix_grows:
  !src dst x sa op sb.
    valid_conversion src dst /\ is_bytestring_type dst /\
    compile_type_convert x (mk_convert_op src dst) sa = (op,sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id
Proof
  cheat
QED

Theorem convert_operand_typed[local]:
  !cenv cx env t e1 es v es1.
    expr_body_pre cenv cx env (TypeBuiltin t Convert t [e1]) es /\
    (do r <- eval_expr cx e1; read_result cx r od) es = (INL v,es1) ==>
    ?tv1 tv2.
      evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
      evaluate_type (get_tenv cx) t = SOME tv2 /\ value_has_type tv1 v
Proof
  cheat
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
  cheat
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
    (!z. x = Var z ==> not_fresh_at sm z) ==>
    frag_exec ctx sm sb (\ss. ss = s)
      (\tt. ?v'. convert_result cx (expr_type e1) (expr_type e) v = INL v' /\
        expr_post ctx func cenv cx e es sa sb s0 es1 v' op tt)
      (expr_exit (convert_result cx (expr_type e1) (expr_type e) v))
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

Theorem compile_convert_to_bytestring_case:
  !nocalls ctx func cenv cx ann t e1.
    exprs_case nocalls ctx func cenv cx [e1] /\
    is_bytestring_type t /\
    (!a f args d. e1 = Call a (IntCall f) args d ==>
       lowered_value_type cenv e1 = expr_type e1) ==>
    expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann Convert t [e1])
Proof
  cheat
QED
