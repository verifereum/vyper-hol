(* A typechecked specification, not a theorem or an admitted assertion.
   C1.2.2.2 checks the interface before the execution proof is scheduled. *)
Theory abiEncodeSinglePtrInterfaceProbe
Ancestors
  abiEncodePtrEmptyPhases
  abiEncodeSinglePtrPhaseCaller
  exprSimAbiEncodeTranslatedResources exprSimAbiEncodeWordSuccess
  exprSimAbiEncodeNonwordResult bodyPtrDefs fragGasPathPtr

val abi_encode_single_ptr_suffix_conditional_statement = ``
  !d ctx PG func cenv cx env ty ann m typ e es code.
  (!cx ty N payload p x actual G tn cap cenv eout es.
    evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic N))) /\
    LENGTH payload <= N /\ p < dimword (:256) /\
    eval_operand (Var x) actual = SOME (n2w p) /\
    ptr_covers G tn x actual cap /\
    mload p actual = n2w (LENGTH payload) /\
    mem_bytes_at (p+32) (LENGTH payload) actual.vs_memory = payload /\
    (!i. p <= i /\ i < p+32+LENGTH payload ==> i NOTIN tn.t_mem) /\
    val_store_size (BaseTV (BytesT (Dynamic N))) (BytesV payload) <= cap /\
    type_memory_bytes cenv (lowered_value_type cenv eout) <= cap ==>
    ptr_vv_ok cx ty (Value (BytesV payload))
      (LocatedValue ty (mk_ptr (Var x) LocMemory)) es G tn actual /\
    ptr_buf_ok cenv eout (Var x) G actual) /\
  expr_body_pre cenv cx env (TypeBuiltin ann (AbiEncode F m) typ [e]) es /\
  (!x sm. code x sm =
    (if is_word_type (expr_type e) then
       do buf <- compile_alloc_buffer 32;
          emit_void MSTORE [buf.buf_operand;x];
          (\st. as_ptr_val ann LocMemory
            (lower_abi_encode F (OPTION_MAP bytes_method_id_word m) buf.buf_operand
              (type_to_abi_enc_info cenv.ce_struct_fields cenv (lowered_value_type cenv e))
              (abi_size_bound cenv.ce_struct_fields (lowered_value_type cenv e)) st))
       od
     else (\st. as_ptr_val ann LocMemory
       (lower_abi_encode F (OPTION_MAP bytes_method_id_word m) x
         (type_to_abi_enc_info cenv.ce_struct_fields cenv (lowered_value_type cenv e))
         (abi_size_bound cenv.ce_struct_fields (lowered_value_type cenv e)) st))) sm) ==>
  !sa sm sb x vv s0 G0 tn0 gs v ee G tn s.
    lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
    code x sm = (vv,sb) /\ fn_has_code sm sb func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    local_ptrs_reserved cenv sm /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
    (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==>
       not_fresh_at sa z) /\
    (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==>
       not_fresh_at sa z) /\
    bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
    ee.gas_obs = [] /\
    expr_post ctx func cenv cx e es sa sm s0 ee v x s /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts /\
    ghost_inv d cenv cx ee G tn s /\
    ptr_val_ok cx (expr_type e) v x G tn s /\
    (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e x G s) /\
    ghost_kept cenv es sa G0 tn0 s0 G tn /\
    stmt_state_rel ctx func cenv cx es s0 ==>
    ?marks. gas_summary_ptr_at (cx_dead cx) (ctx,func) PG marks
      (bind (lift_sum (evaluate_type_builtin cx (AbiEncode F m) typ [expr_type e] [v]))
        (\w. return (Value w))) (ee,s,G,tn)
      (\res ef G' tn' t. ?tv. res = INL tv /\
        vv_post ctx func cenv cx (TypeBuiltin ann (AbiEncode F m) typ [e])
          es sa sb s0 ef tv vv t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        ghost_inv d cenv cx ef G' tn' t /\
        ptr_vv_ok cx (expr_type (TypeBuiltin ann (AbiEncode F m) typ [e]))
          tv vv ef G' tn' t /\
        (!t' op. vv = StackValue t' op /\
          ~is_word_type (expr_type (TypeBuiltin ann (AbiEncode F m) typ [e])) ==>
          ptr_buf_ok cenv (TypeBuiltin ann (AbiEncode F m) typ [e]) op G' t) /\
        (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
          ptr_buf_ok cenv (TypeBuiltin ann (AbiEncode F m) typ [e]) p.ptr_operand G' t) /\
        ghost_kept cenv es sa G0 tn0 s0 G' tn')
      (\res ef gt r. expr_exit res r)
``;
