(* #551: ABI dispatch regressions, independent of JSON normalization and the
   supported_program whitelist. Reference: Vyper cd74ce4, builtins/abi.py. *)
Theory abiBuiltinDispatchTest
Ancestors
  exprLowering builtinAbi abiEncoder compileEnv emitHelper context venomInst
  vyperAST vyperABI vyperContext vyperTypeSystem
Libs
  monadsyntax wordsLib

val dimindex_256 = fcpLib.INDEX_CONV ``dimindex(:256)``;
val () = computeLib.upd_compset (wordsLib.add_words_compset true);
val () = computeLib.add_funs [wordsTheory.dimword_def, dimindex_256,
  compile_expr_component_eq, compile_builtin_dispatch_component_eq,
  compile_type_builtin_dispatch_component_eq];

Theorem encode_type_single_and_multiple:
  abi_encode_type F [t] = t /\
  abi_encode_type T [t] = TupleT [t] /\
  abi_encode_type F [t;u] = TupleT [t;u] /\
  abi_encode_type T [t;u] = TupleT [t;u]
Proof
  simp[abi_encode_type_def]
QED

Theorem decode_type_wrapping:
  abi_decode_type T (BaseT (BytesT (Dynamic n))) =
    TupleT [BaseT (BytesT (Dynamic n))] /\
  abi_decode_type F t = t /\
  abi_decode_type T (TupleT [t]) = TupleT [TupleT [t]] /\
  abi_decode_type T (TupleT [t;u]) = TupleT [t;u]
Proof
  simp[abi_decode_type_def, needs_external_call_wrap_def]
QED

(* Dynamic bytes: unwrap_tuple changes the ABI head by one offset word.
   A nested singleton tuple gets another head; a multi-tuple does not. *)
Theorem decode_dynamic_bounds:
  abi_static_size sf (abi_decode_type F (BaseT (BytesT (Dynamic 3)))) = 0 /\
  abi_size_bound sf (abi_decode_type F (BaseT (BytesT (Dynamic 3)))) = 64 /\
  abi_static_size sf (abi_decode_type T (BaseT (BytesT (Dynamic 3)))) = 32 /\
  abi_size_bound sf (abi_decode_type T (BaseT (BytesT (Dynamic 3)))) = 96
Proof
  EVAL_TAC
QED

Theorem encode_multiple_runtime_bytes:
  evaluate_type_builtin cx (AbiEncode ensure NONE)
    (TupleT [BaseT BoolT; BaseT BoolT]) [BaseT BoolT; BaseT BoolT]
    [BoolV T; BoolV F] =
    INL (BytesV (REPLICATE 31 0w ++ [1w] ++ REPLICATE 32 0w))
Proof
  Cases_on `ensure` >> EVAL_TAC >> simp[dimindex_256] >> EVAL_TAC
QED

Theorem decode_wrapped_dynamic_runtime_bytes:
  evaluate_type_builtin cx (AbiDecode T) (BaseT (BytesT (Dynamic 3)))
    [BaseT (BytesT (Dynamic 96))] [BytesV (REPLICATE 31 0w ++ [32w] ++
             REPLICATE 31 0w ++ [1w; 88w] ++ REPLICATE 31 0w)] =
    INL (BytesV [88w])
Proof
  EVAL_TAC
QED

Theorem decode_unwrapped_dynamic_runtime_bytes:
  evaluate_type_builtin cx (AbiDecode F) (BaseT (BytesT (Dynamic 3)))
    [BaseT (BytesT (Dynamic 64))] [BytesV (REPLICATE 31 0w ++ [1w; 88w] ++ REPLICATE 31 0w)] =
    INL (BytesV [88w])
Proof
  EVAL_TAC
QED

(* These handwritten runtime ASTs are genuinely checker-admitted. *)
Theorem raw_encode_multiple_accepted:
  well_typed_expr env
    (TypeBuiltin (BaseT (BytesT (Dynamic 64))) (AbiEncode ensure NONE)
      (TupleT [BaseT BoolT; BaseT BoolT])
      [Literal (BaseT BoolT) (BoolL T); Literal (BaseT BoolT) (BoolL F)])
Proof
  Cases_on `ensure` >> EVAL_TAC >> simp[]
QED

Theorem raw_encode_multiple_compiles_both_words:
  MAP (\i. i.inst_opcode)
    (SND (compile_expr cenv (BaseT (BytesT (Dynamic 64)))
      (TypeBuiltin (BaseT (BytesT (Dynamic 64))) (AbiEncode ensure NONE)
        (TupleT [BaseT BoolT; BaseT BoolT])
        [Literal (BaseT BoolT) (BoolL T); Literal (BaseT BoolT) (BoolL F)])
      (st with cs_current_insts := []))).cs_current_insts =
    [ALLOCA; ADD; MSTORE; ADD; MSTORE; ALLOCA; ADD; MCOPY; MSTORE]
Proof
  simp[Once compile_expr_component_eq, expr_size_def, expr_type_def] >>
  simp[Once compile_type_builtin_dispatch_component_eq, expr_size_def,
       compile_multi_exprs_def, lower_value_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
       exprCallBoundsTheory.expr_child_callback_def, expr_size_def, expr_type_def,
       compile_expr_component_eq, compile_literal_vv_def, unwrap_value_def] >>
  simp[abi_encode_type_def, compile_abi_encode_input_def,
       compile_create_tuple_in_memory_def, lower_abi_encode_def,
       type_to_abi_enc_info_def, is_abi_dynamic_def, abi_size_bound_def,
       type_memory_bytes_def, is_word_type_def, compile_abi_encode_child_def,
       compile_alloc_buffer_def, as_ptr_val_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, mk_inst_def]
QED

Theorem raw_decode_fixed_input_accepted:
  well_typed_expr env
    (TypeBuiltin (BaseT BoolT) (AbiDecode unwrap) (BaseT BoolT)
      [Literal (BaseT (BytesT (Fixed 32))) (BytesL (REPLICATE 32 0w))])
Proof
  EVAL_TAC >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_AX))) >> simp[]
QED

(* Decode must pass the WRAPPED type's descriptor, sizes and allocation size,
   while returning a VyperValue of the requested, unwrapped result type. *)
Theorem decode_dispatch_uses_flag:
  compile_type_builtin_dispatch_body cfn cenv vv_ty ty (AbiDecode unwrap)
    ret_ty [e] st =
  (let (vv, s1) = cfn cenv (expr_type e) e st in
   let (op, s2) = unwrap_value cenv vv s1 in
   let (ptr, s3) = compile_abi_decode_input (expr_type e) op s2 in
   let wrapped = abi_decode_type unwrap ret_ty in
   as_ptr_val vv_ty LocMemory
     (lower_abi_decode ptr
       (type_to_abi_dec_info cenv.ce_struct_fields cenv wrapped)
       (abi_static_size cenv.ce_struct_fields wrapped)
       (abi_size_bound cenv.ce_struct_fields wrapped)
       (type_memory_bytes cenv wrapped) s3))
Proof
  simp[compile_type_builtin_dispatch_body_def]
QED

(* Callback effects stand for arbitrary admitted children. The first word
   must be loaded before the second effect; tuple allocation/stores must wait
   until BOTH children have been evaluated and unwrapped. The complex pointer
   is copied only then, so later mutations of aliased memory are not hidden. *)
Definition abi_effect_probe_def:
  abi_effect_probe cenv ty e =
    do emit_void SSTORE [Lit 0w; Lit 1w];
       return (LocatedValue ty (mk_ptr (Lit 128w) LocMemory))
    od
End

Theorem encode_staging_effect_order:
  expr_type a = BaseT BoolT /\
  expr_type b = BaseT (BytesT (Dynamic 3)) ==>
  MAP (\i. i.inst_opcode)
    (SND
      (do ops <- compile_multi_exprs abi_effect_probe cenv [a;b];
          compile_abi_encode_input cenv ensure (MAP expr_type [a;b]) ops
       od (st with cs_current_insts := []))).cs_current_insts =
    [SSTORE; MLOAD; SSTORE; ALLOCA; ADD; MSTORE; ADD; MCOPY]
Proof
  simp[compile_multi_exprs_def, lower_value_def, abi_effect_probe_def,
       compile_abi_encode_input_def, compile_create_tuple_in_memory_def,
       unwrap_value_def, mk_ptr_def, is_word_type_def, compile_ptr_load_def,
       type_memory_bytes_def, compile_alloc_buffer_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, mk_inst_def]
QED

Theorem encode_single_complex_staging:
  compile_abi_encode_input cenv F [BaseT (BytesT (Dynamic n))] [op] st =
    (op, st)
Proof
  simp[compile_abi_encode_input_def, is_word_type_def, comp_return_def]
QED

Theorem encode_single_word_staging:
  MAP (\i. i.inst_opcode)
    (SND (compile_abi_encode_input cenv F [BaseT BoolT] [op]
      (st with cs_current_insts := []))).cs_current_insts = [ALLOCA; MSTORE] /\
  MAP (\i. i.inst_opcode)
    (SND (compile_abi_encode_input cenv T [BaseT BoolT] [op]
      (st with cs_current_insts := []))).cs_current_insts = [ALLOCA; ADD; MSTORE]
Proof
  simp[compile_abi_encode_input_def, compile_create_tuple_in_memory_def,
       is_word_type_def, type_memory_bytes_def, compile_alloc_buffer_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, mk_inst_def]
QED

Theorem selector_byte_order:
  bytes_method_id_word [222w; 173w; 190w; 239w] = 0xDEADBEEFw
Proof
  EVAL_TAC
QED

Theorem encode_method_id_order_and_capacity:
  MAP (\i. i.inst_opcode)
    (SND (lower_abi_encode F (SOME mid) src (AbiCopy 32) 32
      (st with cs_current_insts := []))).cs_current_insts =
    [ALLOCA; ADD; MSTORE; ADD; MCOPY; ADD; MSTORE] /\
  (HD (SND (lower_abi_encode F (SOME mid) src (AbiCopy 32) 32
      (st with cs_current_insts := []))).cs_current_insts).inst_operands =
    [Lit 96w]
Proof
  simp[lower_abi_encode_def, compile_abi_encode_child_def,
       compile_alloc_buffer_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, mk_inst_def]
QED

Theorem decode_fixed_input_staging:
  MAP (\i. (i.inst_opcode,
    if i.inst_opcode = MSTORE then LAST i.inst_operands else Lit 0w))
    (SND (compile_abi_decode_input (BaseT (BytesT (Fixed n))) op
      (st with cs_current_insts := []))).cs_current_insts =
    [(ALLOCA, Lit 0w); (MSTORE, Lit (n2w n)); (ADD, Lit 0w); (MSTORE, op)]
Proof
  simp[compile_abi_decode_input_def, compile_alloc_buffer_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, mk_inst_def]
QED
