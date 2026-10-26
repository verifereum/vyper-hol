(* Exact compiler traces for all three AbiEncode dispatcher paths. *)
Theory abiBuiltinEncodeDispatchCode
Ancestors
  abiBuiltinDispatchCorrect exprLowering builtinAbi compileEnv context
  words list arithmetic

Theorem compile_abi_encode_memory_trace:
  ~is_word_type (expr_type e) /\
  cfn ce (expr_type e) e origin = (LocatedValue (expr_type e) srcptr,ready) /\
  srcptr.ptr_location = LocMemory /\
  compile_type_builtin_dispatch_body cfn ce vv_ty ty (AbiEncode F method_id) ret_ty [e] origin =
    (vv,final) ==>
  ?out. lower_abi_encode F (OPTION_MAP bytes_method_id_word method_id) srcptr.ptr_operand
      (type_to_abi_enc_info ce.ce_struct_fields ce (expr_type e))
      (abi_size_bound ce.ce_struct_fields (expr_type e)) ready = (out,final) /\
    vv = LocatedValue vv_ty (mk_ptr out LocMemory)
Proof
  strip_tac >>
  gvs[compile_type_builtin_dispatch_body_def, unwrap_value_def, comp_return_def, LET_THM] >>
  drule as_ptr_val_result >> simp[]
QED

Theorem compile_abi_encode_word_trace:
  is_word_type (expr_type e) /\
  lower_value cfn ce (expr_type e) e origin = (value_op,arg_st) /\
  compile_type_builtin_dispatch_body cfn ce vv_ty ty (AbiEncode F method_id) ret_ty [e] origin =
    (vv,final) ==>
  ?buf allocated staged out.
    compile_alloc_buffer 32 arg_st = (buf,allocated) /\
    emit_void MSTORE [buf.buf_operand;value_op] allocated = ((),staged) /\
    lower_abi_encode F (OPTION_MAP bytes_method_id_word method_id) buf.buf_operand
      (type_to_abi_enc_info ce.ce_struct_fields ce (expr_type e))
      (abi_size_bound ce.ce_struct_fields (expr_type e)) staged = (out,final) /\
    vv = LocatedValue vv_ty (mk_ptr out LocMemory)
Proof
  strip_tac >>
  gvs[compile_type_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `compile_alloc_buffer 32 arg_st = (buf,allocated)` >>
  rename1 `emit_void MSTORE [buf.buf_operand;value_op] allocated = ((),staged)` >>
  drule as_ptr_val_result >> strip_tac >>
  rename1 `lower_abi_encode _ _ _ _ _ staged = (out,final)` >>
  qexists_tac `out` >> simp[]
QED

Theorem compile_abi_encode_tuple_trace:
  ~(LENGTH args = 1 /\ ~ensure) /\
  compile_multi_exprs cfn ce args origin = (ops,arg_st) /\
  compile_type_builtin_dispatch_body cfn ce vv_ty ty (AbiEncode ensure method_id) ret_ty args origin =
    (vv,final) ==>
  ?buf allocated staged out.
    compile_alloc_buffer (type_memory_bytes ce (TupleT (MAP expr_type args))) arg_st = (buf,allocated) /\
    compile_store_abi_tuple ce buf.buf_operand 0 (ZIP (ops,MAP expr_type args)) allocated = ((),staged) /\
    lower_abi_encode ensure (OPTION_MAP bytes_method_id_word method_id) buf.buf_operand
      (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP expr_type args)))
      (abi_size_bound ce.ce_struct_fields (TupleT (MAP expr_type args))) staged = (out,final) /\
    vv = LocatedValue vv_ty (mk_ptr out LocMemory)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_type_builtin_dispatch_body _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [compile_type_builtin_dispatch_body_def, LET_THM] >> strip_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `compile_alloc_buffer _ arg_st = (buf,allocated)` >>
  rename1 `compile_store_abi_tuple _ _ _ _ allocated = ((),staged)` >>
  drule as_ptr_val_result >> strip_tac >>
  rename1 `lower_abi_encode _ _ _ _ _ staged = (out,final)` >>
  qexists_tac `out` >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_ENCODE_DISPATCH_CODE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin encode dispatch code not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinEncodeDispatchCode");
