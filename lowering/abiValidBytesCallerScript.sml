(* Bytes/String source dispatch with semantic guards established, for both unwrap choices.
   Numeric address credit and the actual allocation-site history remain explicit. *)
Theory abiValidBytesCaller
Ancestors
  abiValidBytesBounds abiValidBytesDispatch abiBuiltinValidBytesPre abiBuiltinDecodeSetup
  abiDecoderBytes abiDecoderContract abiDecoderReentry abiDecoderLoop
  exprLowering builtinAbi fragExec compileEnv context valueEncoding
  vyperABI vyperContext venomState finite_map words list

Theorem compile_abi_decode_bytes_source_caller:
  let wrapped_ty = if unwrap /\ needs_external_call_wrap ret_ty then TupleT [ret_ty] else ret_ty in
  let min_size = abi_static_size ce.ce_struct_fields wrapped_ty in
  let max_size = abi_size_bound ce.ce_struct_fields wrapped_ty in
  (ret_ty = BaseT (BytesT (Dynamic n)) \/ ret_ty = BaseT (StringT n)) /\
  evaluate_type (get_tenv cx) ret_ty = SOME tv /\
  evaluate_type_builtin cx (AbiDecode unwrap) ret_ty [BytesV bs] = INL v /\
  cfn ce (expr_type (HD args)) (HD args) origin =
    (LocatedValue (BaseT (BytesT (Dynamic input_bound))) srcptr,ready) /\
  srcptr.ptr_location = LocMemory /\
  compile_type_builtin_dispatch_body cfn ce vv_ty ty (AbiDecode unwrap) ret_ty args origin =
    (vv,final) /\ fn_has_code ready final func /\
  val_in_memory (BaseTV (BytesT (Dynamic input_bound))) (BytesV bs) p prepared.vs_memory /\
  eval_operand srcptr.ptr_operand prepared = SOME (n2w p) /\
  abi_decoder_operand_live ready.cs_next_var srcptr.ptr_operand /\
  max_size < dimword (:256) /\ p + 32 + LENGTH bs < dimword (:256) /\
  d + abi_decode_bytes_copy_size n < dimword (:256) /\ fresh_vars_wrt ready prepared /\
  ((FLOOKUP prepared.vs_allocas (abi_builtin_decode_output_site ready min_size max_size) = NONE /\
      d = prepared.vs_alloca_next) \/
    FLOOKUP prepared.vs_allocas (abi_builtin_decode_output_site ready min_size max_size) =
      SOME (d,abi_decode_bytes_copy_size n)) /\
  ~prepared.vs_halted /\ prepared.vs_current_bb = ready.cs_current_bb /\
  prepared.vs_inst_idx = LENGTH ready.cs_current_insts /\
  abi_decode_sim ctx func initial prepared ==>
  ?actual. vv_location vv = SOME LocMemory /\
    eval_operand (vv_operand vv) actual = SOME (n2w d) /\ val_in_memory tv v d actual.vs_memory /\
    abi_decode_frame d (type_memory_bytes ce ret_ty) prepared actual /\
    fresh_vars_wrt final actual /\
    (!op w. abi_decoder_operand_live ready.cs_next_var op /\ eval_operand op prepared = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all (SIMP_RULE bool_ss [LET_THM] abi_valid_bytes_resources_from_source) >> strip_tac >>
  drule_all (SIMP_RULE bool_ss [LET_THM] compile_abi_decode_memory_valid_bytes) >>
    simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_VALID_BYTES_CALLER_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI valid bytes source caller not kernel closed: " ^ n)
  end) (DB.thms "abiValidBytesCaller");
