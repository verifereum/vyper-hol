(* Exact compiler phases for the singleton Bytes wrapper used by abi_decode. *)
Theory abiDecoderWrappedBytes
Ancestors
  abiDecoderSingletonSetup abiDecoderComplexHead abiDecoderGuardLE
  abiDecoderBytes abiEncoder exprLowering compileEnv emitHelper
  words

Theorem abi_decoder_wrapped_bytes_info:
  type_to_abi_dec_info ce.ce_struct_fields ce (TupleT [BaseT (BytesT (Dynamic n))]) =
  DecComplex T [(DecBytestring n,32,abi_decode_bytes_copy_size n)]
Proof
  simp[type_to_abi_dec_info_def, is_abi_dynamic_def, abi_embedded_static_size_def,
       type_memory_bytes_def, abi_decode_bytes_copy_size_def]
QED

Theorem abi_decode_complex_nil[local]:
  compile_abi_decode_complex_elems dst src opc hi [] aoff voff = return ()
Proof
  simp[compile_abi_decode_to_buf_def]
QED

Theorem abi_decode_singleton_bytes_members[local]:
  compile_abi_decode_complex_elems dst src opc hi [(DecBytestring n,abi_sz,mem_sz)] 0 0 =
    do child_src <- compile_getelemptr_abi src T 0 opc hi;
       child_dst <- emit_op ADD [dst; Lit 0w];
       compile_abi_decode_to_buf child_dst child_src opc hi (DecBytestring n)
    od
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [compile_abi_decode_to_buf_def])) >>
  simp[FUN_EQ_THM, abi_decode_complex_nil, dec_info_needs_offset_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_decode_wrapped_bytes_phases:
  compile_abi_decode_to_buf dst src opc hi (DecComplex T [(DecBytestring n,32,mem_sz)]) =
    do child_ops <- abi_decode_singleton_setup dst src opc hi;
       compile_abi_decode_to_buf (SND child_ops) (FST child_ops) opc hi (DecBytestring n)
    od
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [compile_abi_decode_to_buf_def])) >>
  Cases_on `hi = Lit 0w` >>
  simp[FUN_EQ_THM, abi_decode_singleton_setup_def, abi_decode_complex_head_guard_def,
       abi_decode_le_guard_def, abi_decode_singleton_bytes_members,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_WRAPPED_BYTES_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI wrapped Bytes phases not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderWrappedBytes");
