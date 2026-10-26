(* Reuse the proved real zero-cursor allocation when establishing array entry. *)
Theory abiEncoderArrayInitCode
Ancestors
  abiEncoderArrayPhases abiEncoderComplexCode abiDecoderIndexInit abiDecoderArrayHeader
  compileEnv emitHelper words list
Libs monadsyntax

Theorem abi_decode_index_init_complex_prefix:
  abi_decode_index_init = abi_encode_complex_prefix []
Proof
  simp[abi_decode_index_init_def, abi_encode_complex_prefix_def]
QED

Theorem abi_encode_array_prefix_split:
  abi_encode_array_prefix src dst =
    do parent_ptr <- abi_encode_complex_prefix [];
       cnt <- abi_decode_array_header dst src MLOAD;
       return (parent_ptr,cnt)
    od
Proof
  simp_tac bool_ss [FUN_EQ_THM, abi_encode_array_prefix_def,
    GSYM abi_decode_index_init_complex_prefix, abi_decode_array_header_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_encode_array_prefix_trace:
  abi_encode_array_prefix src dst st = (ops,loop_st) ==>
  ?parent_ptr allocated cnt.
    abi_encode_complex_prefix [] st = (parent_ptr,allocated) /\
    abi_decode_array_header dst src MLOAD allocated = (cnt,loop_st) /\
    ops = (parent_ptr,cnt)
Proof
  simp_tac bool_ss [abi_encode_array_prefix_split, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `abi_encode_complex_prefix [] st = (parent_ptr,allocated)` >>
  rename1 `abi_decode_array_header dst src MLOAD allocated = (cnt,ready)` >>
  qexistsl_tac [`parent_ptr`, `allocated`, `cnt`] >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_INIT_CODE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder array initialization code not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayInitCode");
