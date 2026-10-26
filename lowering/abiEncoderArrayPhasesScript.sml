(* These are equalities for the actual recursive compiler, preserving its loops. *)
Theory abiEncoderArrayPhases
Ancestors
  abiEncoderArrayCode abiEncoderChildCode abiDecoderDynamicLoopSetup abiDecoderLoopEmit
  abiDecoderIndexInit abiEncoder compileEnv emitHelper words list arithmetic
Libs monadsyntax

Theorem abi_encode_array_static_loop_phases:
  compile_abi_encode_dyn_static_loop dst src ei asz msz count_op =
    do ip <- abi_decode_index_init;
       labels <- abi_encode_array_header ip count_op;
       idx <- abi_encode_array_static_body ip src dst ei asz msz;
       abi_decode_loop_suffix ip idx (FST labels) (SND (SND labels));
       abi_encode_array_static_exit src asz
    od
Proof
  simp_tac bool_ss [FUN_EQ_THM, compile_abi_encode_dyn_static_loop_def,
    abi_decode_index_init_def, abi_encode_array_header_def, abi_encode_array_static_body_def,
    abi_encode_array_addresses_def, abi_decode_array_head_setup_def, abi_decode_indexed_coordinates_def,
    abi_decode_loop_suffix_def, abi_encode_array_static_exit_def,
    LET_THM, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_encode_array_dynamic_loop_phases:
  compile_abi_encode_dyn_loop dst src ei asz msz count_op =
    do ptrs <- abi_encode_array_dynamic_init count_op asz;
       labels <- abi_encode_array_header (FST ptrs) count_op;
       idx <- abi_encode_array_dynamic_body (FST ptrs) (SND ptrs) src dst ei asz msz;
       abi_decode_loop_suffix (FST ptrs) idx (FST labels) (SND (SND labels));
       abi_encode_array_dynamic_exit src (SND ptrs)
    od
Proof
  simp_tac bool_ss [FUN_EQ_THM, Once compile_abi_encode_child_def,
    abi_encode_array_dynamic_init_def, abi_decode_index_init_def, abi_encode_array_header_def,
    abi_encode_array_dynamic_body_def, abi_encode_array_addresses_def, abi_encode_child_suffix_def,
    abi_decode_array_head_setup_def, abi_decode_indexed_coordinates_def,
    abi_decode_loop_suffix_def, abi_encode_array_dynamic_exit_def,
    LET_THM, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Definition abi_encode_array_prefix_def:
  abi_encode_array_prefix src dst =
    do parent_ptr <- abi_decode_index_init;
       count_op <- emit_op MLOAD [src];
       emit_void MSTORE [dst;count_op];
       return (parent_ptr,count_op)
    od
End

Definition abi_encode_array_finish_def:
  abi_encode_array_finish parent_ptr size_op =
    do old <- emit_op MLOAD [parent_ptr];
       next <- emit_op ADD [old;size_op];
       emit_void MSTORE [parent_ptr;next];
       emit_op MLOAD [parent_ptr]
    od
End

Theorem abi_encode_array_phases:
  compile_abi_encode_to_buf dst src (AbiDynArray ei asz msz dyn) =
    do ops <- abi_encode_array_prefix src dst;
       size_op <- (if dyn then compile_abi_encode_dyn_loop dst src ei asz msz (SND ops)
         else compile_abi_encode_dyn_static_loop dst src ei asz msz (SND ops));
       abi_encode_array_finish (FST ops) size_op
    od
Proof
  Cases_on `dyn` >>
  simp_tac bool_ss [FUN_EQ_THM, Once compile_abi_encode_child_def, abi_encode_array_prefix_def,
    abi_decode_index_init_def, abi_encode_array_finish_def,
    LET_THM, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_PHASES_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder actual array phases not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayPhases");
