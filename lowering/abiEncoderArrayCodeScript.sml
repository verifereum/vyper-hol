(* Encoder loop phases in the actual instruction order.  Address setup reuses the
   generic indexed operations; the tail uses the shared ADD/MSTORE/JMP backedge. *)
Theory abiEncoderArrayCode
Ancestors
  abiEncoderChildCode abiDecoderDynamicLoopSetup abiDecoderLoopEmit abiDecoderIndexInit
  abiEncoder compileEnv emitHelper venomInst words list arithmetic
Libs monadsyntax

Definition abi_encode_array_addresses_def:
  abi_encode_array_addresses ip src dst asz msz =
    do src_ops <- abi_decode_array_head_setup ip src msz;
       dst_ops <- abi_decode_indexed_coordinates dst (FST src_ops) asz;
       return ((FST src_ops,SND (SND src_ops)),dst_ops)
    od
End

Definition abi_encode_array_static_body_def:
  abi_encode_array_static_body ip src dst ei asz msz =
    do coords <- abi_encode_array_addresses ip src dst asz msz;
       compile_abi_encode_static_info (SND (SND coords)) (SND (FST coords)) ei;
       return (FST (FST coords))
    od
End

Definition abi_encode_array_dynamic_body_def:
  abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz =
    do coords <- abi_encode_array_addresses ip src dst asz msz;
       offset <- emit_op MLOAD [dyn_ptr];
       child_dst <- emit_op ADD [FST (SND coords);offset];
       child_len <- compile_abi_encode_to_buf child_dst (SND (FST coords)) ei;
       abi_encode_child_suffix (SND (SND coords)) dyn_ptr offset child_len;
       return (FST (FST coords))
    od
End

Definition abi_encode_array_header_def:
  abi_encode_array_header ip count_op =
    do hdr <- fresh_label "enc_dyn_hdr";
       body <- fresh_label "enc_dyn_body";
       exit_lbl <- fresh_label "enc_dyn_exit";
       emit_inst JMP [Label hdr] [];
       new_block hdr;
       idx <- emit_op MLOAD [ip];
       cmp <- emit_op LT [idx;count_op];
       done_op <- emit_op ISZERO [cmp];
       emit_inst JNZ [done_op;Label exit_lbl;Label body] [];
       new_block body;
       return (hdr,body,exit_lbl)
    od
End

Definition abi_encode_array_dynamic_init_def:
  abi_encode_array_dynamic_init count_op asz =
    do ip <- abi_decode_index_init;
       dyn_buf <- compile_alloc_buffer 32;
       offset <- emit_op MUL [count_op;Lit (n2w asz)];
       emit_void MSTORE [dyn_buf.buf_operand;offset];
       return (ip,dyn_buf.buf_operand)
    od
End

Definition abi_encode_array_static_exit_def:
  abi_encode_array_static_exit src asz =
    do len <- emit_op MLOAD [src];
       payload <- emit_op MUL [len;Lit (n2w asz)];
       emit_op ADD [Lit 32w;payload]
    od
End

Definition abi_encode_array_dynamic_exit_def:
  abi_encode_array_dynamic_exit src dyn_ptr =
    do emit_op MLOAD [src];
       offset <- emit_op MLOAD [dyn_ptr];
       emit_op ADD [Lit 32w;offset]
    od
End

Theorem abi_encode_array_addresses_trace:
  abi_encode_array_addresses ip src dst asz msz st = (coords,st') ==>
  ?src_ops middle dst_ops.
    abi_decode_array_head_setup ip src msz st = (src_ops,middle) /\
    abi_decode_indexed_coordinates dst (FST src_ops) asz middle = (dst_ops,st') /\
    coords = ((FST src_ops,SND (SND src_ops)),dst_ops)
Proof
  simp_tac bool_ss [abi_encode_array_addresses_def, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `abi_decode_array_head_setup ip src msz st = (src_ops,middle)` >>
  rename1 `abi_decode_indexed_coordinates dst (FST src_ops) asz middle = (dst_ops,st')` >>
  qexistsl_tac [`src_ops`, `middle`, `dst_ops`] >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_ARRAY_CODE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder array phases not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderArrayCode");
