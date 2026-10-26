(* Factor the actual generated loop at its element-address/child boundary. *)
Theory abiDecoderLoopSetup
Ancestors
  abiDecoderIndexedAddress abiDecoderDynamic abiEncoder compileEnv emitHelper

Definition abi_decode_array_element_setup_def:
  abi_decode_array_element_setup ip src dst opc hi di abi_sz mem_sz =
    do idx <- emit_op MLOAD [ip];
       src_data <- emit_op ADD [src; Lit 32w];
       src_off <- emit_op MUL [idx; Lit (n2w abi_sz)];
       head <- emit_op ADD [src_data; src_off];
       child_src <-
         (if dec_info_needs_offset di then
            compile_abi_decode_dyn_elem_ptr opc head src_data hi abi_sz
          else return head);
       child_dst <- abi_decode_indexed_address dst idx mem_sz;
       return (idx,child_src,child_dst)
    od
End

Theorem abi_decoder_loop_dynamic_case[local]:
  (case di of DecBytestring n => T | DecDynArray ei a m d n => T |
    DecComplex T elems => T | _ => F) = abi_decoder_dynamic di
Proof
  Cases_on `di` >> simp[abi_decoder_dynamic_def] >>
  rename1 `if dynamic then _ else _` >> Cases_on `dynamic` >> simp[]
QED

Theorem abi_decode_dyn_loop_setup:
  compile_abi_decode_dyn_loop dst src opc hi di abi_sz mem_sz ip cnt =
    do hdr <- fresh_label "dec_dyn_hdr";
       body <- fresh_label "dec_dyn_body";
       exit <- fresh_label "dec_dyn_exit";
       emit_inst JMP [Label hdr] [];
       new_block hdr;
       idx <- emit_op MLOAD [ip];
       count_op <- emit_op opc [src];
       cmp <- emit_op LT [idx; count_op];
       done_op <- emit_op ISZERO [cmp];
       emit_inst JNZ [done_op; Label exit; Label body] [];
       new_block body;
       child_ops <- abi_decode_array_element_setup ip src dst opc hi di abi_sz mem_sz;
       compile_abi_decode_to_buf (SND (SND child_ops)) (FST (SND child_ops)) opc hi di;
       new_idx <- emit_op ADD [FST child_ops; Lit 1w];
       emit_void MSTORE [ip;new_idx];
       emit_inst JMP [Label hdr] [];
       new_block exit;
       return ()
    od
Proof
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [compile_abi_decode_to_buf_def])) >>
  simp[FUN_EQ_THM, abi_decode_array_element_setup_def, abi_decode_indexed_address_def,
    abi_decoder_loop_dynamic_case, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    LET_THM] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_LOOP_SETUP_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI loop setup not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderLoopSetup");
