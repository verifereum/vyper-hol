(* A named residual computation hides the fixed encoder instruction chain,
   so pointer consumers do not duplicate compiler internals or fresh names. *)
Theory reasonFinishCode
Ancestors stmtLowering exprLowering context emitHelper compileEnv venomInst
Libs monadsyntax

Definition reason_encode_finish_def:
  reason_encode_finish outer payload tuple slot =
    do src_ptr <- emit_op ADD [tuple; Lit 0w];
       head_ptr <- emit_op ADD [payload; Lit 0w];
       dynamic_offset <- emit_op MLOAD [slot];
       tail_ptr <- emit_op ADD [payload; dynamic_offset];
       msg_len <- emit_op MLOAD [src_ptr];
       rounded0 <- emit_op ADD [msg_len; Lit 31w];
       rounded <- emit_op AND [rounded0;
         Lit (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0w : bytes32)];
       tail_end <- emit_op ADD [tail_ptr; rounded];
       emit_void MSTORE [tail_end; Lit 0w];
       copy_len <- emit_op ADD [Lit 32w; msg_len];
       emit_void MCOPY [tail_ptr; src_ptr; copy_len];
       rounded1 <- emit_op ADD [msg_len; Lit 31w];
       rounded2 <- emit_op AND [rounded1;
         Lit (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0w : bytes32)];
       encoded_item_len <- emit_op ADD [Lit 32w; rounded2];
       emit_void MSTORE [head_ptr; dynamic_offset];
       new_size <- emit_op ADD [dynamic_offset; encoded_item_len];
       emit_void MSTORE [slot; new_size];
       encoded_len <- emit_op MLOAD [slot];
       revert_offset <- emit_op ADD [outer; Lit 28w];
       revert_len <- emit_op ADD [Lit 4w; encoded_len];
       emit_inst REVERT [revert_offset; revert_len] []
    od
End

Theorem compile_revert_reason_finish_eq:
  compile_revert_with_reason cenv vv mt ms =
    do buf <- compile_alloc_buffer (64 + ms);
       emit_void MSTORE [buf.buf_operand; Lit (0x08c379a0w : bytes32)];
       payload <- emit_op ADD [buf.buf_operand; Lit 32w];
       tuple <- compile_alloc_buffer ms;
       msg <- unwrap_value cenv vv;
       len <- emit_op MLOAD [msg];
       rounded0 <- emit_op ADD [len; Lit 31w];
       rounded <- emit_op AND [rounded0;
         Lit (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0w : bytes32)];
       cnt <- emit_op ADD [Lit 32w; rounded];
       emit_void MCOPY [tuple.buf_operand; msg; cnt];
       slot <- compile_alloc_buffer 32;
       emit_void MSTORE [slot.buf_operand; Lit 32w];
       reason_encode_finish buf.buf_operand payload tuple.buf_operand slot.buf_operand
    od
Proof
  simp[compile_revert_with_reason_def, reason_encode_finish_def]
QED

Theorem compile_revert_reason_finish_split:
  compile_revert_with_reason cenv vv mt ms sa = ((),sb) ==>
  ?buf payload tuple msg len rounded0 rounded cnt slot
    c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12.
    compile_alloc_buffer (64 + ms) sa = (buf,c1) /\
    emit_void MSTORE [buf.buf_operand;Lit 0x08c379a0w] c1 = ((),c2) /\
    emit_op ADD [buf.buf_operand;Lit 32w] c2 = (payload,c3) /\
    compile_alloc_buffer ms c3 = (tuple,c4) /\
    unwrap_value cenv vv c4 = (msg,c5) /\
    emit_op MLOAD [msg] c5 = (len,c6) /\
    emit_op ADD [len;Lit 31w] c6 = (rounded0,c7) /\
    emit_op AND [rounded0;
      Lit (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0w : bytes32)]
      c7 = (rounded,c8) /\
    emit_op ADD [Lit 32w;rounded] c8 = (cnt,c9) /\
    emit_void MCOPY [tuple.buf_operand;msg;cnt] c9 = ((),c10) /\
    compile_alloc_buffer 32 c10 = (slot,c11) /\
    emit_void MSTORE [slot.buf_operand;Lit 32w] c11 = ((),c12) /\
    reason_encode_finish buf.buf_operand payload tuple.buf_operand slot.buf_operand c12 =
      ((),sb)
Proof
  simp[compile_revert_reason_finish_eq, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[comp_bind_def, comp_ignore_bind_def]) >> metis_tac[]
QED
