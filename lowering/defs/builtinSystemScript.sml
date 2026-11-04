(*
 * System-Level Built-in Functions
 *
 * TOP-LEVEL:
 *   compile_raw_call_outbuf — raw_call's output buffer
 *   compile_raw_call_finish — raw_call's call and result
 *   compile_send        — send ether to address
 *   compile_raw_log     — raw event emission (LOG0-LOG4)
 *   compile_raw_revert  — revert with custom data
 *   compile_selfdestruct — destroy contract
 *
 * Mirrors Python: vyper/codegen_venom/builtins/system.py
 *)

Theory builtinSystem
Ancestors
  emitHelper context compileEnv builtinSimple venomInst
Libs
  monadsyntax

(* ===== raw_call ===== *)
(* Mirrors Python: system.py lower_raw_call
   raw_call(to, data, max_outsize=0, gas=gas, value=0,
            is_delegate_call=F, is_static_call=F, revert_on_failure=T)

   Data layout: src is [32-byte length][data...]
   Outputs depend on max_outsize and revert_on_failure. *)

(* Which EVM call opcode to use *)
Datatype:
  call_type = RegularCall | DelegateCall | StaticCall
End

(* ===== msg.data special case ===== *)
(* Mirrors Python:
   vyper/codegen_venom/builtins/system.py:_is_msg_data and
   vyper/codegen_venom/context.py:Context.new_internal_variable.
   When raw_call data is msg.data, reserve its runtime calldata length and copy
   all calldata into that fresh region. Returns (data_ptr, data_len). *)
Definition compile_msg_data_to_memory_def:
  compile_msg_data_to_memory =
    do data_len <- emit_op CALLDATASIZE [];
       data_ptr <- compile_alloc_dynamic data_len;
       emit_void CALLDATACOPY [data_ptr; Lit 0w; data_len];
       return (data_ptr, data_len)
    od
End

(* The output buffer of raw_call, allocated after the keyword operands.
   Returns (out_val, out_ptr): with max_outsize > 0, out_val is a Bytes[n]
   value (length word, then data) and out_ptr its data, where CALL writes;
   otherwise both are an empty buffer.
   Mirrors Python: system.py lower_raw_call, new_temporary_value(BytesT(n))
   and allocate_buffer(0). *)
Definition compile_raw_call_outbuf_def:
  compile_raw_call_outbuf max_outsize =
    if max_outsize > 0 then
      let padded_outsize = ((max_outsize + 31) DIV 32) * 32 in
      do buf_alloc <- compile_alloc_buffer (padded_outsize + 32);
         out_val <- return buf_alloc.buf_operand;
         out_ptr <- emit_op ADD [out_val; Lit 32w];
         return (out_val, out_ptr)
      od
    else
      do buf_alloc <- compile_alloc_buffer 0;
         return (buf_alloc.buf_operand, buf_alloc.buf_operand)
      od
End

(* The call of raw_call once its operands and output buffer are lowered, and
   its result: nothing (revert_on_failure, max_outsize = 0), the Bytes[n]
   out_val, the success flag, or a (success, Bytes[n]) tuple buffer.
   Mirrors Python: system.py lower_raw_call, from the call instruction on. *)
Definition compile_raw_call_finish_def:
  compile_raw_call_finish to_op data_ptr data_len gas_op value_op
                          call_ty max_outsize revert_on_failure out_val out_ptr =
    do success <-
         (case call_ty of
            DelegateCall =>
              emit_op DELEGATECALL
                [gas_op; to_op; data_ptr; data_len; out_ptr; Lit (n2w max_outsize)]
          | StaticCall =>
              emit_op STATICCALL
                [gas_op; to_op; data_ptr; data_len; out_ptr; Lit (n2w max_outsize)]
          | RegularCall =>
              emit_op CALL
                [gas_op; to_op; value_op; data_ptr; data_len; out_ptr;
                 Lit (n2w max_outsize)]);
       if revert_on_failure then
         do (* Propagate the callee's revert data *)
            fail_lbl <- fresh_label "call_failed";
            ok_lbl <- fresh_label "call_ok";
            emit_inst JNZ [success; Label ok_lbl; Label fail_lbl] [];
            new_block fail_lbl;
            rds <- emit_op RETURNDATASIZE [];
            rbuf <- compile_alloc_buffer 0;
            emit_void RETURNDATACOPY [rbuf.buf_operand; Lit 0w; rds];
            emit_inst REVERT [rbuf.buf_operand; rds] [];
            new_block ok_lbl;
            if max_outsize > 0 then
              do (* Store min(returndatasize, max_outsize) as the length *)
                 rds2 <- emit_op RETURNDATASIZE [];
                 cmp <- emit_op LT [rds2; Lit (n2w max_outsize)];
                 capped <- compile_select cmp rds2 (Lit (n2w max_outsize));
                 emit_void MSTORE [out_val; capped];
                 return out_val
              od
            else
              return (Lit 0w)
         od
       else
         if max_outsize > 0 then
           let bytes_mem_size = 32 + ((max_outsize + 31) DIV 32) * 32 in
           do rds2 <- emit_op RETURNDATASIZE [];
              cmp <- emit_op LT [rds2; Lit (n2w max_outsize)];
              capped <- compile_select cmp rds2 (Lit (n2w max_outsize));
              emit_void MSTORE [out_val; capped];
              (* (success, Bytes[n]) tuple: the flag word, then the bytes
                 value (length and data) inline *)
              tuple_alloc <- compile_alloc_buffer (32 + bytes_mem_size);
              emit_void MSTORE [tuple_alloc.buf_operand; success];
              bytes_dst <- emit_op ADD [tuple_alloc.buf_operand; Lit 32w];
              emit_void MCOPY [bytes_dst; out_val; Lit (n2w bytes_mem_size)];
              return tuple_alloc.buf_operand
           od
         else
           return success
    od
End

(* ===== send ===== *)
(* Mirrors Python: system.py lower_send
   send(to, value, gas=0): CALL with no data, assert success *)
Definition compile_send_def:
  compile_send to_op value_op gas_op =
    do success <- emit_op CALL
         [gas_op; to_op; value_op; Lit 0w; Lit 0w; Lit 0w; Lit 0w];
       emit_void ASSERT [success]
    od
End

(* ===== raw_log ===== *)
(* Mirrors Python: system.py lower_raw_log
   raw_log(topics, data): LOG with 0-4 topics *)
Definition compile_raw_log_def:
  compile_raw_log n_topics data_ptr data_len topic_ops =
    emit_void LOG (Lit (n2w n_topics) :: data_ptr :: data_len :: topic_ops)
End

(* ===== raw_revert ===== *)
(* Mirrors Python: system.py lower_raw_revert
   Revert with custom data bytes *)
Definition compile_raw_revert_def:
  compile_raw_revert data_ptr =
    do data_len <- emit_op MLOAD [data_ptr];
       data_start <- emit_op ADD [data_ptr; Lit 32w];
       emit_inst REVERT [data_start; data_len] []
    od
End

(* ===== selfdestruct ===== *)
Definition compile_selfdestruct_def:
  compile_selfdestruct to_op =
    emit_void SELFDESTRUCT [to_op]
End
