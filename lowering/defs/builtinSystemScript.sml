(*
 * System-Level Built-in Functions
 *
 * TOP-LEVEL:
 *   compile_raw_call    — low-level external call with full control
 *   compile_send        — send ether to address
 *   compile_raw_log     — raw event emission (LOG0-LOG4)
 *   compile_raw_revert  — revert with custom data
 *   compile_selfdestruct — destroy contract
 *
 * Mirrors Python: ~/vyper/vyper/codegen_venom/builtins/system.py
 *)

Theory builtinSystem
Ancestors
  emitHelper context compileEnv builtinSimple venomInst

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
(* Mirrors Python: system.py _is_msg_data + inline handling in lower_raw_call.
   When raw_call data arg is msg.data, copy all calldata to memory at msize.
   Returns (data_ptr, data_len, st). *)
Definition compile_msg_data_to_memory_def:
  compile_msg_data_to_memory st =
    let (data_ptr, st1) = emit_op MSIZE [] st in
    let (data_len, st2) = emit_op CALLDATASIZE [] st1 in
    let (_, st3) = emit_void CALLDATACOPY [data_ptr; Lit 0w; data_len] st2 in
    (data_ptr, data_len, st3)
End

Definition compile_raw_call_def:
  compile_raw_call to_op data_ptr data_len gas_op value_op
                   call_ty max_outsize revert_on_failure st =
    (* Allocate output buffer if needed *)
    let (out_ptr, out_len, st1) =
      if max_outsize > 0 then
        (* Buffer: 32 (length) + ceil32(max_outsize) (data).
           Mirrors Python: BytesT(max_outsize).memory_bytes_required *)
        let padded_outsize = ((max_outsize + 31) DIV 32) * 32 in
                let (buf_alloc, st_b) = compile_alloc_buffer (padded_outsize + 32) st in
                let buf = buf_alloc.buf_operand in
        let (out_data, st_c) = emit_op ADD [buf; Lit 32w] st_b in
        (out_data, Lit (n2w max_outsize), st_c)
      else
        (Lit 0w, Lit 0w, st) in
    (* Emit call instruction *)
    let (success, st2) =
      case call_ty of
        DelegateCall =>
          emit_op DELEGATECALL [gas_op; to_op; data_ptr; data_len; out_ptr; out_len] st1
      | StaticCall =>
          emit_op STATICCALL [gas_op; to_op; data_ptr; data_len; out_ptr; out_len] st1
      | RegularCall =>
          emit_op CALL [gas_op; to_op; value_op; data_ptr; data_len; out_ptr; out_len] st1 in
    if revert_on_failure then
      (* Propagate callee revert reason *)
      let (fail_lbl, st3) = fresh_label "call_fail" st2 in
      let (ok_lbl, st4) = fresh_label "call_ok" st3 in
      let (_, st5) = emit_inst JNZ [success; Label ok_lbl; Label fail_lbl] [] st4 in
      let (_, st6) = new_block fail_lbl st5 in
      let (rds, st7) = emit_op RETURNDATASIZE [] st6 in
      let (_, st8) = emit_void RETURNDATACOPY [Lit 0w; Lit 0w; rds] st7 in
      let (_, st9) = emit_inst REVERT [Lit 0w; rds] [] st8 in
      let (_, st10) = new_block ok_lbl st9 in
      if max_outsize > 0 then
        (* Cap return size: min(returndatasize, max_outsize) *)
        let (rds2, st11) = emit_op RETURNDATASIZE [] st10 in
        let (cmp, st12) = emit_op LT [rds2; Lit (n2w max_outsize)] st11 in
        (* min(rds, max): cmp=1 when rds<max → take rds *)
        let (capped, st13) = compile_select cmp rds2
                               (Lit (n2w max_outsize)) st12 in
        (* Store capped length before output data *)
        let (len_ptr, st14) = emit_op SUB [out_ptr; Lit 32w] st13 in
        let (_, st15) = emit_void MSTORE [len_ptr; capped] st14 in
        (len_ptr, st15)
      else
        (Lit 0w, st10)
    else
      if max_outsize > 0 then
        (* Cap return size even in non-revert path *)
        let (rds2, st3) = emit_op RETURNDATASIZE [] st2 in
        let (cmp, st4) = emit_op LT [rds2; Lit (n2w max_outsize)] st3 in
        (* min(rds, max): cmp=1 when rds<max → take rds *)
        let (capped, st5) = compile_select cmp rds2
                              (Lit (n2w max_outsize)) st4 in
        (* Store capped length at out_buf base (= out_ptr - 32) *)
        let (len_ptr, st6) = emit_op SUB [out_ptr; Lit 32w] st5 in
        let (_, st7) = emit_void MSTORE [len_ptr; capped] st6 in
        (* Build return tuple: (success:uint256, data:Bytes[N])
           Layout: [success (32B)][length (32B)][data (ceil32(max_outsize)B)]
           Allocate tuple buffer and copy. *)
        let bytes_mem_size = 32 + ((max_outsize + 31) DIV 32) * 32 in
        let tuple_size = 32 + bytes_mem_size in
                let (tuple_buf_alloc, st8) = compile_alloc_buffer tuple_size st7 in
                let tuple_buf = tuple_buf_alloc.buf_operand in
        (* Store success at offset 0 *)
        let (_, st9) = emit_void MSTORE [tuple_buf; success] st8 in
        (* Copy bytes (length + data) at offset 32 *)
        let (bytes_dst, st10) = emit_op ADD [tuple_buf; Lit 32w] st9 in
        let (_, st11) = emit_void MCOPY
          [bytes_dst; len_ptr; Lit (n2w bytes_mem_size)] st10 in
        (tuple_buf, st11)
      else
        (success, st2)
End

(* ===== send ===== *)
(* Mirrors Python: system.py lower_send
   send(to, value, gas=0): CALL with no data, assert success *)
Definition compile_send_def:
  compile_send to_op value_op gas_op st =
    let (success, st1) = emit_op CALL
      [gas_op; to_op; value_op; Lit 0w; Lit 0w; Lit 0w; Lit 0w] st in
    emit_void ASSERT [success] st1
End

(* ===== raw_log ===== *)
(* Mirrors Python: system.py lower_raw_log
   raw_log(topics, data): LOG with 0-4 topics *)
Definition compile_raw_log_def:
  compile_raw_log n_topics data_ptr data_len topic_ops st =
    emit_void LOG (Lit (n2w n_topics) :: data_ptr :: data_len :: topic_ops) st
End

(* ===== raw_revert ===== *)
(* Mirrors Python: system.py lower_raw_revert
   Revert with custom data bytes *)
Definition compile_raw_revert_def:
  compile_raw_revert data_ptr st =
    let (data_len, st1) = emit_op MLOAD [data_ptr] st in
    let (data_start, st2) = emit_op ADD [data_ptr; Lit 32w] st1 in
    emit_inst REVERT [data_start; data_len] [] st2
End

(* ===== selfdestruct ===== *)
Definition compile_selfdestruct_def:
  compile_selfdestruct to_op st =
    emit_void SELFDESTRUCT [to_op] st
End
