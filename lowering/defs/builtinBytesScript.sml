(*
 * Byte Manipulation Built-in Functions
 *
 * TOP-LEVEL:
 *   compile_concat     — concat(a, b, ...) bytes/strings
 *   compile_slice      — slice(b, start, length) → substring
 *   compile_extract32_load  — extract32(b, start) after b and start
 *   compile_slice_calldata  — slice(msg.data, start, length)
 *   compile_slice_code      — slice(self.code, start, length)
 *   compile_slice_extcode   — slice(addr.code, start, length)
 *   compile_bytestring_src, compile_slice_data — the two halves of a
 *     general slice, around the lowering of start and length
 *
 * Mirrors Python: ~/vyper/vyper/codegen_venom/builtins/bytes.py
 *)

Theory builtinBytes
Ancestors
  emitHelper context compileEnv venomInst
Libs
  monadsyntax

(* ===== Bounds Check ===== *)
(* Assert start + length <= src_len with overflow protection.
   Mirrors Python: bytes.py _assert_slice_bounds *)
Definition compile_assert_slice_bounds_def:
  compile_assert_slice_bounds start_op length_op src_len_op =
    do end_op <- emit_op ADD [start_op; length_op];
       (* arithmetic overflow: end < start *)
       overflow <- emit_op LT [end_op; start_op];
       (* buffer out of bounds: end > src_len *)
       oob <- emit_op GT [end_op; src_len_op];
       bad <- emit_op OR [overflow; oob];
       ok <- emit_op ISZERO [bad];
       emit_void ASSERT [ok]
    od
End

(* ===== slice ===== *)
(* Mirrors Python: bytes.py lower_slice.  The source's length and data
   pointer are read right after the source is lowered, before start and
   length (src_len/src_data in lower_slice). *)
Definition compile_bytestring_src_def:
  compile_bytestring_src src_ptr =
    do src_len <- emit_op MLOAD [src_ptr];
       src_data <- emit_op ADD [src_ptr; Lit 32w];
       return (src_len, src_data)
    od
End

(* The rest of lower_slice once start and length are lowered: bounds check,
   output buffer (new_temporary_value(out_t), out_size bytes), copy, length. *)
Definition compile_slice_data_def:
  compile_slice_data src_len src_data start_op length_op out_size =
    do compile_assert_slice_bounds start_op length_op src_len;
       out_buf_alloc <- compile_alloc_buffer out_size;
       out_buf <- return out_buf_alloc.buf_operand;
       out_data <- emit_op ADD [out_buf; Lit 32w];
       copy_src <- emit_op ADD [src_data; start_op];
       emit_void MCOPY [out_data; copy_src; length_op];
       emit_void MSTORE [out_buf; length_op];
       return out_buf
    od
End

(* Adhoc slices (bytes.py _lower_adhoc_slice): the output buffer is allocated
   after the size opcode and the bounds check. *)

(* new_temporary_value(out_t) and its data pointer. *)
Definition compile_slice_out_buf_def:
  compile_slice_out_buf out_size =
    do out_buf_alloc <- compile_alloc_buffer out_size;
       out_buf <- return out_buf_alloc.buf_operand;
       out_data <- emit_op ADD [out_buf; Lit 32w];
       return (out_buf, out_data)
    od
End

(* msg.data → calldatacopy *)
Definition compile_slice_calldata_def:
  compile_slice_calldata start_op length_op out_size =
    do src_len <- emit_op CALLDATASIZE [];
       compile_assert_slice_bounds start_op length_op src_len;
       (out_buf, out_data) <- compile_slice_out_buf out_size;
       emit_void CALLDATACOPY [out_data; start_op; length_op];
       emit_void MSTORE [out_buf; length_op];
       return out_buf
    od
End

(* self.code → codecopy *)
Definition compile_slice_code_def:
  compile_slice_code start_op length_op out_size =
    do src_len <- emit_op CODESIZE [];
       compile_assert_slice_bounds start_op length_op src_len;
       (out_buf, out_data) <- compile_slice_out_buf out_size;
       emit_void CODECOPY [out_data; start_op; length_op];
       emit_void MSTORE [out_buf; length_op];
       return out_buf
    od
End

(* <addr>.code → extcodecopy *)
Definition compile_slice_extcode_def:
  compile_slice_extcode addr_op start_op length_op out_size =
    do src_len <- emit_op EXTCODESIZE [addr_op];
       compile_assert_slice_bounds start_op length_op src_len;
       (out_buf, out_data) <- compile_slice_out_buf out_size;
       emit_void EXTCODECOPY [addr_op; out_data; start_op; length_op];
       emit_void MSTORE [out_buf; length_op];
       return out_buf
    od
End

(* ===== extract32 ===== *)
(* Mirrors Python: bytes.py lower_extract32 once start is lowered (the source's
   length and data pointer come from compile_bytestring_src, read before
   start): assert start + 32 <= length, then load 32 bytes.  The caller clamps
   the result with compile_clamp_basetype. *)
Definition compile_extract32_load_def:
  compile_extract32_load src_len src_data start_op =
    do compile_assert_slice_bounds start_op (Lit 32w) src_len;
       load_ptr <- emit_op ADD [src_data; start_op];
       emit_op MLOAD [load_ptr]
    od
End
