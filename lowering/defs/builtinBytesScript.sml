(*
 * Byte Manipulation Built-in Functions
 *
 * TOP-LEVEL:
 *   compile_concat     — concat(a, b, ...) bytes/strings
 *   compile_slice      — slice(b, start, length) → substring
 *   compile_extract32  — extract32(b, start) → bytes32
 *   compile_slice_calldata  — slice(msg.data, start, length)
 *   compile_slice_code      — slice(self.code, start, length)
 *   compile_slice_extcode   — slice(addr.code, start, length)
 *
 * Mirrors Python: ~/vyper/vyper/codegen_venom/builtins/bytes.py
 *)

Theory builtinBytes
Ancestors
  emitHelper context compileEnv venomInst

(* ===== Bounds Check ===== *)
(* Assert start + length <= src_len with overflow protection.
   Mirrors Python: bytes.py _assert_slice_bounds *)
Definition compile_assert_slice_bounds_def:
  compile_assert_slice_bounds start_op length_op src_len_op st =
    let (end_op, st1) = emit_op ADD [start_op; length_op] st in
    (* arithmetic overflow: end < start *)
    let (overflow, st2) = emit_op LT [end_op; start_op] st1 in
    (* buffer out of bounds: end > src_len *)
    let (oob, st3) = emit_op GT [end_op; src_len_op] st2 in
    let (bad, st4) = emit_op OR [overflow; oob] st3 in
    let (ok, st5) = emit_op ISZERO [bad] st4 in
    emit_void ASSERT [ok] st5
End

(* ===== slice ===== *)
(* Mirrors Python: bytes.py lower_slice
   Extract substring: slice(b, start, length) → bytes/string.
   Allocates output buffer, copies from src+start. *)
Definition compile_slice_memory_def:
  compile_slice_memory src_ptr start_op length_op out_size st =
    (* Load source length *)
    let (src_len, st1) = emit_op MLOAD [src_ptr] st in
    let (src_data, st2) = emit_op ADD [src_ptr; Lit 32w] st1 in
    (* Bounds check *)
    let (_, st3) = compile_assert_slice_bounds start_op length_op src_len st2 in
    (* Allocate output buffer *)
        let (out_buf_alloc, st5) = compile_alloc_buffer out_size st3 in
        let out_buf = out_buf_alloc.buf_operand in
    let (out_data, st6) = emit_op ADD [out_buf; Lit 32w] st5 in
    (* Copy bytes *)
    let (copy_src, st7) = emit_op ADD [src_data; start_op] st6 in
    let (_, st8) = emit_void MCOPY [out_data; copy_src; length_op] st7 in
    (* Store length *)
    let (_, st9) = emit_void MSTORE [out_buf; length_op] st8 in
    (out_buf, st9)
End

(* Adhoc slices: msg.data → calldatacopy *)
Definition compile_slice_calldata_def:
  compile_slice_calldata start_op length_op out_size st =
    let (src_len, st1) = emit_op CALLDATASIZE [] st in
    let (_, st2) = compile_assert_slice_bounds start_op length_op src_len st1 in
        let (out_buf_alloc, st4) = compile_alloc_buffer out_size st2 in
        let out_buf = out_buf_alloc.buf_operand in
    let (out_data, st5) = emit_op ADD [out_buf; Lit 32w] st4 in
    let (_, st6) = emit_void CALLDATACOPY [out_data; start_op; length_op] st5 in
    let (_, st7) = emit_void MSTORE [out_buf; length_op] st6 in
    (out_buf, st7)
End

(* self.code → codecopy *)
Definition compile_slice_code_def:
  compile_slice_code start_op length_op out_size st =
    let (src_len, st1) = emit_op CODESIZE [] st in
    let (_, st2) = compile_assert_slice_bounds start_op length_op src_len st1 in
        let (out_buf_alloc, st4) = compile_alloc_buffer out_size st2 in
        let out_buf = out_buf_alloc.buf_operand in
    let (out_data, st5) = emit_op ADD [out_buf; Lit 32w] st4 in
    let (_, st6) = emit_void CODECOPY [out_data; start_op; length_op] st5 in
    let (_, st7) = emit_void MSTORE [out_buf; length_op] st6 in
    (out_buf, st7)
End

(* <addr>.code → extcodecopy *)
Definition compile_slice_extcode_def:
  compile_slice_extcode addr_op start_op length_op out_size st =
    let (src_len, st1) = emit_op EXTCODESIZE [addr_op] st in
    let (_, st2) = compile_assert_slice_bounds start_op length_op src_len st1 in
        let (out_buf_alloc, st4) = compile_alloc_buffer out_size st2 in
        let out_buf = out_buf_alloc.buf_operand in
    let (out_data, st5) = emit_op ADD [out_buf; Lit 32w] st4 in
    let (_, st6) = emit_void EXTCODECOPY [addr_op; out_data; start_op; length_op] st5 in
    let (_, st7) = emit_void MSTORE [out_buf; length_op] st6 in
    (out_buf, st7)
End

(* ===== extract32 ===== *)
(* Mirrors Python: bytes.py lower_extract32
   Load 32 bytes from bytearray at given offset.
   Bounds check: start + 32 <= length *)
Definition compile_extract32_def:
  compile_extract32 src_ptr start_op st =
    let (src_len, st1) = emit_op MLOAD [src_ptr] st in
    let (src_data, st2) = emit_op ADD [src_ptr; Lit 32w] st1 in
    (* Bounds check: start + 32 <= length *)
    let (end_op, st3) = emit_op ADD [start_op; Lit 32w] st2 in
    let (oob, st4) = emit_op GT [end_op; src_len] st3 in
    let (ok, st5) = emit_op ISZERO [oob] st4 in
    let (_, st6) = emit_void ASSERT [ok] st5 in
    (* Load 32 bytes *)
    let (load_ptr, st7) = emit_op ADD [src_data; start_op] st6 in
    emit_op MLOAD [load_ptr] st7
End

(* Clamp extract32 result based on output type.
   - Signed int < 256 bits: signextend check
   - Unsigned int < 256 bits: GT bounds check
   - Address: GT (2^160 - 1) check
   - bytes32/bytesM: no clamping needed
   Mirrors Python: bytes.py _clamp_extract32_result *)
Datatype:
  extract32_clamp =
    Extract32NoClamp
  | Extract32SignedClamp num     (* bits *)
  | Extract32UnsignedClamp num   (* bits *)
  | Extract32AddressClamp
End

Definition compile_clamp_extract32_def:
  compile_clamp_extract32 (val_op:operand) Extract32NoClamp (st:compile_state) =
    (val_op, st) ∧
  compile_clamp_extract32 val_op (Extract32SignedClamp bits) st =
    (let bytes_m1 = bits DIV 8 - 1 in
     let (canonical, st1) = emit_op SIGNEXTEND
       [Lit (n2w bytes_m1); val_op] st in
     let (eq_op, st2) = emit_op EQ [val_op; canonical] st1 in
     let (_, st3) = emit_void ASSERT [eq_op] st2 in
     (val_op, st3)) ∧
  compile_clamp_extract32 val_op (Extract32UnsignedClamp bits) st =
    (let mask = (2 ** bits) - 1 in
     let (too_big, st1) = emit_op GT [val_op; Lit (n2w mask)] st in
     let (ok, st2) = emit_op ISZERO [too_big] st1 in
     let (_, st3) = emit_void ASSERT [ok] st2 in
     (val_op, st3)) ∧
  compile_clamp_extract32 val_op Extract32AddressClamp st =
    (let mask160 = (2 ** 160) - 1 in
     let (too_big, st1) = emit_op GT [val_op; Lit (n2w mask160)] st in
     let (ok, st2) = emit_op ISZERO [too_big] st1 in
     let (_, st3) = emit_void ASSERT [ok] st2 in
     (val_op, st3))
End

(* Determine what clamping extract32 needs based on output type.
   Mirrors Python: bytes.py _clamp_extract32_result dispatch logic. *)
Definition mk_extract32_clamp_def:
  mk_extract32_clamp (BaseT (IntT n)) =
    (if n < 256 then Extract32SignedClamp n else Extract32NoClamp) ∧
  mk_extract32_clamp (BaseT (UintT n)) =
    (if n < 256 then Extract32UnsignedClamp n else Extract32NoClamp) ∧
  mk_extract32_clamp (BaseT AddressT) = Extract32AddressClamp ∧
  mk_extract32_clamp _ = Extract32NoClamp
End
