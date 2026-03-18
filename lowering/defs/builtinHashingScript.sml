(*
 * Hashing Built-in Functions
 *
 * TOP-LEVEL:
 *   compile_keccak256   — SHA3 opcode on memory buffer
 *
 * Mirrors Python: ~/vyper/vyper/codegen_venom/builtins/hashing.py
 *)

Theory builtinHashing
Ancestors
  emitHelper context compileEnv venomInst

(* ===== keccak256 ===== *)
(* Mirrors Python: hashing.py lower_keccak256
   For fixed-size word values: mstore to temp buffer, sha3.
   For bytestrings: ensure in memory, sha3 data portion. *)

(* compile_keccak256_word: hash a 32-byte word value *)
Definition compile_keccak256_word_def:
  compile_keccak256_word val_op st =
        let (buf_alloc, st2) = compile_alloc_buffer 32 st in
        let buf = buf_alloc.buf_operand in
    let (_, st3) = emit_void MSTORE [buf; val_op] st2 in
    emit_op SHA3 [buf; Lit 32w] st3
End

(* compile_keccak256_bytes: hash a bytestring (ptr to [length][data]) *)
Definition compile_keccak256_bytes_def:
  compile_keccak256_bytes ptr_op st =
    let (length, st1) = emit_op MLOAD [ptr_op] st in
    let (data_ptr, st2) = emit_op ADD [ptr_op; Lit 32w] st1 in
    emit_op SHA3 [data_ptr; length] st2
End

(* compile_keccak256_bytesm: hash a bytesM value (only first m bytes) *)
Definition compile_keccak256_bytesm_def:
  compile_keccak256_bytesm val_op (m:num) st =
        let (buf_alloc, st2) = compile_alloc_buffer 32 st in
        let buf = buf_alloc.buf_operand in
    let (_, st3) = emit_void MSTORE [buf; val_op] st2 in
    emit_op SHA3 [buf; Lit (n2w m)] st3
End

(* ===== sha256 ===== *)
(* Mirrors Python: hashing.py lower_sha256
   Computes SHA-256 via STATICCALL to precompile at address 0x2. *)

(* compile_sha256_word: hash a 32-byte word value *)
Definition compile_sha256_word_def:
  compile_sha256_word val_op st =
        let (in_buf_alloc, st1) = compile_alloc_buffer 32 st in
        let in_buf = in_buf_alloc.buf_operand in
    let (_, st2) = emit_void MSTORE [in_buf; val_op] st1 in
        let (out_buf_alloc, st3) = compile_alloc_buffer 32 st2 in
        let out_buf = out_buf_alloc.buf_operand in
    let (gas_op, st4) = emit_op GAS [] st3 in
    let (success, st5) = emit_op STATICCALL
      [gas_op; Lit 2w; in_buf; Lit 32w; out_buf; Lit 32w] st4 in
    let (_, st6) = emit_void ASSERT [success] st5 in
    emit_op MLOAD [out_buf] st6
End

(* compile_sha256_bytes: hash a bytestring (ptr to [length][data]) *)
Definition compile_sha256_bytes_def:
  compile_sha256_bytes ptr_op st =
    let (length, st1) = emit_op MLOAD [ptr_op] st in
    let (data_ptr, st2) = emit_op ADD [ptr_op; Lit 32w] st1 in
        let (out_buf_alloc, st3) = compile_alloc_buffer 32 st2 in
        let out_buf = out_buf_alloc.buf_operand in
    let (gas_op, st4) = emit_op GAS [] st3 in
    let (success, st5) = emit_op STATICCALL
      [gas_op; Lit 2w; data_ptr; length; out_buf; Lit 32w] st4 in
    let (_, st6) = emit_void ASSERT [success] st5 in
    emit_op MLOAD [out_buf] st6
End

(* compile_sha256_bytesm: hash a bytesM value (only first m bytes) *)
Definition compile_sha256_bytesm_def:
  compile_sha256_bytesm val_op (m:num) st =
        let (in_buf_alloc, st1) = compile_alloc_buffer 32 st in
        let in_buf = in_buf_alloc.buf_operand in
    let (_, st2) = emit_void MSTORE [in_buf; val_op] st1 in
        let (out_buf_alloc, st3) = compile_alloc_buffer 32 st2 in
        let out_buf = out_buf_alloc.buf_operand in
    let (gas_op, st4) = emit_op GAS [] st3 in
    let (success, st5) = emit_op STATICCALL
      [gas_op; Lit 2w; in_buf; Lit (n2w m); out_buf; Lit 32w] st4 in
    let (_, st6) = emit_void ASSERT [success] st5 in
    emit_op MLOAD [out_buf] st6
End
