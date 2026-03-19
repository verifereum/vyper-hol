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
Libs
  monadsyntax

(* ===== keccak256 ===== *)
(* Mirrors Python: hashing.py lower_keccak256
   For fixed-size word values: mstore to temp buffer, sha3.
   For bytestrings: ensure in memory, sha3 data portion. *)

(* compile_keccak256_word: hash a 32-byte word value *)
Definition compile_keccak256_word_def:
  compile_keccak256_word val_op =
    do buf_alloc <- compile_alloc_buffer 32;
       buf <- return buf_alloc.buf_operand;
       emit_void MSTORE [buf; val_op];
       emit_op SHA3 [buf; Lit 32w]
    od
End

(* compile_keccak256_bytes: hash a bytestring (ptr to [length][data]) *)
Definition compile_keccak256_bytes_def:
  compile_keccak256_bytes ptr_op =
    do length <- emit_op MLOAD [ptr_op];
       data_ptr <- emit_op ADD [ptr_op; Lit 32w];
       emit_op SHA3 [data_ptr; length]
    od
End

(* compile_keccak256_bytesm: hash a bytesM value (only first m bytes) *)
Definition compile_keccak256_bytesm_def:
  compile_keccak256_bytesm val_op (m:num) =
    do buf_alloc <- compile_alloc_buffer 32;
       buf <- return buf_alloc.buf_operand;
       emit_void MSTORE [buf; val_op];
       emit_op SHA3 [buf; Lit (n2w m)]
    od
End

(* ===== sha256 ===== *)
(* Mirrors Python: hashing.py lower_sha256
   Computes SHA-256 via STATICCALL to precompile at address 0x2. *)

(* compile_sha256_word: hash a 32-byte word value *)
Definition compile_sha256_word_def:
  compile_sha256_word val_op =
    do in_buf_alloc <- compile_alloc_buffer 32;
       in_buf <- return in_buf_alloc.buf_operand;
       emit_void MSTORE [in_buf; val_op];
       out_buf_alloc <- compile_alloc_buffer 32;
       out_buf <- return out_buf_alloc.buf_operand;
       gas_op <- emit_op GAS [];
       success <- emit_op STATICCALL
         [gas_op; Lit 2w; in_buf; Lit 32w; out_buf; Lit 32w];
       emit_void ASSERT [success];
       emit_op MLOAD [out_buf]
    od
End

(* compile_sha256_bytes: hash a bytestring (ptr to [length][data]) *)
Definition compile_sha256_bytes_def:
  compile_sha256_bytes ptr_op =
    do length <- emit_op MLOAD [ptr_op];
       data_ptr <- emit_op ADD [ptr_op; Lit 32w];
       out_buf_alloc <- compile_alloc_buffer 32;
       out_buf <- return out_buf_alloc.buf_operand;
       gas_op <- emit_op GAS [];
       success <- emit_op STATICCALL
         [gas_op; Lit 2w; data_ptr; length; out_buf; Lit 32w];
       emit_void ASSERT [success];
       emit_op MLOAD [out_buf]
    od
End

(* compile_sha256_bytesm: hash a bytesM value (only first m bytes) *)
Definition compile_sha256_bytesm_def:
  compile_sha256_bytesm val_op (m:num) =
    do in_buf_alloc <- compile_alloc_buffer 32;
       in_buf <- return in_buf_alloc.buf_operand;
       emit_void MSTORE [in_buf; val_op];
       out_buf_alloc <- compile_alloc_buffer 32;
       out_buf <- return out_buf_alloc.buf_operand;
       gas_op <- emit_op GAS [];
       success <- emit_op STATICCALL
         [gas_op; Lit 2w; in_buf; Lit (n2w m); out_buf; Lit 32w];
       emit_void ASSERT [success];
       emit_op MLOAD [out_buf]
    od
End
