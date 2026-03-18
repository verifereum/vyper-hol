(*
 * ABI Builtin Functions: abi_encode and abi_decode
 *
 * TOP-LEVEL:
 *   lower_abi_encode  — ABI-encode args with optional method_id prefix
 *   lower_abi_decode  — Decode ABI data to output type
 *
 * Helper:
 *   parse_method_id   — Extract 4-byte function selector from various formats
 *
 * Mirrors Python: ~/vyper/vyper/codegen_venom/builtins/abi.py (~254 LOC)
 *)

Theory builtinAbi
Ancestors
  abiEncoder context compileEnv venomInst

(* ===== Method ID Parsing ===== *)

(* Parse method_id kwarg to word32.
   Handles int literal, bytes literal, hex literal.
   Mirrors Python: builtins/abi.py _parse_method_id *)
Definition parse_method_id_def:
  parse_method_id (IntL n) = SOME (i2w n : bytes32) ∧
  parse_method_id (BytesL bs) =
    (if LENGTH bs >= 4 then
       SOME (word_of_bytes T 0w (TAKE 4 bs) : bytes32)
     else NONE) ∧
  parse_method_id _ = NONE
End

(* ===== Create tuple in memory ===== *)
(* Pack individual values into a contiguous tuple buffer in memory.
   For primitive word types: MSTORE; for complex types: MCOPY.
   elem_infos: list of (is_prim_word, mem_size).
   Mirrors Python: builtins/abi.py _create_tuple_in_memory,
                   builtins/misc.py _create_tuple_in_memory *)
Definition compile_create_tuple_in_memory_def:
  compile_create_tuple_in_memory (buf_op:operand) []
    (_ :num) (st:compile_state) = ((), st) ∧
  compile_create_tuple_in_memory buf_op
    ((arg_op, is_prim, mem_sz) :: rest) offset st =
    (let (dst, st1) =
       (if offset = 0 then (buf_op, st)
        else emit_op ADD [buf_op; Lit (n2w offset)] st) in
     let (_, st2) =
       if is_prim then emit_void MSTORE [dst; arg_op] st1
       else emit_void MCOPY [dst; arg_op; Lit (n2w mem_sz)] st1 in
     compile_create_tuple_in_memory buf_op rest (offset + mem_sz) st2)
End

(* ===== abi_encode ===== *)

(* abi_encode(args, ensure_tuple, method_id) -> Bytes[N]
   Mirrors Python: builtins/abi.py lower_abi_encode
   Steps: eval args, create tuple, encode, optional method_id prefix *)
Definition lower_abi_encode_def:
  lower_abi_encode ensure_tuple method_id_opt src_op enc_info maxlen st =
    (* Allocate output buffer: [32-byte length] | [optional method_id] | [data] *)
    let mid_size = (case method_id_opt of SOME _ => 4 | NONE => 0) in
    let total_size = maxlen + 32 + mid_size in
    let (buf_op_alloc, st1) = compile_alloc_buffer total_size st in
    let buf_op = buf_op_alloc.buf_operand in
    let data_offset = 32 + mid_size in
    let (data_ptr, st2) = emit_op ADD [buf_op; Lit (n2w data_offset)] st1 in
    (* Optionally store method_id at buf+32 (shifted left 224 bits) *)
    let (_, st3) =
      (case method_id_opt of
         SOME mid =>
           let (mid_ptr, st2a) = emit_op ADD [buf_op; Lit 32w] st2 in
           emit_void MSTORE [mid_ptr; Lit (mid << 224)] st2a
       | NONE => ((), st2)) in
    (* Encode data into buffer, get runtime encoded length *)
    let (encoded_len, st4) =
      compile_abi_encode_to_buf data_ptr src_op enc_info st3 in
    (* Store total length = encoded_len + mid_size (runtime value) *)
    let (_, st5) =
      (if mid_size > 0 then
         let (total_len, st4a) =
           emit_op ADD [encoded_len; Lit (n2w mid_size)] st4 in
         emit_void MSTORE [buf_op; total_len] st4a
       else
         emit_void MSTORE [buf_op; encoded_len] st4) in
    (buf_op, st5)
End

(* ===== abi_decode ===== *)

(* abi_decode: decode ABI data to output type.
   Mirrors Python: builtins/abi.py lower_abi_decode
   Steps: get data ptr+len, validate bounds, alloc output, decode *)
Definition lower_abi_decode_def:
  lower_abi_decode data_op dec_info abi_min_size abi_max_size output_size st =
    (* Load length from data pointer *)
    let (data_len, st1) = emit_op MLOAD [data_op] st in
    (* Data starts after length word *)
    let (data_ptr, st2) = emit_op ADD [data_op; Lit 32w] st1 in
    (* Validate: min <= len <= max *)
    let (lt_min, st3) = emit_op LT [data_len; Lit (n2w abi_min_size)] st2 in
    let (ge_min, st4) = emit_op ISZERO [lt_min] st3 in
    let (gt_max, st5) =
      emit_op GT [data_len; Lit (n2w abi_max_size)] st4 in
    let (le_max, st6) = emit_op ISZERO [gt_max] st5 in
    let (valid, st7) = emit_op AND [ge_min; le_max] st6 in
    let (_, st8) = emit_void ASSERT [valid] st7 in
    (* Allocate output buffer *)
    let (out_buf_alloc, st9) = compile_alloc_buffer output_size st8 in
    let out_buf = out_buf_alloc.buf_operand in
    (* Compute hi = data_ptr + data_len for bounds checking *)
    let (hi, st10) = emit_op ADD [data_ptr; data_len] st9 in
    (* Decode ABI data into output buffer.
       load_opc=MLOAD since source is memory. *)
    let (_, st11) =
      compile_abi_decode_to_buf out_buf data_ptr MLOAD hi dec_info st10 in
    (out_buf, st11)
End
