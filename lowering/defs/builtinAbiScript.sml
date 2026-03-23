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
Libs
  monadsyntax

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
    (_ :num) = return () ∧
  compile_create_tuple_in_memory buf_op
    ((arg_op, is_prim, mem_sz) :: rest) offset =
    do dst <-
         (if offset = 0 then return buf_op
          else emit_op ADD [buf_op; Lit (n2w offset)]);
       (if is_prim then emit_void MSTORE [dst; arg_op]
        else emit_void MCOPY [dst; arg_op; Lit (n2w mem_sz)]);
       compile_create_tuple_in_memory buf_op rest (offset + mem_sz)
    od
End

(* ===== abi_encode ===== *)

(* abi_encode(args, ensure_tuple, method_id) -> Bytes[N]
   Mirrors Python: builtins/abi.py lower_abi_encode
   Steps: eval args, create tuple, encode, optional method_id prefix *)
Definition lower_abi_encode_def:
  lower_abi_encode ensure_tuple method_id_opt src_op enc_info maxlen =
    let mid_size = (case method_id_opt of SOME _ => 4 | NONE => 0) in
    let total_size = maxlen + 32 + mid_size in
    let data_offset = 32 + mid_size in
    do (* Allocate output buffer: [32-byte length] | [optional method_id] | [data] *)
       buf_op_alloc <- compile_alloc_buffer total_size;
       buf_op <- return buf_op_alloc.buf_operand;
       data_ptr <- emit_op ADD [buf_op; Lit (n2w data_offset)];
       (* Optionally store method_id at buf+32 (shifted left 224 bits) *)
       (case method_id_opt of
          SOME mid =>
            do mid_ptr <- emit_op ADD [buf_op; Lit 32w];
               emit_void MSTORE [mid_ptr; Lit (mid << 224)]
            od
        | NONE => return ());
       (* Encode data into buffer, get runtime encoded length *)
       encoded_len <-
         compile_abi_encode_to_buf data_ptr src_op enc_info;
       (* Store total length = encoded_len + mid_size (runtime value) *)
       (if mid_size > 0 then
          do total_len <- emit_op ADD [encoded_len; Lit (n2w mid_size)];
             emit_void MSTORE [buf_op; total_len]
          od
        else
          emit_void MSTORE [buf_op; encoded_len]);
       return buf_op
    od
End

(* ===== abi_decode ===== *)

(* abi_decode: decode ABI data to output type.
   Mirrors Python: builtins/abi.py lower_abi_decode
   Steps: get data ptr+len, validate bounds, alloc output, decode *)
Definition lower_abi_decode_def:
  lower_abi_decode data_op dec_info abi_min_size abi_max_size output_size =
    do (* Load length from data pointer *)
       data_len <- emit_op MLOAD [data_op];
       (* Data starts after length word *)
       data_ptr <- emit_op ADD [data_op; Lit 32w];
       (* Validate: min <= len <= max *)
       lt_min <- emit_op LT [data_len; Lit (n2w abi_min_size)];
       ge_min <- emit_op ISZERO [lt_min];
       gt_max <- emit_op GT [data_len; Lit (n2w abi_max_size)];
       le_max <- emit_op ISZERO [gt_max];
       valid <- emit_op AND [ge_min; le_max];
       emit_void ASSERT [valid];
       (* Allocate output buffer *)
       out_buf_alloc <- compile_alloc_buffer output_size;
       out_buf <- return out_buf_alloc.buf_operand;
       (* Compute hi = data_ptr + data_len for bounds checking *)
       hi <- emit_op ADD [data_ptr; data_len];
       (* Decode ABI data into output buffer.
          load_opc=MLOAD since source is memory. *)
       compile_abi_decode_to_buf out_buf data_ptr MLOAD hi dec_info;
       return out_buf
    od
End
