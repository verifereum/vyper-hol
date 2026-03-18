(*
 * ABI Encoder/Decoder Definitions
 *
 * TOP-LEVEL:
 *   compile_abi_encode_static   — encode primitive word type
 *   compile_abi_encode_bytestring — encode bytes/string to ABI format
 *   compile_abi_decode_static   — decode primitive word type (Props only)
 *   compile_abi_decode_bool     — decode bool (Props only)
 *   compile_abi_encode_tuple    — encode tuple (Props only)
 *   compile_abi_decode_tuple    — decode tuple (Props only)
 *   compile_abi_encode_to_buf   — recursive dispatcher for ABI encoding
 *   compile_abi_decode_to_buf   — recursive dispatcher for ABI decoding
 *   compile_abi_encode_child    — encode dynamic child with offset tracking
 *   compile_abi_encode_dyn_array_loop — loop-based dynarray encode for nested types
 *   compile_abi_decode_dyn_array_loop — loop-based dynarray decode for nested types
 *   compile_abi_decode_complex  — decode complex type (tuple/struct/sarray)
 *
 * ABI encoding lays out values as:
 *   - Static types: 32 bytes each, in order
 *   - Dynamic types: 32-byte offset pointer, then data in tail region
 *
 * Mirrors Python: ~/vyper/vyper/codegen_venom/abi/abi_encoder.py
 *                 ~/vyper/vyper/codegen_venom/abi/abi_decoder.py
 *                 ~/vyper/vyper/codegen_venom/builtins/abi.py
 *)

Theory abiEncoder
Ancestors
  emitHelper context compileEnv venomInst

(* NOTE: abi_type_info record deleted — was never instantiated.
   ABI dynamic/static dispatch uses is_abi_dynamic sft from compileEnv. *)

(* ===== ABI Validation / Clamping ===== *)
(* abi_clamp, abi_enc_info, abi_dec_info datatypes are defined in compileEnv
   to avoid circular dependencies. They are inherited via Ancestors. *)

(* int_clamp: validate integer is in range.
   Signed: signextend(val) == val (canonical two's complement)
   Unsigned: val >> bits == 0 (no high bits set)
   Mirrors Python: abi/abi_decoder.py int_clamp *)
Definition compile_abi_int_clamp_def:
  compile_abi_int_clamp val_op bits is_signed st =
    if is_signed then
      (* signextend and compare to original *)
      let bytes_minus_1 = bits DIV 8 - 1 in
      let (canonical, st1) = emit_op SIGNEXTEND
        [Lit (n2w bytes_minus_1); val_op] st in
      let (eq_op, st2) = emit_op EQ [val_op; canonical] st1 in
      emit_void ASSERT [eq_op] st2
    else
      (* check high bits are zero: assert iszero(val >> bits) *)
      let (shifted, st1) = emit_op SHR [Lit (n2w bits); val_op] st in
      let (ok, st2) = emit_op ISZERO [shifted] st1 in
      emit_void ASSERT [ok] st2
End

(* bytes_clamp: validate bytesM has zero padding in low bits.
   BytesM is left-aligned, so low (32-m)*8 bits must be zero.
   Check: assert iszero(val << (m * 8))
   Mirrors Python: abi/abi_decoder.py bytes_clamp *)
Definition compile_abi_bytes_clamp_def:
  compile_abi_bytes_clamp val_op m st =
    let shift_bits = m * 8 in
    let (shifted, st1) = emit_op SHL [Lit (n2w shift_bits); val_op] st in
    let (ok, st2) = emit_op ISZERO [shifted] st1 in
    emit_void ASSERT [ok] st2
End

(* clamp_basetype: dispatch validation based on type.
   Mirrors Python: abi/abi_decoder.py clamp_basetype
   - Flag(n bits): unsigned int_clamp(n)
   - Int/Decimal(bits, signed): int_clamp if bits < 256
   - BytesM(m): bytes_clamp if m < 32
   - Address/Interface: unsigned int_clamp(160)
   - Bool: unsigned int_clamp(1) *)
Definition compile_abi_clamp_basetype_def:
  compile_abi_clamp_basetype val_op NoClamp st = ((), st) ∧
  compile_abi_clamp_basetype val_op (IntClamp bits is_signed) st =
    compile_abi_int_clamp val_op bits is_signed st ∧
  compile_abi_clamp_basetype val_op (BytesMClamp m) st =
    compile_abi_bytes_clamp val_op m st ∧
  compile_abi_clamp_basetype val_op BoolClamp st =
    (* Bool: assert val <= 1. Equivalent to int_clamp(1, unsigned). *)
    let (shifted, st1) = emit_op SHR [Lit 1w; val_op] st in
    let (ok, st2) = emit_op ISZERO [shifted] st1 in
    emit_void ASSERT [ok] st2
End

(* zero_pad: zero-pad bytestring data to 32-byte boundary.
   Layout: bytez_ptr → [length][data...]
   Write a zero word at bytez_ptr + 32 + length to clear any padding bytes.
   Mirrors Python: abi/abi_encoder.py _zero_pad *)
Definition compile_abi_zero_pad_def:
  compile_abi_zero_pad bytez_ptr st =
    let (len_op, st1) = emit_op MLOAD [bytez_ptr] st in
    let (data_end, st2) = emit_op ADD [bytez_ptr; Lit 32w] st1 in
    let (pad_ptr, st3) = emit_op ADD [data_end; len_op] st2 in
    emit_void MSTORE [pad_ptr; Lit 0w] st3
End

(* abi_encoding_matches_vyper: true when ABI layout matches Vyper memory layout.
   This is the case for all static types (no dynamic offsets needed).
   When true, encoding is a simple MCOPY (modeled by AbiCopy constructor
   in abi_enc_info). The caller constructs AbiCopy instead of AbiComplex
   when this predicate holds, so encoding dispatch at call sites is implicit
   in the abi_enc_info type construction.
   NOTE: abi_encoding_matches_vyper deleted — used abi_type_info (also deleted). *)

(* needs_clamp: does a decoded ABI value need validation?
   Bytestrings and dynamic arrays always need bounds checks.
   Primitive words need clamping unless full-width (uint256/int256/bytes32).
   Recursive for sarray/tuple.
   Mirrors Python: abi/abi_decoder.py needs_clamp *)
Definition needs_clamp_def:
  needs_clamp NoClamp = F ∧
  needs_clamp (IntClamp _ _) = T ∧
  needs_clamp (BytesMClamp _) = T ∧
  needs_clamp BoolClamp = T
End

(* ===== Element Pointer Navigation ===== *)
(* Get pointer to element within tuple/struct/sarray in Vyper memory layout.
   offset: compile-time byte offset of the element.
   Mirrors Python: abi/abi_encoder.py _get_element_ptr *)
Definition compile_get_element_ptr_def:
  compile_get_element_ptr parent_ptr (offset:num) st =
    if offset = 0 then (parent_ptr, st)
    else emit_op ADD [parent_ptr; Lit (n2w offset)] st
End

(* Navigate to element in dynamic array (skip length word + index * elem_size).
   Mirrors Python: abi/abi_encoder.py _get_element_ptr DArrayT branch *)
Definition compile_get_dynarray_elem_ptr_def:
  compile_get_dynarray_elem_ptr parent_ptr idx_op elem_size st =
    let (data_ptr, st1) = emit_op ADD [parent_ptr; Lit 32w] st in
    let (offset, st2) = emit_op MUL [idx_op; Lit (n2w elem_size)] st1 in
    emit_op ADD [data_ptr; offset] st2
End

(* ===== ABI Encode (static types) ===== *)
(* For primitive word types: just mstore the value at the destination.
   For bytesM: value is already left-aligned.
   For bool: value is 0 or 1. *)
Definition compile_abi_encode_static_def:
  compile_abi_encode_static src_op dst_op st =
    emit_void MSTORE [dst_op; src_op] st
End

(* ===== ABI Encode Dynamic ===== *)
(* For bytes/string: [32-byte offset in head][length][data] in tail
   For dynamic arrays: [32-byte offset][length][elem0][elem1]...
   Offset is relative to start of encoding. *)

(* Encode a single bytestring value to ABI format.
   Input: ptr to [length][data]
   Output at dst: [offset_to_data][length][padded_data]
   Returns: total encoded size *)
Definition compile_abi_encode_bytestring_def:
  compile_abi_encode_bytestring src_ptr dst head_offset st =
    (* Load length *)
    let (len_op, st1) = emit_op MLOAD [src_ptr] st in
    (* Store offset in head *)
    let (_, st2) = emit_void MSTORE [dst; Lit (n2w head_offset)] st1 in
    (* Tail starts at dst + head_offset *)
    let (tail, st3) = emit_op ADD [dst; Lit (n2w head_offset)] st2 in
    (* Store length at tail *)
    let (_, st4) = emit_void MSTORE [tail; len_op] st3 in
    (* Copy data: tail+32 ← src+32 for len bytes *)
    let (tail_data, st5) = emit_op ADD [tail; Lit 32w] st4 in
    let (src_data, st6) = emit_op ADD [src_ptr; Lit 32w] st5 in
    let (_, st7) = emit_void MCOPY [tail_data; src_data; len_op] st6 in
    (* Compute padded length: ceil32(len) + 32 *)
    let (padded, st8) = emit_op ADD [len_op; Lit 31w] st7 in
    let (ceil32_len, st9) = emit_op AND [padded; Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w] st8 in
    let (total, st10) = emit_op ADD [ceil32_len; Lit 32w] st9 in
    (total, st10)
End

(* ===== ABI Decode (standalone helpers — Props proof only) ===== *)
(* These standalone functions are NOT used by the main pipeline.
   The recursive compile_abi_decode_to_buf handles all cases.
   Kept for Props theorem statements (compile_abi_decode_static_correct, etc). *)

(* Decode a static word value with clamping *)
Definition compile_abi_decode_static_def:
  compile_abi_decode_static src_op dst_op clamp_fn st =
    let (val_op, st1) = emit_op MLOAD [src_op] st in
    (* Apply clamping function *)
    let (_, st2) = clamp_fn val_op st1 in
    emit_void MSTORE [dst_op; val_op] st2
End

(* Decode a bool: assert value is 0 or 1 *)
Definition compile_abi_decode_bool_def:
  compile_abi_decode_bool src_op dst_op st =
    let (val_op, st1) = emit_op MLOAD [src_op] st in
    let (too_big, st2) = emit_op GT [val_op; Lit 1w] st1 in
    let (ok, st3) = emit_op ISZERO [too_big] st2 in
    let (_, st4) = emit_void ASSERT [ok] st3 in
    emit_void MSTORE [dst_op; val_op] st4
End

(* Decode a bytestring: follow offset, bounds check, copy *)
(* NOTE: compile_abi_decode_bytestring deleted — zero callers.
   Bytestring ABI decoding is handled by compile_abi_decode_to_buf
   via the DecBytestring case of abi_dec_info. *)

(* ===== ABI Encode Tuple (standalone — Props proof only) ===== *)
(* NOT used by main pipeline (compile_abi_encode_to_buf handles all cases).
   Encode a tuple/struct by iterating elements.
   Each static element goes in the head section (32 bytes per entry).
   Each dynamic element gets an offset in the head, data in the tail.
   elem_sizes: list of (is_dynamic, mem_size) per element.
   Mirrors Python: abi/abi_encoder.py _abi_encode_to_buf
   NOTE: Not yet wired into compile_expr pipeline — used by compile_abi_encode
   which is called from builtinAbi (abi_encode/abi_decode builtins). *)
Definition compile_abi_encode_tuple_def:
  compile_abi_encode_tuple src_ptr dst_ptr [] _ st = (Lit 0w, st) ∧
  compile_abi_encode_tuple src_ptr dst_ptr
      ((is_dyn, mem_size) :: rest) head_offset st =
    if is_dyn then
      (* Dynamic: store offset in head, data in tail region *)
      (* For simplicity, copy mem_size bytes and compute tail offset *)
      let (head_pos, st1) = emit_op ADD [dst_ptr; Lit (n2w head_offset)] st in
      let (src_elem, st2) = emit_op ADD [src_ptr; Lit (n2w head_offset)] st1 in
      let (_, st3) = emit_void MSTORE [head_pos; Lit 0w] st2 in  (* offset placeholder *)
      compile_abi_encode_tuple src_ptr dst_ptr rest (head_offset + 32) st3
    else
      (* Static: copy 32 bytes from src to dst at head_offset *)
      let (src_elem, st1) = emit_op ADD [src_ptr; Lit (n2w head_offset)] st in
      let (dst_elem, st2) = emit_op ADD [dst_ptr; Lit (n2w head_offset)] st1 in
      let (val_op, st3) = emit_op MLOAD [src_elem] st2 in
      let (_, st4) = emit_void MSTORE [dst_elem; val_op] st3 in
      compile_abi_encode_tuple src_ptr dst_ptr rest (head_offset + 32) st4
End

(* ===== ABI Decode Tuple (element-by-element) ===== *)
(* Decode a tuple/struct by iterating elements.
   Each static element is loaded from head section.
   Each dynamic element follows an offset pointer.
   elem_infos: list of (is_dynamic, mem_size, max_len) per element.
   hi_op: upper bound for safety check.
   Mirrors Python: abi/abi_decoder.py _abi_decode_to_buf *)
Definition compile_abi_decode_tuple_def:
  compile_abi_decode_tuple src_base dst_ptr hi_op [] _ st = ((), st) ∧
  compile_abi_decode_tuple src_base dst_ptr hi_op
      ((is_dyn, mem_size, max_len) :: rest) head_offset st =
    if is_dyn then
      (* Dynamic: read offset from head, decode from tail *)
      let (head_pos, st1) = emit_op ADD [src_base; Lit (n2w head_offset)] st in
      let (offset, st2) = emit_op MLOAD [head_pos] st1 in
      let (data_base, st3) = emit_op ADD [src_base; offset] st2 in
      let (len_op, st4) = emit_op MLOAD [data_base] st3 in
      (* Bounds check *)
      let (too_long, st5) = emit_op GT [len_op; Lit (n2w max_len)] st4 in
      let (ok, st6) = emit_op ISZERO [too_long] st5 in
      let (_, st7) = emit_void ASSERT [ok] st6 in
      (* Copy to dst *)
      let (dst_elem, st8) = emit_op ADD [dst_ptr; Lit (n2w head_offset)] st7 in
      let (_, st9) = emit_void MSTORE [dst_elem; len_op] st8 in
      let (src_data, st10) = emit_op ADD [data_base; Lit 32w] st9 in
      let (dst_data, st11) = emit_op ADD [dst_elem; Lit 32w] st10 in
      let (_, st12) = emit_void MCOPY [dst_data; src_data; len_op] st11 in
      compile_abi_decode_tuple src_base dst_ptr hi_op rest (head_offset + 32) st12
    else
      (* Static: load value from head, store to dst *)
      let (src_elem, st1) = emit_op ADD [src_base; Lit (n2w head_offset)] st in
      let (val_op, st2) = emit_op MLOAD [src_elem] st1 in
      let (dst_elem, st3) = emit_op ADD [dst_ptr; Lit (n2w head_offset)] st2 in
      let (_, st4) = emit_void MSTORE [dst_elem; val_op] st3 in
      compile_abi_decode_tuple src_base dst_ptr hi_op rest (head_offset + 32) st4
End

(* NOTE: compile_abi_encode_dynarray deleted — zero callers.
   DynArray ABI encoding is handled by compile_abi_encode_to_buf
   via the AbiDynArray case of abi_enc_info. *)

(* ===== Recursive ABI Encode Dispatcher ===== *)
(* Dispatches on abi_enc_info (defined in compileEnv) to encode src to dst.
   Mirrors Python: abi/abi_encoder.py _abi_encode_to_buf *)

(* Encode a child element that may be dynamic.
   For dynamic children: encode data to tail section, store offset in head.
   For static children: encode directly at head position.
   dyn_ofst_ptr: memory location tracking current dynamic section offset.
   Mirrors Python: abi/abi_encoder.py _encode_child *)
(* Recursive ABI encode: mutual recursion between child/to_buf/elems/dyn_loop.
   Mirrors Python: abi/abi_encoder.py
   child → to_buf → complex_elems → child (and to_buf → dyn_loop → to_buf) *)
Definition compile_abi_encode_child_def:
  compile_abi_encode_child (dst:operand) child_ptr child_info
                           (is_dyn:bool) (static_ofst:num)
                           (dyn_ofst_ptr:operand) (st:compile_state) =
    (if ¬is_dyn then
      let (child_dst, st1) =
        (if static_ofst = 0 then (dst, st)
         else emit_op ADD [dst; Lit (n2w static_ofst)] st) in
      compile_abi_encode_to_buf child_dst child_ptr child_info st1
    else
      let (dyn_ofst, st1) = emit_op MLOAD [dyn_ofst_ptr] st in
      let (child_dst, st2) = emit_op ADD [dst; dyn_ofst] st1 in
      let (child_len, st3) =
        compile_abi_encode_to_buf child_dst child_ptr child_info st2 in
      let (static_loc, st4) =
        (if static_ofst = 0 then (dst, st3)
         else emit_op ADD [dst; Lit (n2w static_ofst)] st3) in
      let (_, st5) = emit_void MSTORE [static_loc; dyn_ofst] st4 in
      let (new_dyn, st6) = emit_op ADD [dyn_ofst; child_len] st5 in
      let (_, st7) = emit_void MSTORE [dyn_ofst_ptr; new_dyn] st6 in
      (child_len, st7)) ∧

  compile_abi_encode_to_buf (dst:operand) (src:operand)
                            AbiPrimWord (st:compile_state) =
    (let (val_op, st1) = emit_op MLOAD [src] st in
     let (_, st2) = emit_void MSTORE [dst; val_op] st1 in
     (Lit 32w, st2)) ∧

  compile_abi_encode_to_buf dst src (AbiBytestring max_len) st =
    (* Copy memory, zero-pad, compute ceil32 length.
       Mirrors Python: _abi_encode_to_buf bytestring branch.
       mem_size = 32 + ceil32(max_len) for 32-byte alignment. *)
    (let mem_size = 32 + ((max_len + 31) DIV 32) * 32 in
     let (_, st1) = emit_void MCOPY [dst; src; Lit (n2w mem_size)] st in
     let (_, st2) = compile_abi_zero_pad dst st1 in
     (* ABI length = ceil32(32 + actual_length) *)
     let (len_op, st3) = emit_op MLOAD [dst] st2 in
     let (padded, st4) = emit_op ADD [Lit 32w; len_op] st3 in
     let (ceil_len, st5) = emit_op ADD [padded; Lit 31w] st4 in
     emit_op AND [ceil_len;
       Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w] st5) ∧

  compile_abi_encode_to_buf dst src (AbiCopy mem_size) st =
    (let (_, st1) = emit_void MCOPY [dst; src; Lit (n2w mem_size)] st in
     (Lit (n2w mem_size), st1)) ∧

  compile_abi_encode_to_buf dst src
    (AbiDynArray elem_info elem_abi_sz elem_mem_sz elem_is_dyn) st =
    (let (len_op, st1) = emit_op MLOAD [src] st in
     let (_, st2) = emit_void MSTORE [dst; len_op] st1 in
     if ¬elem_is_dyn then
       let (copy_sz, st3) = emit_op MUL [len_op; Lit (n2w elem_abi_sz)] st2 in
       let (src_data, st4) = emit_op ADD [src; Lit 32w] st3 in
       let (dst_data, st5) = emit_op ADD [dst; Lit 32w] st4 in
       let (_, st6) = emit_void MCOPY [dst_data; src_data; copy_sz] st5 in
       emit_op ADD [Lit 32w; copy_sz] st6
     else
       let (dst_data, st3) = emit_op ADD [dst; Lit 32w] st2 in
       compile_abi_encode_dyn_loop
         dst_data src elem_info elem_abi_sz elem_mem_sz
         len_op st3) ∧

  compile_abi_encode_to_buf dst src (AbiComplex []) st =
    (Lit 0w, st) ∧

  compile_abi_encode_to_buf dst src (AbiComplex elems) st =
    ((* Dynamic offset starts AFTER all static head slots.
        static_size = sum of embedded_static_size for each element (= abi_sz).
        Mirrors Python: dyn_section_start = abi_t.static_size() *)
     let static_size = SUM (MAP (λ(_, abi_sz:num, _, _). abi_sz) elems) in
     let has_dynamic = EXISTS (λ(_, _, _, is_dyn). is_dyn) elems in
     if has_dynamic then
              let (dyn_ptr_alloc, st2) = compile_alloc_buffer 32 st in
              let dyn_ptr = dyn_ptr_alloc.buf_operand in
       let (_, st3) = emit_void MSTORE [dyn_ptr; Lit (n2w static_size)] st2 in
       let (_, st4) = compile_abi_encode_complex_elems dst src elems
                        (0:num) (0:num) dyn_ptr st3 in
       (* Return final dynamic offset = total encoded size *)
       emit_op MLOAD [dyn_ptr] st4
     else
       (* All static: encode elements, return static_size.
          Python returns abi_t.embedded_static_size() for all-static. *)
       let (_, st1) = compile_abi_encode_complex_elems dst src elems (0:num)
                        (0:num) (Lit 0w (* unused *)) st in
       (Lit (n2w static_size), st1)) ∧

  (* AbiComplex element list: (abi_enc_info, abi_static_size, mem_size, is_dynamic).
     src_offset increments by mem_size, head_offset by abi_static_size.
     Mirrors Python: _abi_encode_to_buf complex type loop. *)
  compile_abi_encode_complex_elems (dst:operand) (src:operand) []
    (_ :num) (_ :num) (dyn_ptr:operand) (st:compile_state) =
    (Lit 0w, st) ∧
  compile_abi_encode_complex_elems dst src
    ((ei, abi_sz, mem_sz, is_dyn)::rest) (src_offset:num) (head_offset:num)
    (dyn_ptr:operand) st =
    (let (elem_src, st1) =
       (if src_offset = 0 then (src, st)
        else emit_op ADD [src; Lit (n2w src_offset)] st) in
     let (_, st2) =
       compile_abi_encode_child dst elem_src ei is_dyn
                                head_offset dyn_ptr st1 in
     compile_abi_encode_complex_elems dst src rest
       (src_offset + mem_sz) (head_offset + abi_sz) dyn_ptr st2) ∧

  (* Dynamic array encode loop for DYNAMIC elements.
     Handles child_dyn_ofst tracking: head stores offset, data goes to tail.
     Mirrors Python: abi_encoder.py _encode_dyn_array with is_dynamic elements.
     For each element:
       1. Head = dst + i * 32 (embedded_static_size is 32 for dynamic elements)
       2. Tail = dst + child_dyn_ofst
       3. Encode child to tail
       4. Store child_dyn_ofst at head (offset word)
       5. child_dyn_ofst += child_len *)
  compile_abi_encode_dyn_loop (dst:operand) (src:operand)
    (elem_info:abi_enc_info) (elem_abi_sz:num) (elem_mem_sz:num)
    (len_op:operand) (st:compile_state) =
    ((* Allocate loop counter in memory *)
          let (i_ptr_alloc, st2) = compile_alloc_buffer 32 st in
          let i_ptr = i_ptr_alloc.buf_operand in
     let (_, st3) = emit_void MSTORE [i_ptr; Lit 0w] st2 in
     (* Allocate child_dyn_ofst tracker in memory.
        Initial value = length * elem_abi_sz (= length * 32 for dynamic elems).
        Dynamic section starts after the head section. *)
          let (dyn_ptr_alloc, st5) = compile_alloc_buffer 32 st3 in
          let dyn_ptr = dyn_ptr_alloc.buf_operand in
     let (init_dyn, st6) = emit_op MUL [len_op; Lit (n2w elem_abi_sz)] st5 in
     let (_, st7) = emit_void MSTORE [dyn_ptr; init_dyn] st6 in
     (* Create loop blocks *)
     let (hdr_lbl, st8) = fresh_label "enc_dyn_hdr" st7 in
     let (body_lbl, st9) = fresh_label "enc_dyn_body" st8 in
     let (exit_lbl, st10) = fresh_label "enc_dyn_exit" st9 in
     (* Jump to header *)
     let (_, st11) = emit_inst JMP [Label hdr_lbl] [] st10 in
     (* Header block: check i < length *)
     let (_, st12) = new_block hdr_lbl st11 in
     let (i_op, st13) = emit_op MLOAD [i_ptr] st12 in
     let (cmp, st14) = emit_op LT [i_op; len_op] st13 in
     let (done_op, st15) = emit_op ISZERO [cmp] st14 in
     let (_, st16) = emit_inst JNZ [done_op; Label exit_lbl; Label body_lbl] [] st15 in
     (* Body block: encode one element with offset tracking *)
     let (_, st17) = new_block body_lbl st16 in
     let (i_op2, st18) = emit_op MLOAD [i_ptr] st17 in
     (* Source element: src + 32 + i * elem_mem_sz *)
     let (src_data, st19) = emit_op ADD [src; Lit 32w] st18 in
     let (src_off, st20) = emit_op MUL [i_op2; Lit (n2w elem_mem_sz)] st19 in
     let (child_src, st21) = emit_op ADD [src_data; src_off] st20 in
     (* Read child_dyn_ofst for tail position *)
     let (dyn_ofst, st22) = emit_op MLOAD [dyn_ptr] st21 in
     (* Encode child to tail: child_dst = dst + dyn_ofst *)
     let (child_dst, st23) = emit_op ADD [dst; dyn_ofst] st22 in
     let (child_len, st24) =
       compile_abi_encode_to_buf child_dst child_src elem_info st23 in
     (* Store offset at head: head_pos = dst + i * elem_abi_sz *)
     let (head_off, st25) = emit_op MUL [i_op2; Lit (n2w elem_abi_sz)] st24 in
     let (head_pos, st26) = emit_op ADD [dst; head_off] st25 in
     let (_, st27) = emit_void MSTORE [head_pos; dyn_ofst] st26 in
     (* Update child_dyn_ofst += child_len *)
     let (new_dyn, st28) = emit_op ADD [dyn_ofst; child_len] st27 in
     let (_, st29) = emit_void MSTORE [dyn_ptr; new_dyn] st28 in
     (* Increment counter *)
     let (new_i, st30) = emit_op ADD [i_op2; Lit 1w] st29 in
     let (_, st31) = emit_void MSTORE [i_ptr; new_i] st30 in
     let (_, st32) = emit_inst JMP [Label hdr_lbl] [] st31 in
     (* Exit block: total size = final child_dyn_ofst (includes head+tail) *)
     let (_, st33) = new_block exit_lbl st32 in
     let (final_dyn, st34) = emit_op MLOAD [dyn_ptr] st33 in
     emit_op ADD [Lit 32w; final_dyn] st34)
Termination
  WF_REL_TAC `inv_image ($< LEX $<)
    (λx. case x of
       INL (dst,cp,ci,isDyn,soff,dop,st) => (abi_enc_info_size ci, 2)
     | INR (INL (dst,src,info,st)) => (abi_enc_info_size info, 1)
     | INR (INR (INL (dst,src,elems,so,ho,dp,st))) =>
         (list_size (pair_size abi_enc_info_size
           (pair_size (λx. x) (pair_size (λx. x) bool_size))) elems, 0)
     | INR (INR (INR (dst,src,ei,asz,msz,lo,st))) =>
         (abi_enc_info_size ei, 2))`
End

(* ===== Recursive ABI Decode Dispatcher ===== *)
(* abi_dec_info datatype is defined in compileEnv.
   Dispatches on abi_dec_info to decode ABI data into Vyper memory layout.
   Mirrors Python: abi/abi_decoder.py _abi_decode_to_buf *)

(* Get ABI element pointer, following offset indirection for dynamic types.
   For static: src + abi_offset
   For dynamic: src + deref(src + abi_offset) [offset indirection]
   Mirrors Python: abi/abi_decoder.py _getelemptr_abi *)
Definition compile_getelemptr_abi_def:
  compile_getelemptr_abi src_op is_dyn abi_offset load_opc st =
    let (head_ptr, st1) =
      (if abi_offset = 0 then (src_op, st)
       else emit_op ADD [src_op; Lit (n2w abi_offset)] st) in
    if ¬is_dyn then
      (head_ptr, st1)
    else
      (* Dynamic: read offset from head, add to base.
         Security: prevent underflow (actual_ptr >= parent).
         Mirrors Python: abi/abi_decoder.py _getelemptr_abi *)
      let (offset_val, st2) = emit_op load_opc [head_ptr] st1 in
      let (actual_ptr, st3) = emit_op ADD [src_op; offset_val] st2 in
      let (underflow, st4) = emit_op LT [actual_ptr; src_op] st3 in
      let (ok, st5) = emit_op ISZERO [underflow] st4 in
      let (_, st6) = emit_void ASSERT [ok] st5 in
      (actual_ptr, st6)
End

(* Offset indirection + bounds check for dynamic elements in decode loop.
   Shared by DecBytestring, DecDynArray, DecComplex(T) cases.
   Reads offset from elem_src, resolves to absolute ptr = src_data + offset,
   validates: ptr >= src_data (no underflow), ptr + elem_abi_sz <= hi (no OOB). *)
Definition compile_abi_decode_dyn_elem_ptr_def:
  compile_abi_decode_dyn_elem_ptr load_opc elem_src src_data hi_op elem_abi_sz st =
    let (off_val, st_a) = emit_op load_opc [elem_src] st in
    let (ptr, st_b) = emit_op ADD [src_data; off_val] st_a in
    let (bad, st_c) = emit_op LT [ptr; src_data] st_b in
    let (ok, st_d) = emit_op ISZERO [bad] st_c in
    let (_, st_e) = emit_void ASSERT [ok] st_d in
    let (eend, st_f) = emit_op ADD [ptr; Lit (n2w elem_abi_sz)] st_e in
    let (oob, st_g) = emit_op GT [eend; hi_op] st_f in
    let (ok2, st_h) = emit_op ISZERO [oob] st_g in
    let (_, st_i) = emit_void ASSERT [ok2] st_h in
    (ptr, st_i)
End

(* Recursive ABI decode dispatcher + helpers.
   Mirrors Python: abi/abi_decoder.py *)
Definition compile_abi_decode_to_buf_def:
  (* Primitive word: load, clamp per type, store.
     clamp_info dispatches: NoClamp (uint256/int256/bytes32), IntClamp (sub-256),
     BytesMClamp (padding check), BoolClamp (0 or 1).
     Mirrors Python: abi/abi_decoder.py _decode_primitive + clamp_basetype *)
  compile_abi_decode_to_buf dst src_op load_opc hi_op
                            (DecPrimWord clamp_info) st =
    (let (val_op, st1) = emit_op load_opc [src_op] st in
     let (_, st2) = compile_abi_clamp_basetype val_op clamp_info st1 in
     emit_void MSTORE [dst; val_op] st2) ∧

  (* Bytestring: bounds check + copy.
     Dispatches bulk copy by source: CALLDATACOPY for calldata,
     DLOADBYTES for code, MCOPY for memory/returndataXX. *)
  compile_abi_decode_to_buf dst src_op load_opc hi_op
                            (DecBytestring max_len) st =
    (let (len_op, st1) = emit_op load_opc [src_op] st in
     (* Check length <= max_len *)
     let (too_long, st2) = emit_op GT [len_op; Lit (n2w max_len)] st1 in
     let (ok, st3) = emit_op ISZERO [too_long] st2 in
     let (_, st4) = emit_void ASSERT [ok] st3 in
     (* Bounds check: src + 32 + length <= hi *)
     let (data_start, st5) = emit_op ADD [src_op; Lit 32w] st4 in
     let (data_end, st6) = emit_op ADD [data_start; len_op] st5 in
     let (oob, st7) = emit_op GT [data_end; hi_op] st6 in
     let (ok2, st8) = emit_op ISZERO [oob] st7 in
     let (_, st9) = emit_void ASSERT [ok2] st8 in
     (* Copy: store length + data.
        Dispatch copy opcode by source location. *)
     let (_, st10) = emit_void MSTORE [dst; len_op] st9 in
     let (dst_data, st11) = emit_op ADD [dst; Lit 32w] st10 in
     let (_, st12) = (case load_opc of
         CALLDATALOAD =>
           emit_void CALLDATACOPY [dst_data; data_start; len_op] st11
       | DLOAD =>
           emit_void DLOADBYTES [dst_data; data_start; len_op] st11
       | _ =>
           emit_void MCOPY [dst_data; data_start; len_op] st11) in
     ((), st12)) ∧

  (* Dynamic array: validate count, decode elements *)
  compile_abi_decode_to_buf dst src_op load_opc hi_op
    (DecDynArray elem_info elem_abi_sz elem_mem_sz elem_is_dyn max_count) st =
    (let (count, st1) = emit_op load_opc [src_op] st in
     (* Validate count <= max_count.
        Mirrors Python: abi/abi_decoder.py clamp_dyn_array *)
     let (too_many, st2) = emit_op GT [count; Lit (n2w max_count)] st1 in
     let (ok, st3) = emit_op ISZERO [too_many] st2 in
     let (_, st4) = emit_void ASSERT [ok] st3 in
     (* Payload bounds: src + 32 + count * elem_abi_sz <= hi.
        Prevents buffer overrun on untrusted data.
        Mirrors Python: abi/abi_decoder.py clamp_dyn_array hi check *)
     let (payload_sz, st4a) = emit_op MUL [count; Lit (n2w elem_abi_sz)] st4 in
     let (payload_plus_hdr, st4b) = emit_op ADD [payload_sz; Lit 32w] st4a in
     let (payload_end, st4c) = emit_op ADD [src_op; payload_plus_hdr] st4b in
     let (oob, st4d) = emit_op GT [payload_end; hi_op] st4c in
     let (ok2, st4e) = emit_op ISZERO [oob] st4d in
     let (_, st4f) = emit_void ASSERT [ok2] st4e in
     (* Store count *)
     let (_, st5) = emit_void MSTORE [dst; count] st4f in
     let can_bulk_copy =
       (case elem_info of
          DecPrimWord clamp => ¬elem_is_dyn ∧ ¬needs_clamp clamp
        | _ => F) in
     if can_bulk_copy then
       (* Static, no-clamp elements: safe bulk copy.
          Dispatch copy by source: CALLDATACOPY/DLOADBYTES/MCOPY.
          Mirrors Python: not needs_clamp(elem_typ) and not is_dynamic() *)
       let (copy_sz, st6) = emit_op MUL [count; Lit (n2w elem_mem_sz)] st5 in
       let (src_data, st7) = emit_op ADD [src_op; Lit 32w] st6 in
       let (dst_data, st8) = emit_op ADD [dst; Lit 32w] st7 in
       (case load_opc of
          CALLDATALOAD =>
            emit_void CALLDATACOPY [dst_data; src_data; copy_sz] st8
        | DLOAD =>
            emit_void DLOADBYTES [dst_data; src_data; copy_sz] st8
        | _ =>
            emit_void MCOPY [dst_data; src_data; copy_sz] st8)
     else
       (* Element-by-element decode loop *)
              let (i_ptr_alloc, st7) = compile_alloc_buffer 32 st5 in
              let i_ptr = i_ptr_alloc.buf_operand in
       let (_, st8) = emit_void MSTORE [i_ptr; Lit 0w] st7 in
       compile_abi_decode_dyn_loop dst src_op load_opc hi_op
         elem_info elem_abi_sz elem_mem_sz
         i_ptr count st8) ∧

  (* Complex type (tuple/struct/sarray): decode element by element *)
  compile_abi_decode_to_buf dst src_op load_opc hi_op
                            (DecComplex _ elems) st =
    (* Bounds check: src + static_size <= hi *)
    (let static_sz = FOLDR (λ(_, abi_sz:num, _:num) acc. abi_sz + acc) 0 elems in
     let (item_end, st1) = emit_op ADD [src_op; Lit (n2w static_sz)] st in
     let (oob, st2) = emit_op GT [item_end; hi_op] st1 in
     let (ok, st3) = emit_op ISZERO [oob] st2 in
     let (_, st4) = emit_void ASSERT [ok] st3 in
     compile_abi_decode_complex_elems dst src_op load_opc hi_op
       elems 0 0 st4) ∧

  (* Decode complex type elements iteratively.
     abi_offset: current ABI offset for reading.
     vyper_offset: current memory offset for writing.
     Mirrors Python: abi/abi_decoder.py _decode_complex *)
  compile_abi_decode_complex_elems dst src_op load_opc hi_op
    [] _ _ st = ((), st) ∧
  compile_abi_decode_complex_elems dst src_op load_opc hi_op
    ((ei, abi_sz, mem_sz)::rest) abi_offset vyper_offset st =
    (* Get source pointer, with offset indirection for dynamic *)
    (let is_dyn = (case ei of DecBytestring _ => T
                            | DecDynArray _ _ _ _ _ => T
                            | DecComplex is_d _ => is_d
                            | _ => F) in
     let (elem_src, st1) =
       compile_getelemptr_abi src_op is_dyn abi_offset load_opc st in
     let (elem_dst, st2) =
       (if vyper_offset = 0 then (dst, st1)
        else emit_op ADD [dst; Lit (n2w vyper_offset)] st1) in
     let (_, st3) = compile_abi_decode_to_buf elem_dst elem_src
                      load_opc hi_op ei st2 in
     compile_abi_decode_complex_elems dst src_op load_opc hi_op
       rest (abi_offset + abi_sz) (vyper_offset + mem_sz) st3) ∧

  (* Loop body for decoding dynamic array elements.
     Mirrors Python: abi/abi_decoder.py _decode_dyn_array loop *)
  (* Dynamic array decode loop: proper basic blocks with JMP/JNZ.
     Emits header/body/exit blocks. i_ptr is pre-allocated by caller.
     Mirrors Python: abi/abi_decoder.py _decode_dyn_array loop. *)
  compile_abi_decode_dyn_loop dst src_op load_opc hi_op
    elem_info elem_abi_sz elem_mem_sz i_ptr count st =
    ((* Create loop blocks *)
     let (hdr_lbl, st1) = fresh_label "dec_dyn_hdr" st in
     let (body_lbl, st2) = fresh_label "dec_dyn_body" st1 in
     let (exit_lbl, st3) = fresh_label "dec_dyn_exit" st2 in
     (* Jump to header *)
     let (_, st4) = emit_inst JMP [Label hdr_lbl] [] st3 in
     (* Header block: check i < count *)
     let (_, st5) = new_block hdr_lbl st4 in
     let (i_op, st6) = emit_op MLOAD [i_ptr] st5 in
     let (cmp, st7) = emit_op LT [i_op; count] st6 in
     let (done_op, st8) = emit_op ISZERO [cmp] st7 in
     let (_, st9) = emit_inst JNZ [done_op; Label exit_lbl; Label body_lbl] [] st8 in
     (* Body block *)
     let (_, st10) = new_block body_lbl st9 in
     let (i_op2, st11) = emit_op MLOAD [i_ptr] st10 in
     (* Source element: src + 32 + i * elem_abi_sz *)
     let (src_data, st12) = emit_op ADD [src_op; Lit 32w] st11 in
     let (src_off, st13) = emit_op MUL [i_op2; Lit (n2w elem_abi_sz)] st12 in
     let (elem_src, st14) = emit_op ADD [src_data; src_off] st13 in
     (* For dynamic elements, follow offset indirection + bounds check *)
     let is_dyn_elem = (case elem_info of
          DecBytestring _ => T
        | DecDynArray _ _ _ _ _ => T
        | DecComplex T _ => T
        | _ => F) in
     let (actual_src, st15) =
       (if is_dyn_elem then
          compile_abi_decode_dyn_elem_ptr load_opc elem_src src_data
            hi_op elem_abi_sz st14
        else (elem_src, st14)) in
     (* Dest element: dst + 32 + i * elem_mem_sz *)
     let (dst_data, st16) = emit_op ADD [dst; Lit 32w] st15 in
     let (dst_off, st17) = emit_op MUL [i_op2; Lit (n2w elem_mem_sz)] st16 in
     let (elem_dst, st18) = emit_op ADD [dst_data; dst_off] st17 in
     (* Decode element *)
     let (_, st19) = compile_abi_decode_to_buf elem_dst actual_src
                       load_opc hi_op elem_info st18 in
     (* Increment counter *)
     let (new_i, st20) = emit_op ADD [i_op2; Lit 1w] st19 in
     let (_, st21) = emit_void MSTORE [i_ptr; new_i] st20 in
     let (_, st22) = emit_inst JMP [Label hdr_lbl] [] st21 in
     (* Exit block: continue *)
     let (_, st23) = new_block exit_lbl st22 in
     ((), st23))
Termination
  WF_REL_TAC `inv_image ($< LEX $<)
    (λx. case x of
       INL (dst,src,lopc,hi,info,st) => (abi_dec_info_size info, 1)
     | INR (INL (dst,src,lopc,hi,elems,ao,vo,st)) =>
         (list_size (pair_size abi_dec_info_size
           (pair_size (λx. x) (λ(x:num). x))) elems, 0)
     | INR (INR (dst,src,lopc,hi,ei,asz,msz,ip,cnt,st)) =>
         (abi_dec_info_size ei, 2))`
End
