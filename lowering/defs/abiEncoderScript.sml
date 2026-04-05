(*
 * ABI Encoder/Decoder Definitions
 *
 * TOP-LEVEL:
 *   compile_abi_encode_static   — encode primitive word type
 *   compile_abi_decode_static   — decode primitive word type
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
Libs
  monadsyntax

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
  compile_abi_int_clamp val_op bits is_signed =
    if is_signed then
      let bytes_minus_1 = bits DIV 8 - 1 in
      do canonical <- emit_op SIGNEXTEND
           [Lit (n2w bytes_minus_1); val_op];
         eq_op <- emit_op EQ [val_op; canonical];
         emit_void ASSERT [eq_op]
      od
    else
      do shifted <- emit_op SHR [Lit (n2w bits); val_op];
         ok <- emit_op ISZERO [shifted];
         emit_void ASSERT [ok]
      od
End

(* bytes_clamp: validate bytesM has zero padding in low bits.
   BytesM is left-aligned, so low (32-m)*8 bits must be zero.
   Check: assert iszero(val << (m * 8))
   Mirrors Python: abi/abi_decoder.py bytes_clamp *)
Definition compile_abi_bytes_clamp_def:
  compile_abi_bytes_clamp val_op m =
    let shift_bits = m * 8 in
    do shifted <- emit_op SHL [Lit (n2w shift_bits); val_op];
       ok <- emit_op ISZERO [shifted];
       emit_void ASSERT [ok]
    od
End

(* clamp_basetype: dispatch validation based on type.
   Mirrors Python: abi/abi_decoder.py clamp_basetype *)
Definition compile_abi_clamp_basetype_def:
  compile_abi_clamp_basetype val_op NoClamp = return () ∧
  compile_abi_clamp_basetype val_op (IntClamp bits is_signed) =
    compile_abi_int_clamp val_op bits is_signed ∧
  compile_abi_clamp_basetype val_op (BytesMClamp m) =
    compile_abi_bytes_clamp val_op m ∧
  compile_abi_clamp_basetype val_op BoolClamp =
    do shifted <- emit_op SHR [Lit 1w; val_op];
       ok <- emit_op ISZERO [shifted];
       emit_void ASSERT [ok]
    od
End

(* zero_pad: zero-pad bytestring data to 32-byte boundary.
   Mirrors Python: abi/abi_encoder.py _zero_pad *)
Definition compile_abi_zero_pad_def:
  compile_abi_zero_pad bytez_ptr =
    do len_op <- emit_op MLOAD [bytez_ptr];
       data_end <- emit_op ADD [bytez_ptr; Lit 32w];
       pad_ptr <- emit_op ADD [data_end; len_op];
       emit_void MSTORE [pad_ptr; Lit 0w]
    od
End

(* needs_clamp: does a decoded ABI value need validation?
   Pure function — no state. *)
Definition needs_clamp_def:
  needs_clamp NoClamp = F ∧
  needs_clamp (IntClamp _ _) = T ∧
  needs_clamp (BytesMClamp _) = T ∧
  needs_clamp BoolClamp = T
End

(* ===== Element Pointer Navigation ===== *)
Definition compile_get_element_ptr_def:
  compile_get_element_ptr parent_ptr (offset:num) =
    if offset = 0 then return parent_ptr
    else emit_op ADD [parent_ptr; Lit (n2w offset)]
End

Definition compile_get_dynarray_elem_ptr_def:
  compile_get_dynarray_elem_ptr parent_ptr idx_op elem_size =
    do data_ptr <- emit_op ADD [parent_ptr; Lit 32w];
       offset <- emit_op MUL [idx_op; Lit (n2w elem_size)];
       emit_op ADD [data_ptr; offset]
    od
End

(* ===== ABI Encode (static types) ===== *)
Definition compile_abi_encode_static_def:
  compile_abi_encode_static src_op dst_op =
    emit_void MSTORE [dst_op; src_op]
End

(* ===== ABI Decode (standalone helpers) ===== *)
Definition compile_abi_decode_static_def:
  compile_abi_decode_static src_op dst_op clamp_fn =
    do val_op <- emit_op MLOAD [src_op];
       clamp_fn val_op;
       emit_void MSTORE [dst_op; val_op]
    od
End

(* ===== Recursive ABI Encode Dispatcher ===== *)
(* Mutual recursion: child/to_buf/complex_elems/dyn_loop.
   Mirrors Python: abi/abi_encoder.py *)
Definition compile_abi_encode_child_def:
  compile_abi_encode_child (dst:operand) child_ptr child_info
                           (is_dyn:bool) (static_ofst:num)
                           (dyn_ofst_ptr:operand) =
    (if ¬is_dyn then
      do child_dst <-
           (if static_ofst = 0 then return dst
            else emit_op ADD [dst; Lit (n2w static_ofst)]);
         compile_abi_encode_to_buf child_dst child_ptr child_info
      od
    else
      do dyn_ofst <- emit_op MLOAD [dyn_ofst_ptr];
         child_dst <- emit_op ADD [dst; dyn_ofst];
         child_len <-
           compile_abi_encode_to_buf child_dst child_ptr child_info;
         static_loc <-
           (if static_ofst = 0 then return dst
            else emit_op ADD [dst; Lit (n2w static_ofst)]);
         emit_void MSTORE [static_loc; dyn_ofst];
         new_dyn <- emit_op ADD [dyn_ofst; child_len];
         emit_void MSTORE [dyn_ofst_ptr; new_dyn];
         return child_len
      od) ∧

  compile_abi_encode_to_buf (dst:operand) (src:operand)
                            AbiPrimWord =
    (do val_op <- emit_op MLOAD [src];
        emit_void MSTORE [dst; val_op];
        return (Lit 32w)
     od) ∧

  compile_abi_encode_to_buf dst src (AbiBytestring max_len) =
    (let mem_size = 32 + ((max_len + 31) DIV 32) * 32 in
     do emit_void MCOPY [dst; src; Lit (n2w mem_size)];
        compile_abi_zero_pad dst;
        len_op <- emit_op MLOAD [dst];
        padded <- emit_op ADD [Lit 32w; len_op];
        ceil_len <- emit_op ADD [padded; Lit 31w];
        emit_op AND [ceil_len;
          Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w]
     od) ∧

  compile_abi_encode_to_buf dst src (AbiCopy mem_size) =
    (do emit_void MCOPY [dst; src; Lit (n2w mem_size)];
        return (Lit (n2w mem_size))
     od) ∧

  compile_abi_encode_to_buf dst src
    (AbiDynArray elem_info elem_abi_sz elem_mem_sz elem_is_dyn) =
    (do len_op <- emit_op MLOAD [src];
        emit_void MSTORE [dst; len_op];
        if ¬elem_is_dyn then
          do copy_sz <- emit_op MUL [len_op; Lit (n2w elem_abi_sz)];
             src_data <- emit_op ADD [src; Lit 32w];
             dst_data <- emit_op ADD [dst; Lit 32w];
             emit_void MCOPY [dst_data; src_data; copy_sz];
             emit_op ADD [Lit 32w; copy_sz]
          od
        else
          do dst_data <- emit_op ADD [dst; Lit 32w];
             compile_abi_encode_dyn_loop
               dst_data src elem_info elem_abi_sz elem_mem_sz
               len_op
          od
     od) ∧

  compile_abi_encode_to_buf dst src (AbiComplex []) =
    (return (Lit 0w)) ∧

  compile_abi_encode_to_buf dst src (AbiComplex elems) =
    (let static_size = SUM (MAP (λ(_, abi_sz:num, _, _). abi_sz) elems) in
     let has_dynamic = EXISTS (λ(_, _, _, is_dyn). is_dyn) elems in
     if has_dynamic then
       do dyn_ptr_alloc <- compile_alloc_buffer 32;
          let dyn_ptr = dyn_ptr_alloc.buf_operand in
          do emit_void MSTORE [dyn_ptr; Lit (n2w static_size)];
             compile_abi_encode_complex_elems dst src elems
               (0:num) (0:num) dyn_ptr;
             emit_op MLOAD [dyn_ptr]
          od
       od
     else
       do compile_abi_encode_complex_elems dst src elems (0:num)
            (0:num) (Lit 0w);
          return (Lit (n2w static_size))
       od) ∧

  compile_abi_encode_complex_elems (dst:operand) (src:operand) []
    (_ :num) (_ :num) (dyn_ptr:operand) =
    (return (Lit 0w)) ∧
  compile_abi_encode_complex_elems dst src
    ((ei, abi_sz, mem_sz, is_dyn)::rest) (src_offset:num) (head_offset:num)
    (dyn_ptr:operand) =
    (do elem_src <-
          (if src_offset = 0 then return src
           else emit_op ADD [src; Lit (n2w src_offset)]);
        compile_abi_encode_child dst elem_src ei is_dyn
                                 head_offset dyn_ptr;
        compile_abi_encode_complex_elems dst src rest
          (src_offset + mem_sz) (head_offset + abi_sz) dyn_ptr
     od) ∧

  compile_abi_encode_dyn_loop (dst:operand) (src:operand)
    (elem_info:abi_enc_info) (elem_abi_sz:num) (elem_mem_sz:num)
    (len_op:operand) =
    do i_ptr_alloc <- compile_alloc_buffer 32;
       let i_ptr = i_ptr_alloc.buf_operand in
       do emit_void MSTORE [i_ptr; Lit 0w];
          dyn_ptr_alloc <- compile_alloc_buffer 32;
          let dyn_ptr = dyn_ptr_alloc.buf_operand in
          do init_dyn <- emit_op MUL [len_op; Lit (n2w elem_abi_sz)];
             emit_void MSTORE [dyn_ptr; init_dyn];
             hdr_lbl <- fresh_label "enc_dyn_hdr";
             body_lbl <- fresh_label "enc_dyn_body";
             exit_lbl <- fresh_label "enc_dyn_exit";
             emit_inst JMP [Label hdr_lbl] [];
             new_block hdr_lbl;
             i_op <- emit_op MLOAD [i_ptr];
             cmp <- emit_op LT [i_op; len_op];
             done_op <- emit_op ISZERO [cmp];
             emit_inst JNZ [done_op; Label exit_lbl; Label body_lbl] [];
             new_block body_lbl;
             i_op2 <- emit_op MLOAD [i_ptr];
             src_data <- emit_op ADD [src; Lit 32w];
             src_off <- emit_op MUL [i_op2; Lit (n2w elem_mem_sz)];
             child_src <- emit_op ADD [src_data; src_off];
             dyn_ofst <- emit_op MLOAD [dyn_ptr];
             child_dst <- emit_op ADD [dst; dyn_ofst];
             child_len <-
               compile_abi_encode_to_buf child_dst child_src elem_info;
             head_off <- emit_op MUL [i_op2; Lit (n2w elem_abi_sz)];
             head_pos <- emit_op ADD [dst; head_off];
             emit_void MSTORE [head_pos; dyn_ofst];
             new_dyn <- emit_op ADD [dyn_ofst; child_len];
             emit_void MSTORE [dyn_ptr; new_dyn];
             new_i <- emit_op ADD [i_op2; Lit 1w];
             emit_void MSTORE [i_ptr; new_i];
             emit_inst JMP [Label hdr_lbl] [];
             new_block exit_lbl;
             final_dyn <- emit_op MLOAD [dyn_ptr];
             emit_op ADD [Lit 32w; final_dyn]
          od
       od
    od
Termination
  WF_REL_TAC `inv_image ($< LEX $<)
    (λx. case x of
       INL (dst,cp,ci,isDyn,soff,dop) => (abi_enc_info_size ci, 2)
     | INR (INL (dst,src,info)) => (abi_enc_info_size info, 1)
     | INR (INR (INL (dst,src,elems,so,ho,dp))) =>
         (list_size (pair_size abi_enc_info_size
           (pair_size (λx. x) (pair_size (λx. x) bool_size))) elems, 0)
     | INR (INR (INR (dst,src,ei,asz,msz,lo))) =>
         (abi_enc_info_size ei, 2))`
End

(* ===== Recursive ABI Decode Dispatcher ===== *)

(* Get ABI element pointer, following offset indirection for dynamic types.
   Mirrors Python: abi/abi_decoder.py _getelemptr_abi *)
Definition compile_getelemptr_abi_def:
  compile_getelemptr_abi src_op is_dyn abi_offset load_opc =
    do head_ptr <-
         (if abi_offset = 0 then return src_op
          else emit_op ADD [src_op; Lit (n2w abi_offset)]);
       if ¬is_dyn then
         return head_ptr
       else
         do offset_val <- emit_op load_opc [head_ptr];
            actual_ptr <- emit_op ADD [src_op; offset_val];
            underflow <- emit_op LT [actual_ptr; src_op];
            ok <- emit_op ISZERO [underflow];
            emit_void ASSERT [ok];
            return actual_ptr
         od
    od
End

(* Offset indirection + bounds check for dynamic elements in decode loop. *)
Definition compile_abi_decode_dyn_elem_ptr_def:
  compile_abi_decode_dyn_elem_ptr load_opc elem_src src_data hi_op elem_abi_sz =
    do off_val <- emit_op load_opc [elem_src];
       ptr <- emit_op ADD [src_data; off_val];
       bad <- emit_op LT [ptr; src_data];
       ok <- emit_op ISZERO [bad];
       emit_void ASSERT [ok];
       eend <- emit_op ADD [ptr; Lit (n2w elem_abi_sz)];
       oob <- emit_op GT [eend; hi_op];
       ok2 <- emit_op ISZERO [oob];
       emit_void ASSERT [ok2];
       return ptr
    od
End

(* Recursive ABI decode dispatcher + helpers.
   Mirrors Python: abi/abi_decoder.py *)
Definition compile_abi_decode_to_buf_def:
  compile_abi_decode_to_buf (dst:operand) (src_op:operand) (load_opc:opcode)
                            (hi_op:operand) (DecPrimWord clamp_info) =
    (do val_op <- emit_op load_opc [src_op];
        compile_abi_clamp_basetype val_op clamp_info;
        emit_void MSTORE [dst; val_op]
     od) ∧

  compile_abi_decode_to_buf dst src_op load_opc hi_op
                            (DecBytestring max_len) =
    (do len_op <- emit_op load_opc [src_op];
        too_long <- emit_op GT [len_op; Lit (n2w max_len)];
        ok <- emit_op ISZERO [too_long];
        emit_void ASSERT [ok];
        data_start <- emit_op ADD [src_op; Lit 32w];
        data_end <- emit_op ADD [data_start; len_op];
        oob <- emit_op GT [data_end; hi_op];
        ok2 <- emit_op ISZERO [oob];
        emit_void ASSERT [ok2];
        emit_void MSTORE [dst; len_op];
        dst_data <- emit_op ADD [dst; Lit 32w];
        (case load_opc of
           CALLDATALOAD =>
             emit_void CALLDATACOPY [dst_data; data_start; len_op]
         | DLOAD =>
             emit_void DLOADBYTES [dst_data; data_start; len_op]
         | _ =>
             emit_void MCOPY [dst_data; data_start; len_op])
     od) ∧

  compile_abi_decode_to_buf dst src_op load_opc hi_op
    (DecDynArray elem_info elem_abi_sz elem_mem_sz elem_is_dyn max_count) =
    (do cnt <- emit_op load_opc [src_op];
        too_many <- emit_op GT [cnt; Lit (n2w max_count)];
        ok <- emit_op ISZERO [too_many];
        emit_void ASSERT [ok];
        payload_sz <- emit_op MUL [cnt; Lit (n2w elem_abi_sz)];
        payload_plus_hdr <- emit_op ADD [payload_sz; Lit 32w];
        payload_end <- emit_op ADD [src_op; payload_plus_hdr];
        oob <- emit_op GT [payload_end; hi_op];
        ok2 <- emit_op ISZERO [oob];
        emit_void ASSERT [ok2];
        emit_void MSTORE [dst; cnt];
        let can_bulk_copy =
          (case elem_info of
             DecPrimWord clamp =>
               if elem_is_dyn then F else ¬needs_clamp clamp
           | _ => F) in
        if can_bulk_copy then
          do copy_sz <- emit_op MUL [cnt; Lit (n2w elem_mem_sz)];
             src_data <- emit_op ADD [src_op; Lit 32w];
             dst_data <- emit_op ADD [dst; Lit 32w];
             (case load_opc of
                CALLDATALOAD =>
                  emit_void CALLDATACOPY [dst_data; src_data; copy_sz]
              | DLOAD =>
                  emit_void DLOADBYTES [dst_data; src_data; copy_sz]
              | _ =>
                  emit_void MCOPY [dst_data; src_data; copy_sz])
          od
        else
          do i_ptr_alloc <- compile_alloc_buffer 32;
             let i_ptr = i_ptr_alloc.buf_operand in
             do emit_void MSTORE [i_ptr; Lit 0w];
                compile_abi_decode_dyn_loop dst src_op load_opc hi_op
                  elem_info elem_abi_sz elem_mem_sz
                  i_ptr cnt
             od
          od
     od) ∧

  compile_abi_decode_to_buf dst src_op load_opc hi_op
                            (DecComplex is_dyn_complex elems) =
    (let static_sz = FOLDR (λ(_, abi_sz:num, _:num) acc. abi_sz + acc) 0 elems in
     do item_end <- emit_op ADD [src_op; Lit (n2w static_sz)];
        oob <- emit_op GT [item_end; hi_op];
        ok <- emit_op ISZERO [oob];
        emit_void ASSERT [ok];
        compile_abi_decode_complex_elems dst src_op load_opc hi_op
          elems 0 0
     od) ∧

  compile_abi_decode_complex_elems (dst:operand) (src_op:operand)
    (load_opc:opcode) (hi_op:operand)
    ([] : (abi_dec_info # num # num) list) (_ : num) (_ : num) =
    (return () : unit compiler) ∧
  compile_abi_decode_complex_elems dst src_op load_opc hi_op
    ((ei, abi_sz, mem_sz)::rest) abi_offset vyper_offset =
    (let is_dyn = (case ei of DecBytestring _ => T
                             | DecDynArray _ _ _ _ _ => T
                             | DecComplex is_d _ => is_d
                             | _ => F) in
     do elem_src <-
          compile_getelemptr_abi src_op is_dyn abi_offset load_opc;
        elem_dst <-
          (if vyper_offset = 0 then return dst
           else emit_op ADD [dst; Lit (n2w vyper_offset)]);
        compile_abi_decode_to_buf elem_dst elem_src
                       load_opc hi_op ei;
        compile_abi_decode_complex_elems dst src_op load_opc hi_op
          rest (abi_offset + abi_sz) (vyper_offset + mem_sz)
     od) ∧

  compile_abi_decode_dyn_loop (dst:operand) (src_op:operand)
    (load_opc:opcode) (hi_op:operand)
    (elem_info:abi_dec_info) (elem_abi_sz:num) (elem_mem_sz:num)
    (i_ptr:operand) (cnt:operand) =
    (let is_dyn_elem = (case elem_info of
            DecBytestring _ => T
          | DecDynArray _ _ _ _ _ => T
          | DecComplex T _ => T
          | _ => F) in
     do hdr_lbl <- fresh_label "dec_dyn_hdr";
        body_lbl <- fresh_label "dec_dyn_body";
        exit_lbl <- fresh_label "dec_dyn_exit";
        emit_inst JMP [Label hdr_lbl] [];
        new_block hdr_lbl;
        i_op <- emit_op MLOAD [i_ptr];
        cmp <- emit_op LT [i_op; cnt];
        done_op <- emit_op ISZERO [cmp];
        emit_inst JNZ [done_op; Label exit_lbl; Label body_lbl] [];
        new_block body_lbl;
        i_op2 <- emit_op MLOAD [i_ptr];
        src_data <- emit_op ADD [src_op; Lit 32w];
        src_off <- emit_op MUL [i_op2; Lit (n2w elem_abi_sz)];
        elem_src <- emit_op ADD [src_data; src_off];
        actual_src <-
          (if is_dyn_elem then
             compile_abi_decode_dyn_elem_ptr load_opc elem_src src_data
               hi_op elem_abi_sz
           else return elem_src);
        dst_data <- emit_op ADD [dst; Lit 32w];
        dst_off <- emit_op MUL [i_op2; Lit (n2w elem_mem_sz)];
        elem_dst <- emit_op ADD [dst_data; dst_off];
        compile_abi_decode_to_buf elem_dst actual_src
                     load_opc hi_op elem_info;
        new_i <- emit_op ADD [i_op2; Lit 1w];
        emit_void MSTORE [i_ptr; new_i];
        emit_inst JMP [Label hdr_lbl] [];
        new_block exit_lbl;
        return ()
     od)
Termination
  WF_REL_TAC `inv_image ($< LEX $<)
    (λx. case x of
       INL (dst,src,lopc,hi,info) => (abi_dec_info_size info, 1)
     | INR (INL (dst,src,lopc,hi,elems,ao,vo)) =>
         (list_size (pair_size abi_dec_info_size
           (pair_size (λx. x) (λ(x:num). x))) elems, 0)
     | INR (INR (dst,src,lopc,hi,ei,asz,msz,ip,cnt)) =>
         (abi_dec_info_size ei, 2))`
End
