(*
 * Statement Lowering: Vyper statements → Venom IR instructions
 *
 * TOP-LEVEL:
 *   compile_stmt       — compile a single statement
 *   compile_stmts      — compile a list of statements
 *
 * Helper:
 *   compile_if         — if/else multi-block control flow
 *   compile_for_range  — for-range loop (5-block CFG)
 *   compile_assert     — assertion with revert
 *   compile_return     — return value or stop
 *
 * Mirrors Python codegen: ~/vyper/vyper/codegen_venom/stmt.py
 * Phase 1 scope: primitive types only (uint256, int256, int128, bool, address, bytes32)
 *)

Theory stmtLowering
Ancestors
  exprLowering context compileEnv venomInst abiEncoder

(* ===== Target Compilation ===== *)

(* ===== Statement Compilation ===== *)

(* All compile_stmt / compile_stmts use explicit state passing for
   recursive calls, same pattern as compile_expr. Non-recursive helpers
   use explicit let-threading style. *)

(* Loop context: tracks break/continue targets *)
Datatype:
  loop_ctx =
    NoLoop
  | InLoop string string   (* break_label, continue_label *)
End

(* ===== Log args: evaluate all exprs first, then split ===== *)
(* CRITICAL: All log args must be evaluated in AST order first, then split
   into indexed (topics) and non-indexed (data). This matches Python which
   evaluates all args before splitting. *)

(* Evaluate all log arg expressions in AST order.
   Returns list of (operand, type) pairs preserving AST order. *)
Definition compile_log_eval_all_def:
  compile_log_eval_all cenv [] st = ([] : (operand # type) list, st) ∧
  compile_log_eval_all cenv (e::es) st =
    (let arg_ty = expr_type e in
     let (v, st1) = lower_value compile_expr cenv arg_ty e st in
     let (rest, st2) = compile_log_eval_all cenv es st1 in
     ((v, arg_ty) :: rest, st2))
Termination
  WF_REL_TAC `measure (λ(cenv,es,st). LENGTH es)`
End

(* Split already-evaluated operands into indexed topics and non-indexed data.
   indexed_flags: bool list parallel to evaluated ops. *)
Definition split_log_ops_def:
  split_log_ops [] [] = ([] : (operand # bool) list,
                          [] : (operand # type) list) ∧
  split_log_ops ((op, ty) :: rest) (T :: flags) =
    (let (topics, data) = split_log_ops rest flags in
     let is_bs = is_bytestring_type ty in
     ((op, is_bs) :: topics, data)) ∧
  split_log_ops ((op, ty) :: rest) (F :: flags) =
    (let (topics, data) = split_log_ops rest flags in
     (topics, (op, ty) :: data)) ∧
  split_log_ops _ _ = ([], [])
End

(* Hash indexed topic operands (bytestrings need keccak256).
   Input: list of (operand, is_bytestring) *)
Definition compile_log_topic_ops_def:
  compile_log_topic_ops [] st = ([] : operand list, st) ∧
  compile_log_topic_ops (x :: rest) st =
    (let (topic_op, st1) = compile_encode_log_topic (FST x) (SND x) st in
     let (rest_ops, st2) = compile_log_topic_ops rest st1 in
     (topic_op :: rest_ops, st2))
Termination
  WF_REL_TAC `measure (λ(ops,st). LENGTH ops)`
End

(* Store already-evaluated data operands to buffer.
   Input: list of (operand, type) *)
Definition compile_log_store_data_def:
  compile_log_store_data cenv [] buf_op offset st = ((), st) ∧
  compile_log_store_data cenv (x :: rest) buf_op offset st =
    (let v = FST x in let arg_ty = SND x in
     let mem_size = type_memory_bytes cenv arg_ty in
     let is_prim = is_word_type arg_ty in
     let (dst, st1) = if offset = 0 then (buf_op, st)
                       else emit_op ADD [buf_op; Lit (n2w offset)] st in
     let (_, st2) =
       if is_prim then emit_void MSTORE [dst; v] st1
       else if is_bytestring_type arg_ty then
         compile_store_bytestring v dst st1
       else emit_void MCOPY [dst; v; Lit (n2w mem_size)] st1 in
     compile_log_store_data cenv rest buf_op (offset + mem_size) st2)
Termination
  WF_REL_TAC `measure (λ(cenv,ops,buf,off,st). LENGTH ops)`
End

(* Extract target name as string for metadata lookup *)
Definition target_to_string_def:
  target_to_string (NameTarget id) = id ∧
  target_to_string (BareGlobalNameTarget id) = id ∧
  target_to_string (TopLevelNameTarget nsid) = SND nsid ∧
  target_to_string (SubscriptTarget bt _) = target_to_string bt ∧
  target_to_string (AttributeTarget bt _) = target_to_string bt
End

(* Convert assignment target to expression for location inference *)
Definition target_to_expr_def:
  target_to_expr (NameTarget id) = Name NoneT id ∧
  target_to_expr (BareGlobalNameTarget id) = BareGlobalName NoneT id ∧
  target_to_expr (TopLevelNameTarget nsid) =
    Attribute NoneT (Name NoneT "self") (SND nsid) ∧
  target_to_expr (SubscriptTarget bt idx) =
    Subscript NoneT (target_to_expr bt) idx ∧
  target_to_expr (AttributeTarget bt fld) =
    Attribute NoneT (target_to_expr bt) fld
End

(* ===== Revert with Reason ===== *)
(* Emit revert with Error(string) encoding.
   Error(string) selector: 0x08c379a0
   Buffer layout: buf+0: selector word, buf+32: ABI-encoded (string,) tuple.
   Final revert from buf+28 with length 4 + encoded_len.
   Mirrors Python: stmt.py _revert_with_reason *)
  (* KNOWN LIMITATION: Manual ABI encoding. Assumes msg_op is a memory pointer
     to [length][data] layout (correct for in-memory string literals).
     Python uses abi_encode_to_buf which handles storage/transient unwrap.
     Vyper only allows string literals as assert/revert reasons, so this is
     correct in practice. *)
(* Revert with Error(string) encoding using shared ABI encoder.
   Wraps message in TupleT((msg_typ,)) and uses compile_abi_encode_to_buf.
   Mirrors Python: stmt.py _revert_with_reason.
   msg_op: pointer to message in memory.
   msg_type: type of the message (usually StringT).
   msg_enc_info: ABI encoding info for the message type. *)
Definition compile_revert_with_reason_def:
  compile_revert_with_reason cenv msg_op msg_type msg_mem_size st =
    (* Wrap message type as tuple: (msg_type,) for ABI encoding.
       Mirrors Python: wrapped_typ = TupleT((msg_typ,)) *)
    let wrapped_type = TupleT [msg_type] in
    let wrapped_enc_info = type_to_abi_enc_info cenv wrapped_type in
    let wrapped_abi_size = abi_size_bound (cenv_sft cenv) wrapped_type in
    (* Allocate buffer: 32 (selector word) + encoded payload *)
    let buf_size = 32 + wrapped_abi_size in
    let (buf_op_alloc, st2) = compile_alloc_buffer buf_size st in
    let buf_op = buf_op_alloc.buf_operand in
    (* Store Error(string) selector at buf: 0x08c379a0 *)
    let selector = 0x08c379a0w : bytes32 in
    let (_, st3) = emit_void MSTORE [buf_op; Lit selector] st2 in
    (* Payload starts at buf + 32 *)
    let (payload_buf, st4) = emit_op ADD [buf_op; Lit 32w] st3 in
    (* Store message pointer into a tuple buffer (single-element tuple) *)
    let (tuple_buf_alloc, st5) = compile_alloc_buffer msg_mem_size st4 in
    let tuple_buf = tuple_buf_alloc.buf_operand in
    let (_, st6) = compile_copy_memory tuple_buf msg_op msg_mem_size st5 in
    (* ABI encode the wrapped tuple to payload buffer *)
    let (encoded_len, st7) =
      compile_abi_encode_to_buf payload_buf tuple_buf wrapped_enc_info st6 in
    (* Revert from buf+28 (selector at bytes 0-3) with length 4 + encoded_len *)
    let (revert_offset, st8) = emit_op ADD [buf_op; Lit 28w] st7 in
    let (revert_len, st9) = emit_op ADD [Lit 4w; encoded_len] st8 in
    emit_inst REVERT [revert_offset; revert_len] [] st9
End

(* ===== Internal Return ===== *)
(* Lower internal function return: load values and pass via RET.
   Mirrors Python: stmt.py _lower_internal_return
   returns_count: number of stack-returned values.
   return_pc: operand holding the return address.
   return_buf: SOME ptr for memory return, NONE otherwise. *)
(* ===== Load Tuple Elements for Stack Return ===== *)
(* Load n elements from a memory pointer, each at 32-byte intervals.
   Returns list of loaded operands.
   Mirrors Python: stmt.py _lower_internal_return tuple case *)
(* Load tuple elements from memory. Returns list of operands.
   Uses type_memory_bytes per element for proper stride.
   For word types: MLOAD the value.
   For complex types: computes pointer (base + offset).
   Python: offset += elem_typ.memory_bytes_required per element.
   NOTE: returns_stack_count guarantees ≤ MAX_STACK_RETURNS and all word,
   so for stack-returned tuples all elements are word-type. Complex elements
   always use memory return (returns_count = 0). *)
Definition compile_load_tuple_elements_def:
  compile_load_tuple_elements cenv base_op [] offset st = ([], st) ∧
  compile_load_tuple_elements cenv base_op (ty :: tys) offset st =
    let (elem_ptr, st1) =
      if offset = 0 then (base_op, st)
      else emit_op ADD [base_op; Lit (n2w offset)] st in
    let elem_size = type_memory_bytes cenv ty in
    let (val_op, st2) = emit_op MLOAD [elem_ptr] st1 in
    let (rest, st3) = compile_load_tuple_elements cenv base_op tys
                        (offset + elem_size) st2 in
    (val_op :: rest, st3)
End

Definition compile_internal_return_def:
  compile_internal_return cenv ret_val return_pc returns_count
                          ret_type src_type elem_types return_buf st =
    if returns_count > 0 then
      (* Stack return: pass ret_val(s) on stack *)
      case ret_val of
        NONE => emit_inst RET [return_pc] [] st
      | SOME val_op =>
          if returns_count = 1 then
            (* Single value: RET val, return_pc *)
            emit_inst RET [val_op; return_pc] [] st
          else
            (* Tuple/struct: load each element from memory, pass all on stack.
               NOTE: returns_count > 1 only for TupleT with all word types
               (from returns_stack_count), so all elements are 32 bytes. *)
            let (elems, st1) = compile_load_tuple_elements cenv val_op
                                 elem_types 0 st in
            emit_inst RET (elems ++ [return_pc]) [] st1
    else
      case return_buf of
        SOME buf_op =>
          (case ret_val of
             NONE => emit_inst RET [return_pc] [] st
           | SOME val_op =>
               (* Memory return: layout-aware copy to caller's buffer.
                  Uses compile_store_memory_typed to handle type
                  mismatch between source and declared return type.
                  Mirrors Python: ctx.store_memory(ret_val, return_buffer,
                    ret_typ, src_typ=ret_src_typ) *)
               let (_, st1) =
                 compile_store_memory_typed cenv buf_op ret_type
                                            val_op src_type st in
               emit_inst RET [return_pc] [] st1)
      | NONE =>
          emit_inst RET [return_pc] [] st
End

(* ===== External Return ===== *)
(* Lower external function return with ABI encoding.
   Mirrors Python: stmt.py _lower_external_return *)
Definition compile_external_return_def:
  compile_external_return ret_val is_prim_word is_raw_return
                          (ret_enc_info:abi_enc_info)
                          max_return_size is_nonreentrant nkey use_transient is_view st =
    (* Nonreentrant unlock (view functions skip) *)
    let (_, st1) =
      if is_nonreentrant then compile_nonreentrant_unlock nkey use_transient is_view st
      else ((), st) in
    case ret_val of
      NONE => emit_inst STOP [] [] st1
    | SOME val_op =>
        if is_raw_return then
          (* Raw return: val is ptr to [length][data] *)
          let (return_len, st2) = emit_op MLOAD [val_op] st1 in
          let (return_offset, st3) = emit_op ADD [val_op; Lit 32w] st2 in
          emit_inst RETURN [return_offset; return_len] [] st3
        else if is_prim_word then
          (* Primitive word: direct mstore + return 32 bytes *)
                    let (buf_op_alloc, st3) = compile_alloc_buffer 32 st1 in
                    let buf_op = buf_op_alloc.buf_operand in
          let (_, st4) = emit_void MSTORE [buf_op; val_op] st3 in
          emit_inst RETURN [buf_op; Lit 32w] [] st4
        else
          (* Complex: ABI encode to buffer, RETURN encoded_len bytes.
             Mirrors Python: stmt.py lower_Return → context.py _return_external
             Uses compile_abi_encode_to_buf for proper ABI encoding. *)
                    let (buf_op_alloc, st3) = compile_alloc_buffer max_return_size st1 in
                    let buf_op = buf_op_alloc.buf_operand in
          let (encoded_len, st4) =
            compile_abi_encode_to_buf buf_op val_op ret_enc_info st3 in
          emit_inst RETURN [buf_op; encoded_len] [] st4
End

(* ===== Get Target Ptr ===== *)
(* Full target pointer dispatch for assignments.
   Mirrors Python: stmt.py _get_target_ptr
   Returns (operand, data_location option, type option).
   The type is threaded through for nested access (SubscriptTarget,
   AttributeTarget) to correctly resolve element/field types. *)
Definition compile_get_target_ptr_def:
  (* Name target: local variable in memory *)
  compile_get_target_ptr cenv (NameTarget id) st =
    (case FLOOKUP cenv.ce_vars id of
       SOME (MemLoc offset _) =>
         ((Lit (n2w offset), SOME LocMemory, cenv.ce_var_type id), st)
     | SOME (PtrVar ptr_op _) =>
         ((ptr_op, SOME LocMemory, cenv.ce_var_type id), st)
     | SOME (ImmutableLoc offset) =>
         ((Lit (n2w offset), SOME LocCode, cenv.ce_var_type id), st)
     | _ => ((Lit 0w, NONE, NONE), st)) ∧
  (* BareGlobalName: immutable in constructor *)
  compile_get_target_ptr cenv (BareGlobalNameTarget id) st =
    (case FLOOKUP cenv.ce_vars id of
       SOME (ImmutableLoc offset) =>
         ((Lit (n2w offset), SOME LocCode, cenv.ce_var_type id), st)
     | _ => ((Lit 0w, NONE, NONE), st)) ∧
  (* TopLevelName: storage or transient variable *)
  compile_get_target_ptr cenv (TopLevelNameTarget nsid) st =
    (let name = nsid_to_string nsid in
     case FLOOKUP cenv.ce_vars name of
       SOME (StorageLoc slot) =>
         ((Lit slot, SOME LocStorage, cenv.ce_var_type name), st)
     | SOME (TransientLoc slot) =>
         ((Lit slot, SOME LocTransient, cenv.ce_var_type name), st)
     | _ => ((Lit 0w, NONE, NONE), st)) ∧
  (* Subscript target: compute element pointer from base + index.
     Uses compile_array_subscript for location-aware access.
     Mirrors Python: _get_target_ptr → Expr(target).lower().ptr()
     Uses base_type from recursive call instead of root variable lookup. *)
  compile_get_target_ptr cenv (SubscriptTarget bt idx_e) st =
    (let var_name = target_to_string bt in
     (* HashMap dispatch: uses compile_mapping_subscript for keccak256 slot.
        Mirrors Python: Expr(target, self.ctx).lower().ptr() which goes
        through compile_subscript → isinstance(base_typ, HashMapT).
        Must check BEFORE the array subscript path.
        For nested hashmaps (map[k1][k2]):
        - Recursively evaluate base target to get intermediate slot
        - Then keccak256(intermediate_slot || key) for outer subscript *)
     if cenv.ce_is_hashmap var_name then
       let (key_op, st1) = lower_value compile_expr cenv (BaseT (UintT 256)) idx_e st in
       (* Get base slot: for NameTarget, direct lookup.
          For SubscriptTarget (nested hashmap), recurse to get intermediate slot. *)
       let (base_slot, st2) =
         (case bt of
            NameTarget _ =>
              (case FLOOKUP cenv.ce_vars var_name of
                 SOME (StorageLoc slot) => (Lit slot, st1)
               | _ => (Lit 0w, st1))
          | _ =>
              let ((base_op, _, _), st_r) =
                compile_get_target_ptr cenv bt st1 in
              (base_op, st_r)) in
       let (slot_op, st3) = compile_mapping_subscript base_slot key_op st2 in
       (* HashMap values are always in storage.
          TODO: Value type not tracked — returns NONE for type. *)
       ((slot_op, SOME LocStorage, NONE), st3)
     else
     let ((base_op, loc_opt, base_type_opt), st1) =
           compile_get_target_ptr cenv bt st in
     let (idx_op, st2) = lower_value compile_expr cenv (BaseT (UintT 256)) idx_e st1 in
     let loc = (case loc_opt of SOME l => l | NONE => LocMemory) in
     let is_dynamic = (case base_type_opt of
                         SOME (ArrayT _ (Dynamic _)) => T
                       | _ => F) in
     let elem_ty = (case base_type_opt of
                      SOME (ArrayT t _) => t
                    | _ => BaseT (UintT 256)) in
     let ws = word_scale loc in
     let elem_size = elem_size_in_location cenv loc elem_ty in
     let static_count = (case base_type_opt of
                           SOME (ArrayT _ (Fixed n)) => n
                         | _ => 0) in
     let is_signed_idx = is_signed_type (expr_type idx_e) in
     let load_opc = (case loc of
                       LocStorage => SLOAD
                     | LocTransient => TLOAD
                     | _ => MLOAD) in
     let (elem_ptr, st3) =
       compile_array_subscript base_op idx_op is_dynamic static_count
                               ws elem_size is_signed_idx load_opc st2 in
     ((elem_ptr, loc_opt, SOME elem_ty), st3)) ∧
  (* Attribute target: add struct field offset to base.
     Mirrors Python: _get_target_ptr for struct.field
     Uses base_type from recursive call to resolve struct name. *)
  compile_get_target_ptr cenv (AttributeTarget bt field) st =
    (let ((base_op, loc_opt, base_type_opt), st1) =
           compile_get_target_ptr cenv bt st in
     let struct_name = (case base_type_opt of
                          SOME (StructT sn) => sn
                        | _ => "") in
     let fields = cenv.ce_struct_fields struct_name in
     let is_storage = (case loc_opt of
                         SOME LocStorage => T
                       | SOME LocTransient => T
                       | _ => F) in
     let field_offset =
       if is_storage then struct_field_offset_slots fields field
       else struct_field_offset fields field in
     let field_type = (case ALOOKUP fields field of
                         SOME (fty, _) => SOME fty | NONE => NONE) in
     if field_offset = 0 then ((base_op, loc_opt, field_type), st1)
     else
       let (ptr, st2) = emit_op ADD [base_op; Lit (n2w field_offset)] st1 in
       ((ptr, loc_opt, field_type), st2))
End

(* ===== Assign Value ===== *)
(* Dispatch assign by location and type.

   Mirrors Python: stmt.py _assign_value *)
(* Store value to target with location-aware dispatch.
   For memory-to-memory complex types, stages through temp buffer for
   overlap safety. Skips staging when source was not originally in memory
   (e.g., materialized from storage → fresh buffer, no aliasing possible).
   Mirrors Python: stmt.py _assign_value + _copy_complex_type
   NOTE: val_op is assumed to be a memory pointer for complex types.
   Callers use lower_value (unwrap_value handles materialization). *)
(* src_loc: source data_location option (for staging decision).
   SOME LocMemory means source is in memory → may alias destination.
   NONE means stack/computed value → no aliasing possible.
   Mirrors Python: src_vv.location (None for stack, DataLocation.X for located).
   dynarray_info: NONE for non-dynarray types, SOME (elem_words, elem_mem_size) for DynArray.
   When SOME, uses dynarray_to_storage (copies only length + actual elems).
   When NONE, uses bulk word copy (copies all words).
   Mirrors Python: context.py dispatch on isinstance(typ, DArrayT) *)
Definition compile_assign_value_def:
  compile_assign_value cenv dst_op dst_loc val_op is_prim_word
                       (src_loc : data_location option)
                       (dst_ty : type) (src_ty : type)
                       (dynarray_info : (num # num) option) mem_size st =
    case dst_loc of
      LocMemory =>
        if is_prim_word then emit_void MSTORE [dst_op; val_op] st
        else if src_loc = SOME LocMemory then
          (* Both memory: stage through temp buffer for overlap safety.
             Python: flat copy src→tmp (preserving src layout), then
             typed copy tmp→dst (converting layout if needed).
             Mirrors Python: stmt.py _copy_complex_type + _store_complex_type *)
          let src_mem_size = type_memory_bytes cenv src_ty in
          let (tmp_op_alloc, st2) = compile_alloc_buffer src_mem_size st in
          let tmp_op = tmp_op_alloc.buf_operand in
          (* Step 1: flat copy src→tmp (preserving src layout) *)
          let (_, st3) = compile_copy_memory tmp_op val_op src_mem_size st2 in
          (* Step 2: typed copy or flat copy tmp→dst *)
          if dst_ty ≠ src_ty then
            compile_store_memory_typed cenv dst_op dst_ty tmp_op src_ty st3
          else
            compile_copy_memory dst_op tmp_op mem_size st3
        else if dst_ty ≠ src_ty then
          (* Different layouts: use typed copy (no staging needed — src is
             from a fresh buffer or non-memory source).
             Mirrors Python: context.py store_memory src_typ != typ *)
          compile_store_memory_typed cenv dst_op dst_ty val_op src_ty st
        else
          (* Same layout, non-aliasing → flat copy *)
          compile_copy_memory dst_op val_op mem_size st
    | LocStorage =>
        (* Normalize source layout when types differ (non-bytestring).
           Storage/transient only understand destination layout, so convert
           src→dst layout in memory first.
           Mirrors Python: stmt.py _store_complex_type normalization *)
        let (val_op', st') =
          if ¬is_prim_word ∧ dst_ty ≠ src_ty
             ∧ ¬(is_bytestring_type dst_ty ∧ is_bytestring_type src_ty) then
            let (norm_alloc, st1) = compile_alloc_buffer mem_size st in
            let (_, st2) = compile_store_memory_typed cenv
                             norm_alloc.buf_operand dst_ty val_op src_ty st1 in
            (norm_alloc.buf_operand, st2)
          else (val_op, st) in
        if is_prim_word then emit_void SSTORE [dst_op; val_op'] st'
        else
          (case dynarray_info of
             SOME (ew, ems) =>
               (* DynArray→storage: copy only length + actual elements.
                  Mirrors Python: context.py _copy_dynarray_to_storage *)
               compile_dynarray_to_storage val_op' dst_op ew ems F st'
           | NONE =>
             if mem_size ≤ 32 then
               let (loaded, st1) = emit_op MLOAD [val_op'] st' in
               emit_void SSTORE [dst_op; loaded] st1
             else
               let (_, st1) = compile_memory_to_storage val_op' dst_op
                                                        (mem_size DIV 32) st' in
               ((), st1))
    | LocTransient =>
        let (val_op', st') =
          if ¬is_prim_word ∧ dst_ty ≠ src_ty
             ∧ ¬(is_bytestring_type dst_ty ∧ is_bytestring_type src_ty) then
            let (norm_alloc, st1) = compile_alloc_buffer mem_size st in
            let (_, st2) = compile_store_memory_typed cenv
                             norm_alloc.buf_operand dst_ty val_op src_ty st1 in
            (norm_alloc.buf_operand, st2)
          else (val_op, st) in
        if is_prim_word then emit_void TSTORE [dst_op; val_op'] st'
        else
          (case dynarray_info of
             SOME (ew, ems) =>
               compile_dynarray_to_storage val_op' dst_op ew ems T st'
           | NONE =>
             if mem_size ≤ 32 then
               let (loaded, st1) = emit_op MLOAD [val_op'] st' in
               emit_void TSTORE [dst_op; loaded] st1
             else
               let (_, st1) = compile_memory_to_transient val_op' dst_op
                                                          (mem_size DIV 32) st' in
               ((), st1))
    | LocCode =>
        if is_prim_word then emit_void ISTORE [dst_op; val_op] st
        else if mem_size ≤ 32 then
          let (loaded, st1) = emit_op MLOAD [val_op] st in
          emit_void ISTORE [dst_op; loaded] st1
        else
          let (_, st1) = compile_word_copy_loop val_op dst_op
                           (mem_size DIV 32) LocMemory LocCode T st in
          ((), st1)
    | LocCalldata =>
        (* Calldata is read-only — store is invalid *)
        let (_, st') = emit_inst INVALID [] [] st in ((), st')
End

(* ===== Tuple unpack: two-pass for overlap safety ===== *)
(* Pass 1: load all elements from source.
   For word types: MLOAD the value.
   For complex types: compute pointer to element (base + offset).
   Uses type_memory_bytes per element for proper stride.
   Mirrors Python: stmt.py _lower_tuple_unpack pass 1 *)
Definition compile_tuple_load_all_def:
  compile_tuple_load_all cenv src_op [] offset st = ([], st) ∧
  compile_tuple_load_all cenv src_op (ty :: tys) offset st =
    let mem_size = type_memory_bytes cenv ty in
    let (src_elem, st0) =
      if offset = 0 then (src_op, st)
      else emit_op ADD [src_op; Lit (n2w offset)] st in
    let (elem_op, st1) =
      if is_word_type ty then emit_op MLOAD [src_elem] st0
      else (src_elem, st0) in  (* complex: return pointer *)
    let (rest_ops, st2) = compile_tuple_load_all cenv src_op tys
                            (offset + mem_size) st1 in
    (elem_op :: rest_ops, st2)
End

(* Store a single value to a target at a given location.
   Dispatches store opcode based on location.
   Mirrors Python: ctx.ptr_store dispatching by location. *)
Definition compile_store_at_loc_def:
  compile_store_at_loc dst_op val_op NONE st =
    emit_void MSTORE [dst_op; val_op] st ∧
  compile_store_at_loc dst_op val_op (SOME LocMemory) st =
    emit_void MSTORE [dst_op; val_op] st ∧
  compile_store_at_loc dst_op val_op (SOME LocStorage) st =
    emit_void SSTORE [dst_op; val_op] st ∧
  compile_store_at_loc dst_op val_op (SOME LocTransient) st =
    emit_void TSTORE [dst_op; val_op] st ∧
  compile_store_at_loc dst_op val_op (SOME LocCode) st =
    (* Code location: use ISTORE for immutables in constructor context *)
    emit_void ISTORE [dst_op; val_op] st ∧
  compile_store_at_loc dst_op val_op (SOME LocCalldata) st =
    (* Calldata is read-only — emit INVALID *)
    emit_void INVALID [] st
End

(* Pass 2: store loaded values to targets.
   Uses compile_get_target_ptr for full target support (storage, subscript, etc.).
   Dispatches by element type: word types use compile_store_at_loc (single store),
   complex types use compile_assign_value (multi-word location-aware copy).
   Mirrors Python: stmt.py _lower_tuple_unpack pass 2 *)
(* Store unpacked tuple elements to targets.
   src_tys: types from the RHS tuple (source element types).
   Each target may have a different declared type (dst_ty from get_target_ptr).
   Tuple elements are memory pointers → src_loc = SOME LocMemory.
   Mirrors Python: stmt.py _lower_tuple_unpack pass 2 *)
Definition compile_tuple_store_all_def:
  compile_tuple_store_all cenv [] [] [] st = ((), st) ∧
  compile_tuple_store_all cenv (src_ty :: src_tys) (BaseTarget bt :: targets) (val_op :: vals) st =
    (let ((dst_op, loc_opt, dst_ty_opt), st1) = compile_get_target_ptr cenv bt st in
     let dst_loc = (case loc_opt of SOME l => l | NONE => LocMemory) in
     (* dst_ty from target, falls back to src_ty if unknown *)
     let dst_ty = (case dst_ty_opt of SOME t => t | NONE => src_ty) in
     let is_prim = is_word_type dst_ty in
     let mem_sz = type_memory_bytes cenv dst_ty in
     (* Tuple elements: prim values are stack (src_loc=NONE), complex
        pointers are into the already-staged buffer (src_loc=NONE to skip
        re-staging in compile_assign_value, since the entire source tuple
        is already staged). Mirrors Python pass 2 which calls
        _store_complex_type directly (no staging wrapper). *)
     let (_, st2) = compile_assign_value cenv dst_op dst_loc val_op is_prim
                      NONE dst_ty src_ty NONE mem_sz st1 in
     compile_tuple_store_all cenv src_tys targets vals st2) ∧
  (* Non-BaseTarget element: emit INVALID (shouldn't occur in valid AST) *)
  compile_tuple_store_all cenv (_ :: tys) (_ :: targets) (_ :: vals) st =
    (let (_, st1) = emit_void INVALID [] st in
     compile_tuple_store_all cenv tys targets vals st1) ∧
  compile_tuple_store_all cenv _ _ _ st = ((), st)
End

(* Two-pass tuple unpack: load ALL values first, then store ALL.
   This ensures a, b = b, a works correctly (no aliasing issues).
   When any member is complex (!is_word_type), stage entire source
   tuple to temp buffer first to prevent aliasing corruption.
   Mirrors Python: stmt.py _lower_tuple_unpack *)
Definition compile_tuple_unpack_def:
  compile_tuple_unpack cenv ty targets src_op st =
    let elem_types = (case ty of
        TupleT tys => tys
      | StructT name =>
          MAP (FST o SND) (cenv.ce_struct_fields name)
      | _ => REPLICATE (LENGTH targets) (BaseT (UintT 256))) in
    (* Stage source tuple to prevent aliasing when complex members present.
       Python stages when source_is_memory_view ∧ any(!_is_prim_word).
       We always stage when complex members exist (conservative but correct). *)
    let has_complex = EXISTS (λt. ¬is_word_type t) elem_types in
    let total_mem = SUM (MAP (type_memory_bytes cenv) elem_types) in
    let (staged_op, st0) =
      if has_complex ∧ total_mem > 0 then
        let (staged_buf, st_s) = compile_alloc_buffer total_mem st in
        let staged_ptr = staged_buf.buf_operand in
        let (_, st_s2) = emit_void MCOPY [staged_ptr; src_op;
                                          Lit (n2w total_mem)] st_s in
        (staged_ptr, st_s2)
      else (src_op, st) in
    let (vals, st1) = compile_tuple_load_all cenv staged_op elem_types 0 st0 in
    compile_tuple_store_all cenv elem_types targets vals st1
End

(* ===== Range Loop Bound Checks ===== *)
(* Emit bound checks for dynamic range loops.
   For signed types: assert start <= end using SGT.
   For unsigned: assert start <= end using GT.
   Also assert rounds <= rounds_bound.
   Mirrors Python: stmt.py _lower_range_loop bound checks *)
Definition compile_range_bound_checks_def:
  compile_range_bound_checks start_op end_op rounds_op rounds_bound
                             is_signed st =
    (* Check start <= end *)
    let (invalid_order, st1) =
      if is_signed then emit_op SGT [start_op; end_op] st
      else emit_op GT [start_op; end_op] st in
    let (valid_order, st2) = emit_op ISZERO [invalid_order] st1 in
    let (_, st3) = emit_void ASSERT [valid_order] st2 in
    (* Check rounds <= rounds_bound *)
    let (invalid_rounds, st4) = emit_op GT [rounds_op;
                                            Lit (n2w rounds_bound)] st3 in
    let (valid_rounds, st5) = emit_op ISZERO [invalid_rounds] st4 in
    emit_void ASSERT [valid_rounds] st5
End

(* ===== Iter Loop Element Copy ===== *)
(* Copy element from array to loop variable, location-aware.
   For memory: single mload/mcopy depending on size.
   For storage/transient: sload/tload for single slot, multi-slot loop.
   loc: source data_location (LocMemory, LocStorage, LocTransient, etc.)
   Mirrors Python: stmt.py _lower_iter_loop body element copy *)
(* Copy one for-loop element from source to loop variable (in memory).
   Dispatches by source location and element type.

   For memory complex types with type mismatch: uses compile_store_memory_typed
   for layout-aware copy (e.g., DynArray[Bytes[540]] → Bytes[704]).
   For memory bytestrings: uses compile_store_bytestring for runtime-length copy.
   For calldata/code >32B: uses CALLDATACOPY/CODECOPY (not MCOPY).

   Mirrors Python: stmt.py _lower_iter_loop element copy dispatch *)
Definition compile_iter_elem_copy_def:
  compile_iter_elem_copy cenv elem_ptr item_ptr elem_size
                         loc is_slot_addressed
                         (target_ty : type) (elem_ty : type) st =
    if is_slot_addressed then
      if elem_size = 1 then
        (* Single slot: load from storage/transient, mstore to memory *)
        let load_opc = case loc of LocStorage => SLOAD
                                 | LocTransient => TLOAD
                                 | LocCode => DLOAD
                                 | _ => MLOAD in
        let (val_op, st1) = emit_op load_opc [elem_ptr] st in
        emit_void MSTORE [item_ptr; val_op] st1
      else
        (* Multi-slot: use compile_slot_to_memory from contextScript *)
        let (_, st1) = compile_slot_to_memory elem_ptr item_ptr elem_size loc st in
        ((), st1)
    else if loc ≠ LocMemory then
      (* Non-memory, byte-addressed: calldata/code/immutables.
         For ≤32B, single load+mstore. For >32B, location-specific bulk copy.
         Mirrors Python: self.ctx.copy_to_memory(dst, elem_addr, elem_size, location) *)
      if elem_size ≤ 32 then
        let load_opc = case loc of
                          LocCalldata => CALLDATALOAD
                        | LocCode => DLOAD
                        | _ => MLOAD in
        let (val_op, st1) = emit_op load_opc [elem_ptr] st in
        emit_void MSTORE [item_ptr; val_op] st1
      else
        (case loc of
           LocCalldata =>
             emit_void CALLDATACOPY [item_ptr; elem_ptr; Lit (n2w elem_size)] st
         | LocCode =>
             emit_void CODECOPY [item_ptr; elem_ptr; Lit (n2w elem_size)] st
         | _ =>
             compile_copy_memory item_ptr elem_ptr elem_size st)
    else if is_word_type target_ty then
      (* Memory, primitive word: mload + mstore *)
      let (val_op, st1) = emit_op MLOAD [elem_ptr] st in
      emit_void MSTORE [item_ptr; val_op] st1
    else if target_ty ≠ elem_ty then
      (* Memory, complex, type mismatch: layout-aware copy.
         Handles cases like DynArray[Bytes[540]] → Bytes[704].
         Mirrors Python: self.ctx.store_memory(elem_addr, dst, target_type,
                          src_typ=array_typ.value_type) *)
      compile_store_memory_typed cenv item_ptr target_ty elem_ptr elem_ty st
    else if is_bytestring_type target_ty then
      (* Memory, bytestring, same type: copy actual runtime length.
         Mirrors Python: store_memory → _BytestringT branch *)
      compile_store_bytestring elem_ptr item_ptr st
    else
      (* Memory, complex, same type: flat copy *)
      compile_copy_memory item_ptr elem_ptr elem_size st
End

(* infer_array_location, infer_array_is_dynamic defined in exprLoweringScript.
   type_memory_bytes, elem_size_in_location, is_bytestring_type in compileEnvScript.
   (shared between compile_expr, for-iter loops, and typed copy) *)

(* NOTE: is_word_type deleted — unified with is_word_type in compileEnv *)

Definition compile_stmt_def:
  (* Pass: no-op *)
  compile_stmt cenv lctx ty (Pass : stmt) st = ((), st) ∧

  (* Expression statement: compile for side effects, discard result.
     Use expr_type e, not function return type ty. *)
  compile_stmt cenv lctx ty (Expr e) st =
    (let (_, st1) = compile_expr cenv (expr_type e) e st in ((), st1)) ∧

  (* AnnAssign: variable declaration with initialization.
     Variable is already in ce_vars (alloca pre-allocated).
     Dispatches to compile_assign_value for proper complex type handling.
     dst_ty = vtyp (declared type), src_ty = expr_type e (expression type).
     These may differ for subtype assignments (e.g. Bytes[540] → Bytes[704]).
     Mirrors Python: stmt.py lower_AnnAssign → _assign_value *)
  compile_stmt cenv lctx ty (AnnAssign id vtyp e) st =
    (let src_ty = expr_type e in
     let ((val_op, src_loc), st1) = lower_value_with_loc compile_expr cenv vtyp e st in
     case FLOOKUP cenv.ce_vars id of
       SOME (MemLoc offset _) =>
         let is_prim = is_word_type vtyp in
         let mem_size = type_memory_bytes cenv vtyp in
         let da_info = (case vtyp of
            ArrayT elem_ty (Dynamic _) =>
              let ems = type_memory_bytes cenv elem_ty in
              SOME ((ems + 31) DIV 32, ems)
          | _ => NONE) in
         compile_assign_value cenv (Lit (n2w offset)) LocMemory val_op
                              is_prim src_loc vtyp src_ty da_info mem_size st1
     | _ => ((), st1)) ∧

  (* Assign: store to target (memory, storage, transient, code).
     RHS evaluated before LHS target (matches Python eval order).
     dst_ty from compile_get_target_ptr (target's declared type),
     src_ty from expr_type e (expression's type). These may differ
     for subtype assignments (e.g., DynArray[Bytes[540]] → DynArray[Bytes[704]]).
     Mirrors Python: stmt.py lower_Assign with _assign_value *)
  compile_stmt cenv lctx ty (Assign (BaseTarget bt) e) st =
    (let src_ty = expr_type e in
     let ((val_op, src_loc), st1) = lower_value_with_loc compile_expr cenv src_ty e st in
     let ((dst_op, dst_loc_opt, dst_ty_opt), st2) = compile_get_target_ptr cenv bt st1 in
     (* dst_ty: target's declared type. Falls back to src_ty if unknown. *)
     let dst_ty = (case dst_ty_opt of SOME t => t | NONE => src_ty) in
     let is_prim = is_word_type dst_ty in
     let mem_size = type_memory_bytes cenv dst_ty in
     let da_info = (case dst_ty of
        ArrayT elem_ty (Dynamic _) =>
          let ems = type_memory_bytes cenv elem_ty in
          SOME ((ems + 31) DIV 32, ems)
      | _ => NONE) in
     case dst_loc_opt of
       SOME loc => compile_assign_value cenv dst_op loc val_op is_prim
                    src_loc dst_ty src_ty da_info mem_size st2
     | NONE => ((), st2)) ∧

  (* AugAssign: load + binop + store.
     Handles memory, storage, transient targets.
     Mirrors Python: stmt.py lower_AugAssign *)
  compile_stmt cenv lctx ty (AugAssign target_ty bt bop e) st =
    (let ((dst_op, dst_loc_opt, _), st1) = compile_get_target_ptr cenv bt st in
     (* Python order: get_target → load current → eval RHS → binop → store *)
     let load_opc = (case dst_loc_opt of
                       SOME LocStorage => SLOAD
                     | SOME LocTransient => TLOAD
                     | _ => MLOAD) in
     let store_opc = (case dst_loc_opt of
                        SOME LocStorage => SSTORE
                      | SOME LocTransient => TSTORE
                      | _ => MSTORE) in
     let (cur_op, st2) = emit_op load_opc [dst_op] st1 in
     let (rhs_op, st3) = lower_value compile_expr cenv target_ty e st2 in
     let (res_op, st4) = compile_binop bop cur_op rhs_op target_ty st3 in
     emit_void store_opc [dst_op; res_op] st4) ∧

  (* Assert: evaluate condition, handle failure.
     Three cases: bare assert, UNREACHABLE, or with reason string.
     Mirrors Python: stmt.py lower_Assert, _assert_with_reason *)
  compile_stmt cenv lctx ty (Assert cond_e AssertBare) st =
    (* Bare assert: revert 0,0 on failure *)
    (let (cond_op, st1) = lower_value compile_expr cenv (BaseT BoolT) cond_e st in
     let (ok_lbl, st2) = fresh_label "assert_ok" st1 in
     let (fail_lbl, st3) = fresh_label "assert_fail" st2 in
     let (_, st4) = emit_inst JNZ [cond_op; Label ok_lbl; Label fail_lbl] [] st3 in
     let (_, st5) = new_block fail_lbl st4 in
     let (_, st6) = emit_inst REVERT [Lit 0w; Lit 0w] [] st5 in
     let (_, st7) = new_block ok_lbl st6 in
     ((), st7)) ∧
  compile_stmt cenv lctx ty (Assert cond_e AssertUnreachable) st =
    (* UNREACHABLE: INVALID opcode on failure *)
    (let (cond_op, st1) = lower_value compile_expr cenv (BaseT BoolT) cond_e st in
     let (ok_lbl, st2) = fresh_label "assert_ok" st1 in
     let (fail_lbl, st3) = fresh_label "assert_fail" st2 in
     let (_, st4) = emit_inst JNZ [cond_op; Label ok_lbl; Label fail_lbl] [] st3 in
     let (_, st5) = new_block fail_lbl st4 in
     let (_, st6) = emit_inst INVALID [] [] st5 in
     let (_, st7) = new_block ok_lbl st6 in
     ((), st7)) ∧
  compile_stmt cenv lctx ty (Assert cond_e (AssertReason reason_e)) st =
    (* Assert with reason: compile reason, encode Error(string), revert *)
    (let (cond_op, st1) = lower_value compile_expr cenv (BaseT BoolT) cond_e st in
     let (ok_lbl, st2) = fresh_label "assert_ok" st1 in
     let (fail_lbl, st3) = fresh_label "assert_fail" st2 in
     let (_, st4) = emit_inst JNZ [cond_op; Label ok_lbl; Label fail_lbl] [] st3 in
     let (_, st5) = new_block fail_lbl st4 in
     let reason_ty = expr_type reason_e in
     let msg_mem_size = type_memory_bytes cenv reason_ty in
     let (msg_op, st6) = lower_value compile_expr cenv reason_ty reason_e st5 in
     let (_, st7) = compile_revert_with_reason cenv msg_op reason_ty msg_mem_size st6 in
     let (_, st8) = new_block ok_lbl st7 in
     ((), st8)) ∧

  (* Log: event emission with indexed topics + ABI-encoded data.
     Mirrors Python: stmt.py lower_Log.
     CRITICAL: evaluate ALL args in AST order first (for side-effect ordering),
     then split into indexed (topics) and non-indexed (data).
     1. Evaluate all args in AST order
     2. Split evaluated ops into topics and data
     3. Hash bytestring topics
     4. Store data to buffer, ABI-encode
     5. Emit LOG *)
  compile_stmt cenv lctx ty (Log event_id args) st =
    (let event_name = nsid_to_string event_id in
     let (event_hash, indexed_flags, topic_bs_flags) =
       cenv.ce_event_info event_name in
     let (eval_ops, st1) = compile_log_eval_all cenv args st in
     let (raw_topics, data_ops) = split_log_ops eval_ops indexed_flags in
     let (topic_ops, st2) = compile_log_topic_ops raw_topics st1 in
     let all_topics = Lit (n2w event_hash) :: topic_ops in
     let n_topics = LENGTH all_topics in
     if NULL data_ops then
       emit_inst (LOG : opcode)
         (Lit (n2w n_topics) :: Lit 0w :: Lit 0w :: all_topics) [] st2
     else
       let data_types = MAP SND data_ops in
       let data_tuple_t = TupleT data_types in
       let data_mem_size = SUM (MAP (type_memory_bytes cenv) data_types) in
              let (data_buf_alloc, st3) = compile_alloc_buffer (MAX 32 data_mem_size) st2 in
              let data_buf = data_buf_alloc.buf_operand in
       let (_, st4) = compile_log_store_data cenv data_ops data_buf 0 st3 in
       let abi_size = abi_size_bound (cenv_sft cenv) data_tuple_t in
       let data_enc_info = type_to_abi_enc_info cenv data_tuple_t in
              let (abi_buf_alloc, st6) = compile_alloc_buffer (MAX 32 abi_size) st4 in
              let abi_buf = abi_buf_alloc.buf_operand in
       let (encoded_len, st7) =
         compile_abi_encode_to_buf abi_buf data_buf data_enc_info st6 in
       emit_inst (LOG : opcode)
         (Lit (n2w n_topics) :: abi_buf :: encoded_len :: all_topics) [] st7) ∧


  (* Raise: revert with optional reason.
     Mirrors Python: stmt.py lower_Raise
     Three cases: bare raise (revert 0,0), UNREACHABLE (INVALID),
     or with reason (Error(string) encoding). *)
  compile_stmt cenv lctx ty (Raise RaiseBare) st =
    emit_inst REVERT [Lit 0w; Lit 0w] [] st ∧
  compile_stmt cenv lctx ty (Raise RaiseUnreachable) st =
    emit_inst INVALID [] [] st ∧
  compile_stmt cenv lctx ty (Raise (RaiseReason reason_e)) st =
    (let reason_ty = expr_type reason_e in
     let msg_mem_size = type_memory_bytes cenv reason_ty in
     let (msg_op, st1) = lower_value compile_expr cenv reason_ty reason_e st in
     compile_revert_with_reason cenv msg_op reason_ty msg_mem_size st1) ∧

  (* Return NONE: emit STOP for external (with unlock), RET for internal.
     Mirrors Python: stmt.py lower_Return → _lower_external_return (unlocks first) *)
  compile_stmt cenv lctx ty (Return NONE) st =
    (case FLOOKUP cenv.ce_vars "__return_pc__" of
       SOME (MemLoc rpc_off _) =>
         (* Internal: ret to return_pc *)
         let (rpc, st1) = emit_op MLOAD [Lit (n2w rpc_off)] st in
         emit_inst RET [rpc] [] st1
     | _ =>
         (* External: nonreentrant unlock + STOP *)
         let (is_nonreentrant, nkey, use_transient, is_view) = cenv.ce_nonreentrant in
         let (_, st1) =
           if is_nonreentrant then compile_nonreentrant_unlock nkey use_transient is_view st
           else ((), st) in
         emit_inst STOP [] [] st1) ∧

  (* Return (SOME e): compile value, dispatch internal vs external.
     Mirrors Python: stmt.py lower_Return.
     Internal functions: uses compile_internal_return with returns_count from cenv.
     External functions: uses compile_external_return with ABI encoding. *)
  compile_stmt cenv lctx ty (Return (SOME e)) st =
    (let (val_op, st1) = lower_value compile_expr cenv ty e st in
     let is_prim = is_word_type ty in
     let mem_size = type_memory_bytes cenv ty in
     case FLOOKUP cenv.ce_vars "__return_pc__" of
       SOME (MemLoc rpc_off _) =>
         (* Internal return: dispatch via compile_internal_return.
            Handles single-value, tuple, and memory return paths. *)
         let (rpc, st2) = emit_op MLOAD [Lit (n2w rpc_off)] st1 in
         (* Load return buffer pointer from __return_buf__ local.
            The PARAM for the caller's buffer is stored there at function entry.
            compile_internal_return dispatches MCOPY for complex types. *)
         let (ret_buf, st2a) =
           (case FLOOKUP cenv.ce_vars "__return_buf__" of
              SOME (MemLoc rbuf_off _) =>
                let (buf_ptr, st_r) =
                  emit_op MLOAD [Lit (n2w rbuf_off)] st2
                in (SOME buf_ptr, st_r)
            | _ => (NONE, st2)) in
         (* elem_types: for tuple/struct returns, use element types.
            Python: hasattr(ret_typ, "tuple_items") matches TupleT + StructT.
            Mirrors Python: stmt.py _lower_internal_return *)
         let elem_types = (case ty of
             TupleT tys => tys
           | StructT name =>
               MAP (FST o SND) (cenv.ce_struct_fields name)
           | _ => []) in
         let src_ty = expr_type e in
         compile_internal_return cenv (SOME val_op) rpc
           cenv.ce_returns_count ty src_ty elem_types ret_buf st2a
     | _ =>
         (* External return: ABI encoding + nonreentrant unlock.
            Mirrors Python: stmt.py _lower_external_return which unlocks
            before encoding/returning.
            Normalize when ret_src_typ ≠ ret_typ for non-prim,
            non-bytestring-to-bytestring. Python lines 936-945. *)
         let is_prim = is_word_type ty in
         let src_ty = expr_type e in
         let needs_normalize =
           (¬is_prim ∧
            ¬(is_bytestring_type ty ∧ is_bytestring_type src_ty) ∧
            src_ty ≠ ty) in
         let (ret_op, st1a) =
           if needs_normalize then
             let norm_size = type_memory_bytes cenv ty in
             let (norm_buf, st_n) = compile_alloc_buffer norm_size st1 in
             let norm_ptr = norm_buf.buf_operand in
             let (_, st_n2) =
               compile_store_memory_typed cenv norm_ptr ty val_op src_ty st_n in
             (norm_ptr, st_n2)
           else (val_op, st1) in
         let (is_nonreentrant, nkey, use_transient, is_view) = cenv.ce_nonreentrant in
         compile_external_return (SOME ret_op) is_prim F
           cenv.ce_ret_enc_info cenv.ce_max_return_size
           is_nonreentrant nkey use_transient is_view st1a) ∧

  (* Append: dynarray append — location-aware.
     Delegates to compile_dynarray_append for correct opcode dispatch.
     Mirrors Python: expr.py _lower_dynarray_append *)
  compile_stmt cenv lctx ty (Append target val_e) st =
    (let target_op = compile_target_base cenv target in
     let target_name = target_to_string target in
     (* Use array element type, not threading ty.
        Python: elem_typ = darray_typ.value_type *)
     let elem_ty = (case cenv.ce_var_type target_name of
                      SOME (ArrayT t _) => t | _ => ty) in
     let (val_op, st1) = lower_value compile_expr cenv elem_ty val_e st in
     let is_prim = is_word_type elem_ty in
     (* Stage complex elements through temp buffer to guard against aliasing
        (e.g., arr.append(arr[0])). MemoryCopyElisionPass elides when safe.
        Mirrors Python: if not elem_typ._is_prim_word: stage through temp_buf *)
     let (staged_val, st1) =
       if is_prim then (val_op, st1)
       else
         let mem_sz = type_memory_bytes cenv elem_ty in
         let (tmp_alloc, st_t) = compile_alloc_buffer mem_sz st1 in
         let (_, st_t2) = compile_copy_memory tmp_alloc.buf_operand val_op
                            mem_sz st_t in
         (tmp_alloc.buf_operand, st_t2)
     in
     let capacity = cenv.ce_dynarray_capacity target_name in
     let loc = infer_array_location cenv (target_to_expr target) in
     let ws = word_scale loc in
     let elem_size = elem_size_in_location cenv loc elem_ty in
     let load_opc = load_opc_for loc in
     let store_opc = store_opc_for loc in
     let src_elem_ty = expr_type val_e in
     (* For storage/transient destination with type mismatch,
        normalize source layout to destination layout in memory first.
        Without this, word_copy_loop reads source-layout bytes into
        destination-layout storage slots, corrupting data.
        Mirrors Python: if data_loc in (STORAGE, TRANSIENT) and
        elem_src_typ != elem_typ: normalize through store_memory *)
     let (staged_val, src_elem_ty, st1) =
       if is_prim ∨ loc = LocMemory ∨ src_elem_ty = elem_ty then
         (staged_val, src_elem_ty, st1)
       else
         let norm_sz = type_memory_bytes cenv elem_ty in
         let (norm_alloc, st_n) = compile_alloc_buffer norm_sz st1 in
         let (_, st_n2) = compile_store_memory_typed cenv
                            norm_alloc.buf_operand elem_ty
                            staged_val src_elem_ty st_n in
         (norm_alloc.buf_operand, elem_ty, st_n2)
     in
     compile_dynarray_append cenv target_op staged_val ws elem_size
                                  elem_ty src_elem_ty
                                  capacity is_prim
                                  load_opc store_opc st1) ∧

  (* Assign with TupleTarget: tuple unpacking.
     Mirrors Python: stmt.py _lower_tuple_unpack
     First evaluate RHS, then assign each element to its target. *)
  compile_stmt cenv lctx ty (Assign (TupleTarget targets) e) st =
    (let (src_op, st1) = lower_value compile_expr cenv ty e st in
     compile_tuple_unpack cenv ty targets src_op st1) ∧

  (* If: multi-block control flow *)
  compile_stmt cenv lctx ty (If cond_e then_body else_body) st =
    (let (cond_op, st1) = lower_value compile_expr cenv (BaseT BoolT) cond_e st in
     let (then_lbl, st2) = fresh_label "then" st1 in
     let (else_lbl, st3) = fresh_label "else" st2 in
     let (exit_lbl, st4) = fresh_label "if_exit" st3 in
     let (_, st5) = emit_inst JNZ [cond_op; Label then_lbl; Label else_lbl] [] st4 in
     (* Then branch — only JMP to exit if not already terminated (e.g. by Return) *)
     let (_, st6) = new_block then_lbl st5 in
     let (_, st7) = compile_stmts cenv lctx ty then_body st6 in
     let then_terminated = block_is_terminated st7 in
     let (_, st8) = emit_jmp_if_not_terminated exit_lbl st7 in
     (* Else branch — same terminator check *)
     let (_, st9) = new_block else_lbl st8 in
     let (_, st10) = compile_stmts cenv lctx ty else_body st9 in
     let else_terminated = block_is_terminated st10 in
     let (_, st11) = emit_jmp_if_not_terminated exit_lbl st10 in
     (* Exit block: only needed if at least one branch is non-terminated.
        Mirrors Python: stmt.py L488-494 *)
     if ¬then_terminated ∨ ¬else_terminated then
       let (_, st12) = new_block exit_lbl st11 in ((), st12)
     else ((), st11)) ∧

  (* For: range loop — for id in range(start, end) with bound n
     Creates 5-block CFG: entry → cond → body → incr → exit
     In the Vyper AST: For id typ (Range start end) n body
     Handles both static and dynamic ranges, signed and unsigned.
     For dynamic ranges (bound > 0): rounds = end - start, assert start <= end,
     assert rounds <= bound.
     For static ranges (bound = 0): no runtime checks — relies on type checker
     having validated start <= end at compile time. Loop uses EQ termination
     (counter != end_val), matching Python exactly.
     PRECONDITION (static ranges): start <= end for unsigned, start <=_s end for
     signed. If violated, the loop would run ~2^256 iterations until fuel exhausts.
     Vyper's type checker guarantees this for static ranges (both are literals).
     Mirrors Python: stmt.py _lower_range_loop *)
  compile_stmt cenv lctx ty (For id fty (Range start_e end_e) bound body) st =
    (let (start_op, st1) = lower_value compile_expr cenv fty start_e st in
     let (end_op, st2) = lower_value compile_expr cenv fty end_e st1 in
     let is_signed = is_signed_type fty in
     let (entry_lbl, st3) = fresh_label "for_entry" st2 in
     let (cond_lbl, st4) = fresh_label "for_cond" st3 in
     let (body_lbl, st5) = fresh_label "for_body" st4 in
     let (incr_lbl, st6) = fresh_label "for_incr" st5 in
     let (exit_lbl, st7) = fresh_label "for_exit" st6 in
     (* Jump to entry *)
     let (_, st8) = emit_inst JMP [Label entry_lbl] [] st7 in
     (* Entry: initialize counter, bound checks for dynamic ranges *)
     let (_, st9) = new_block entry_lbl st8 in
     let (counter_var, st10) = fresh_var st9 in
     let (_, st11) = emit_inst ASSIGN [start_op] [counter_var] st10 in
     (* Compute rounds and end_val.
        If bound > 0, this is a dynamic range: rounds = end - start.
        Otherwise static: end_val = end_op directly. *)
     let (end_val, st12) =
       if bound > 0 then
         let (rounds, st_r1) = emit_op SUB [end_op; start_op] st11 in
         let (_, st_r2) = compile_range_bound_checks start_op end_op rounds
                                                      bound is_signed st_r1 in
         emit_op ADD [start_op; rounds] st_r2
       else
         (end_op, st11) in
     let (_, st13) = emit_inst JMP [Label cond_lbl] [] st12 in
     (* Cond: check counter != end *)
     let (_, st14) = new_block cond_lbl st13 in
     let (done_op, st15) = emit_op EQ [Var counter_var; end_val] st14 in
     let (_, st16) = emit_inst JNZ [done_op; Label exit_lbl; Label body_lbl] [] st15 in
     (* Body: store counter to loop var, execute body *)
     let (_, st17) = new_block body_lbl st16 in
     let (_, st18) =
       (case FLOOKUP cenv.ce_vars id of
          SOME (MemLoc offset _) =>
            emit_void MSTORE [Lit (n2w offset); Var counter_var] st17
        | _ => ((), st17)) in
     let loop_ctx = InLoop exit_lbl incr_lbl in
     let (_, st19) = compile_stmts cenv loop_ctx ty body st18 in
     (* Only JMP to incr if body didn't terminate (e.g. via break/return) *)
     let (_, st20) = emit_jmp_if_not_terminated incr_lbl st19 in
     (* Incr: counter = counter + 1 *)
     let (_, st21) = new_block incr_lbl st20 in
     let (new_counter, st22) = emit_op ADD [Var counter_var; Lit 1w] st21 in
     let (_, st23) = emit_inst ASSIGN [new_counter] [counter_var] st22 in
     let (_, st24) = emit_inst JMP [Label cond_lbl] [] st23 in
     (* Exit block *)
     let (_, st25) = new_block exit_lbl st24 in ((), st25)) ∧

  (* For: iter loop — for id in array
     Creates 5-block CFG: entry → cond → body → incr → exit
     Location-aware: handles memory, storage, transient, code, calldata.
     is_dynamic: T for DynArray (has length word), F for SArray
     word_scale: 1 for storage/transient, 32 for memory/code/calldata
     elem_size: size of element in location units
     load_opc: MLOAD/SLOAD/TLOAD/CALLDATALOAD/DLOADN
     is_slot_addressed: T for storage/transient
     SEMANTIC DIFFERENCE: The Vyper interpreter materializes the entire array
     to a value list before iterating (eval_iterator → materialise → extract_elements).
     The lowering reads elements from source on each iteration. If the loop body
     modifies the source array, the interpreter sees original values but the lowering
     sees modified values. Vyper's type checker forbids mutation of the iterated
     array during the loop, so this is correct for well-typed programs.
     Correctness theorem needs precondition: loop body does not modify arr_e.
     Mirrors Python: stmt.py _lower_iter_loop *)
  compile_stmt cenv lctx ty (For id fty (Array arr_e) bound body) st =
    (let (arr_vv, st1) = compile_expr cenv (expr_type arr_e) arr_e st in
     let arr_op = vv_operand arr_vv in
     (* Determine location from array expression (not loop variable!).
        Mirrors Python: array_vv.location or node.iter._expr_info.location.
        Storage/transient: word_scale=1, slot-addressed.
        Memory: word_scale=32, byte-addressed. *)
     let is_dynamic = infer_array_is_dynamic cenv arr_e in
     let loc = infer_array_location cenv arr_e in
     let slot_addr = is_slot_addressed loc in
     let ws = word_scale loc in
     let elem_size = elem_size_in_location cenv loc fty in
     let load_opc = load_opc_for loc in
     (* Load array length *)
     let (len_op, st2) =
       if is_dynamic then emit_op load_opc [arr_op] st1
       else (Lit (n2w bound), st1) in
     (* Bound check for DynArrays: length <= bound *)
     let (_, st2a) =
       if is_dynamic ∧ bound > 0 then
         let (invalid, st_b1) = emit_op GT [len_op; Lit (n2w bound)] st2 in
         let (valid, st_b2) = emit_op ISZERO [invalid] st_b1 in
         emit_void ASSERT [valid] st_b2
       else ((), st2) in
     let (entry_lbl, st3) = fresh_label "iter_entry" st2a in
     let (cond_lbl, st4) = fresh_label "iter_cond" st3 in
     let (body_lbl, st5) = fresh_label "iter_body" st4 in
     let (incr_lbl, st6) = fresh_label "iter_incr" st5 in
     let (exit_lbl, st7) = fresh_label "iter_exit" st6 in
     (* Jump to entry *)
     let (_, st8) = emit_inst JMP [Label entry_lbl] [] st7 in
     (* Entry: initialize index = 0 *)
     let (_, st9) = new_block entry_lbl st8 in
     let (idx_var, st10) = fresh_var st9 in
     let (_, st11) = emit_inst ASSIGN [Lit 0w] [idx_var] st10 in
     let (_, st12) = emit_inst JMP [Label cond_lbl] [] st11 in
     (* Cond: check index == length *)
     let (_, st13) = new_block cond_lbl st12 in
     let (done_op, st14) = emit_op EQ [Var idx_var; len_op] st13 in
     let (_, st15) = emit_inst JNZ [done_op; Label exit_lbl; Label body_lbl] [] st14 in
     (* Body: compute element address, copy to loop var, execute body *)
     let (_, st16) = new_block body_lbl st15 in
     (* offset_base: skip length word for DynArray *)
     let offset_base = if is_dynamic then ws else 0 in
     let (idx_offset, st17) = emit_op MUL [Var idx_var;
                                           Lit (n2w elem_size)] st16 in
     let (total_offset, st18) =
       if offset_base > 0 then
         emit_op ADD [Lit (n2w offset_base); idx_offset] st17
       else (idx_offset, st17) in
     let (elem_ptr, st19) = emit_op ADD [arr_op; total_offset] st18 in
     (* Copy element to loop variable (in memory).
        target_ty = fty (loop variable type), elem_ty = array value_type.
        These can differ (e.g., for x: Bytes[704] in arr where
        arr: DynArray[Bytes[540], 10]).
        Mirrors Python: store_memory(elem_addr, dst, target_type,
                         src_typ=array_typ.value_type) *)
     let arr_elem_ty = (case expr_type arr_e of
                           ArrayT et _ => et | _ => fty) in
     let (_, st20) =
       (case FLOOKUP cenv.ce_vars id of
          SOME (MemLoc off _) =>
            compile_iter_elem_copy cenv elem_ptr (Lit (n2w off)) elem_size
                                   loc slot_addr fty arr_elem_ty st19
        | _ => ((), st19)) in
     let loop_ctx = InLoop exit_lbl incr_lbl in
     let (_, st21) = compile_stmts cenv loop_ctx ty body st20 in
     (* Only JMP to incr if body didn't terminate *)
     let (_, st22) = emit_jmp_if_not_terminated incr_lbl st21 in
     (* Incr: index = index + 1 *)
     let (_, st23) = new_block incr_lbl st22 in
     let (new_idx, st24) = emit_op ADD [Var idx_var; Lit 1w] st23 in
     let (_, st25) = emit_inst ASSIGN [new_idx] [idx_var] st24 in
     let (_, st26) = emit_inst JMP [Label cond_lbl] [] st25 in
     (* Exit block *)
     let (_, st27) = new_block exit_lbl st26 in ((), st27)) ∧

  (* Break: jump to loop exit *)
  compile_stmt cenv (InLoop exit_lbl _) ty Break st =
    emit_inst JMP [Label exit_lbl] [] st ∧

  (* Continue: jump to loop increment *)
  compile_stmt cenv (InLoop _ incr_lbl) ty Continue st =
    emit_inst JMP [Label incr_lbl] [] st ∧

  (* Catch-all for unsupported statements: emit INVALID *)
  compile_stmt cenv lctx ty _ st =
    (let (_, st') = emit_inst INVALID [] [] st in ((), st')) ∧

  (* Compile a list of statements.
     Skips dead code after terminating statements (return, raise, break, continue).
     Mirrors Python: stmt.py _lower_body with is_terminated check *)
  compile_stmts cenv lctx ty [] st = ((), st) ∧
  compile_stmts cenv lctx ty (s::ss) st =
    (if block_is_terminated st then ((), st)
     else
       let (_, st1) = compile_stmt cenv lctx ty s st in
       compile_stmts cenv lctx ty ss st1)
Termination
  WF_REL_TAC `measure (λx. case x of
    INL (cenv, lctx, ty, s, st) => 2 * stmt_size s + 2
  | INR (cenv, lctx, ty, ss, st) => 2 * list_size stmt_size ss + 1)`
End
