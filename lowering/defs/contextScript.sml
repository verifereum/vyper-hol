(*
 * Codegen Context: data locations, VyperValue, buffer/ptr, memory operations
 *
 * TOP-LEVEL:
 *   data_location      — where a value lives (MEMORY, STORAGE, TRANSIENT, CODE, CALLDATA)
 *   vyper_value      — StackValue type operand | LocatedValue type ptr
 *   vv_type          — extract type
 *   vv_operand       — extract raw operand
 *   vv_location      — extract location (NONE for stack)
 *   vv_is_stack      — predicate: is stack value?
 *   base_ptr         — buffer → ptr (LocMemory with provenance)
 *   mk_ptr           — convenience: ptr for non-memory locations
 *   ptr                 — pointer with location tag
 *   buffer              — allocated memory region
 *   word_scale          — addressing scale for a location (1 for slots, 32 for bytes)
 *   ptr_load            — dispatch load by location
 *   ptr_store           — dispatch store by location
 *   copy_memory         — copy memory region (mcopy or word-by-word)
 *   word_copy_loop      — parameterized loop for slot↔memory copies
 *   store_memory        — store value to memory (handles prim vs complex)
 *   store_memory_typed  — layout-aware copy (when src_typ ≠ dst_typ)
 *   copy_sarray_typed   — per-element SArray copy with different layouts
 *   copy_dynarray_typed — per-element DynArray copy with different layouts
 *
 * Mirrors Python: ~/vyper/vyper/codegen_venom/context.py, buffer.py, value.py
 *)

Theory context
Ancestors
  emitHelper compileEnv venomInst

(* data_location, word_scale, is_slot_addressed now in compileEnvScript
   (shared so exprLowering can use them without circular dependency) *)

(* ===== Buffer ===== *)
(* An allocated memory region. Mirrors Python: buffer.py Buffer
   buf.base_ptr() gives a Ptr to the start with provenance. *)
Datatype:
  buffer = <|
    buf_operand : operand;   (* the alloca result operand *)
    buf_size : num            (* allocation size in bytes *)
  |>
End

(* ===== Ptr ===== *)
(* A pointer with location tag. Mirrors Python: buffer.py Ptr
   Invariant: ptr_buf is SOME iff ptr_location = LocMemory.
   Every memory pointer tracks its buffer provenance for non-aliasing proofs. *)
Datatype:
  ptr = <|
    ptr_operand : operand;
    ptr_location : data_location;
    ptr_buf : buffer option   (* provenance — SOME for memory, NONE otherwise *)
  |>
End

(* Create a Ptr from a Buffer (always LocMemory, always has provenance).
   Mirrors Python: buffer.py Buffer.base_ptr() *)
Definition base_ptr_def:
  base_ptr buf = <| ptr_operand := buf.buf_operand;
                    ptr_location := LocMemory;
                    ptr_buf := SOME buf |>
End

(* Convenience: make a ptr for non-memory locations (no buffer provenance) *)
Definition mk_ptr_def:
  mk_ptr op loc = <| ptr_operand := op; ptr_location := loc; ptr_buf := NONE |>
End

(* ===== VyperValue ===== *)
(* Location-aware wrapper for IR operands.
   Mirrors Python: vyper/codegen_venom/value.py VyperValue
   Carries type so unwrap_value is self-contained (no separate ty parameter).
   - StackValue ty op: operand IS the value (no load needed)
   - LocatedValue ty p: operand is a POINTER via ptr record (needs load for prims)
   Factoring: prove unwrap_value correct ONCE; each compile_expr case
   only proves "I tagged correctly"; every consumer applies unwrap theorem. *)
Datatype:
  vyper_value = StackValue type operand | LocatedValue type ptr
End

(* Get the type from a VyperValue *)
Definition vv_type_def:
  vv_type (StackValue ty _) = ty ∧
  vv_type (LocatedValue ty _) = ty
End

(* Get the raw operand from a VyperValue *)
Definition vv_operand_def:
  vv_operand (StackValue _ op) = op ∧
  vv_operand (LocatedValue _ p) = p.ptr_operand
End

(* Get the location (NONE for stack values) *)
Definition vv_location_def:
  vv_location (StackValue _ _) = NONE ∧
  vv_location (LocatedValue _ p) = SOME p.ptr_location
End

(* Is this a stack value? *)
Definition vv_is_stack_def:
  vv_is_stack (StackValue _ _) = T ∧
  vv_is_stack (LocatedValue _ _) = F
End

(* ===== Load/Store by Location ===== *)

(* Emit a load instruction based on location.
   is_ctor: T in constructor context — LocCode uses ILOAD (staging area).
            F in runtime context — LocCode uses DLOAD (deployed bytecode).
   Mirrors Python: context.py ptr_load + unwrap() is_ctor dispatch. *)
Definition compile_ptr_load_def:
  compile_ptr_load is_ctor LocMemory op = emit_op MLOAD [op] ∧
  compile_ptr_load is_ctor LocStorage op = emit_op SLOAD [op] ∧
  compile_ptr_load is_ctor LocTransient op = emit_op TLOAD [op] ∧
  compile_ptr_load is_ctor LocCalldata op = emit_op CALLDATALOAD [op] ∧
  compile_ptr_load is_ctor LocCode op =
    if is_ctor then emit_op ILOAD [op]
    else emit_op DLOAD [op]
End

(* Emit a store instruction based on location.
   is_ctor: T in constructor context — LocCode uses ISTORE (staging area).
            F in runtime context — LocCode store is invalid (read-only).
   Mirrors Python: context.py ptr_store + is_ctor dispatch. *)
Definition compile_ptr_store_def:
  compile_ptr_store is_ctor LocMemory dst val st =
    emit_void MSTORE [dst; val] st ∧
  compile_ptr_store is_ctor LocStorage dst val st =
    emit_void SSTORE [dst; val] st ∧
  compile_ptr_store is_ctor LocTransient dst val st =
    emit_void TSTORE [dst; val] st ∧
  compile_ptr_store is_ctor LocCode dst val st =
    (if is_ctor then emit_void ISTORE [dst; val]
     else emit_void INVALID []) st ∧  (* runtime: code is read-only *)
  (* Python raises CompilerPanic("cannot store to: CALLDATA").
     Emit INVALID instead of silent no-op. Unreachable for well-typed programs. *)
  compile_ptr_store is_ctor LocCalldata _ _ st = emit_void INVALID [] st
End

(* ===== Memory Copy ===== *)

(* Copy memory region via MCOPY (Cancun+).
   Mirrors Python: context.py copy_memory *)
Definition compile_copy_memory_def:
  compile_copy_memory dst src 0 st = ((), st) ∧
  compile_copy_memory dst src size st =
    emit_void MCOPY [dst; src; Lit (n2w size)] st
End

(* Parameterized word-copy loop between two address spaces.
   Mirrors Python: context.py _word_copy_loop
   Used for storage↔memory and transient↔memory bulk copies. *)
Definition compile_word_copy_loop_def:
  compile_word_copy_loop src_op dst_op word_count load_loc store_loc is_ctor st =
    let src_scale = word_scale load_loc in
    let dst_scale = word_scale store_loc in
    (* Create blocks: cond, body, exit *)
    let (cond_lbl, st1) = fresh_label "wcopy_cond" st in
    let (body_lbl, st2) = fresh_label "wcopy_body" st1 in
    let (exit_lbl, st3) = fresh_label "wcopy_exit" st2 in
    (* Initialize counter *)
    let (counter_var, st4) = fresh_var st3 in
    let (_, st5) = emit_inst ASSIGN [Lit 0w] [counter_var] st4 in
    let (_, st6) = emit_inst JMP [Label cond_lbl] [] st5 in
    (* Cond block *)
    let (_, st7) = new_block cond_lbl st6 in
    let (done_op, st8) = emit_op EQ [Var counter_var; Lit (n2w word_count)] st7 in
    let (_, st9) = emit_inst JNZ [done_op; Label exit_lbl; Label body_lbl] [] st8 in
    (* Body block *)
    let (_, st10) = new_block body_lbl st9 in
    (* Compute source offset *)
    let (src_off, st11) =
      if src_scale = 1 then
        emit_op ADD [src_op; Var counter_var] st10
      else
        let (scaled, st_a) = emit_op MUL [Var counter_var; Lit (n2w src_scale)] st10 in
        emit_op ADD [src_op; scaled] st_a in
    (* Load from source *)
    let (val_loaded, st12) = compile_ptr_load is_ctor load_loc src_off st11 in
    (* Compute dest offset *)
    let (dst_off, st13) =
      if dst_scale = 1 then
        emit_op ADD [dst_op; Var counter_var] st12
      else
        let (scaled, st_a) = emit_op MUL [Var counter_var; Lit (n2w dst_scale)] st12 in
        emit_op ADD [dst_op; scaled] st_a in
    (* Store to dest *)
    let (_, st14) = compile_ptr_store is_ctor store_loc dst_off val_loaded st13 in
    (* Increment counter *)
    let (new_ctr, st15) = emit_op ADD [Var counter_var; Lit 1w] st14 in
    let (_, st16) = emit_inst ASSIGN [new_ctr] [counter_var] st15 in
    let (_, st17) = emit_inst JMP [Label cond_lbl] [] st16 in
    (* Exit block *)
    new_block exit_lbl st17
End

(* ===== Store Memory ===== *)
(* Store value to memory pointer.
   Mirrors Python: context.py store_memory
   Primitive word types: direct mstore.
   Complex types: memory copy (val is src ptr).
   KNOWN BUG: Missing bytestring case. Python has 3 cases:
   1. prim_word → MSTORE
   2. _BytestringT → dynamic copy: 32 + ceil32(actual_length)
   3. other complex → MCOPY of mem_bytes_required (static)
   This function only handles cases 1 and 3. Case 2 is in
   compile_store_bytestring (contextScript.sml:476). Callers
   must dispatch to the correct function for bytestrings. *)
(* Simple store memory (no typed copy). Used when src_typ = dst_typ.
   For layout-aware copy when src_typ ≠ dst_typ, see
   compile_store_memory_typed and compile_assign_value. *)
Definition compile_store_memory_def:
  compile_store_memory val_op dst_op is_prim_word mem_size st =
    if is_prim_word then
      emit_void MSTORE [dst_op; val_op] st
    else
      compile_copy_memory dst_op val_op mem_size st
End

(* ===== Load from Storage/Transient to Memory ===== *)
(* Mirrors Python: context.py _load_storage_to_memory *)
Definition compile_storage_to_memory_def:
  compile_storage_to_memory slot buf word_count st =
    compile_word_copy_loop slot buf word_count LocStorage LocMemory F st
End

(* Mirrors Python: context.py _store_memory_to_storage *)
Definition compile_memory_to_storage_def:
  compile_memory_to_storage buf slot word_count st =
    compile_word_copy_loop buf slot word_count LocMemory LocStorage F st
End

(* Mirrors Python: context.py _load_transient_to_memory *)
Definition compile_transient_to_memory_def:
  compile_transient_to_memory slot buf word_count st =
    compile_word_copy_loop slot buf word_count LocTransient LocMemory F st
End

(* Mirrors Python: context.py _store_memory_to_transient *)
Definition compile_memory_to_transient_def:
  compile_memory_to_transient buf slot word_count st =
    compile_word_copy_loop buf slot word_count LocMemory LocTransient F st
End

(* ===== Allocate Buffer ===== *)
(* Allocate memory buffer with provenance tracking.
   Returns (buffer # compile_state).
   buffer.buf_operand is the IR operand; buffer.buf_size is the allocation size.
   Use base_ptr buf for a LocatedValue with provenance.
   Mirrors Python: context.py allocate_buffer → Buffer *)
Definition compile_alloc_buffer_def:
  compile_alloc_buffer size st =
    let (op, st1) = emit_op ALLOCA [Lit (n2w size); Lit 0w] st in
    (<| buf_operand := op; buf_size := size |>, st1)
End

(* ===== Load/Store Storage ===== *)
(* Mirrors Python: context.py load_storage
   Primitive: sload directly.
   Complex: allocate buffer, copy from storage to memory. *)
Definition compile_load_storage_def:
  compile_load_storage slot is_prim_word word_count alloca_size st =
    if is_prim_word then
      emit_op SLOAD [slot] st
    else if word_count = 1 then
            let (buf_op_alloc, st2) = compile_alloc_buffer alloca_size st in
            let buf_op = buf_op_alloc.buf_operand in
      let (loaded, st3) = emit_op SLOAD [slot] st2 in
      let (_, st4) = emit_void MSTORE [buf_op; loaded] st3 in
      (buf_op, st4)
    else
            let (buf_op_alloc, st2) = compile_alloc_buffer alloca_size st in
            let buf_op = buf_op_alloc.buf_operand in
      let (_, st3) = compile_storage_to_memory slot buf_op word_count st2 in
      (buf_op, st3)
End

(* Mirrors Python: context.py store_storage *)
Definition compile_store_storage_def:
  compile_store_storage val slot is_prim_word word_count st =
    if is_prim_word then
      emit_void SSTORE [slot; val] st
    else if word_count = 1 then
      let (loaded, st1) = emit_op MLOAD [val] st in
      emit_void SSTORE [slot; loaded] st1
    else
      let (_, st1) = compile_memory_to_storage val slot word_count st in
      ((), st1)
End

(* ===== Load/Store Transient ===== *)
Definition compile_load_transient_def:
  compile_load_transient slot is_prim_word word_count alloca_size st =
    if is_prim_word then
      emit_op TLOAD [slot] st
    else if word_count = 1 then
            let (buf_op_alloc, st2) = compile_alloc_buffer alloca_size st in
            let buf_op = buf_op_alloc.buf_operand in
      let (loaded, st3) = emit_op TLOAD [slot] st2 in
      let (_, st4) = emit_void MSTORE [buf_op; loaded] st3 in
      (buf_op, st4)
    else
            let (buf_op_alloc, st2) = compile_alloc_buffer alloca_size st in
            let buf_op = buf_op_alloc.buf_operand in
      let (_, st3) = compile_transient_to_memory slot buf_op word_count st2 in
      (buf_op, st3)
End

(* Mirrors Python: context.py code_to_memory
   Always uses DLOAD (reads from code section), never ILOAD.
   Python: code_to_memory always calls dload, even in ctor context.
   ILOAD is only used for single-word immutables in load_immutable_ctor. *)
Definition compile_code_to_memory_def:
  compile_code_to_memory offset dst word_count st =
    if word_count = 0 then ((), st)
    else
      let (_, st1) = compile_word_copy_loop offset dst word_count
                       LocCode LocMemory F st in
      ((), st1)
End

(* ===== Load/Store Immutables ===== *)
(* Mirrors Python: context.py load_immutable
   is_ctor: T → ILOAD (ctor staging), F → DLOAD (deployed bytecode). *)
Definition compile_load_immutable_def:
  compile_load_immutable offset is_prim_word word_count alloca_size is_ctor st =
    if is_prim_word then
      (if is_ctor then emit_op ILOAD [offset] st
       else emit_op DLOAD [offset] st)
    else
            let (buf_op_alloc, st2) = compile_alloc_buffer alloca_size st in
            let buf_op = buf_op_alloc.buf_operand in
      let (_, st3) = compile_code_to_memory offset buf_op word_count st2 in
      (buf_op, st3)
End

(* ===== Materialize to Memory ===== *)
(* Materialize a complex value from its source location to memory if needed.
   For primitive types or already-in-memory: returns val_op unchanged.
   For storage/transient: allocates buffer, copies to memory, returns buffer ptr.
   For code: allocates buffer, copies via DLOAD/ILOAD loop, returns buffer ptr.
   is_ctor: T in constructor context — LocCode uses ILOAD instead of DLOAD.
   Mirrors Python: context.py unwrap() for complex types. *)
Definition compile_materialize_to_memory_def:
  compile_materialize_to_memory val_op src_loc is_prim word_count
                                alloca_size is_ctor st =
    if is_prim then (val_op, st)
    else case src_loc of
       LocStorage =>
         compile_load_storage val_op F word_count alloca_size st
     | LocTransient =>
         compile_load_transient val_op F word_count alloca_size st
     | LocCode =>
         compile_load_immutable val_op F word_count alloca_size is_ctor st
     | _ => (val_op, st)
End

(* ===== Nonreentrant Lock ===== *)
(* Mirrors Python: context.py emit_nonreentrant_lock/unlock
   is_view: T for view functions — check lock but don't acquire it.
   Python: if func_t.mutability != VIEW: STORE(key, temp_value) *)
Definition compile_nonreentrant_lock_def:
  compile_nonreentrant_lock nkey use_transient is_view st =
    if use_transient then
      let (current, st1) = emit_op TLOAD [Lit (n2w nkey)] st in
      let (locked, st2) = emit_op EQ [current; Lit 1w] st1 in
      let (not_locked, st3) = emit_op ISZERO [locked] st2 in
      let (_, st4) = emit_void ASSERT [not_locked] st3 in
      if is_view then ((), st4)
      else emit_void TSTORE [Lit (n2w nkey); Lit 1w] st4
    else
      let (current, st1) = emit_op SLOAD [Lit (n2w nkey)] st in
      let (locked, st2) = emit_op EQ [current; Lit 2w] st1 in
      let (not_locked, st3) = emit_op ISZERO [locked] st2 in
      let (_, st4) = emit_void ASSERT [not_locked] st3 in
      if is_view then ((), st4)
      else emit_void SSTORE [Lit (n2w nkey); Lit 2w] st4
End

(* Python: if func_t.mutability == VIEW: return (no unlock needed)
   is_view: T → no-op *)
Definition compile_nonreentrant_unlock_def:
  compile_nonreentrant_unlock nkey use_transient is_view st =
    if is_view then ((), st)
    else if use_transient then
      emit_void TSTORE [Lit (n2w nkey); Lit 0w] st
    else
      emit_void SSTORE [Lit (n2w nkey); Lit 3w] st
End

(* ===== Zero Memory ===== *)
(* Mirrors Python: builtins/simple.py _zero_memory *)
(* Zero memory: emit MSTORE(ptr+i*32, 0) for each 32-byte word.
   i: current word index, words: total words to zero.
   Mirrors Python: context.py zero_memory *)
Definition compile_zero_memory_loop_def:
  compile_zero_memory_loop ptr_op i words st =
    if i >= words then ((), st)
    else
      let (dst, st1) = if i = 0 then (ptr_op, st)
                        else emit_op ADD [ptr_op; Lit (n2w (i * 32))] st in
      let (_, st2) = emit_void MSTORE [dst; Lit 0w] st1 in
      compile_zero_memory_loop ptr_op (i + 1) words st2
Termination
  WF_REL_TAC `measure (λ(ptr,i,words,st). words - i)`
End

Definition compile_zero_memory_def:
  compile_zero_memory ptr_op 0 st = ((), st) ∧
  compile_zero_memory ptr_op size st =
    let words = (size + 31) DIV 32 in
    compile_zero_memory_loop ptr_op 0 words st
End

(* ===== Bytestring Operations ===== *)
(* Mirrors Python: context.py ensure_bytestring_in_memory,
   bytes_data_ptr, bytestring_length *)

(* Get data pointer from bytestring pointer: ptr + word_scale.
   Memory/None: +32 (byte-addressed). Storage/Transient: +1 (slot-addressed).
   Mirrors Python: context.py bytes_data_ptr *)
Definition compile_bytes_data_ptr_def:
  compile_bytes_data_ptr ptr_op loc =
    let scale = word_scale loc in
    emit_op ADD [ptr_op; Lit (n2w scale)]
End

(* Get bytestring length: dispatches on location.
   Mirrors Python: context.py bytestring_length *)
(* Load bytestring length from first slot at pointer.
   is_ctor needed for LocCode: ctor uses ILOAD, runtime uses DLOAD. *)
Definition compile_bytestring_length_def:
  compile_bytestring_length is_ctor ptr_op loc =
    compile_ptr_load is_ctor loc ptr_op
End

(* Ensure bytestring is in memory. If from storage/transient/code,
   copy to memory first. *)
(* Ensure a value is in memory. If already in memory, return ptr.
   Otherwise allocate buffer and copy from source location.
   mem_bytes: memory_bytes_required (allocation size).
   word_count: storage_size_in_words (number of 32-byte slots to copy).
   Mirrors Python: context.py ensure_in_memory *)
Definition compile_ensure_in_memory_def:
  compile_ensure_in_memory ptr_op loc mem_bytes word_count is_ctor st =
    case loc of
      LocMemory => (ptr_op, st)
    | LocStorage =>
        let (buf_op_alloc, st1) = compile_alloc_buffer (mem_bytes + 32) st in
        let buf_op = buf_op_alloc.buf_operand in
        let (_, st2) = compile_storage_to_memory ptr_op buf_op word_count st1 in
        (buf_op, st2)
    | LocTransient =>
        let (buf_op_alloc, st1) = compile_alloc_buffer (mem_bytes + 32) st in
        let buf_op = buf_op_alloc.buf_operand in
        let (_, st2) = compile_transient_to_memory ptr_op buf_op word_count st1 in
        (buf_op, st2)
    | LocCode =>
        (* Always DLOAD: code_to_memory reads from code section.
           Mirrors Python: ensure_bytestring_in_memory → code_to_memory → dload. *)
        let (buf_op_alloc, st1) = compile_alloc_buffer (mem_bytes + 32) st in
        let buf_op = buf_op_alloc.buf_operand in
        let (_, st2) = compile_code_to_memory ptr_op buf_op word_count st1 in
        (buf_op, st2)
    | LocCalldata =>
        (* Load actual length from calldata (ptr_op points to length word).
           Allocate buffer, copy length + data. mem_bytes is max size. *)
        let (len_op, st1) = emit_op CALLDATALOAD [ptr_op] st in
        let (buf_op_alloc, st2) = compile_alloc_buffer (mem_bytes + 32) st1 in
        let buf_op = buf_op_alloc.buf_operand in
        let (_, st3) = emit_void MSTORE [buf_op; len_op] st2 in
        let (data_ptr, st4) = emit_op ADD [buf_op; Lit 32w] st3 in
        let (src_data, st5) = emit_op ADD [ptr_op; Lit 32w] st4 in
        let (_, st6) = emit_void CALLDATACOPY [data_ptr; src_data; len_op] st5 in
        (buf_op, st6)
End

(* ===== Slot-to-Memory Copy ===== *)
(* Copy multi-slot data from storage/transient to memory.
   Used in iter loop for complex element types.
   Mirrors Python: context.py slot_to_memory *)
Definition compile_slot_to_memory_def:
  compile_slot_to_memory src_slot dst_ptr num_slots loc =
    compile_word_copy_loop src_slot dst_ptr num_slots loc LocMemory F
End

(* ===== Store Immutable ===== *)
(* Store multi-word value to immutable location during constructor.
   is_ctor=T because store_immutable only runs in constructor context.
   Mirrors Python: context.py store_immutable *)
Definition compile_store_immutable_def:
  compile_store_immutable src_ptr dst_offset num_words =
    compile_word_copy_loop src_ptr (Lit (n2w dst_offset)) num_words
      LocMemory LocCode T
End

(* ===== Dynamic Array to Storage Copy ===== *)
(* Copy only length + actual elements from memory to storage.
   Mirrors Python: stmt.py _copy_dynarray_to_storage *)
(* ===== Load Calldata ===== *)
(* Mirrors Python: context.py load_calldata *)
Definition compile_load_calldata_def:
  compile_load_calldata offset is_prim_word word_count alloca_size st =
    if is_prim_word then
      emit_op CALLDATALOAD [offset] st
    else if word_count = 1 then
            let (buf_op_alloc, st2) = compile_alloc_buffer alloca_size st in
            let buf_op = buf_op_alloc.buf_operand in
      let (loaded, st3) = emit_op CALLDATALOAD [offset] st2 in
      let (_, st4) = emit_void MSTORE [buf_op; loaded] st3 in
      (buf_op, st4)
    else
            let (buf_op_alloc, st2) = compile_alloc_buffer alloca_size st in
            let buf_op = buf_op_alloc.buf_operand in
      (* calldatacopy from offset to buf, size bytes *)
      let (_, st3) = emit_void CALLDATACOPY [buf_op; offset; Lit (n2w alloca_size)] st2 in
      (buf_op, st3)
End

(* ===== Copy Memory Dynamic ===== *)
(* Mirrors Python: context.py copy_memory_dynamic *)
Definition compile_copy_memory_dynamic_def:
  compile_copy_memory_dynamic dst src length_op st =
    emit_void MCOPY [dst; src; length_op] st
End

(* NOTE: compile_load_by_loc deleted — duplicate of compile_ptr_load *)

(* ===== With Byte Offset ===== *)
(* Add byte offset to base pointer. Mirrors Python: context.py _with_byte_offset *)
Definition compile_with_byte_offset_def:
  compile_with_byte_offset base 0 st = (base, st) ∧
  compile_with_byte_offset base offset st =
    emit_op ADD [base; Lit (n2w offset)] st
End

(* ===== Store Memory for Bytestrings ===== *)
(* Copy bytestring to memory: copies 32 + ceil32(actual_length) bytes.
   Mirrors Python: context.py store_memory for _BytestringT.
   Placed before typed copy defs since they dispatch to it. *)
Definition compile_store_bytestring_def:
  compile_store_bytestring val_op dst_op st =
    (* Load actual length from val *)
    let (src_len, st1) = emit_op MLOAD [val_op] st in
    (* ceil32(length) = (length + 31) & ~31 *)
    let (padded_len, st2) = emit_op ADD [src_len; Lit 31w] st1 in
    (* ~31 = 0xffffffffffffffe0 *)
    let mask = i2w (- &32) : bytes32 in
    let (rounded, st3) = emit_op AND [padded_len; Lit mask] st2 in
    (* Total copy: 32 (length word) + ceil32(length) *)
    let (copy_len, st4) = emit_op ADD [rounded; Lit 32w] st3 in
    emit_void MCOPY [dst_op; val_op; copy_len] st4
End

(* ===== Layout-Aware Memory Copy ===== *)
(* Copy between memory regions where source and destination types may have
   different memory layouts. For example, DynArray[Bytes[540]] (elem=572B)
   → DynArray[Bytes[704]] (elem=736B) needs per-element bytestring copy.
   Mirrors Python: context.py _store_memory_typed *)

(* ===== Mutually Recursive Typed Copy ===== *)
(* compile_store_memory_typed dispatches by type structure:
     TupleT → compile_typed_copy_fields (per-field, recursive)
     SArrayT → compile_copy_sarray_typed (fast batch or per-element loop)
     DynArrayT → compile_copy_dynarray_typed (length check + per-element loop)
     StructT → compile_struct_typed_copy (per-field by name, recursive)
   All dispatch functions RECURSE into compile_store_memory_typed.
   Terminates because sub-type depth strictly decreases (requires
   well_formed_sft acyclicity for struct recursion through cenv).
   Mirrors Python: context.py _store_memory_typed (recursive) *)
val compile_store_memory_typed_defn = Defn.Hol_defn "compile_store_memory_typed" `
  (* Top-level dispatch *)
  compile_store_memory_typed cenv dst dst_ty src src_ty st =
    (if is_word_type dst_ty then
      let (val_op, st1) = emit_op MLOAD [src] st in
      emit_void MSTORE [dst; val_op] st1
    else if is_bytestring_type dst_ty ∧ is_bytestring_type src_ty then
      compile_store_bytestring src dst st
    else
      case (dst_ty, src_ty) of
        (ArrayT dst_elem (Dynamic dst_cap), ArrayT src_elem (Dynamic _)) =>
          compile_copy_dynarray_typed cenv dst dst_elem dst_cap src src_elem st
      | (ArrayT dst_elem (Fixed n), ArrayT src_elem (Fixed _)) =>
          compile_copy_sarray_typed cenv dst dst_elem src src_elem n st
      | (TupleT dst_tys, TupleT src_tys) =>
          compile_typed_copy_fields cenv dst src dst_tys src_tys 0 0 st
      | (StructT dst_name, StructT src_name) =>
          let dst_fields = cenv.ce_struct_fields dst_name in
          let src_fields = cenv.ce_struct_fields src_name in
          compile_struct_typed_copy cenv
            dst src dst_fields src_fields 0 0 st
      | _ =>
          compile_copy_memory dst src (type_memory_bytes cenv dst_ty) st) ∧

  (* Tuple/struct per-field copy: recursive per-field.
     Mirrors Python: _store_memory_typed TupleT branch. *)
  compile_typed_copy_fields cenv dst src [] (src_tys : type list)
                            dst_off src_off st = ((), st) ∧
  compile_typed_copy_fields cenv dst src (dst_ty::dst_rest) []
                            dst_off src_off st = ((), st) ∧
  compile_typed_copy_fields cenv dst src (dst_ty::dst_rest) (src_ty::src_rest)
                            dst_off src_off st =
    (let (dst_ptr, st1) = compile_with_byte_offset dst dst_off st in
     let (src_ptr, st2) = compile_with_byte_offset src src_off st1 in
     let dst_sz = type_memory_bytes cenv dst_ty in
     let src_sz = type_memory_bytes cenv src_ty in
     (* Recurse into compile_store_memory_typed for full type-aware copy *)
     let (_, st3) = compile_store_memory_typed cenv dst_ptr dst_ty src_ptr src_ty st2 in
     compile_typed_copy_fields cenv dst src dst_rest src_rest
                               (dst_off + dst_sz) (src_off + src_sz) st3) ∧

  (* SArray typed copy: fast path or per-element loop.
     Mirrors Python: context.py _copy_sarray_memory_typed *)
  compile_copy_sarray_typed cenv dst dst_elem_ty src src_elem_ty count st =
    (let dst_elem_sz = type_memory_bytes cenv dst_elem_ty in
    let src_elem_sz = type_memory_bytes cenv src_elem_ty in
    if dst_elem_sz = src_elem_sz ∧ ¬is_abi_dynamic (cenv_sft cenv) dst_elem_ty then
      compile_copy_memory dst src (count * dst_elem_sz) st
    else
      let (cond_lbl, st1) = fresh_label "typed_sa_cond" st in
      let (body_lbl, st2) = fresh_label "typed_sa_body" st1 in
      let (exit_lbl, st3) = fresh_label "typed_sa_exit" st2 in
      let (counter, st4) = fresh_var st3 in
      let (_, st5) = emit_inst ASSIGN [Lit 0w] [counter] st4 in
      let (_, st6) = emit_inst JMP [Label cond_lbl] [] st5 in
      let (_, st7) = new_block cond_lbl st6 in
      let (lt_op, st8) = emit_op LT [Var counter; Lit (n2w count)] st7 in
      let (done_op, st9) = emit_op ISZERO [lt_op] st8 in
      let (_, st10) = emit_inst JNZ [done_op; Label exit_lbl; Label body_lbl]
                                [] st9 in
      let (_, st11) = new_block body_lbl st10 in
      let (src_off, st12) = emit_op MUL [Var counter;
                                          Lit (n2w src_elem_sz)] st11 in
      let (dst_off, st13) = emit_op MUL [Var counter;
                                          Lit (n2w dst_elem_sz)] st12 in
      let (src_elem, st14) = emit_op ADD [src; src_off] st13 in
      let (dst_elem, st15) = emit_op ADD [dst; dst_off] st14 in
      (* Recurse on element type for full type-aware copy *)
      let (_, st16) = compile_store_memory_typed cenv
                        dst_elem dst_elem_ty src_elem src_elem_ty st15 in
      let (new_ctr, st17) = emit_op ADD [Var counter; Lit 1w] st16 in
      let (_, st18) = emit_inst ASSIGN [new_ctr] [counter] st17 in
      let (_, st19) = emit_inst JMP [Label cond_lbl] [] st18 in
      let (_, st20) = new_block exit_lbl st19 in
      ((), st20)) ∧

  (* DynArray typed copy: length + capacity check + per-element loop.
     Mirrors Python: context.py _copy_dynarray_memory_typed *)
  compile_copy_dynarray_typed cenv dst dst_elem_ty dst_capacity
                              src src_elem_ty st =
    (let dst_elem_sz = type_memory_bytes cenv dst_elem_ty in
    let src_elem_sz = type_memory_bytes cenv src_elem_ty in
    let (length, st1) = emit_op MLOAD [src] st in
    let (too_long, st2) = emit_op GT [length; Lit (n2w dst_capacity)] st1 in
    let (ok, st3) = emit_op ISZERO [too_long] st2 in
    let (_, st4) = emit_void ASSERT [ok] st3 in
    let (_, st5) = emit_void MSTORE [dst; length] st4 in
    let (src_data, st6) = emit_op ADD [src; Lit 32w] st5 in
    let (dst_data, st7) = emit_op ADD [dst; Lit 32w] st6 in
    if dst_elem_sz = src_elem_sz ∧ dst_elem_ty = src_elem_ty then
      let (data_sz, st8) = emit_op MUL [length; Lit (n2w dst_elem_sz)] st7 in
      compile_copy_memory_dynamic dst_data src_data data_sz st8
    else
      let (cond_lbl, st8) = fresh_label "typed_dyn_cond" st7 in
      let (body_lbl, st9) = fresh_label "typed_dyn_body" st8 in
      let (exit_lbl, st10) = fresh_label "typed_dyn_exit" st9 in
      let (counter, st11) = fresh_var st10 in
      let (_, st12) = emit_inst ASSIGN [Lit 0w] [counter] st11 in
      let (_, st13) = emit_inst JMP [Label cond_lbl] [] st12 in
      let (_, st14) = new_block cond_lbl st13 in
      let (lt_op, st15) = emit_op LT [Var counter; length] st14 in
      let (done_op, st16) = emit_op ISZERO [lt_op] st15 in
      let (_, st17) = emit_inst JNZ [done_op; Label exit_lbl; Label body_lbl]
                                [] st16 in
      let (_, st18) = new_block body_lbl st17 in
      let (src_off, st19) = emit_op MUL [Var counter;
                                          Lit (n2w src_elem_sz)] st18 in
      let (dst_off, st20) = emit_op MUL [Var counter;
                                          Lit (n2w dst_elem_sz)] st19 in
      let (src_elem, st21) = emit_op ADD [src_data; src_off] st20 in
      let (dst_elem, st22) = emit_op ADD [dst_data; dst_off] st21 in
      (* Recurse on element type for full type-aware copy *)
      let (_, st23) = compile_store_memory_typed cenv
                        dst_elem dst_elem_ty src_elem src_elem_ty st22 in
      let (new_ctr, st24) = emit_op ADD [Var counter; Lit 1w] st23 in
      let (_, st25) = emit_inst ASSIGN [new_ctr] [counter] st24 in
      let (_, st26) = emit_inst JMP [Label cond_lbl] [] st25 in
      let (_, st27) = new_block exit_lbl st26 in
      ((), st27)) ∧

  (* Struct per-field copy: per-field by name, fully recursive.
     Each field recurses into compile_store_memory_typed for layout-aware copy.
     Mirrors Python: _store_memory_typed StructT branch. *)
  compile_struct_typed_copy cenv dst src [] src_fields
                            dst_off src_off st = ((), st) ∧
  compile_struct_typed_copy cenv dst src ((name, dst_fty, dst_sz)::dst_rest)
                            src_fields dst_off src_off st =
    (let (src_fty, src_sz) = (case ALOOKUP src_fields name of
                                SOME (ft, sz) => (ft, sz)
                              | NONE => (dst_fty, dst_sz)) in
     let (dst_ptr, st1) = compile_with_byte_offset dst dst_off st in
     let (src_ptr, st2) = compile_with_byte_offset src src_off st1 in
     (* Recurse into compile_store_memory_typed for full type-aware copy *)
     let (_, st3) = compile_store_memory_typed cenv
                      dst_ptr dst_fty src_ptr src_fty st2 in
     compile_struct_typed_copy cenv dst src dst_rest src_fields
                               (dst_off + dst_sz) (src_off + src_sz) st3)
`;

(* Termination: struct recursion through cenv.ce_struct_fields requires
   well_formed_sft (acyclic struct graph). Same root cause as the 3
   compileEnv termination cheats. Provable with struct_type_depth measure. *)
val _ = Defn.save_defn compile_store_memory_typed_defn;

(* NOTE: compile_store_complex_type and compile_copy_complex_type deleted —
   dead code. Actual callers use compile_word_copy_loop / compile_ptr_load
   directly with explicit is_ctor from cenv.ce_is_ctor. *)

(* ===== Encode Log Topic ===== *)
(* Mirrors Python: stmt.py _encode_log_topic
   Primitive words: use directly. Bytestrings: keccak256 hash. *)
Definition compile_encode_log_topic_def:
  compile_encode_log_topic val_op is_bytestring st =
    if is_bytestring then
      let (data_ptr, st1) = emit_op ADD [val_op; Lit 32w] st in
      let (length, st2) = emit_op MLOAD [val_op] st1 in
      emit_op SHA3 [data_ptr; length] st2
    else
      (val_op, st)
End

(* compile_store_bytestring moved before typed copy defs (forward ref) *)

(* ===== Load Memory ===== *)
(* Mirrors Python: context.py load_memory
   Primitive types: mload the value.
   Complex types: return the pointer. *)
Definition compile_load_memory_def:
  compile_load_memory ptr_op is_prim_word st =
    if is_prim_word then
      emit_op MLOAD [ptr_op] st
    else
      (ptr_op, st)
End

(* ===== Store Transient ===== *)
(* Full store_transient: primitive vs complex.
   Mirrors Python: context.py store_transient *)
Definition compile_store_transient_def:
  compile_store_transient val slot is_prim_word word_count st =
    if is_prim_word then
      emit_void TSTORE [slot; val] st
    else if word_count = 1 then
      let (loaded, st1) = emit_op MLOAD [val] st in
      emit_void TSTORE [slot; loaded] st1
    else
      let (_, st1) = compile_memory_to_transient val slot word_count st in
      ((), st1)
End

Definition compile_dynarray_to_storage_def:
  compile_dynarray_to_storage src_ptr dst_slot elem_words elem_mem_size transient st =
    (* Load length *)
    let (len_op, st1) = emit_op MLOAD [src_ptr] st in
    (* Create loop blocks *)
    let (cond_lbl, st2) = fresh_label "dyn_cond" st1 in
    let (body_lbl, st3) = fresh_label "dyn_body" st2 in
    let (exit_lbl, st4) = fresh_label "dyn_exit" st3 in
    (* Entry: counter = 0 *)
    let (counter, st5) = fresh_var st4 in
    let (_, st6) = emit_inst ASSIGN [Lit 0w] [counter] st5 in
    let (_, st7) = emit_inst JMP [Label cond_lbl] [] st6 in
    (* Cond: counter < length *)
    let (_, st8) = new_block cond_lbl st7 in
    let (lt_op, st9) = emit_op LT [Var counter; len_op] st8 in
    let (done_op, st10) = emit_op ISZERO [lt_op] st9 in
    let (_, st11) = emit_inst JNZ [done_op; Label exit_lbl; Label body_lbl] [] st10 in
    (* Body: copy one element *)
    let (_, st12) = new_block body_lbl st11 in
    if elem_words = 1 then
      (* Simple case: single word per element.
         src_offset = 32 + counter * 32, dst = dst_slot + 1 + counter *)
      let (mul_op, st13) = emit_op MUL [Var counter; Lit 32w] st12 in
      let (src_off, st14) = emit_op ADD [Lit 32w; mul_op] st13 in
      let (src_elem, st15) = emit_op ADD [src_ptr; src_off] st14 in
      let (val_op, st16) = emit_op MLOAD [src_elem] st15 in
      let (slot_off, st17) = emit_op ADD [Var counter; Lit 1w] st16 in
      let (dst_elem, st18) = emit_op ADD [dst_slot; slot_off] st17 in
      let (_, st19) = (if transient then emit_void TSTORE [dst_elem; val_op]
                       else emit_void SSTORE [dst_elem; val_op]) st18 in
      (* Increment counter *)
      let (new_ctr, st20) = emit_op ADD [Var counter; Lit 1w] st19 in
      let (_, st21) = emit_inst ASSIGN [new_ctr] [counter] st20 in
      let (_, st22) = emit_inst JMP [Label cond_lbl] [] st21 in
      (* Exit: store length *)
      let (_, st23) = new_block exit_lbl st22 in
      (if transient then emit_void TSTORE [dst_slot; len_op]
       else emit_void SSTORE [dst_slot; len_op]) st23
    else
      (* Multi-word elements: src_offset = 32 + counter * elem_mem_size,
         dst_slot_i = dst_slot + 1 + counter * elem_words.
         Uses word_copy_loop for each element.
         Mirrors Python: stmt.py _copy_dynarray_to_storage complex case *)
      let (mul_op, st13) = emit_op MUL [Var counter; Lit (n2w elem_mem_size)] st12 in
      let (src_off, st14) = emit_op ADD [Lit 32w; mul_op] st13 in
      let (src_elem, st15) = emit_op ADD [src_ptr; src_off] st14 in
      let (slot_mul, st16) = emit_op MUL [Var counter; Lit (n2w elem_words)] st15 in
      let (slot_off, st17) = emit_op ADD [Lit 1w; slot_mul] st16 in
      let (dst_elem, st18) = emit_op ADD [dst_slot; slot_off] st17 in
      let (_, st19) = compile_word_copy_loop src_elem dst_elem elem_words
                         LocMemory (if transient then LocTransient else LocStorage)
                         F st18 in
      (* Increment counter *)
      let (new_ctr, st20) = emit_op ADD [Var counter; Lit 1w] st19 in
      let (_, st21) = emit_inst ASSIGN [new_ctr] [counter] st20 in
      let (_, st22) = emit_inst JMP [Label cond_lbl] [] st21 in
      (* Exit: store length *)
      let (_, st23) = new_block exit_lbl st22 in
      (if transient then emit_void TSTORE [dst_slot; len_op]
       else emit_void SSTORE [dst_slot; len_op]) st23
End

(* Helper: ILOAD word-by-word to memory buffer (ctor, no immutables_alloca).
   Python: load_immutable_ctor without alloca uses iload per word.
   Can't use compile_word_copy_loop because LocCode dispatches to DLOAD. *)
Definition compile_iload_to_memory_def:
  compile_iload_to_memory src_offset dst_buf 0 st = ((), st) ∧
  compile_iload_to_memory src_offset dst_buf (SUC n) st =
    let byte_off = n * 32 in
    let (imm_off, st1) = emit_op ADD [src_offset; Lit (n2w byte_off)] st in
    let (word_op, st2) = emit_op ILOAD [imm_off] st1 in
    let (mem_ptr, st3) = emit_op ADD [dst_buf; Lit (n2w byte_off)] st2 in
    let (_, st4) = emit_void MSTORE [mem_ptr; word_op] st3 in
    compile_iload_to_memory src_offset dst_buf n st4
End

(* Helper: copy from GEP-based source to memory buffer, word by word.
   Mirrors the loop in Python load_immutable_ctor for complex types. *)
Definition compile_gep_to_memory_def:
  compile_gep_to_memory src_base src_offset dst_buf 0 st = ((), st) ∧
  compile_gep_to_memory src_base src_offset dst_buf (SUC n) st =
    let (imm_off, st1) = emit_op ADD [src_offset; Lit (n2w (n * 32))] st in
    let (ptr, st2) = emit_op GEP [src_base; imm_off] st1 in
    let (word_op, st3) = emit_op MLOAD [ptr] st2 in
    let (mem_ptr, st4) = emit_op ADD [dst_buf; Lit (n2w (n * 32))] st3 in
    let (_, st5) = emit_void MSTORE [mem_ptr; word_op] st4 in
    compile_gep_to_memory src_base src_offset dst_buf n st5
End

(* ===== Load Immutable (Constructor) ===== *)
(* Mirrors Python: context.py load_immutable_ctor
   During constructor, immutables live in an alloca'd buffer.
   If immutables_alloca is available, use GEP + MLOAD.
   Otherwise, fall back to ILOAD (same as runtime).
   NOTE: Currently unused — will be wired in when constructor immutable
   loading is added to compile_expr. The SOME imm_alloca (GEP) path
   has no direct Python equivalent; Python always uses iload/dload. *)
Definition compile_load_immutable_ctor_def:
  compile_load_immutable_ctor offset is_prim_word word_count alloca_size
                              imm_alloca_opt st =
    case imm_alloca_opt of
      NONE =>
        (* No immutables_alloca: use ILOAD (ctor pseudo-instruction).
           Python: load_immutable_ctor without alloca uses iload, NOT dload.
           DLOAD reads deployed CODE — doesn't exist during constructor. *)
        if is_prim_word then
          emit_op ILOAD [offset] st
        else
                    let (buf_op_alloc, st2) = compile_alloc_buffer alloca_size st in
                    let buf_op = buf_op_alloc.buf_operand in
          (* Use iload_to_memory — word_copy_loop with LocCode uses DLOAD *)
          let (_, st3) =
            compile_iload_to_memory offset buf_op word_count st2 in
          (buf_op, st3)
    | SOME imm_alloca =>
      if is_prim_word then
        let (ptr, st1) = emit_op GEP [imm_alloca; offset] st in
        emit_op MLOAD [ptr] st1
      else
                let (buf_op_alloc, st2) = compile_alloc_buffer alloca_size st in
                let buf_op = buf_op_alloc.buf_operand in
        let (_, st3) =
          compile_gep_to_memory imm_alloca offset buf_op word_count st2 in
        (buf_op, st3)
End
