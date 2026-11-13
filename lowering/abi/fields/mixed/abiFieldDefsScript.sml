(* TOP-LEVEL: concrete observations for mixed native ABI fields. Source
   predicates describe initial memory and ownership, without execution callbacks. *)
Theory abiFieldDefs
Ancestors
  abiFlatFieldsDefs abiFieldLayoutDefs abiAllocatedWindows abiBytesArrayModel
  memoryValueDefs valueEncoding vyperABI vyperValue vyperTyping compileEnv venomState
  contractABI list words

Datatype:
  abi_field = AbiFieldFlat abi_flat_field
            | AbiFieldDynBytes vyperAST$type type_value num (vyperValue$value list) ((word8 list) list)
End

Definition abi_field_entry_def:
  abi_field_entry sfields cenv (AbiFieldFlat row) = abi_flat_entry row /\
  abi_field_entry sfields cenv (AbiFieldDynBytes ty tv capacity vs bss) =
    (type_to_abi_enc_info sfields cenv (ArrayT ty (Dynamic capacity)),32,
      type_memory_size (ArrayTV tv (Dynamic capacity)),T)
End

Definition abi_field_output_def:
  abi_field_output (AbiFieldFlat row) = abi_flat_output row /\
  abi_field_output (AbiFieldDynBytes ty tv capacity vs bss) =
    (T,enc (Array NONE (Bytes NONE)) (ListV (MAP contractABI$BytesV bss)))
End

Definition abi_field_mem_size_def:
  abi_field_mem_size (AbiFieldFlat row) = abi_flat_mem_size row /\
  abi_field_mem_size (AbiFieldDynBytes ty tv capacity vs bss) = type_memory_size (ArrayTV tv (Dynamic capacity))
End

Definition abi_field_source_count_def:
  abi_field_source_count (AbiFieldFlat row) = abi_flat_source_count row /\
  abi_field_source_count (AbiFieldDynBytes ty tv capacity vs bss) = type_memory_size (ArrayTV tv (Dynamic capacity))
End

Definition abi_field_valid_def:
  (abi_field_valid tenv (AbiFieldFlat row) <=> abi_flat_valid row) /\
  (abi_field_valid tenv (AbiFieldDynBytes ty tv capacity vs bss) <=>
    is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\
    value_has_type (ArrayTV tv (Dynamic capacity)) (ArrayV (DynArrayV vs)) /\
    LIST_REL (\v bs. raw_return_bytes v = SOME bs) vs bss)
End

Definition abi_field_source_def:
  (abi_field_source (AbiFieldFlat row) src_addr tail_addr ss <=> abi_flat_source row src_addr tail_addr ss) /\
  (abi_field_source (AbiFieldDynBytes ty tv capacity vs bss) src_addr tail_addr ss <=>
    memory_value_rel (ArrayTV tv (Dynamic capacity)) (ArrayV (DynArrayV vs)) (w2n src_addr) ss.vs_memory)
End

Definition abi_field_sources_def:
  (abi_field_sources [] source_id root_addr source_offset dst_addr tail_cursor ss <=> T) /\
  (abi_field_sources (row::rest) source_id root_addr source_offset dst_addr tail_cursor ss <=>
    abi_field_source row (root_addr + n2w source_offset) (dst_addr + n2w tail_cursor) ss /\
    abi_allocated_window ss source_id (w2n (root_addr + n2w source_offset)) (abi_field_source_count row) /\
    abi_field_sources rest source_id root_addr (source_offset + abi_field_mem_size row) dst_addr
      (tail_cursor + abi_field_tail_size [abi_field_output row]) ss)
End
