(* TOP-LEVEL: dynamic-child array memory records the complete raw source,
   length headers, completed ABI heads/tails and the two live loop counters.
   A complete invariant yields the full packed array bytes and byte count. *)
Theory abiNativeDynamicArrayState
Ancestors
  abiMemoryEncoding abiFieldMemory abiFieldLayoutDefs valueEncoding memoryReadProps compileEnv
  venomMemDefs venomState list rich_list words arithmetic

Definition abi_native_dynamic_array_data_def:
  abi_native_dynamic_array_data info width stride fields (dst_addr:bytes32) (root_addr:bytes32)
      (counter_addr:bytes32) (dyn_addr:bytes32) source_capacity index ss <=>
    32 <= source_capacity /\ index <= LENGTH fields /\
    abi_memory_fields (REPLICATE (LENGTH fields) (info,width,stride,T))
      (w2n root_addr + 32) (source_capacity - 32) ss.vs_memory fields /\
    mload (w2n root_addr) ss = n2w (LENGTH fields) /\ mload (w2n dst_addr) ss = n2w (LENGTH fields) /\
    abi_fields_layout (TAKE index fields) (w2n dst_addr + 32) 0 (abi_field_head_size fields) ss /\
    mload (w2n counter_addr) ss = n2w index /\
    mload (w2n dyn_addr) ss = n2w (abi_field_head_size fields + abi_field_tail_size (TAKE index fields))
End

Theorem abi_native_dynamic_array_initial:
  !info width stride fields dst_addr root_addr counter_addr dyn_addr source_capacity ss.
    32 <= source_capacity /\
    abi_memory_fields (REPLICATE (LENGTH fields) (info,width,stride,T))
      (w2n root_addr + 32) (source_capacity - 32) ss.vs_memory fields /\
    mload (w2n root_addr) ss = n2w (LENGTH fields) /\ mload (w2n dst_addr) ss = n2w (LENGTH fields) /\
    mload (w2n counter_addr) ss = 0w /\ mload (w2n dyn_addr) ss = n2w (abi_field_head_size fields) ==>
    abi_native_dynamic_array_data info width stride fields dst_addr root_addr counter_addr dyn_addr source_capacity 0 ss
Proof
  simp[abi_native_dynamic_array_data_def]
QED

Theorem abi_native_dynamic_array_data_memory:
  !info width stride fields dst_addr root_addr counter_addr dyn_addr source_capacity index before after.
    after.vs_memory = before.vs_memory ==>
    (abi_native_dynamic_array_data info width stride fields dst_addr root_addr counter_addr dyn_addr source_capacity index after <=>
     abi_native_dynamic_array_data info width stride fields dst_addr root_addr counter_addr dyn_addr source_capacity index before)
Proof
  rpt gen_tac >> DISCH_TAC >> simp[abi_native_dynamic_array_data_def, abi_fields_layout_def, read_memory_def, mload_def]
QED

Theorem abi_native_dynamic_array_complete:
  !info width stride fields dst_addr root_addr counter_addr dyn_addr source_capacity ss.
    abi_native_dynamic_array_data info width stride fields dst_addr root_addr counter_addr dyn_addr source_capacity (LENGTH fields) ss ==>
    read_memory (w2n dst_addr)
      (LENGTH (word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields)) ss =
      word_to_bytes (n2w (LENGTH fields):bytes32) T ++ abi_field_bytes (abi_field_head_size fields) fields /\
    mload (w2n counter_addr) ss = n2w (LENGTH fields) /\
    mload (w2n dyn_addr) ss = n2w (LENGTH (abi_field_bytes (abi_field_head_size fields) fields))
Proof
  rpt gen_tac >> DISCH_TAC >>
  qpat_x_assum `abi_native_dynamic_array_data _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [abi_native_dynamic_array_data_def]) >>
  drule abi_fields_layout_contiguous >> DISCH_TAC >>
  `LENGTH (word_to_bytes (n2w (LENGTH fields):bytes32) T) = 32` by simp[] >>
  conj_tac
  >- (asm_simp_tac bool_ss [LENGTH_APPEND] >>
      CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [read_memory_split])) >>
      asm_simp_tac bool_ss [read_memory_word]) >>
  asm_simp_tac (srw_ss()) []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed raw dynamic-child array memory invariant: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayState")
