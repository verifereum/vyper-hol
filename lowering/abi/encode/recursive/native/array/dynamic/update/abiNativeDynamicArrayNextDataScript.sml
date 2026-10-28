(* TOP-LEVEL: the next packed layout and counter values rebuild the full
   array invariant. Its source and destination length header follow from
   the actual enclosing traversal and retained header allocation. *)
Theory abiNativeDynamicArrayNextData
Ancestors
  abiNativeDynamicArrayState abiNativeArraySource abiNativeTraversalRead abiNativeTraversal abiNativeEncodingDefs
  abiAllocatedWindows abiFieldMemory abiFieldLayoutDefs abiMemoryFrame memoryReadProps compileAllocaProvenance
  compileEnv venomMemDefs venomState list words arithmetic

Theorem abi_native_dynamic_array_data_traversal:
  !ctx func cs after source_id target_id root_addr source_capacity dst_addr fields info width stride initial
      point ss index counter_addr dyn_addr.
    abi_native_memory_ready func cs after source_id target_id root_addr source_capacity (dst_addr + 32w)
      (abi_field_bytes (abi_field_head_size fields) fields) initial /\
    abi_native_traversal ctx func cs after (dst_addr + 32w) (abi_field_bytes (abi_field_head_size fields) fields) initial point ss /\
    abi_native_dynamic_array_data info width stride fields dst_addr root_addr counter_addr dyn_addr source_capacity 0 initial /\
    abi_allocated_window initial target_id (w2n dst_addr) 32 /\ w2n (dst_addr + 32w) = w2n dst_addr + 32 /\
    index <= LENGTH fields /\
    abi_fields_layout (TAKE index fields) (w2n dst_addr + 32) 0 (abi_field_head_size fields) ss /\
    mload (w2n counter_addr) ss = n2w index /\
    mload (w2n dyn_addr) ss = n2w (abi_field_head_size fields + abi_field_tail_size (TAKE index fields)) ==>
    abi_native_dynamic_array_data info width stride fields dst_addr root_addr counter_addr dyn_addr source_capacity index ss
Proof
  rpt gen_tac >> strip_tac >>
  `alloca_inv initial /\ ~MEM target_id (compiler_alloca_ids cs after)` by fs[abi_native_memory_ready_def] >>
  qpat_assum `abi_native_dynamic_array_data _ _ _ _ _ _ _ _ _ _ initial`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_dynamic_array_data_def]) >>
  qspecl_then [`ctx`, `func`, `cs`, `after`, `source_id`, `target_id`, `root_addr`, `source_capacity`,
    `dst_addr + 32w`, `abi_field_bytes (abi_field_head_size fields) fields`, `initial`, `point`, `ss`,
    `REPLICATE (LENGTH fields) (info,width,stride,T)`, `fields`, `n2w (LENGTH fields)`]
    mp_tac abi_native_array_source >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `mload (w2n dst_addr) ss = mload (w2n dst_addr) initial` by
    (qspecl_then [`ctx`, `func`, `cs`, `after`, `dst_addr + 32w`, `abi_field_bytes (abi_field_head_size fields) fields`,
       `initial`, `point`, `ss`, `target_id`, `w2n dst_addr`, `32`] mp_tac abi_native_traversal_owned_read >>
     impl_tac >- asm_simp_tac (srw_ss()) [abi_window_separated_def, compileEnvTheory.regions_disjoint_def] >>
     disch_then (mp_tac o AP_TERM ``word_of_bytes T (0w:bytes32)``) >>
     simp_tac bool_ss [GSYM mload_read_memory]) >>
  asm_simp_tac bool_ss [abi_native_dynamic_array_data_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed next dynamic array source, header and full data invariant: " ^ name)
  end) (DB.thms "abiNativeDynamicArrayNextData")
