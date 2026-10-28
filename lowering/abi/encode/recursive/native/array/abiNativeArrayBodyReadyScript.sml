(* TOP-LEVEL: a length-prefixed array's owned output supplies both its
   recursive body resources and the separately retained length header. *)
Theory abiNativeArrayBodyReady
Ancestors
  abiNativeResources abiNativeEncodingDefs abiAllocationTrace abiAllocatedSubwindows abiAllocatedWindows abiFieldBytesPath
  compileAllocaProvenance compileEnv fragExec venomState list words arithmetic

Theorem abi_native_array_body_ready:
  !func cs after source_id target_id root_addr source_capacity (dst_addr:bytes32) length_word body_bytes ss.
    abi_native_memory_ready func cs after source_id target_id root_addr source_capacity dst_addr
      (word_to_bytes (length_word:bytes32) T ++ body_bytes) ss ==>
    abi_native_memory_ready func cs after source_id target_id root_addr source_capacity (dst_addr + 32w) body_bytes ss /\
    abi_allocated_window ss target_id (w2n dst_addr) 32 /\ w2n (dst_addr + 32w) = w2n dst_addr + 32
Proof
  rpt gen_tac >> strip_tac >> `compiler_id_history cs` by fs[abi_native_memory_ready_def] >>
  drule abi_native_memory_bounds >> strip_tac >>
  `w2n (dst_addr + 32w) = w2n dst_addr + 32` by
    (irule abi_field_word_address >> qpat_x_assum `w2n dst_addr + LENGTH _ < _` mp_tac >> simp[] >> decide_tac) >>
  qspecl_then [`func`, `cs`, `after`, `source_id`, `target_id`, `root_addr`, `source_capacity`, `dst_addr`,
    `word_to_bytes (length_word:bytes32) T ++ body_bytes`, `ss`, `cs`, `after`, `ss`, `root_addr`, `source_capacity`, `dst_addr + 32w`, `body_bytes`]
    mp_tac abi_native_child_ready >>
  impl_tac >- simp[cs_extends_refl, abi_allocation_trace_identity] >> DISCH_TAC >>
  `abi_allocated_window ss target_id (w2n dst_addr) (LENGTH (word_to_bytes (length_word:bytes32) T ++ body_bytes))` by
    fs[abi_native_memory_ready_def] >>
  qspecl_then [`ss`, `target_id`, `w2n dst_addr`, `LENGTH (word_to_bytes (length_word:bytes32) T ++ body_bytes)`, `w2n dst_addr`, `32`]
    mp_tac abi_allocated_window_subwindow >> impl_tac >- simp[] >> DISCH_TAC >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed native array body and length-header resources: " ^ name)
  end) (DB.thms "abiNativeArrayBodyReady")
